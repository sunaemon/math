#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Applicative ((<|>))
import Control.Exception (IOException, catch)
import Control.Monad (forM_, guard, unless, when)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit, isLetter, isSpace)
import Data.Foldable (asum)
import Data.IORef
import Data.List (find, foldl', intercalate, isPrefixOf, sortOn, stripPrefix)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe)
import Data.Ord (Down (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs, lookupEnv)
import System.Exit
import System.IO
import Text.Pandoc.JSON
import Text.Pandoc.Walk (query, walk, walkM)

import DependencyGraph (
  OptimizationConfig (..),
  planCacheNodes,
  planCacheSignature,
  planDependencyGraph,
  readDependencyLayoutCache,
  renderDependencyGraph,
  writeDependencyLayoutCache,
 )
import SectionRef (nextSectionRef)

main :: IO ()
main = do
  args <- getArgs
  case args of
    "lint" : rest -> lintMain rest
    "inject-booklinks" : rest -> injectBooklinksMain rest
    _ -> toJSONFilter processDoc

data LintConfig = LintConfig
  { lintMaxLineLength :: Int
  , lintMaxReports :: Int
  , lintFix :: Bool
  , lintMacros :: Maybe FilePath
  , lintPaths :: [FilePath]
  }

data RawNotationRule = RawNotationRule
  { rawNotationPattern :: Text
  , rawNotationReplacement :: Text
  , rawNotationReason :: Text
  , rawNotationFixKind :: RawNotationFixKind
  }

data RawNotationFixKind = RawNotationLiteral | RawNotationBinaryOperator | RawNotationUnarySubscript

data RawNotationLintTag = RawNotationLintEnforce | RawNotationLintIgnore

defaultLintConfig :: LintConfig
defaultLintConfig =
  LintConfig
    { lintMaxLineLength = 120
    , lintMaxReports = 40
    , lintFix = False
    , lintMacros = Nothing
    , lintPaths = []
    }

lintMain :: [String] -> IO ()
lintMain args =
  case parseLintArgs defaultLintConfig args of
    Left message -> do
      hPutStrLn stderr ("book-filter lint: " <> message)
      hPutStrLn stderr "usage: book-filter lint [--fix] [--macros=FILE] [--max-line-length=N] [--max-reports=N] FILE..."
      exitWith (ExitFailure 2)
    Right config -> do
      rawNotationRules <- maybe (return []) readRawNotationRules (lintMacros config)
      when (lintFix config) $
        mapM_ (fixLintSource config rawNotationRules) (lintPaths config)
      headerIds <- collectLintHeaderIds (lintPaths config)
      violations <- concat <$> mapM (lintSource config rawNotationRules headerIds) (lintPaths config)
      unless (null violations) $ do
        hPutStrLn stderr "[lint] source lint failed:"
        forM_ (take (lintMaxReports config) violations) $ \violation ->
          hPutStrLn stderr ("  " <> violation)
        let remaining = length violations - lintMaxReports config
        unless (remaining <= 0) $
          hPutStrLn stderr ("  ... " <> show remaining <> " more")
        exitWith (ExitFailure 1)

parseLintArgs :: LintConfig -> [String] -> Either String LintConfig
parseLintArgs config [] =
  if null (lintPaths config)
    then Left "missing input file"
    else Right config
parseLintArgs config (arg : rest)
  | arg == "--fix" =
      parseLintArgs config{lintFix = True} rest
  | Just raw <- stripPrefix "--macros=" arg =
      if null raw
        then Left "empty --macros value"
        else parseLintArgs config{lintMacros = Just raw} rest
  | Just raw <- stripPrefix "--max-line-length=" arg =
      case readMaybeInt raw of
        Just value
          | value > 0 ->
              parseLintArgs config{lintMaxLineLength = value} rest
        _ ->
          Left ("invalid --max-line-length value: " <> raw)
  | Just raw <- stripPrefix "--max-reports=" arg =
      case readMaybeInt raw of
        Just value
          | value > 0 ->
              parseLintArgs config{lintMaxReports = value} rest
        _ ->
          Left ("invalid --max-reports value: " <> raw)
  | Just _ <- stripPrefix "-" arg =
      Left ("unknown option: " <> arg)
  | otherwise =
      parseLintArgs config{lintPaths = lintPaths config <> [arg]} rest

lintSource :: LintConfig -> [RawNotationRule] -> Set Text -> FilePath -> IO [String]
lintSource config rawNotationRules headerIds path = do
  contents <- TIO.readFile path
  return
    ( lintLineLength config path contents
        ++ lintRawNotation rawNotationRules path contents
        ++ lintDanglingSectionRefs headerIds path contents
    )

lintLineLength :: LintConfig -> FilePath -> Text -> [String]
lintLineLength config path contents =
  [ path
      <> ":"
      <> show lineNumber
      <> ": line length "
      <> show width
      <> " > "
      <> show (lintMaxLineLength config)
  | (lineNumber, line) <- zip [(1 :: Int) ..] (T.lines contents)
  , let width = T.length line
  , width > lintMaxLineLength config
  ]

lintRawNotation :: [RawNotationRule] -> FilePath -> Text -> [String]
lintRawNotation rawNotationRules path contents =
  concat
    [ lintRawNotationLine rawNotationRules path lineNumber line
    | (lineNumber, line) <- zip [(1 :: Int) ..] (T.lines contents)
    ]

lintRawNotationLine :: [RawNotationRule] -> FilePath -> Int -> Text -> [String]
lintRawNotationLine rawNotationRules path lineNumber line =
  concatMap reportRule rawNotationRules
 where
  reportRule rule =
    [ path
        <> ":"
        <> show lineNumber
        <> ":"
        <> show column
        <> ": prohibited raw notation "
        <> T.unpack (rawNotationPattern rule)
        <> "; use "
        <> T.unpack (rawNotationReplacement rule)
        <> " instead"
        <> reasonSuffix rule
    | column <- textColumns (rawNotationPattern rule) line
    ]

  reasonSuffix rule
    | T.null (rawNotationReason rule) = ""
    | otherwise = " (" <> T.unpack (rawNotationReason rule) <> ")"

collectLintHeaderIds :: [FilePath] -> IO (Set Text)
collectLintHeaderIds paths =
  Set.unions <$> mapM collectPathHeaderIds paths
 where
  collectPathHeaderIds path =
    collectMarkdownHeaderIds <$> TIO.readFile path

lintDanglingSectionRefs :: Set Text -> FilePath -> Text -> [String]
lintDanglingSectionRefs headerIds path contents =
  [ path
      <> ":"
      <> show lineNumber
      <> ":"
      <> show column
      <> ": dangling section reference "
      <> T.unpack hid
      <> "; no matching Markdown header id"
  | (lineNumber, line) <- zip [(1 :: Int) ..] (T.lines contents)
  , (column, hid) <- sectionRefsInLine line
  , hid `Set.notMember` headerIds
  ]

collectMarkdownHeaderIds :: Text -> Set Text
collectMarkdownHeaderIds contents =
  Set.fromList (mapMaybe markdownHeaderId (T.lines contents))

markdownHeaderId :: Text -> Maybe Text
markdownHeaderId line = do
  let stripped = T.stripStart line
      (hashes, afterHashes) = T.span (== '#') stripped
  guard (not (T.null hashes))
  guard (T.length hashes <= 6)
  guard (" " `T.isPrefixOf` afterHashes)
  let body = T.strip afterHashes
      (_beforeMarker, afterMarker) = T.breakOnEnd "{#" body
  guard (not (T.null afterMarker))
  let (hid, afterId) = T.span (\char -> not (isSpace char) && char /= '}') afterMarker
  guard (not (T.null hid))
  guard ("}" `T.isInfixOf` afterId)
  return hid

sectionRefsInLine :: Text -> [(Int, Text)]
sectionRefsInLine = go 1
 where
  go offset txt =
    case nextSectionRef txt of
      Nothing -> []
      Just (before, hid, after) ->
        -- column is the 1-based position of the § sign; afterOffset steps past
        -- "§{" + id + "}". Empty ids (§{}) are skipped, not reported.
        let column = offset + T.length before
            afterOffset = column + 2 + T.length hid + 1
            rest = go afterOffset after
         in if T.null hid then rest else (column, hid) : rest

fixLintSource :: LintConfig -> [RawNotationRule] -> FilePath -> IO ()
fixLintSource config rawNotationRules path = do
  contents <- TIO.readFile path
  let fixedNotation = fixRawNotation rawNotationRules contents
      fixed = T.unlines (concatMap (wrapLintLine (lintMaxLineLength config)) (T.lines fixedNotation))
  when (fixed /= contents) $
    TIO.writeFile path fixed

fixRawNotation :: [RawNotationRule] -> Text -> Text
fixRawNotation rawNotationRules content =
  foldl' applyRule content (prioritizedRawNotationRules rawNotationRules)
 where
  applyRule source rule =
    case rawNotationFixKind rule of
      RawNotationLiteral ->
        T.replace (rawNotationPattern rule) (rawNotationReplacement rule) source
      RawNotationBinaryOperator ->
        fixBinaryRawNotation rule source
      RawNotationUnarySubscript ->
        fixUnarySubscriptRawNotation rule source

prioritizedRawNotationRules :: [RawNotationRule] -> [RawNotationRule]
prioritizedRawNotationRules =
  sortOn (Down . T.length . rawNotationPattern)

-- Read the semantic-macros file, failing with a labeled message and a fix hint
-- instead of a raw IOException when the configured macros-file path is wrong or
-- unreadable.
readMacrosFile :: Text -> FilePath -> IO Text
readMacrosFile label path =
  TIO.readFile path `catch` \e -> do
    hPutStrLn stderr ("[" <> T.unpack label <> "] cannot read macros file:")
    hPutStrLn stderr ("  path: " <> path)
    hPutStrLn stderr ("  " <> show (e :: IOException))
    hPutStrLn stderr "  check the macros-file: field in the document metadata"
    exitFailure

readRawNotationRules :: FilePath -> IO [RawNotationRule]
readRawNotationRules path = do
  content <- readMacrosFile "lint" path
  return (collectRawNotationRules path Nothing (T.lines content))

collectRawNotationRules :: FilePath -> Maybe RawNotationLintTag -> [Text] -> [RawNotationRule]
collectRawNotationRules _ _ [] = []
collectRawNotationRules path pending (line : rest)
  | Just tag <- parseRawNotationLintTag line =
      collectRawNotationRules path (Just tag) rest
  | Just (name, body) <- parseNewCommandBody line =
      case pending of
        Just RawNotationLintEnforce ->
          maybe id (:) (rawNotationRuleFromMacro path name body) (collectRawNotationRules path Nothing rest)
        _ ->
          collectRawNotationRules path Nothing rest
  | T.null (T.strip line) || "%" `T.isPrefixOf` T.strip line =
      collectRawNotationRules path pending rest
  | otherwise =
      collectRawNotationRules path Nothing rest

parseRawNotationLintTag :: Text -> Maybe RawNotationLintTag
parseRawNotationLintTag line = do
  raw <- T.strip <$> T.stripPrefix "% lint-raw-notation:" (T.strip line)
  case raw of
    "enforce" -> Just RawNotationLintEnforce
    "ignore" -> Just RawNotationLintIgnore
    _ -> Nothing

rawNotationRuleFromMacro :: FilePath -> Text -> Text -> Maybe RawNotationRule
rawNotationRuleFromMacro path name body =
  unarySubscriptRule <|> binaryOperatorRule <|> literalRule
 where
  replacement = "\\" <> name

  literalRule = do
    raw <- normalizeRawNotationBody body
    guard ("\\" `T.isPrefixOf` raw)
    guard (not ("#" `T.isInfixOf` raw))
    guard (raw /= replacement)
    return
      RawNotationRule
        { rawNotationPattern = raw
        , rawNotationReplacement = replacement
        , rawNotationReason = "semantic macro is tagged in " <> T.pack path
        , rawNotationFixKind = RawNotationLiteral
        }

  binaryOperatorRule = do
    raw <- normalizeRawNotationBody body
    operator <- parseBinaryOperatorBody raw
    guard (operator /= replacement)
    return
      RawNotationRule
        { rawNotationPattern = operator
        , rawNotationReplacement = replacement
        , rawNotationReason = "binary semantic macro is tagged in " <> T.pack path
        , rawNotationFixKind = RawNotationBinaryOperator
        }

  unarySubscriptRule = do
    raw <- normalizeRawNotationBody body
    pattern <- parseUnarySubscriptBody raw
    guard (pattern /= replacement)
    return
      RawNotationRule
        { rawNotationPattern = pattern
        , rawNotationReplacement = replacement
        , rawNotationReason = "subscript semantic macro is tagged in " <> T.pack path
        , rawNotationFixKind = RawNotationUnarySubscript
        }

parseUnarySubscriptBody :: Text -> Maybe Text
parseUnarySubscriptBody body = do
  let stripped = T.strip body
      (base, afterBase) = T.breakOn "_" stripped
  guard ("\\" `T.isPrefixOf` base)
  guard (not (T.null afterBase))
  afterUnderscore <- T.stripPrefix "_" afterBase
  guard (T.all (not . isSpace) base)
  guard (afterUnderscore == "#1" || afterUnderscore == "{#1}")
  return (base <> "_")

parseBinaryOperatorBody :: Text -> Maybe Text
parseBinaryOperatorBody body = do
  afterFirstArg <- T.stripPrefix "#1" (T.strip body)
  let stripped = T.strip afterFirstArg
      (operator, afterOperator) = T.breakOn "#2" stripped
      rawOperator = T.strip operator
  guard (not (T.null rawOperator))
  guard (not (T.null afterOperator))
  guard (T.strip (T.drop 2 afterOperator) == "")
  guard ("\\" `T.isPrefixOf` rawOperator)
  guard (T.all (not . isSpace) rawOperator)
  return rawOperator

parseNewCommandBody :: Text -> Maybe (Text, Text)
parseNewCommandBody line = do
  rest <- T.stripPrefix "\\newcommand{\\" (T.strip line)
  let (name, afterName) = T.breakOn "}" rest
  guard (not (T.null name) && not (T.null afterName))
  body <- parseNewCommandReplacement (T.drop 1 afterName)
  return (name, body)

parseNewCommandReplacement :: Text -> Maybe Text
parseNewCommandReplacement afterName =
  let (_, afterArgCount) = parseArgCount afterName
      afterOptional = dropOptionalDefault afterArgCount
   in parseBracedGroup (T.stripStart afterOptional)

dropOptionalDefault :: Text -> Text
dropOptionalDefault txt =
  case T.stripPrefix "[" (T.stripStart txt) of
    Nothing -> txt
    Just rest ->
      let (inside, afterInside) = T.breakOn "]" rest
       in if T.null afterInside && not (T.null inside)
            then txt
            else T.drop 1 afterInside

parseBracedGroup :: Text -> Maybe Text
parseBracedGroup txt = do
  rest <- T.stripPrefix "{" txt
  let (depth, current, _after) = T.foldl' step (1 :: Int, "", Nothing :: Maybe Text) rest
  guard (depth == 0)
  return current
 where
  step done@(_, _, Just _) _ = done
  step (depth, current, Nothing) char
    | char == '{' =
        (depth + 1, current <> T.singleton char, Nothing)
    | char == '}' && depth == 1 =
        (0, current, Just "")
    | char == '}' =
        (depth - 1, current <> T.singleton char, Nothing)
    | otherwise =
        (depth, current <> T.singleton char, Nothing)

normalizeRawNotationBody :: Text -> Maybe Text
normalizeRawNotationBody body =
  let stripped = T.strip body
      unwrapped = fromMaybe stripped (parseBracedGroup stripped)
      wrapperUnwrapped = fromMaybe unwrapped (unwrapRawNotationWrapper unwrapped)
      normalized = T.strip wrapperUnwrapped
   in if normalized == stripped
        then Just normalized
        else normalizeRawNotationBody normalized

unwrapRawNotationWrapper :: Text -> Maybe Text
unwrapRawNotationWrapper txt =
  asum
    [ unwrapCommandBody "\\mathrel" txt
    , unwrapCommandBody "\\mathbin" txt
    , unwrapCommandBody "\\mathord" txt
    ]

unwrapCommandBody :: Text -> Text -> Maybe Text
unwrapCommandBody command txt = do
  rest <- T.stripPrefix command (T.strip txt)
  parseBracedGroup (T.stripStart rest)

fixBinaryRawNotation :: RawNotationRule -> Text -> Text
fixBinaryRawNotation rule =
  T.pack
    . fixBinaryRawNotationString
      (T.unpack (rawNotationPattern rule))
      (T.unpack (rawNotationReplacement rule))
    . T.unpack

fixBinaryRawNotationString :: String -> String -> String -> String
fixBinaryRawNotationString pattern replacement source =
  case breakOnString pattern source of
    Nothing ->
      source
    Just (before, afterPattern) ->
      case (takeLeftOperand before, takeRightOperand afterPattern) of
        (Just (prefix, leftOperand), Just (rightOperand, suffix))
          | not (null (trimString leftOperand))
              && not (null (trimString rightOperand)) ->
              prefix
                <> replacement
                <> "{"
                <> fixBinaryRawNotationString pattern replacement (trimString leftOperand)
                <> "}{"
                <> fixBinaryRawNotationString pattern replacement (trimString rightOperand)
                <> "}"
                <> fixBinaryRawNotationString pattern replacement suffix
        _ ->
          before <> pattern <> fixBinaryRawNotationString pattern replacement afterPattern

fixUnarySubscriptRawNotation :: RawNotationRule -> Text -> Text
fixUnarySubscriptRawNotation rule =
  T.pack
    . fixUnarySubscriptRawNotationString
      (T.unpack (rawNotationPattern rule))
      (T.unpack (rawNotationReplacement rule))
    . T.unpack

fixUnarySubscriptRawNotationString :: String -> String -> String -> String
fixUnarySubscriptRawNotationString pattern replacement source =
  case breakOnString pattern source of
    Nothing ->
      source
    Just (before, afterPattern) ->
      case takeSubscriptArgument afterPattern of
        Just (argument, suffix)
          | not (null argument) ->
              before
                <> replacement
                <> "{"
                <> argument
                <> "}"
                <> fixUnarySubscriptRawNotationString pattern replacement suffix
        _ ->
          before <> pattern <> fixUnarySubscriptRawNotationString pattern replacement afterPattern

takeSubscriptArgument :: String -> Maybe (String, String)
takeSubscriptArgument source =
  case source of
    ('{' : _) -> do
      groupLength <- balancedGroupLength '{' '}' source
      let group = take groupLength source
      Just (drop 1 (take (groupLength - 1) group), drop groupLength source)
    ('\\' : _) ->
      let lengthOfCommand = commandLength source
       in guard (lengthOfCommand > 0)
            *> Just (splitAt lengthOfCommand source)
    (char : rest)
      | isLetter char ->
          let argument = char : takeWhile (\next -> isLetter next || isDigit next) rest
           in Just (argument, drop (length argument) source)
      | isDigit char ->
          let argument = char : takeWhile isDigit rest
           in Just (argument, drop (length argument) source)
      | otherwise ->
          Just ([char], rest)
    [] ->
      Nothing

breakOnString :: String -> String -> Maybe (String, String)
breakOnString needle = go ""
 where
  go _ "" = Nothing
  go prefix rest
    | needle `isPrefixOf` rest =
        Just (reverse prefix, drop (length needle) rest)
    | otherwise =
        go (head rest : prefix) (tail rest)

takeLeftOperand :: String -> Maybe (String, String)
takeLeftOperand source =
  let (trimmedSource, _trailingSpace) = trimRightWithSuffix source
      (prefix, operand) = splitLeftOperand trimmedSource
      (leadingSpace, operandWithoutLeadingSpace) = span isSpace operand
   in if null (trimString operandWithoutLeadingSpace)
        then Nothing
        else Just (prefix <> leadingSpace, operandWithoutLeadingSpace)

-- Scan right-to-left for the start of the left operand. Walks the reversed
-- string once, carrying 'forward' (the original-order suffix already scanned)
-- so the boundary-command check and the final split are O(1)/O(command) instead
-- of indexing the String with (!!) each step.
splitLeftOperand :: String -> (String, String)
splitLeftOperand source = go 0 0 0 [] (reverse source)
 where
  -- 'forward' = source[index+1 ..]; 'revRemaining' = reverse source[0..index].
  go _ _ _ forward [] = ("", forward)
  go parenDepth bracketDepth braceDepth forward revRemaining@(char : revRest) =
    case char of
      ')' -> descend (parenDepth + 1) bracketDepth braceDepth
      ']' -> descend parenDepth (bracketDepth + 1) braceDepth
      '}' -> descend parenDepth bracketDepth (braceDepth + 1)
      '('
        | parenDepth > 0 -> descend (parenDepth - 1) bracketDepth braceDepth
        | otherwise -> splitAfterChar
      '['
        | bracketDepth > 0 -> descend parenDepth (bracketDepth - 1) braceDepth
        | otherwise -> splitAfterChar
      '{'
        | braceDepth > 0 -> descend parenDepth bracketDepth (braceDepth - 1)
        | otherwise -> splitAfterChar
      _
        | depthsClear && isLeftBoundaryChar char ->
            splitAfterChar
        | depthsClear
            && char == '\\'
        , Just boundaryLength <- leftBoundaryCommandLength forwardAtIndex ->
            -- Split after the whole command: its tail (the L-1 chars past this
            -- backslash) lives in 'forward', so move it into the left part.
            ( reverse revRemaining ++ take (boundaryLength - 1) forward
            , drop (boundaryLength - 1) forward
            )
        | otherwise ->
            descend parenDepth bracketDepth braceDepth
   where
    depthsClear = parenDepth == 0 && bracketDepth == 0 && braceDepth == 0
    forwardAtIndex = char : forward
    splitAfterChar = (reverse revRemaining, forward)
    descend p b c = go p b c forwardAtIndex revRest

takeRightOperand :: String -> Maybe (String, String)
takeRightOperand source =
  let (_leadingSpace, rest) = span isSpace source
      (operand, suffix) = splitRightOperand rest
      (strippedOperand, punctuation) = stripRightMathPunctuation operand
   in if null (trimString strippedOperand)
        then Nothing
        else Just (strippedOperand, punctuation <> suffix)

-- Scan left-to-right for the end of the right operand. Walks the String once,
-- accumulating consumed characters (reversed) so 'rest' is just the current
-- tail; no (!!) indexing or repeated 'length source'.
splitRightOperand :: String -> (String, String)
splitRightOperand = go 0 0 0 []
 where
  go _ _ _ acc [] = (reverse acc, [])
  go parenDepth bracketDepth braceDepth acc rest@(char : more)
    | depthsClear && isRightBoundaryCommand rest = boundary
    | otherwise =
        case char of
          '(' -> consume (parenDepth + 1) bracketDepth braceDepth
          '[' -> consume parenDepth (bracketDepth + 1) braceDepth
          '{' -> consume parenDepth bracketDepth (braceDepth + 1)
          ')'
            | parenDepth > 0 -> consume (parenDepth - 1) bracketDepth braceDepth
            | otherwise -> boundary
          ']'
            | bracketDepth > 0 -> consume parenDepth (bracketDepth - 1) braceDepth
            | otherwise -> boundary
          '}'
            | braceDepth > 0 -> consume parenDepth bracketDepth (braceDepth - 1)
            | otherwise -> boundary
          _
            | depthsClear && isRightBoundaryChar char -> boundary
            | otherwise -> consume parenDepth bracketDepth braceDepth
   where
    depthsClear = parenDepth == 0 && bracketDepth == 0 && braceDepth == 0
    boundary = (reverse acc, rest)
    consume p b c = go p b c (char : acc) more

isLeftBoundaryChar :: Char -> Bool
isLeftBoundaryChar char =
  char `elem` ("$&=,:;\n" :: String)

isRightBoundaryChar :: Char -> Bool
isRightBoundaryChar char =
  char `elem` ("$&=,:;" :: String)

isLeftBoundaryCommand :: String -> Bool
isLeftBoundaryCommand source =
  commandAt source `elem` leftBoundaryCommands

leftBoundaryCommandLength :: String -> Maybe Int
leftBoundaryCommandLength source = do
  guard (isLeftBoundaryCommand source)
  Just (commandWithSuffixLength source)

isRightBoundaryCommand :: String -> Bool
isRightBoundaryCommand source =
  commandAt source `elem` rightBoundaryCommands

leftBoundaryCommands :: [String]
leftBoundaryCommands =
  [ "\\IncludedIn"
  , "\\StrictlyIncludedIn"
  , "\\in"
  , "\\notin"
  , "\\le"
  , "\\leq"
  , "\\ge"
  , "\\geq"
  , "\\to"
  , "\\mapsto"
  , "\\cong"
  , "\\equiv"
  , "\\quad"
  , "\\qquad"
  , "\\text"
  , "\\Longleftrightarrow"
  , "\\longleftrightarrow"
  , "\\Longrightarrow"
  , "\\longrightarrow"
  , "\\iff"
  , "\\begin"
  , "\\end"
  , "\\\\"
  ]

rightBoundaryCommands :: [String]
rightBoundaryCommands =
  leftBoundaryCommands
    <> [ "\\;"
       , "\\,"
       , "\\quad"
       , "\\qquad"
       , "\\tag"
       , "\\text"
       , "\\cup"
       , "\\cap"
       , "\\big"
       , "\\Big"
       , "\\bigl"
       , "\\bigr"
       , "\\Bigl"
       , "\\Bigr"
       , "\\right"
       , "\\\\"
       ]

commandAt :: String -> String
commandAt ('\\' : char : rest)
  | isLetter char =
      '\\' : char : takeWhile isLetter rest
  | otherwise =
      ['\\', char]
commandAt _ = ""

commandLength :: String -> Int
commandLength =
  length . commandAt

commandWithSuffixLength :: String -> Int
commandWithSuffixLength source =
  commandLength source + suffixLength (drop (commandLength source) source)

suffixLength :: String -> Int
suffixLength source =
  case source of
    ('_' : rest) ->
      1 + scriptLength rest + suffixLength (drop (scriptLength rest) rest)
    ('^' : rest) ->
      1 + scriptLength rest + suffixLength (drop (scriptLength rest) rest)
    ('{' : _) ->
      case balancedGroupLength '{' '}' source of
        Just groupLength -> groupLength + suffixLength (drop groupLength source)
        Nothing -> 0
    ('[' : _) ->
      case balancedGroupLength '[' ']' source of
        Just groupLength -> groupLength + suffixLength (drop groupLength source)
        Nothing -> 0
    _ ->
      0

scriptLength :: String -> Int
scriptLength source =
  case source of
    ('{' : _) -> fromMaybe 1 (balancedGroupLength '{' '}' source)
    ('\\' : _) -> commandLength source
    (char : rest)
      | isLetter char ->
          1 + length (takeWhile (\next -> isLetter next || isDigit next) rest)
      | isDigit char ->
          1 + length (takeWhile isDigit rest)
      | otherwise ->
          1
    [] ->
      0

balancedGroupLength :: Char -> Char -> String -> Maybe Int
balancedGroupLength open close source = do
  guard (not (null source) && head source == open)
  go 0 0 source
 where
  go _ _ [] = Nothing
  go index depth (char : rest)
    | char == open =
        go (index + 1) (depth + 1) rest
    | char == close && depth == 1 =
        Just (index + 1)
    | char == close =
        go (index + 1) (depth - 1) rest
    | otherwise =
        go (index + 1) depth rest

trimString :: String -> String
trimString =
  fst . trimRightWithSuffix . dropWhile isSpace

trimRightWithSuffix :: String -> (String, String)
trimRightWithSuffix source =
  let (suffixReversed, bodyReversed) = span isSpace (reverse source)
   in (reverse bodyReversed, reverse suffixReversed)

stripRightMathPunctuation :: String -> (String, String)
stripRightMathPunctuation source =
  case trimRightWithSuffix source of
    (body, spaceSuffix) ->
      let (punctuationReversed, strippedReversed) =
            span (`elem` (".," :: String)) (reverse body)
       in (reverse strippedReversed, reverse punctuationReversed <> spaceSuffix)

textColumns :: Text -> Text -> [Int]
textColumns needle haystack
  | T.null needle = []
  | otherwise = go 1 haystack
 where
  go offset rest =
    case T.breakOn needle rest of
      (before, after)
        | T.null after -> []
        | otherwise ->
            let column = offset + T.length before
                next = T.drop 1 after
             in column : go (column + 1) next

wrapLintLine :: Int -> Text -> [Text]
wrapLintLine maxLength line
  | T.length line <= maxLength = [line]
  | T.null (T.strip line) = [line]
  | isFenceLine stripped = [line]
  | isHeadingLine stripped = [line]
  | otherwise = wrapWords maxLength firstPrefix continuationPrefix body
 where
  stripped = T.stripStart line
  (firstPrefix, continuationPrefix, body) = linePrefixes line

linePrefixes :: Text -> (Text, Text, Text)
linePrefixes line =
  case parseUnorderedListPrefix line <|> parseOrderedListPrefix line of
    Just (prefix, body) ->
      (prefix, T.replicate (T.length prefix) " ", body)
    Nothing ->
      let (indent, body) = T.span (== ' ') line
       in (indent, indent, body)

parseUnorderedListPrefix :: Text -> Maybe (Text, Text)
parseUnorderedListPrefix line =
  let (indent, rest) = T.span (== ' ') line
   in case T.uncons rest of
        Just (marker, afterMarker)
          | marker `elem` ("*-" :: String)
          , T.length (T.takeWhile (== ' ') afterMarker) >= 1 ->
              let spaces = T.takeWhile (== ' ') afterMarker
                  body = T.drop (T.length spaces) afterMarker
               in Just (indent <> T.singleton marker <> spaces, body)
        _ ->
          Nothing

parseOrderedListPrefix :: Text -> Maybe (Text, Text)
parseOrderedListPrefix line =
  let (indent, rest) = T.span (== ' ') line
      (digits, afterDigits) = T.span isDigit rest
   in case T.uncons afterDigits of
        Just ('.', afterDot)
          | not (T.null digits)
          , T.length (T.takeWhile (== ' ') afterDot) >= 1 ->
              let spaces = T.takeWhile (== ' ') afterDot
                  body = T.drop (T.length spaces) afterDot
               in Just (indent <> digits <> "." <> spaces, body)
        _ ->
          Nothing

wrapWords :: Int -> Text -> Text -> Text -> [Text]
wrapWords maxLength firstPrefix continuationPrefix body =
  case lintWords body of
    [] ->
      [firstPrefix]
    word : wordsRest ->
      finalize (foldl' addWord (initial word) wordsRest)
 where
  initial word = ([firstPrefix <> word], firstPrefix, firstPrefix <> word)

  addWord (finished, currentPrefix, current) word =
    let candidate = current <> " " <> word
        nextPrefix =
          if currentPrefix == firstPrefix
            then continuationPrefix
            else currentPrefix
     in if T.length candidate <= maxLength
          then (finished, currentPrefix, candidate)
          else
            ( initOrEmpty finished ++ [current, nextPrefix <> word]
            , nextPrefix
            , nextPrefix <> word
            )

  finalize (finished, _, current) =
    initOrEmpty finished ++ [current]

initOrEmpty :: [a] -> [a]
initOrEmpty [] = []
initOrEmpty xs = init xs

isFenceLine :: Text -> Bool
isFenceLine txt = "```" `T.isPrefixOf` txt || "~~~" `T.isPrefixOf` txt

isHeadingLine :: Text -> Bool
isHeadingLine txt = "#" `T.isPrefixOf` txt

lintWords :: Text -> [Text]
lintWords =
  reverse . finish . T.foldl' step (0 :: Int, "", [])
 where
  step (depth, current, finished) char
    | isSpace char && depth == 0 =
        if T.null current
          then (depth, "", finished)
          else (depth, "", current : finished)
    | char == '{' =
        (depth + 1, current <> T.singleton char, finished)
    | char == '}' && depth > 0 =
        (depth - 1, current <> T.singleton char, finished)
    | otherwise =
        (depth, current <> T.singleton char, finished)

  finish (_, current, finished)
    | T.null current = finished
    | otherwise = current : finished

-- ----------------------------------------------------------------------------
-- Notation gate.
--
-- Goal: catch any use of a watched notation `\name` inside a Math node that
-- precedes its `mathmeta` `\define{name}` directive or explicit
-- `\forward{name}` directive, with a clear build-time error.
--
-- Two independent sources of state:
--
--   - WATCH LIST  — declared in YAML metadata as `notation-watch:` (a list
--                   of macro names, no leading backslash). This is
--                   configuration; removing it silences the gate.
--   - NOTATION STATE — records `\forward{name1,name2,...}` separately
--                      from `\define{name1,name2,...}` directives in
--                      `mathmeta` blocks. Each directive is consumed by the
--                      filter.
--
-- `\forward` only opens the gate for uses before a later definition.
-- `\define` opens the gate and emits the index entry. Uses link to that
-- index entry, whose page links point back to the definition and references.
--
-- An error fires when a Math node is reached where any watched name appears
-- in the math content but has not yet been forwarded or defined. A second
-- error fires at the end of the document if a forwarded watched notation never
-- receives its real `\define`, because otherwise the generated hyperlink would
-- point at no anchor.
--
-- Splitting these two concerns means deleting a `\define` correctly triggers
-- the error (it does not also remove the macro from the watch list).
-- ----------------------------------------------------------------------------

processDoc :: Pandoc -> IO Pandoc
processDoc doc@(Pandoc meta blocks) = do
  debugGraph <- isJust <$> lookupEnv "DEPENDENCY_GRAPH_DEBUG"
  graphOnly <- isJust <$> lookupEnv "DEPENDENCY_GRAPH_ONLY"
  graphTiming <- isJust <$> lookupEnv "DEPENDENCY_GRAPH_TIMING"
  disableAnnealingSwaps <- isJust <$> lookupEnv "DEPENDENCY_GRAPH_DISABLE_ANNEALING_SWAPS"
  disableRefinementSwaps <- isJust <$> lookupEnv "DEPENDENCY_GRAPH_DISABLE_REFINEMENT_SWAPS"
  newtonBlockOverride <- (>>= readMaybeInt) <$> lookupEnv "DEPENDENCY_GRAPH_NEWTON_BLOCKS"
  let watchSet = watchSetFromMeta meta
      headerMap = collectHeaderMap doc
      graphConfig =
        OptimizationConfig
          { configTimingEnabled = graphTiming
          , configDisableAnnealingSwaps = disableAnnealingSwaps
          , configDisableRefinementSwaps = disableRefinementSwaps
          , configNewtonBlockOverride = newtonBlockOverride
          }
      dependencyPlan = planDependencyGraph graphOnly (dependencyExcludeFromMeta meta) doc
      duplicateIds = duplicateHeaderIds doc
  unless (null duplicateIds) $ do
    hPutStrLn stderr "[ref-filter] duplicate header id(s); each section anchor must be unique:"
    forM_ duplicateIds $ \hid ->
      hPutStrLn stderr ("  duplicate id: " <> T.unpack hid)
    exitWith (ExitFailure 1)
  notationData <- maybe (return emptyNotationData) readNotationData (macrosFileFromMeta meta)
  notationRef <- newIORef initialNotationState
  declRef <- newIORef initialDeclState
  termRef <- newIORef initialTermState
  pendingDeclRef <- newIORef []
  let env = Env notationData notationRef declRef termRef pendingDeclRef watchSet
  blocks' <- processBlockList env blocks
  checkDeclStateFinal declRef pendingDeclRef
  checkNotationForwards notationRef watchSet
  checkTermForwards termRef
  -- Run the dependency-graph layout only when the rendered graph is actually
  -- needed (a \DependencyGraph marker, or the standalone graph-only mode), and
  -- do the layout-cache read/write here in IO rather than through
  -- unsafePerformIO inside the pure layout code.
  dependencyGraph <-
    if graphOnly || dependencyGraphReferenced blocks'
      then do
        let signature = planCacheSignature graphConfig dependencyPlan
            cacheNodes = planCacheNodes dependencyPlan
        cached <- readDependencyLayoutCache dependencyLayoutCachePath signature cacheNodes
        let (tikz, freshPositions) = renderDependencyGraph debugGraph graphConfig dependencyPlan cached
        forM_ freshPositions (writeDependencyLayoutCache dependencyLayoutCachePath signature cacheNodes)
        return tikz
      else return ""
  unresolved <- newIORef Set.empty
  let graphBlocks =
        if graphOnly
          then [RawBlock (Format "latex") dependencyGraph]
          else
            walk (replaceDependencyGraphInline dependencyGraph) $
              walk (replaceDependencyGraphBlock dependencyGraph) blocks'
  blocks'' <- walkM (resolveSecRefs headerMap unresolved) graphBlocks
  blocks''' <- walkM (resolveRawBlockSecRefs headerMap unresolved) blocks''
  blocks'''' <- walkM (resolveRawInlineSecRefs headerMap unresolved) blocks'''
  bad <- readIORef unresolved
  unless (Set.null bad) $ do
    hPutStrLn stderr "[ref-filter] dangling section reference(s):"
    forM_ (Set.toAscList bad) $ \name ->
      hPutStrLn stderr ("  unknown id: " <> T.unpack name)
    exitWith (ExitFailure 1)
  let blocksStripped = walk stripHtmlCommentInline (walk stripHtmlCommentBlock blocks'''')
  return (Pandoc meta blocksStripped)

-- Extract a plain string from a metadata value.
metaText :: MetaValue -> Maybe Text
metaText (MetaString s) = Just s
metaText (MetaInlines inlines) = Just (inlinesToText inlines)
 where
  inlinesToText = T.concat . map go
   where
    go (Str s) = s
    go Space = " "
    go SoftBreak = " "
    -- Keep literal content from Code/Math so a value written with backticks
    -- or $...$ (e.g. a macros-file path) yields its text instead of being
    -- silently dropped to an empty/wrong string.
    go (Code _ s) = s
    go (Math _ s) = s
    go _ = ""
metaText _ = Nothing

-- Extract a set of names from a metadata list value.
metaNameSet :: Text -> Meta -> Set Text
metaNameSet key meta =
  case Map.lookup key (unMeta meta) of
    Just (MetaList xs) -> Set.fromList (mapMaybe metaText xs)
    Just other -> Set.fromList (mapMaybe metaText [other])
    Nothing -> Set.empty

-- Read the watch list from `notation-watch:` YAML metadata.
watchSetFromMeta :: Meta -> Set Text
watchSetFromMeta = metaNameSet "notation-watch"

-- Read the semantic-macros file path from `macros-file:` YAML metadata. The
-- filter holds no book-specific paths: a book that wants notation displays,
-- typed notation specs, and macro-derived behavior names its macros file here.
macrosFileFromMeta :: Meta -> Maybe FilePath
macrosFileFromMeta meta =
  T.unpack <$> (Map.lookup "macros-file" (unMeta meta) >>= metaText)

-- Read the section ids excluded from the dependency graph (e.g. a preface or
-- outlook chapter) from `dependency-graph-exclude:` YAML metadata.
dependencyExcludeFromMeta :: Meta -> Set Text
dependencyExcludeFromMeta = metaNameSet "dependency-graph-exclude"

emptyNotationData :: NotationData
emptyNotationData = NotationData Map.empty Map.empty

data NotationMarker = NotationForward (Set Text) | NotationDefine (Set Text)
  deriving (Eq, Show)

data RawNotationPart = RawNotationText Text | RawNotationMarker NotationMarker

data TermMarker
  = TermIndex Text
  | TermDefine Text Text
  | TermForward Text Text
  | TermRef Text
  | TermUse Text Text
  | -- A malformed use detected during parsing (e.g. the forbidden two-argument
    -- \termuse{term}{display} form). Carries the diagnostic; termIndexText reports
    -- it through the standard [term-filter] error path rather than throwing.
    TermMalformed Text

data TermState = TermState
  { termDefined :: Set Text
  , termForwarded :: Set Text
  }

initialTermState :: TermState
initialTermState = TermState Set.empty Set.empty

data NotationState = NotationState
  { notationForwarded :: Set Text
  , notationDefined :: Set Text
  }

initialNotationState :: NotationState
initialNotationState = NotationState Set.empty Set.empty

activeNotations :: NotationState -> Set Text
activeNotations st = notationForwarded st `Set.union` notationDefined st

applyNotationMarker :: NotationMarker -> NotationState -> NotationState
applyNotationMarker (NotationForward names) st =
  st{notationForwarded = notationForwarded st `Set.union` names}
applyNotationMarker (NotationDefine names) st =
  st{notationDefined = notationDefined st `Set.union` names}

checkNotationForwards :: IORef NotationState -> Set Text -> IO ()
checkNotationForwards ref watchSet = do
  st <- readIORef ref
  let missing =
        (notationForwarded st `Set.difference` notationDefined st)
          `Set.intersection` watchSet
  unless (Set.null missing) $ do
    hPutStrLn stderr "[notation-filter] notation forwarded but never defined:"
    forM_ (Set.toAscList missing) $ \name ->
      hPutStrLn stderr ("  missing \\define{" <> T.unpack name <> "}")
    exitWith (ExitFailure 1)

-- Parse notation markers. Returns Nothing if not a marker.
parseNotationMarker :: Text -> Maybe NotationMarker
parseNotationMarker raw =
  let uncommented = stripLatexComments raw
   in case ( parseMarkerNames "\\NotationDefine{" uncommented
           , parseMarkerNames "\\NotationForward{" uncommented
           ) of
        (names, _) | not (Set.null names) -> Just (NotationDefine names)
        (_, names) | not (Set.null names) -> Just (NotationForward names)
        _ -> Nothing

parseRawNotationParts :: Text -> [RawNotationPart]
parseRawNotationParts =
  intercalate [RawNotationText "\n"] . map parseLine . T.splitOn "\n"
 where
  parseLine line =
    let (code, comment) = breakLatexComment line
     in parseCode code ++ [RawNotationText comment | not (T.null comment)]

  parseCode txt =
    case nextMarker txt of
      Nothing -> [RawNotationText txt | not (T.null txt)]
      Just (before, marker, rest) ->
        [RawNotationText before | not (T.null before)]
          ++ [RawNotationMarker marker]
          ++ parseCode rest

nextMarker :: Text -> Maybe (Text, NotationMarker, Text)
nextMarker = go ""
 where
  -- Step over a malformed marker (no closing brace, or no names) instead of
  -- abandoning the rest of the text: fold its prefix and token into the
  -- literal accumulator and keep scanning, mirroring nextTermMarker, so a
  -- well-formed marker after a malformed one is still processed.
  go acc txt =
    case earliest txt of
      Nothing -> Nothing
      Just (prefix, markerText, mkMarker) ->
        let body = T.drop (T.length markerText) (T.drop (T.length prefix) txt)
         in case T.breakOn "}" body of
              (_, tailText)
                | T.null tailText -> go (acc <> prefix <> markerText) body
              (inner, tailText) ->
                let names = markerNames inner
                 in if Set.null names
                      then go (acc <> prefix <> markerText) body
                      else Just (acc <> prefix, mkMarker names, T.drop 1 tailText)

  earliest txt =
    chooseEarliest
      (candidate txt "\\NotationDefine{" NotationDefine)
      (candidate txt "\\NotationForward{" NotationForward)

  candidate txt markerText mkMarker =
    let (prefix, rest) = T.breakOn markerText txt
     in if T.null rest then Nothing else Just (prefix, markerText, mkMarker)

  chooseEarliest Nothing y = y
  chooseEarliest x Nothing = x
  chooseEarliest x@(Just (prefixX, _, _)) y@(Just (prefixY, _, _))
    | T.length prefixX <= T.length prefixY = x
    | otherwise = y

  markerNames inner =
    Set.fromList (filter (not . T.null) (map T.strip (T.splitOn "," inner)))

-- Split a line into (code-before-comment, comment-including-%). An escaped
-- \% is a literal percent and never starts a comment; a lone backslash escapes
-- nothing else. Scans in chunks via T.break (stopping only at \ or %) and
-- concatenates once, so it is linear in the line length rather than quadratic.
breakLatexComment :: Text -> (Text, Text)
breakLatexComment = go []
 where
  go acc rest =
    let (plain, special) = T.break (\c -> c == '\\' || c == '%') rest
        done = T.concat (reverse (plain : acc))
     in case T.uncons special of
          Nothing -> (done, "")
          Just ('%', _) -> (done, special)
          Just ('\\', after) ->
            case T.uncons after of
              -- \% : escaped percent; copy both and keep scanning.
              Just ('%', _) -> go (T.take 2 special : plain : acc) (T.drop 2 special)
              -- lone backslash: copy it and keep scanning.
              _ -> go ("\\" : plain : acc) after
          Just _ -> (done, special)

stripLatexComments :: Text -> Text
stripLatexComments =
  T.unlines . map (fst . breakLatexComment) . T.lines

-- Remove HTML comments (<!-- ... -->) from text. Pandoc drops standalone HTML
-- comments in the LaTeX writer, but when a comment sits inside raw-LaTeX content
-- (e.g. between \item entries, inside a proof environment, or amid display math)
-- pandoc sweeps it into a RawBlock and emits it verbatim, so it reaches the .tex
-- and breaks the build. The `<!-- formalization: ... -->` scope annotations
-- (read by tools/booklink_coverage.py) are exactly such comments; strip them so
-- they never render. Booklink injection uses `%`-style LaTeX comments, not
-- HTML comments, so it is unaffected.
stripHtmlComments :: Text -> Text
stripHtmlComments t =
  case T.breakOn "<!--" t of
    (before, rest)
      | T.null rest -> before
      | otherwise ->
          case T.breakOn "-->" (T.drop 4 rest) of
            (_, after)
              -- Unterminated `<!--`: keep the remainder verbatim rather than
              -- silently dropping everything after the opener. A stray literal
              -- comment marker is a visible artifact the author can fix; lost
              -- prose is not.
              | T.null after -> before <> rest
              | otherwise -> before <> stripHtmlComments (T.drop 3 after)

stripHtmlCommentBlock :: Block -> Block
stripHtmlCommentBlock (RawBlock fmt t) = RawBlock fmt (stripHtmlComments t)
stripHtmlCommentBlock b = b

stripHtmlCommentInline :: Inline -> Inline
stripHtmlCommentInline (RawInline fmt t) = RawInline fmt (stripHtmlComments t)
stripHtmlCommentInline i = i

parseMarkerNames :: Text -> Text -> Set Text
parseMarkerNames marker = go Set.empty
 where
  go acc raw =
    case T.breakOn marker raw of
      (_, rest)
        | T.null rest -> acc
        | otherwise ->
            let body = T.drop (T.length marker) rest
             in case T.breakOn "}" body of
                  (_, tailText)
                    | T.null tailText -> acc
                  (inner, tailText) ->
                    let names =
                          Set.fromList
                            (filter (not . T.null) (map T.strip (T.splitOn "," inner)))
                     in go (acc `Set.union` names) (T.drop 1 tailText)

type DeclType = Text

data DeclHeadKind = DeclHeadUpper | DeclHeadLower
  deriving (Eq, Ord, Show)

data DeclAssoc = DeclAssocLeft | DeclAssocRight | DeclAssocNon
  deriving (Eq, Show)

data DeclInfix = DeclInfix
  { declInfixName :: Text
  , declInfixType :: DeclType
  , declInfixLevel :: Int
  , declInfixAssoc :: DeclAssoc
  }
  deriving (Eq, Show)

data DeclCommand
  = DeclTypeDef DeclType
  | DeclNotationType Text DeclType Text
  | DeclInferContains [Text] DeclType
  | DeclInferAtom Text DeclType
  | DeclInferPrefix Text DeclType
  | DeclInferBinder Text DeclType
  | DeclInferInfix DeclInfix
  | DeclInferHead DeclHeadKind DeclType
  | DeclInferPostfix Text
  | DeclInferJuxtaposed DeclType
  | DeclVars [Text] DeclType
  | DeclScopeBegin
  | DeclScopeEnd
  | DeclExportBegin Text
  | DeclExportEnd
  | DeclImport Text
  deriving (Eq, Show)

data MathMetaDirective
  = MathMetaNotation NotationMarker
  | MathMetaDecl DeclCommand
  | MathMetaWith [DeclCommand]
  | MathMetaLean Text
  deriving (Eq, Show)

data DeclState = DeclState
  { declSectionFrames :: [(Int, Map Text DeclType)]
  , declLocalFrames :: [Map Text DeclType]
  , declExports :: Map Text (Map Text DeclType)
  , declActiveExport :: Maybe (Text, Map Text DeclType)
  , declKnownTypes :: Set DeclType
  , declNotationTypes :: Map (Text, DeclType) Text
  , declInferContains :: [(Text, DeclType)]
  , declInferAtoms :: Map Text DeclType
  , declInferPrefixes :: Map Text DeclType
  , declInferBinders :: Map Text DeclType
  , declInferInfixes :: Map Text DeclInfix
  , declInferHeads :: Map DeclHeadKind DeclType
  , declInferPostfix :: Set Text
  , declInferJuxtaposed :: Set DeclType
  }

initialDeclState :: DeclState
initialDeclState =
  DeclState [(0, Map.empty)] [] Map.empty Nothing Set.empty Map.empty [] Map.empty Map.empty Map.empty Map.empty Map.empty Set.empty Set.empty

parseMathMetaBlock :: Text -> Maybe [MathMetaDirective]
parseMathMetaBlock raw = do
  body <- stripMathMetaEnvironment raw
  let ls = filter activeLine (map T.strip (T.lines body))
  case mapM parseMathMetaDirective ls of
    Just directives | not (null directives) -> Just directives
    _ -> Nothing
 where
  activeLine line = not (T.null line) && not ("%" `T.isPrefixOf` line)

isMathMetaEnvironment :: Text -> Bool
isMathMetaEnvironment raw =
  isJust (stripMathMetaEnvironment raw)

stripMathMetaEnvironment :: Text -> Maybe Text
stripMathMetaEnvironment raw = do
  rest <- T.stripPrefix "\\begin{mathmeta}" (T.strip raw)
  body <- T.stripSuffix "\\end{mathmeta}" (T.strip rest)
  return (T.strip body)

parseMathMetaDirective :: Text -> Maybe MathMetaDirective
parseMathMetaDirective raw =
  let txt = T.strip (stripLatexComments raw)
   in case parseOneArg "\\with" txt of
        Just body -> MathMetaWith <$> parseMathMetaWithBody body
        Nothing -> parseMathMetaPlainDirective txt

parseMathMetaPlainDirective :: Text -> Maybe MathMetaDirective
parseMathMetaPlainDirective txt =
  parseMathMetaDefine
    <|> parseMathMetaForward
    <|> parseMathMetaType
    <|> parseMathMetaNotationType
    <|> parseMathMetaInferContains
    <|> parseMathMetaInferAtom
    <|> parseMathMetaInferPrefix
    <|> parseMathMetaInferBinder
    <|> parseMathMetaInferInfix
    <|> parseMathMetaInferHead
    <|> parseMathMetaInferPostfix
    <|> parseMathMetaInferJuxtaposed
    <|> parseMathMetaVars
    <|> parseMathMetaScopeBegin
    <|> parseMathMetaScopeEnd
    <|> parseMathMetaExportBegin
    <|> parseMathMetaExportEnd
    <|> parseMathMetaImport
    <|> parseMathMetaLean
 where
  notationDirective marker names =
    MathMetaNotation (marker (parseNotationNames names))

  declDirective =
    MathMetaDecl

  parseMathMetaDefine =
    notationDirective NotationDefine <$> parseOneArg "\\define" txt

  parseMathMetaForward =
    notationDirective NotationForward <$> parseOneArg "\\forward" txt

  parseMathMetaType =
    declDirective . DeclTypeDef . normalizeDeclName <$> parseOneArg "\\type" txt

  parseMathMetaNotationType = do
    (notationText, typeText, targetText) <- parseThreeArgs "\\notationtype" txt
    return
      ( declDirective
          ( DeclNotationType
              (normalizeNotationName notationText)
              (normalizeDeclName typeText)
              (normalizeNotationName targetText)
          )
      )

  parseMathMetaInferContains = do
    (tokensText, typeText) <- parseTwoArgs "\\infercontains" txt
    return (declDirective (DeclInferContains (parseDeclNames tokensText) (normalizeDeclName typeText)))

  parseMathMetaInferAtom = do
    (tokenText, typeText) <- parseTwoArgs "\\inferatom" txt
    return (declDirective (DeclInferAtom (normalizeNotationName tokenText) (normalizeDeclName typeText)))

  parseMathMetaInferPrefix = do
    (tokenText, typeText) <- parseTwoArgs "\\inferprefix" txt
    return (declDirective (DeclInferPrefix (normalizeNotationName tokenText) (normalizeDeclName typeText)))

  parseMathMetaInferBinder = do
    (tokenText, typeText) <- parseTwoArgs "\\inferbinder" txt
    return (declDirective (DeclInferBinder (normalizeNotationName tokenText) (normalizeDeclName typeText)))

  parseMathMetaInferInfix = do
    (tokenText, typeText, levelText, assocText) <- parseFourArgs "\\inferinfix" txt
    level <- parseDeclLevel levelText
    assoc <- parseDeclAssoc assocText
    let name = normalizeNotationName tokenText
        ty = normalizeDeclName typeText
    return (declDirective (DeclInferInfix (DeclInfix name ty level assoc)))

  parseMathMetaInferHead = do
    (kindText, typeText) <- parseTwoArgs "\\inferhead" txt
    kind <- parseDeclHeadKind kindText
    return (declDirective (DeclInferHead kind (normalizeDeclName typeText)))

  parseMathMetaInferPostfix =
    declDirective . DeclInferPostfix . normalizeNotationName <$> parseOneArg "\\inferpostfix" txt

  parseMathMetaInferJuxtaposed =
    declDirective . DeclInferJuxtaposed . normalizeDeclName <$> parseOneArg "\\inferjuxtaposed" txt

  parseMathMetaVars = do
    (namesText, typeText) <- parseTwoArgs "\\vars" txt
    return (declDirective (DeclVars (parseDeclNames namesText) (normalizeDeclName typeText)))

  parseMathMetaScopeBegin =
    declDirective DeclScopeBegin <$ parseNoArg "\\scopebegin" txt

  parseMathMetaScopeEnd =
    declDirective DeclScopeEnd <$ parseNoArg "\\scopeend" txt

  parseMathMetaExportBegin =
    declDirective . DeclExportBegin . T.strip <$> parseOneArg "\\export" txt

  parseMathMetaExportEnd =
    declDirective DeclExportEnd <$ parseNoArg "\\exportend" txt

  parseMathMetaImport =
    declDirective . DeclImport . T.strip <$> parseOneArg "\\import" txt

  parseMathMetaLean =
    MathMetaLean . T.strip <$> parseOneArg "\\lean" txt

parseMathMetaWithBody :: Text -> Maybe [DeclCommand]
parseMathMetaWithBody body =
  let ls = filter activeLine (map T.strip (T.lines body))
   in case mapM parseScopedDecl ls of
        Just cmds | not (null cmds) -> Just cmds
        _ -> Nothing
 where
  activeLine line = not (T.null line) && not ("%" `T.isPrefixOf` line)

  parseScopedDecl line =
    case parseMathMetaPlainDirective line of
      Just (MathMetaDecl cmd)
        | isScopedWithDecl cmd -> Just cmd
      _ -> Nothing

  isScopedWithDecl (DeclVars _ _) = True
  isScopedWithDecl (DeclImport _) = True
  isScopedWithDecl _ = False

parseNotationNames :: Text -> Set Text
parseNotationNames =
  Set.fromList . filter (not . T.null) . map normalizeNotationName . T.splitOn ","

normalizeNotationName :: Text -> Text
normalizeNotationName txt =
  fromMaybe stripped (T.stripPrefix "\\" stripped)
 where
  stripped = normalizeDeclName txt

parseDeclNames :: Text -> [Text]
parseDeclNames =
  filter (not . T.null) . map normalizeDeclName . T.splitOn ","

normalizeDeclName :: Text -> Text
normalizeDeclName =
  T.filter (/= ' ') . T.filter (/= '\n') . T.strip

parseDeclHeadKind :: Text -> Maybe DeclHeadKind
parseDeclHeadKind txt =
  case normalizeDeclName txt of
    "upper" -> Just DeclHeadUpper
    "lower" -> Just DeclHeadLower
    _ -> Nothing

parseDeclAssoc :: Text -> Maybe DeclAssoc
parseDeclAssoc txt =
  case normalizeDeclName txt of
    "left" -> Just DeclAssocLeft
    "right" -> Just DeclAssocRight
    "non" -> Just DeclAssocNon
    _ -> Nothing

parseDeclLevel :: Text -> Maybe Int
parseDeclLevel txt =
  case reads (T.unpack (normalizeDeclName txt)) of
    [(n, "")] -> Just n
    _ -> Nothing

parseNoArg :: Text -> Text -> Maybe ()
parseNoArg marker txt =
  if txt == marker then Just () else Nothing

parseOneArg :: Text -> Text -> Maybe Text
parseOneArg marker txt = do
  rest <- T.stripPrefix marker txt
  (arg, tailText) <- parseMandatoryArg rest
  if T.null (T.strip tailText)
    then Just (stripOuterBraces arg)
    else Nothing

parseTwoArgs :: Text -> Text -> Maybe (Text, Text)
parseTwoArgs marker txt = do
  rest <- T.stripPrefix marker txt
  (arg1, rest1) <- parseMandatoryArg rest
  (arg2, tailText) <- parseMandatoryArg rest1
  if T.null (T.strip tailText)
    then Just (stripOuterBraces arg1, stripOuterBraces arg2)
    else Nothing

parseThreeArgs :: Text -> Text -> Maybe (Text, Text, Text)
parseThreeArgs marker txt = do
  rest <- T.stripPrefix marker txt
  (arg1, rest1) <- parseMandatoryArg rest
  (arg2, rest2) <- parseMandatoryArg rest1
  (arg3, tailText) <- parseMandatoryArg rest2
  if T.null (T.strip tailText)
    then Just (stripOuterBraces arg1, stripOuterBraces arg2, stripOuterBraces arg3)
    else Nothing

parseFourArgs :: Text -> Text -> Maybe (Text, Text, Text, Text)
parseFourArgs marker txt = do
  rest <- T.stripPrefix marker txt
  (arg1, rest1) <- parseMandatoryArg rest
  (arg2, rest2) <- parseMandatoryArg rest1
  (arg3, rest3) <- parseMandatoryArg rest2
  (arg4, tailText) <- parseMandatoryArg rest3
  if T.null (T.strip tailText)
    then Just (stripOuterBraces arg1, stripOuterBraces arg2, stripOuterBraces arg3, stripOuterBraces arg4)
    else Nothing

stripOuterBraces :: Text -> Text
stripOuterBraces txt =
  fromMaybe txt $ do
    rest <- T.stripPrefix "{" txt
    T.stripSuffix "}" rest

enterSection :: IORef DeclState -> Int -> IO ()
enterSection ref level =
  modifyIORef ref $ \st ->
    let kept = filter ((< level) . fst) (declSectionFrames st)
     in st{declSectionFrames = kept ++ [(level, Map.empty)]}

applyDeclCommand :: IORef DeclState -> DeclCommand -> IO ()
applyDeclCommand ref cmd = do
  st <- readIORef ref
  st' <- applyDeclCommandChecked cmd st
  writeIORef ref st'

applyDeclCommandChecked :: DeclCommand -> DeclState -> IO DeclState
applyDeclCommandChecked cmd st = case cmd of
  DeclTypeDef ty ->
    return st{declKnownTypes = Set.insert ty (declKnownTypes st)}
  DeclNotationType notation ty target ->
    if ty `Set.member` declKnownTypes st
      then return st{declNotationTypes = Map.insert (notation, ty) target (declNotationTypes st)}
      else
        declStateError
          ( "\\notationtype{\\"
              <> notation
              <> "}{"
              <> ty
              <> "}{\\"
              <> target
              <> "} references an unknown type; add \\type{"
              <> ty
              <> "} before using it"
          )
  DeclInferContains tokens ty ->
    return
      st
        { declKnownTypes = Set.insert ty (declKnownTypes st)
        , declInferContains = declInferContains st ++ [(token, ty) | token <- tokens]
        }
  DeclInferAtom name ty ->
    return
      st
        { declKnownTypes = Set.insert ty (declKnownTypes st)
        , declInferAtoms = Map.insert name ty (declInferAtoms st)
        }
  DeclInferPrefix name ty ->
    return
      st
        { declKnownTypes = Set.insert ty (declKnownTypes st)
        , declInferPrefixes = Map.insert name ty (declInferPrefixes st)
        }
  DeclInferBinder name ty ->
    return
      st
        { declKnownTypes = Set.insert ty (declKnownTypes st)
        , declInferBinders = Map.insert name ty (declInferBinders st)
        }
  DeclInferInfix spec ->
    return
      st
        { declKnownTypes = Set.insert (declInfixType spec) (declKnownTypes st)
        , declInferInfixes = Map.insert (declInfixName spec) spec (declInferInfixes st)
        }
  DeclInferHead kind ty ->
    return
      st
        { declKnownTypes = Set.insert ty (declKnownTypes st)
        , declInferHeads = Map.insert kind ty (declInferHeads st)
        }
  DeclInferPostfix name ->
    return st{declInferPostfix = Set.insert name (declInferPostfix st)}
  DeclInferJuxtaposed ty ->
    return
      st
        { declKnownTypes = Set.insert ty (declKnownTypes st)
        , declInferJuxtaposed = Set.insert ty (declInferJuxtaposed st)
        }
  DeclVars names ty ->
    return $ addDeclMap (Map.fromList [(name, ty) | name <- names]) (st{declKnownTypes = Set.insert ty (declKnownTypes st)})
  DeclScopeBegin ->
    return st{declLocalFrames = Map.empty : declLocalFrames st}
  DeclScopeEnd ->
    case declLocalFrames st of
      [] -> declStateError "\\scopeend without matching \\scopebegin"
      (_ : rest) -> return st{declLocalFrames = rest}
  DeclExportBegin name ->
    case declActiveExport st of
      Nothing -> return st{declActiveExport = Just (name, Map.empty)}
      Just (activeName, _) ->
        declStateError
          ("\\export{" <> name <> "} started before closing active \\export{" <> activeName <> "}")
  DeclExportEnd ->
    case declActiveExport st of
      Nothing -> declStateError "\\exportend without matching \\export{...}"
      Just (name, exported) ->
        return
          st
            { declExports = Map.insert name exported (declExports st)
            , declActiveExport = Nothing
            }
  DeclImport name ->
    case Map.lookup name (declExports st) of
      Nothing -> declStateError ("\\import{" <> name <> "} references an unknown export")
      Just imported -> return $ addDeclMap imported st

checkDeclStateFinal :: IORef DeclState -> IORef [DeclCommand] -> IO ()
checkDeclStateFinal declRef pendingDeclRef = do
  pending <- readIORef pendingDeclRef
  unless (null pending) $
    declStateError "\\with declarations appeared at end of document with no following block"
  st <- readIORef declRef
  unless (null (declLocalFrames st)) $
    declStateError "\\scopebegin without matching \\scopeend"
  case declActiveExport st of
    Nothing -> return ()
    Just (name, _) ->
      declStateError ("\\export{" <> name <> "} without matching \\exportend")

declStateError :: Text -> IO a
declStateError message = do
  hPutStrLn stderr "[decl-filter] malformed declaration state:"
  hPutStrLn stderr ("  " <> T.unpack message)
  exitWith (ExitFailure 1)

addDeclMap :: Map Text DeclType -> DeclState -> DeclState
addDeclMap newDecls st =
  case declActiveExport st of
    Just (name, exported) ->
      st{declActiveExport = Just (name, Map.union newDecls exported)}
    Nothing ->
      case declLocalFrames st of
        (local : locals) ->
          st{declLocalFrames = Map.union newDecls local : locals}
        [] ->
          let frames = declSectionFrames st
           in st
                { declSectionFrames =
                    case reverse frames of
                      [] -> [(0, newDecls)]
                      ((level, frame) : rest) ->
                        reverse rest ++ [(level, Map.union newDecls frame)]
                }

activeDeclEnv :: DeclState -> Map Text DeclType
activeDeclEnv st =
  let sectionEnv = foldl (flip Map.union) Map.empty (map snd (declSectionFrames st))
      localEnv = foldl (flip Map.union) Map.empty (reverse (declLocalFrames st))
   in Map.union localEnv sectionEnv

data NotationData = NotationData
  { notationDisplays :: Map Text Text
  , notationSpecs :: Map Text MacroSpec
  }

data MacroSpec = MacroSpec
  { macroMandatoryArgs :: Int
  , macroHasOptionalArg :: Bool
  }

data MathToken
  = TokCommand Text
  | TokLBrace
  | TokRBrace
  | TokLBracket
  | TokRBracket
  | TokSub
  | TokSup
  | TokText Text
  deriving (Eq, Show)

data MathExpr
  = MathSeq [MathExpr]
  | MathCommand Text (Maybe MathExpr) [MathExpr]
  | MathGroup MathExpr
  | MathScript MathExpr Text MathExpr
  | MathText Text
  | MathRaw Text
  deriving (Eq, Show)

data PendingBooklinkMatch = PendingBooklinkMatch
  { pendingBooklinkName :: Text
  , pendingBooklinkIndex :: Int
  , pendingBooklinkKind :: Maybe Text
  , pendingBooklinkStatus :: Maybe Text
  , pendingBooklinkSource :: Maybe FilePath
  , pendingBooklinkStart :: Maybe Int
  , pendingBooklinkEnd :: Maybe Int
  }

data BooklinkInjection = BooklinkInjection
  { booklinkInjectionNames :: [Text]
  , booklinkInjectionIndex :: Int
  , booklinkInjectionKind :: Maybe Text
  , booklinkInjectionStart :: Int
  , booklinkInjectionEnd :: Int
  }
  deriving (Eq, Show)

emptyPendingBooklinkMatch :: Text -> Int -> Maybe Text -> PendingBooklinkMatch
emptyPendingBooklinkMatch name index kind =
  PendingBooklinkMatch name index kind Nothing Nothing Nothing Nothing

injectBooklinksMain :: [String] -> IO ()
injectBooklinksMain args =
  case parseInjectBooklinksArgs args of
    Just (sourceMapPath, sourcePath, outPath) -> do
      sourceText <- TIO.readFile sourcePath
      mapText <- TIO.readFile sourceMapPath
      let injections =
            groupBooklinkInjections
              [ pending
              | pending <- parseBooklinkSourceMap mapText
              , pendingBooklinkSource pending == Just sourcePath
              ]
          skips =
            [ skip
            | skip <- parseSkipInjections mapText
            , skipInjectionSource skip == sourcePath
            ]
      validateBooklinkInjections sourcePath sourceText injections
      validateSkipInjections sourcePath sourceText skips
      createDirectoryIfMissing True (parentDirectory outPath)
      TIO.writeFile outPath (applyInsertions sourceText (booklinkInsertions sourceText injections <> skipInsertions skips))
    _ -> do
      hPutStrLn stderr "usage: book-filter inject-booklinks --sourcemap MAP.json --source SOURCE.md --out OUT.md"
      exitWith (ExitFailure 2)

parseInjectBooklinksArgs :: [String] -> Maybe (FilePath, FilePath, FilePath)
parseInjectBooklinksArgs =
  go Nothing Nothing Nothing
 where
  go sm src out [] = (,,) <$> sm <*> src <*> out
  go _ _ _ [_] = Nothing
  go sm src out ("--sourcemap" : value : rest) = go (Just value) src out rest
  go sm src out ("--source" : value : rest) = go sm (Just value) out rest
  go sm src out ("--out" : value : rest) = go sm src (Just value) rest
  go _ _ _ _ = Nothing

parentDirectory :: FilePath -> FilePath
parentDirectory path =
  case reverse (dropWhile (/= '/') (reverse path)) of
    "" -> "."
    dir -> dir

parseBooklinkSourceMap :: Text -> [PendingBooklinkMatch]
parseBooklinkSourceMap =
  go Nothing (-1) Nothing False Nothing []
    . T.lines
 where
  go _ _ _ _ pending entries [] =
    entries ++ maybe [] finishPending pending
  go currentName currentIndex currentKind inMatch pending entries (line : rest)
    | jsonKeyLine "declName" line =
        -- The "declName" line delimits one entry in the source map, so the
        -- entry index must advance here even when the value is null (a marker
        -- with no following declaration). Binding the name through
        -- jsonTextValue keeps it Nothing for a null declName while still
        -- counting the entry, so later entry=N indices stay in sync with the
        -- source map array and the PDF's booklink-entry-N hypertargets.
        -- Reset currentKind here too: it is set by this entry's later "target"
        -- line, so it must not leak from the previous entry when this one has
        -- no "target" line of its own.
        go (jsonTextValue "declName" line) (currentIndex + 1) Nothing False Nothing entries rest
    | Just target <- jsonTextValue "target" line =
        let kind = if target == "statement" then Just "statement" else Nothing
         in go currentName currentIndex kind inMatch pending entries rest
    | "\"match\"" `T.isInfixOf` line
    , Just name <- currentName =
        go currentName currentIndex currentKind True (Just (emptyPendingBooklinkMatch name currentIndex currentKind)) entries rest
    | inMatch =
        let pending' = updatePendingBooklink line <$> pending
            finished = T.strip line == "}," || T.strip line == "}"
         in if finished
              then go currentName currentIndex currentKind False Nothing (entries ++ maybe [] finishPending pending') rest
              else go currentName currentIndex currentKind True pending' entries rest
    | otherwise =
        go currentName currentIndex currentKind inMatch pending entries rest

  finishPending pending
    | pendingBooklinkStatus pending == Just "matched"
    , Just _ <- pendingBooklinkSource pending
    , Just _ <- pendingBooklinkStart pending
    , Just _ <- pendingBooklinkEnd pending =
        [pending]
    | otherwise = []

  updatePendingBooklink line pending =
    pending
      { pendingBooklinkStatus = jsonTextValue "status" line <|> pendingBooklinkStatus pending
      , pendingBooklinkSource = T.unpack <$> jsonTextValue "source" line <|> pendingBooklinkSource pending
      , pendingBooklinkStart = jsonIntValue "startOffset" line <|> pendingBooklinkStart pending
      , pendingBooklinkEnd = jsonIntValue "endOffset" line <|> pendingBooklinkEnd pending
      }

{- | True when the (trimmed) line is the given JSON key, regardless of value
type, e.g. matches both @"declName": "foo"@ and @"declName": null@.
-}
jsonKeyLine :: Text -> Text -> Bool
jsonKeyLine key line = ("\"" <> key <> "\":") `T.isPrefixOf` T.strip line

jsonTextValue :: Text -> Text -> Maybe Text
jsonTextValue key line = do
  rest <- T.stripPrefix ("\"" <> key <> "\":") (T.strip line)
  afterOpen <- T.stripPrefix "\"" (T.stripStart rest)
  decodeJsonStringBody afterOpen

{- | Decode a JSON string body (the text just after the opening quote) up to its
closing unescaped double quote, resolving the standard backslash escapes.
Returns Nothing when there is no closing quote, so a non-string value (null or
a number) — which has no opening quote to strip above — yields Nothing.

The source map is emitted by tools/booklink_sourcemap.py via
json.dumps(..., ensure_ascii=False), so values are standard JSON-escaped but
never use \\uXXXX for the data this map carries (Lean identifiers, fixed
target/status words, and POSIX source paths). This replaces an earlier
T.breakOn "\\"" that silently truncated a value at its first escaped quote and
kept a trailing backslash from an escaped backslash.
-}
decodeJsonStringBody :: Text -> Maybe Text
decodeJsonStringBody = go []
 where
  go acc t = case T.uncons t of
    Nothing -> Nothing
    Just ('"', _) -> Just (T.pack (reverse acc))
    Just ('\\', rest) -> case T.uncons rest of
      Just (c, rest') -> go (unescape c : acc) rest'
      Nothing -> Nothing
    Just (c, rest) -> go (c : acc) rest

  unescape c = case c of
    '"' -> '"'
    '\\' -> '\\'
    '/' -> '/'
    'n' -> '\n'
    't' -> '\t'
    'r' -> '\r'
    'b' -> '\b'
    'f' -> '\f'
    other -> other

jsonIntValue :: Text -> Text -> Maybe Int
jsonIntValue key line = do
  rest <- T.stripPrefix ("\"" <> key <> "\":") (T.strip line)
  readMaybeInt (T.unpack (T.takeWhile isDigit (T.strip rest)))

groupBooklinkInjections :: [PendingBooklinkMatch] -> [BooklinkInjection]
groupBooklinkInjections pending =
  mapMaybe toInjection grouped
 where
  complete =
    [ p
    | p <- pending
    , Just _ <- [pendingBooklinkStart p]
    , Just _ <- [pendingBooklinkEnd p]
    ]
  key p = (pendingBooklinkStart p, pendingBooklinkEnd p, pendingBooklinkKind p)
  grouped = groupByKey key (sortOn key complete)
  -- groupByKey never yields empty groups; matching the head keeps the function
  -- total instead of relying on that with `head`.
  toInjection [] = Nothing
  toInjection group@(first : _) =
    Just
      BooklinkInjection
        { booklinkInjectionNames = map pendingBooklinkName group
        , booklinkInjectionIndex = minimum (map pendingBooklinkIndex group)
        , booklinkInjectionKind = pendingBooklinkKind first
        , booklinkInjectionStart = fromMaybe 0 (pendingBooklinkStart first)
        , booklinkInjectionEnd = fromMaybe 0 (pendingBooklinkEnd first)
        }

groupByKey :: (Eq k) => (a -> k) -> [a] -> [[a]]
groupByKey _ [] = []
groupByKey key (x : xs) =
  let (same, rest) = span ((== key x) . key) xs
   in (x : same) : groupByKey key rest

validateBooklinkInjections :: FilePath -> Text -> [BooklinkInjection] -> IO ()
validateBooklinkInjections sourcePath sourceText injections = do
  let ordered = sortOn booklinkInjectionStart injections
  forM_ ordered $ \injection -> do
    when (booklinkInjectionStart injection < 0 || booklinkInjectionEnd injection <= booklinkInjectionStart injection || booklinkInjectionEnd injection > T.length sourceText) $
      booklinkInjectError sourcePath injection "invalid source-map span"
    when (insideInlineDollar sourceText (booklinkInjectionStart injection) || insideInlineDollar sourceText (booklinkInjectionEnd injection)) $
      booklinkInjectError sourcePath injection "source-map span boundary falls inside inline math; refusing to widen it"
  forM_ (zip ordered (drop 1 ordered)) $ \(left, right) ->
    when (booklinkInjectionEnd left > booklinkInjectionStart right) $
      booklinkInjectError sourcePath right "overlapping source-map spans cannot be injected exactly"

booklinkInjectError :: FilePath -> BooklinkInjection -> String -> IO a
booklinkInjectError sourcePath injection message = do
  hPutStrLn stderr $
    "book-filter inject-booklinks: "
      <> sourcePath
      <> ": "
      <> message
      <> " at offsets "
      <> show (booklinkInjectionStart injection)
      <> ".."
      <> show (booklinkInjectionEnd injection)
  exitWith (ExitFailure 1)

data SkipInjection = SkipInjection
  { skipInjectionKey :: Text
  , skipInjectionSource :: FilePath
  , skipInjectionStart :: Int
  , skipInjectionEnd :: Int
  }
  deriving (Eq, Show)

data PendingSkip = PendingSkip
  { pendingSkipKey :: Maybe Text
  , pendingSkipSource :: Maybe FilePath
  , pendingSkipStart :: Maybe Int
  , pendingSkipEnd :: Maybe Int
  }

emptyPendingSkip :: PendingSkip
emptyPendingSkip = PendingSkip Nothing Nothing Nothing Nothing

{- | Parse the top-level @"skips"@ array emitted by tools/booklink_sourcemap.py.
Line-based like 'parseBooklinkSourceMap': scan from the @"skips":@ header to the
array's closing bracket, accumulating each object's key/source/offsets. Skip
objects carry no @declName@/@match@, so the booklink parser ignores them and this
one ignores the surrounding entries.
-}
parseSkipInjections :: Text -> [SkipInjection]
parseSkipInjections fullText =
  case dropWhile (not . T.isInfixOf "\"skips\":") (T.lines fullText) of
    [] -> []
    (header : rest)
      | "[]" `T.isInfixOf` header -> [] -- empty inline array, no objects
      | otherwise -> go emptyPendingSkip [] rest
 where
  go _ acc [] = reverse acc
  go pending acc (line : rest)
    | isArrayClose line = reverse acc
    | T.strip line == "{" = go emptyPendingSkip acc rest
    | isObjectClose line =
        case toSkip pending of
          Just skip -> go emptyPendingSkip (skip : acc) rest
          Nothing -> go emptyPendingSkip acc rest
    | otherwise = go (updatePendingSkip line pending) acc rest

  isArrayClose line = let s = T.strip line in s == "]" || s == "],"
  isObjectClose line = let s = T.strip line in s == "}" || s == "},"

  toSkip pending =
    SkipInjection
      <$> pendingSkipKey pending
      <*> pendingSkipSource pending
      <*> pendingSkipStart pending
      <*> pendingSkipEnd pending

  updatePendingSkip line pending =
    pending
      { pendingSkipKey = jsonTextValue "key" line <|> pendingSkipKey pending
      , pendingSkipSource = T.unpack <$> jsonTextValue "source" line <|> pendingSkipSource pending
      , pendingSkipStart = jsonIntValue "startOffset" line <|> pendingSkipStart pending
      , pendingSkipEnd = jsonIntValue "endOffset" line <|> pendingSkipEnd pending
      }

validateSkipInjections :: FilePath -> Text -> [SkipInjection] -> IO ()
validateSkipInjections sourcePath sourceText =
  mapM_ check
 where
  check skip =
    when (skipInjectionStart skip < 0 || skipInjectionEnd skip <= skipInjectionStart skip || skipInjectionEnd skip > T.length sourceText) $ do
      hPutStrLn stderr $
        "book-filter inject-booklinks: "
          <> sourcePath
          <> ": invalid skip span at offsets "
          <> show (skipInjectionStart skip)
          <> ".."
          <> show (skipInjectionEnd skip)
      exitWith (ExitFailure 1)

insideInlineDollar :: Text -> Int -> Bool
insideInlineDollar text offset = go (T.unpack (T.take offset text)) False
 where
  -- An escaped \$ is a literal dollar and never toggles math; a $$ delimiter
  -- opens display (not inline) math, so it must not flip inline parity.
  go [] inside = inside
  go ('\\' : _ : rest) inside = go rest inside
  go ('$' : '$' : rest) inside = go rest inside
  go ('$' : rest) inside = go rest (not inside)
  go (_ : rest) inside = go rest inside

-- A single zero-width text insertion. Booklink and skip markers both reduce to a
-- pair of these (an opener at one offset, a closer at another), so they share one
-- offset-stable merge instead of two passes that would shift each other's offsets.
data Insertion = Insertion
  { insertionOffset :: Int
  , insertionPriority :: Int
  , insertionText :: Text
  }

-- Merge every insertion into the source in one forward pass over offset-sorted
-- points, so insertions never disturb each other's (original-text) offsets. At a
-- shared offset, insertionPriority orders them: closers before openers, with the
-- zero-width skip anchors nested between, so adjacent booklink color groups still
-- close before the next opens.
applyInsertions :: Text -> [Insertion] -> Text
applyInsertions sourceText =
  go 0 . sortOn (\i -> (insertionOffset i, insertionPriority i))
 where
  go cursor [] = T.drop cursor sourceText
  go cursor (i : is) =
    let offset = insertionOffset i
        between = T.take (offset - cursor) (T.drop cursor sourceText)
     in between <> insertionText i <> go offset is

booklinkInsertions :: Text -> [BooklinkInjection] -> [Insertion]
booklinkInsertions sourceText = concatMap toInsertions
 where
  toInsertions injection =
    [ Insertion (booklinkInjectionStart injection) 3 (booklinkCommand "Start" injection)
    , Insertion (endInsertionOffset sourceText (booklinkInjectionEnd injection)) 0 (booklinkCommand "End" injection)
    ]

{- | Where to physically drop a booklink end anchor for a span whose end offset is
@end@. When the span ends with an environment closer @\\end{env}@ — every
statement span, and any proof whose excerpt ends with @\\end{proof}@ — that offset
sits just *after* the closer, where the bare end hypertarget runs in vertical mode
and attaches to the last content line's left edge instead of after its last glyph.
The viewer's reading-order end resolver then reads that left-edge anchor as an
overshoot onto the next paragraph and drops the span's last line (a two-line
statement like "Open/Closed subspaces of Polish spaces are\nPolish." lost the
"Polish." line). Moving the anchor to just *before* the @\\end{env}@ puts it right
after the body's last glyph in horizontal mode — the intervening newline is a
space — so the anchor is exact and the last line is covered. Only the rendered
anchor moves; the logical end offset the source map reports for coverage is
unchanged. A proof that ends mid-paragraph (no trailing @\\end@) is already exact
and left untouched.
-}
endInsertionOffset :: Text -> Int -> Int
endInsertionOffset sourceText end =
  case trailingEnvEndLength (T.take end sourceText) of
    Just len -> end - len
    Nothing -> end

-- | Length of a trailing @\\end{name}@ (name = letters and @*@), else Nothing.
trailingEnvEndLength :: Text -> Maybe Int
trailingEnvEndLength t = do
  withoutBrace <- T.stripSuffix "}" t
  let name = T.takeWhileEnd (\c -> isLetter c || c == '*') withoutBrace
  guard (not (T.null name))
  _ <- T.stripSuffix "\\end{" (T.dropEnd (T.length name) withoutBrace)
  pure (T.length name + T.length "\\end{}")

skipInsertions :: [SkipInjection] -> [Insertion]
skipInsertions = concatMap toInsertions
 where
  toInsertions skip =
    [ Insertion (skipInjectionStart skip) 2 ("\\SkipStart{" <> skipInjectionKey skip <> "}")
    , Insertion (skipInjectionEnd skip) 1 ("\\SkipEnd{" <> skipInjectionKey skip <> "}")
    ]

booklinkCommand :: Text -> BooklinkInjection -> Text
booklinkCommand suffix injection =
  "\\Booklink"
    <> suffix
    <> "["
    <> T.intercalate "," attrs
    <> "]{"
    <> T.intercalate "," (map sanitizeBooklinkName (booklinkInjectionNames injection))
    <> "}"
 where
  attrs =
    ("entry=" <> T.pack (show (booklinkInjectionIndex injection)))
      : maybe [] (\kind -> ["kind=" <> kind]) (booklinkInjectionKind injection)

{- | The state threaded through the document walk: the loaded notation data, the
mutable notation/decl/term/pending-decl references, and the set of watched
notation names. Bundled into one record so the walk functions take a single
@env@ instead of six positional arguments. The fields are env-prefixed so
their selectors never collide with the short locals (notationData, ref, ...)
that the walk functions bind by destructuring @Env notationData ref ...@.
-}
data Env = Env
  { envNotationData :: NotationData
  , envRef :: IORef NotationState
  , envDeclRef :: IORef DeclState
  , envTermRef :: IORef TermState
  , envPendingDeclRef :: IORef [DeclCommand]
  , envWatchSet :: Set Text
  }

processBlockList ::
  Env ->
  [Block] ->
  IO [Block]
processBlockList env =
  go []
 where
  -- Accumulate per-block results in reverse, then flatten once. Appending to a
  -- growing list per block would make this O(n^2) on the whole-book walker.
  go acc [] =
    return (concat (reverse acc))
  go acc (b : bs) = do
    block <- processBlockWithPending env b
    go (blockList block : acc) bs

  blockList (Div _ []) = []
  blockList (Div attr blocks)
    | attr == nullAttr = blocks
  blockList block = [block]

wrapBooklinkTexBlock :: [Text] -> Maybe Text -> [Block] -> [Block]
wrapBooklinkTexBlock _ _ [] = []
wrapBooklinkTexBlock names markerKind blocks =
  [ Div
      nullAttr
      ( [RawBlock (Format "latex") (booklinkTexComment "START" names markerKind)]
          ++ blocks
          ++ [RawBlock (Format "latex") (booklinkTexComment "END" names markerKind)]
      )
  ]

booklinkBlockKind :: [Block] -> Maybe Text
booklinkBlockKind blocks
  | any blockIsStatement blocks = Just "statement"
  | otherwise = Nothing

-- The unnumbered amsthm statement environments from
-- polish-space/tex/macros.tex, paired with the heading label each one
-- prints. Keep in sync with STATEMENT_ENVS in tools/booklink_sourcemap.py
-- and the documented list in CLAUDE.md.
statementEnvironments :: [(Text, Text)]
statementEnvironments =
  [ ("theorem*", "Theorem")
  , ("lemma*", "Lemma")
  , ("proposition*", "Proposition")
  , ("corollary*", "Corollary")
  , ("claim*", "Claim")
  , ("fact*", "Fact")
  , ("recall*", "Recall")
  , ("definition*", "Definition")
  , ("example*", "Example")
  , ("construction*", "Construction")
  , ("remark*", "Remark")
  , ("statement*", "Statement")
  ]

blockIsStatement :: Block -> Bool
blockIsStatement (RawBlock fmt txt)
  | isTexFormat fmt =
      any
        (`T.isInfixOf` txt)
        [ "\\begin{" <> T.dropEnd 1 envName
        | (envName, _) <- statementEnvironments
        ]
blockIsStatement (Div _ blocks) = any blockIsStatement blocks
blockIsStatement _ = False

booklinkTexComment :: Text -> [Text] -> Maybe Text -> Text
booklinkTexComment commentKind names markerKind =
  "% BOOKLINK-"
    <> commentKind
    <> " lean="
    <> T.intercalate "," (map sanitizeBooklinkName names)
    <> maybe "" (" kind=" <>) markerKind
    <> "\n"

sanitizeBooklinkName :: Text -> Text
sanitizeBooklinkName =
  T.map sanitizeChar
 where
  sanitizeChar c
    | c == ',' || c == '\n' || c == '\r' = '_'
    | otherwise = c

processNestedBlockList ::
  Env ->
  [Block] ->
  IO [Block]
processNestedBlockList env@(Env notationData ref declRef termRef pendingDeclRef watchSet) bs = do
  bs' <- processBlockList env bs
  pending <- readIORef pendingDeclRef
  unless (null pending) $
    declStateError "\\with declarations appeared at end of a nested block with no following block"
  return bs'

processBlockWithPending ::
  Env ->
  Block ->
  IO Block
processBlockWithPending env@(Env notationData ref declRef termRef pendingDeclRef watchSet) b
  | isMathMetaOnlyBlock b =
      processBlock env b
  | otherwise = do
      pending <- readIORef pendingDeclRef
      if null pending
        then processBlock env b
        else do
          writeIORef pendingDeclRef []
          applyDeclCommand declRef DeclScopeBegin
          mapM_ (applyDeclCommand declRef) pending
          block' <- processBlock env b
          applyDeclCommand declRef DeclScopeEnd
          return block'

isMathMetaOnlyBlock :: Block -> Bool
isMathMetaOnlyBlock (RawBlock fmt txt) =
  isTexFormat fmt && isJust (parseMathMetaBlock txt)
isMathMetaOnlyBlock _ = False

processBlock :: Env -> Block -> IO Block
processBlock env@(Env notationData ref declRef termRef pendingDeclRef watchSet) b = case b of
  RawBlock fmt txt
    | isTexFormat fmt
    , Just directives <- parseMathMetaBlock txt ->
        processMathMetaDirectives env directives
    | isTexFormat fmt
    , isMathMetaEnvironment txt ->
        declStateError "malformed mathmeta block; each active line must be a valid mathmeta directive, and \\with{...} may contain only \\vars or \\import directives"
    | isTexFormat fmt
    , hasRawNotationMarker txt ->
        processRawNotationBlock env fmt txt
    | isTexFormat fmt
    , hasRawTermMarker txt -> do
        processRawLatexBlock env fmt txt
    | isTexFormat fmt ->
        processRawLatexBlock env fmt txt
  BlockQuote bs -> BlockQuote <$> processNestedBlockList env bs
  OrderedList attrs items -> OrderedList attrs <$> mapM (processNestedBlockList env) items
  BulletList items -> BulletList <$> mapM (processNestedBlockList env) items
  Div attr bs -> Div attr <$> processNestedBlockList env bs
  Figure attr cap bs ->
    Figure attr
      <$> processCaption env cap
      <*> processNestedBlockList env bs
  DefinitionList items -> DefinitionList <$> mapM (processDefItem env) items
  Plain ils -> Plain <$> processInlineSeqWithComments True env ils
  Para ils -> Para <$> processInlineSeqWithComments True env ils
  Header level attr ils -> do
    enterSection declRef level
    Header level attr <$> processInlineSeqWithComments False env ils
  _ -> walkM (processInline env) b

processMathMetaDirectives ::
  Env ->
  [MathMetaDirective] ->
  IO Block
processMathMetaDirectives env@(Env notationData ref declRef termRef pendingDeclRef watchSet) directives = do
  blocks <- concat <$> mapM applyDirective directives
  return $ case blocks of
    [] -> Div nullAttr []
    [block] -> block
    _ -> Div nullAttr blocks
 where
  applyDirective (MathMetaDecl cmd) = do
    applyDeclCommand declRef cmd
    return []
  applyDirective (MathMetaWith cmds) = do
    modifyIORef pendingDeclRef (++ cmds)
    return []
  applyDirective (MathMetaNotation marker) = do
    modifyIORef ref (applyNotationMarker marker)
    return $ case marker of
      NotationForward _ ->
        []
      NotationDefine names ->
        blockList (notationIndexBlock (notationDisplays notationData) watchSet names)
  applyDirective (MathMetaLean _) =
    return []

  blockList (Div _ []) = []
  blockList block = [block]

notationIndexBlock :: Map Text Text -> Set Text -> Set Text -> Block
notationIndexBlock displays watchSet names =
  let entries = notationIndexText displays watchSet names
   in if T.null entries
        then Div nullAttr []
        else RawBlock (Format "latex") entries

hasRawNotationMarker :: Text -> Bool
hasRawNotationMarker =
  any isMarkerPart . parseRawNotationParts
 where
  isMarkerPart (RawNotationMarker _) = True
  isMarkerPart _ = False

hasRawTermMarker :: Text -> Bool
hasRawTermMarker txt =
  any
    (`T.isInfixOf` txt)
    [ "\\termdefineas{"
    , "\\termdefine{"
    , "\\termforwardas{"
    , "\\termforward{"
    , "\\termref{"
    , "\\termuseas{"
    , "\\termuse{"
    , "\\TermDefine{"
    , "\\TermRef{"
    , "\\TermUse{"
    , "\\index{"
    ]

replaceRawTermMarkers :: IORef TermState -> Text -> IO Text
replaceRawTermMarkers termRef =
  replaceTermMarkers termRef . normalizeTheoremTermHeadings

normalizeTheoremTermHeadings :: Text -> Text
normalizeTheoremTermHeadings raw =
  foldl' normalizeForEnv raw statementEnvironments
 where
  normalizeForEnv :: Text -> (Text, Text) -> Text
  normalizeForEnv acc (envName, headingLabel) =
    go acc
   where
    marker = "\\begin{" <> envName <> "}[\\termdefineas{"

    go txt
      | T.null rest = txt
      | otherwise =
          case parseTermTitle body of
            Nothing ->
              prefix <> marker <> go body
            Just (key, display, suffix) ->
              prefix
                <> marker
                <> key
                <> "}{"
                <> stripEnvironmentHeading headingLabel display
                <> "}]"
                <> go suffix
     where
      (prefix, afterPrefix) = T.breakOn marker txt
      rest = afterPrefix
      body = T.drop (T.length marker) afterPrefix

  parseTermTitle :: Text -> Maybe (Text, Text, Text)
  parseTermTitle body = do
    (key, afterKey) <- takeBalancedArg body
    displayBody <- T.stripPrefix "{" afterKey
    (display, afterDisplay) <- takeBalancedArg displayBody
    suffix <- T.stripPrefix "]" afterDisplay
    return (key, display, suffix)

  stripEnvironmentHeading :: Text -> Text -> Text
  stripEnvironmentHeading headingLabel display =
    fromMaybe display parenthesizedHeading
   where
    stripped = T.strip display
    parenthesizedHeading = do
      innerWithClose <- T.stripPrefix (headingLabel <> " (") stripped
      T.stripSuffix ")" innerWithClose

replaceTermMarkers :: IORef TermState -> Text -> IO Text
replaceTermMarkers termRef txt =
  case nextTermMarker txt of
    Nothing ->
      return txt
    Just (before, marker, rest) ->
      do
        rendered <- termIndexText termRef marker
        remaining <- replaceTermMarkers termRef rest
        return (before <> rendered <> remaining)

nextTermMarker :: Text -> Maybe (Text, TermMarker, Text)
nextTermMarker = go ""
 where
  -- Step over a malformed marker (e.g. an unterminated \termuse{...}) instead
  -- of abandoning the rest of the text: when the earliest marker fails to
  -- parse, fold its prefix and token into the literal accumulator and keep
  -- scanning, so well-formed markers after it are still processed.
  go acc txt =
    case earliest txt of
      Nothing -> Nothing
      Just (prefix, markerText, parseMarker) ->
        let body = T.drop (T.length markerText) (T.drop (T.length prefix) txt)
         in case parseMarker body of
              Just (marker, rest) -> Just (acc <> prefix, marker, rest)
              Nothing -> go (acc <> prefix <> markerText) body

  earliest txt = foldr chooseEarliest Nothing (candidates txt)

  candidates txt =
    [ candidate txt "\\termdefineas{" termDefineArgs
    , candidate txt "\\termdefine{" termDefineOneArg
    , candidate txt "\\TermDefine{" termDefineOneArg
    , candidate txt "\\termforwardas{" termForwardAliasArgs
    , candidate txt "\\termforward{" termForwardArg
    , candidate txt "\\termref{" (oneArg TermRef)
    , candidate txt "\\TermRef{" (oneArg TermRef)
    , candidate txt "\\termuseas{" termUseAliasArgs
    , candidate txt "\\termuse{" termUseArg
    , candidate txt "\\TermUse{" termUseArg
    , candidate txt "\\index{" (oneArg TermIndex)
    ]

  candidate txt markerText parseMarker =
    let (prefix, rest) = T.breakOn markerText txt
     in if T.null rest then Nothing else Just (prefix, markerText, parseMarker)

  oneArg mkMarker body = do
    (inner, rest) <- takeBalancedArg body
    return (mkMarker (T.strip inner), rest)

  -- A one-arg term macro immediately followed by `{` is the forbidden two-arg
  -- form (e.g. \termuse{term}{display}); flag it as TermMalformed with a clear
  -- message (reported through the standard error path) instead of rendering the
  -- second group as literal text. The "as" variants (\termuseas etc.) are the
  -- supported {term}{display} forms.
  requireOneArg :: Text -> TermMarker -> Text -> (TermMarker, Text)
  requireOneArg macro marker rest
    | "{" `T.isPrefixOf` rest =
        ( TermMalformed
            ( "\\"
                <> macro
                <> "{...} takes one argument; for {term}{display} use \\"
                <> macro
                <> "as{term}{display}"
            )
        , rest
        )
    | otherwise = (marker, rest)

  termDefineOneArg body = do
    (inner, rest) <- takeBalancedArg body
    let rendered = T.strip inner
    return (requireOneArg "termdefine" (TermDefine rendered rendered) rest)

  termForwardArg body = do
    (first, afterFirst) <- takeBalancedArg body
    let rendered = T.strip first
    return (requireOneArg "termforward" (TermForward rendered rendered) afterFirst)

  termForwardAliasArgs body = do
    (key, afterKey) <- takeBalancedArg body
    displayBody <- T.stripPrefix "{" afterKey
    (display, rest) <- takeBalancedArg displayBody
    return (TermForward (T.strip key) display, rest)

  termUseArg body = do
    (first, afterFirst) <- takeBalancedArg body
    let rendered = T.strip first
    return (requireOneArg "termuse" (TermUse rendered rendered) afterFirst)

  termUseAliasArgs body = do
    (key, afterKey) <- takeBalancedArg body
    displayBody <- T.stripPrefix "{" afterKey
    (display, rest) <- takeBalancedArg displayBody
    return (TermUse (T.strip key) display, rest)

  termDefineArgs body = do
    (key, afterKey) <- takeBalancedArg body
    case T.stripPrefix "{" afterKey of
      Just displayBody -> do
        (display, rest) <- takeBalancedArg displayBody
        return (TermDefine (T.strip key) display, rest)
      Nothing ->
        return (TermDefine (T.strip key) (T.strip key), afterKey)

  chooseEarliest Nothing y = y
  chooseEarliest x Nothing = x
  chooseEarliest x@(Just (prefixX, _, _)) y@(Just (prefixY, _, _))
    | T.length prefixX <= T.length prefixY = x
    | otherwise = y

takeBalancedArg :: Text -> Maybe (Text, Text)
takeBalancedArg = go (1 :: Int) ""
 where
  go depth acc raw =
    case T.uncons raw of
      Nothing -> Nothing
      -- A backslash escapes the next character; copy both verbatim so that
      -- \{, \}, and \\ never affect the brace depth. This matches the
      -- escaping convention used by balancedDelimited.
      Just ('\\', rest) ->
        case T.uncons rest of
          Just (escaped, rest') -> go depth (T.snoc (T.snoc acc '\\') escaped) rest'
          Nothing -> go depth (T.snoc acc '\\') rest
      Just ('{', rest) -> go (depth + 1) (T.snoc acc '{') rest
      Just ('}', rest)
        | depth <= 1 -> Just (acc, rest)
        | otherwise -> go (depth - 1) (T.snoc acc '}') rest
      Just (c, rest) -> go depth (T.snoc acc c) rest

termIndexText :: IORef TermState -> TermMarker -> IO Text
termIndexText _ (TermIndex key)
  | T.null key = return ""
  | isExistingStructuredIndex key = return ("\\index{" <> key <> "}")
  -- A raw \index{A!B} with a subentry separator is a genuine makeindex
  -- locator, not a term definition: pass it through verbatim. Forcing it
  -- through the "defined in" rewrite would append a spurious deepest level
  -- (\index{A!B!defined in}), anchor the page to A's term entry rather than B,
  -- and could overflow makeindex's subsubitem limit on a three-level key.
  | "!" `T.isInfixOf` key = return ("\\index{" <> key <> "}")
  | otherwise = return ("\\index{" <> termIndexKey key <> "!defined in|termindexpage{" <> termIndexAnchorName key <> "}}")
termIndexText termRef (TermDefine key rendered)
  | T.null key = return rendered
  | isExistingStructuredIndex key = do
      markTermDefined termRef key
      return ("\\textbf{" <> rendered <> "}\\index{" <> key <> "}")
  | otherwise = do
      markTermDefined termRef key
      return $
        "\\hyperlink{"
          <> termIndexAnchorName key
          <> "}{\\textbf{"
          <> rendered
          <> "}}"
          <> "\\index{"
          <> termIndexKey key
          <> "!defined in|termindexpage{"
          <> termIndexAnchorName key
          <> "}}"
termIndexText termRef (TermForward key rendered)
  | T.null key = return rendered
  | otherwise = do
      modifyIORef termRef $ \st ->
        st{termForwarded = Set.insert key (termForwarded st)}
      return $
        "\\hyperlink{"
          <> termIndexAnchorName key
          <> "}{"
          <> rendered
          <> "}"
          <> "\\index{"
          <> termIndexKey key
          <> "!referenced by}"
termIndexText _ (TermRef key)
  | T.null key = return ""
  | otherwise = return ("\\index{" <> termIndexKey key <> "!referenced by}")
termIndexText termRef (TermUse key rendered)
  | T.null key = return rendered
  | otherwise = do
      requireTermAvailable termRef key rendered
      return $
        "\\hyperlink{"
          <> termIndexAnchorName key
          <> "}{"
          <> rendered
          <> "}"
          <> "\\index{"
          <> termIndexKey key
          <> "!referenced by}"
termIndexText _ (TermMalformed message) = do
  hPutStrLn stderr "[term-filter] malformed term macro:"
  hPutStrLn stderr ("  " <> T.unpack message)
  exitWith (ExitFailure 1)

markTermDefined :: IORef TermState -> Text -> IO ()
markTermDefined termRef key =
  modifyIORef termRef $ \st ->
    st{termDefined = Set.insert key (termDefined st)}

requireTermAvailable :: IORef TermState -> Text -> Text -> IO ()
requireTermAvailable termRef key rendered = do
  st <- readIORef termRef
  unless (key `Set.member` termDefined st || key `Set.member` termForwarded st) $ do
    hPutStrLn stderr "[term-filter] term used before \\termdefine or \\termforward:"
    hPutStrLn stderr ("  term: " <> T.unpack key)
    hPutStrLn stderr ("  rendered: " <> T.unpack rendered)
    hPutStrLn stderr "  use \\termforward{...} or \\termforwardas{...}{...} for the informal use, or move the \\termdefine{...} earlier"
    exitWith (ExitFailure 1)

checkTermForwards :: IORef TermState -> IO ()
checkTermForwards termRef = do
  st <- readIORef termRef
  let missing = termForwarded st `Set.difference` termDefined st
  unless (Set.null missing) $ do
    hPutStrLn stderr "[term-filter] term forwarded but never defined:"
    forM_ (Set.toAscList missing) $ \key ->
      hPutStrLn stderr ("  term: " <> T.unpack key)
    hPutStrLn stderr "  add a later \\termdefine{...} or \\termdefineas{...}{...}, or replace the forward with plain text"
    exitWith (ExitFailure 1)

termIndexKey :: Text -> Text
termIndexKey key
  | "@" `T.isInfixOf` key = key
  | otherwise =
      case mathTermSortKey key of
        Nothing -> key
        Just sortKey -> sortKey <> "@" <> key

termIndexAnchorName :: Text -> Text
termIndexAnchorName key =
  "term-index-" <> T.map anchorChar (termAnchorKey key)
 where
  anchorChar c
    | isAsciiLower c || isAsciiUpper c || isDigit c = c
    | otherwise = '-'

termAnchorKey :: Text -> Text
termAnchorKey key =
  let base = fst (T.breakOn "!" key)
      sortKey = fst (T.breakOn "@" base)
   in T.toLower (fromMaybe (T.strip sortKey) (mathTermSortKey sortKey))

mathTermSortKey :: Text -> Maybe Text
mathTermSortKey key
  | "$" `T.isInfixOf` stripped || "\\" `T.isInfixOf` stripped =
      let sortKey =
            T.filter (/= '$')
              . T.filter (/= '{')
              . T.filter (/= '}')
              . T.filter (/= '_')
              . T.filter (/= '^')
              . T.replace "\\" ""
              $ stripped
       in if T.null (T.strip sortKey) then Nothing else Just (T.strip sortKey)
  | otherwise = Nothing
 where
  stripped = T.strip key

isExistingStructuredIndex :: Text -> Bool
isExistingStructuredIndex key =
  any
    (`T.isInfixOf` key)
    [ "!defined in"
    , "!referenced by"
    , "|see"
    , "|seealso"
    , "|hyperpage"
    ]
    || "further reading!" `T.isPrefixOf` key
    || "0Notation@Notation!" `T.isPrefixOf` key

processRawNotationBlock ::
  Env -> Format -> Text -> IO Block
processRawNotationBlock env@(Env notationData ref declRef termRef pendingDeclRef watchSet) fmt raw = do
  blocks <- go "" [] (parseRawNotationParts raw)
  return $ case blocks of
    [] -> Div nullAttr []
    [block] -> block
    _ -> Div nullAttr blocks
 where
  go buffer acc [] =
    (acc ++) <$> rawBlocksFromText buffer
  go buffer acc (part : parts) =
    case part of
      RawNotationText txt ->
        go (buffer <> txt) acc parts
      RawNotationMarker marker -> do
        modifyIORef ref (applyNotationMarker marker)
        let markerBlocks = case marker of
              NotationForward _ ->
                []
              NotationDefine names ->
                blockList (notationIndexBlock (notationDisplays notationData) watchSet names)
        rawBlocks <- rawBlocksFromText buffer
        go "" (acc ++ rawBlocks ++ markerBlocks) parts

  blockList (Div _ []) = []
  blockList block = [block]

  rawBlocksFromText txt = do
    block <- processRawLatexBlock env fmt txt
    return $ case block of
      Div _ [] -> []
      _ -> [block]

processRawLatexBlock ::
  Env -> Format -> Text -> IO Block
processRawLatexBlock env@(Env notationData ref declRef termRef pendingDeclRef watchSet) fmt raw = do
  replaced <- replaceRawTermMarkers termRef raw
  linked <- linkRawLatexMath notationData ref declRef watchSet replaced
  return $
    if T.null (T.strip linked)
      then Div nullAttr []
      else RawBlock fmt linked

linkRawLatexMath ::
  NotationData -> IORef NotationState -> IORef DeclState -> Set Text -> Text -> IO Text
linkRawLatexMath notationData ref declRef watchSet = go
 where
  go txt
    | T.null txt = return ""
    | isRawHeadingLine txt =
        let (line, rest) = T.breakOn "\n" txt
            (newline, afterNewline) =
              if "\n" `T.isPrefixOf` rest
                then ("\n", T.drop 1 rest)
                else ("", rest)
         in ((line <> newline) <>) <$> go afterNewline
    | "\\$" `T.isPrefixOf` txt =
        ("\\$" <>) <$> go (T.drop 2 txt)
    | "\\%" `T.isPrefixOf` txt =
        ("\\%" <>) <$> go (T.drop 2 txt)
    | "%" `T.isPrefixOf` txt =
        let (line, rest) = T.breakOn "\n" txt
            (newline, afterNewline) =
              if "\n" `T.isPrefixOf` rest
                then ("\n", T.drop 1 rest)
                else ("", rest)
         in ((line <> newline) <>) <$> go afterNewline
    | "\\(" `T.isPrefixOf` txt =
        linkDelimited InlineMath "\\(" "\\)" (T.drop 2 txt)
    | "\\[" `T.isPrefixOf` txt =
        linkDelimited DisplayMath "\\[" "\\]" (T.drop 2 txt)
    | "$$" `T.isPrefixOf` txt =
        linkDelimited DisplayMath "$$" "$$" (T.drop 2 txt)
    | "$" `T.isPrefixOf` txt =
        linkDelimited InlineMath "$" "$" (T.drop 1 txt)
    | otherwise =
        -- Copy this char plus the maximal run of ordinary text in one chunk
        -- rather than one character per recursion. Every guard above triggers
        -- on \, %, or $, so a run free of those three can never start one;
        -- stopping at the next such character preserves the same dispatch
        -- while making the pass linear instead of quadratic.
        let (ordinary, rest) = T.span (`notElem` ("\\%$" :: String)) (T.drop 1 txt)
            prefix = T.take 1 txt <> ordinary
         in (prefix <>) <$> go rest

  isRawHeadingLine txt =
    let stripped = T.stripStart txt
     in any
          (`T.isPrefixOf` stripped)
          [ "\\part{"
          , "\\chapter{"
          , "\\section{"
          , "\\subsection{"
          , "\\subsubsection{"
          , "\\paragraph{"
          , "\\subparagraph{"
          ]

  linkDelimited mathType open close rest =
    case breakRawMath close rest of
      Nothing ->
        (open <>) <$> go rest
      Just (content, afterClose) -> do
        (linked, refEntries) <- linkMathContentChecked True notationData ref declRef watchSet content
        tailText <- go afterClose
        return (open <> linked <> close <> refEntries <> tailText)

breakRawMath :: Text -> Text -> Maybe (Text, Text)
breakRawMath close = go ""
 where
  go acc txt
    | T.null txt = Nothing
    | "\\$" `T.isPrefixOf` txt =
        go (acc <> "\\$") (T.drop 2 txt)
    | close `T.isPrefixOf` txt =
        Just (acc, T.drop (T.length close) txt)
    | otherwise =
        let (prefix, rest) = T.splitAt 1 txt
         in go (acc <> prefix) rest

-- Enforce the first-use gate for watched notation, then (when linking is
-- allowed) hyperlink defined notations and collect their reference index
-- entries. Shared by raw-TeX math and Pandoc Math inlines.
linkMathContentChecked ::
  Bool -> NotationData -> IORef NotationState -> IORef DeclState -> Set Text -> Text -> IO (Text, Text)
linkMathContentChecked allowLinks notationData ref declRef watchSet content = do
  notationState <- readIORef ref
  -- The first-use gate is deliberately broader than the linker: it flags a
  -- watched name appearing anywhere in the math via isUsedIn (a control-sequence
  -- substring test), whereas linking only acts on names the math parser sees as
  -- commands. So a watched name used before its \define is caught even in a spot
  -- the linker would skip (e.g. inside \text{...}); the cost is that such a use
  -- still fails the build, which is the intended conservative behavior. Keep
  -- watched names out of those positions before their definition.
  let active = activeNotations notationState
      pending = watchSet `Set.difference` active
      offenders = Set.filter (`isUsedIn` content) pending
  if Set.null offenders
    then do
      -- Linking parses the math to a MathExpr and re-renders it; that round-trip
      -- is the identity only on brace-balanced input. Skip linking on unbalanced
      -- braces (already invalid LaTeX) so the content is passed through verbatim
      -- rather than having a closing brace fabricated for an unclosed group.
      let linkable = allowLinks && bracesBalanced content
      (content', typedNames) <-
        if linkable
          then linkTypedNotations (notationSpecs notationData) declRef active content
          else return (content, Set.empty)
      let (content'', usedNames) =
            if linkable
              then linkDefinedNotations (notationSpecs notationData) watchSet active content'
              else (content', Set.empty)
          refEntries =
            notationReferenceIndexText (notationDisplays notationData) (usedNames `Set.union` typedNames)
      return (content'', refEntries)
    else do
      hPutStrLn stderr "[notation-filter] notation used before \\define or \\forward:"
      hPutStrLn
        stderr
        ( "  missing: "
            <> intercalate ", " (map (\n -> '\\' : T.unpack n) (Set.toList offenders))
        )
      hPutStrLn stderr ("  in math: " <> T.unpack content)
      exitWith (ExitFailure 1)

notationIndexText :: Map Text Text -> Set Text -> Set Text -> Text
notationIndexText displays watchSet names =
  let watchedNames = Set.toAscList (names `Set.intersection` watchSet)
      entry name =
        "\\index{0Notation@Notation!"
          <> name
          <> "@"
          <> notationIndexDisplayForIndex displays name
          <> "!defined in|notationindexpage{"
          <> notationIndexAnchorName name
          <> "}}"
   in T.unlines (map entry watchedNames)

notationReferenceIndexText :: Map Text Text -> Set Text -> Text
notationReferenceIndexText displays names =
  T.concat (map entry (Set.toAscList names))
 where
  entry name =
    "\\index{0Notation@Notation!" <> name <> "@" <> notationIndexDisplayForIndex displays name <> "!referenced by}"

notationIndexAnchorName :: Text -> Text
notationIndexAnchorName name = "notation-index-" <> name

notationHyperlink :: Text -> Text -> Text
notationHyperlink name body =
  "{\\hyperlink{" <> notationIndexAnchorName name <> "}{" <> body <> "}}"

notationIndexDisplay :: Map Text Text -> Text -> Text
notationIndexDisplay displays name =
  case Map.lookup name displays of
    Just display -> display
    Nothing -> "$\\" <> name <> "$"

notationIndexDisplayForIndex :: Map Text Text -> Text -> Text
notationIndexDisplayForIndex displays name =
  protectLatexCommands (notationIndexDisplay displays name)

protectLatexCommands :: Text -> Text
protectLatexCommands txt
  | T.null txt = ""
  | Just rest <- T.stripPrefix "\\" txt =
      let (cmd, tailText) = T.span isLetter rest
       in if T.null cmd
            then case T.uncons rest of
              Nothing -> "\\"
              Just (c, rest') -> "\\protect\\" <> T.singleton c <> protectLatexCommands rest'
            else "\\protect\\" <> cmd <> protectLatexCommands tailText
  | otherwise =
      T.take 1 txt <> protectLatexCommands (T.drop 1 txt)

-- Read notation displays from the book's semantic-macros file. A line of the form
--
--   % notation-index: $\diam_d(A)$
--   \newcommand{\diam}{...}
--
-- supplies a contextual display. Without that hint, the display is synthesized
-- from the macro arity, e.g. \newcommand{\funcspace}[2]{...} gives

readNotationData :: FilePath -> IO NotationData
readNotationData path = do
  content <- readMacrosFile "notation-filter" path
  let (displays, specs) = collectNotationData Nothing Map.empty Map.empty (T.lines content)
  return (NotationData displays specs)

collectNotationData ::
  Maybe Text ->
  Map Text Text ->
  Map Text MacroSpec ->
  [Text] ->
  (Map Text Text, Map Text MacroSpec)
collectNotationData _ displays specs [] = (displays, specs)
collectNotationData pending displays specs (line : rest)
  | Just display <- parseNotationIndexHint line =
      collectNotationData (Just display) displays specs rest
  | Just (name, spec) <- parseNewCommand line =
      let display = fromMaybe (synthesizedDisplay name (macroMandatoryArgs spec)) pending
       in collectNotationData Nothing (Map.insert name display displays) (Map.insert name spec specs) rest
  | T.null (T.strip line) || "%" `T.isPrefixOf` T.strip line =
      collectNotationData pending displays specs rest
  | otherwise =
      collectNotationData Nothing displays specs rest

parseNotationIndexHint :: Text -> Maybe Text
parseNotationIndexHint line =
  T.strip <$> T.stripPrefix "% notation-index:" (T.strip line)

parseNewCommand :: Text -> Maybe (Text, MacroSpec)
parseNewCommand line = do
  rest <- T.stripPrefix "\\newcommand{\\" (T.strip line)
  let (name, afterName) = T.breakOn "}" rest
  if T.null name || T.null afterName
    then Nothing
    else Just (name, macroSpec (T.drop 1 afterName))

macroSpec :: Text -> MacroSpec
macroSpec afterName =
  let (totalArgs, afterArgSpec) = parseArgCount afterName
      hasOptional = hasOptionalDefault afterArgSpec && totalArgs > 0
   in MacroSpec
        { macroMandatoryArgs = if hasOptional then totalArgs - 1 else totalArgs
        , macroHasOptionalArg = hasOptional
        }

parseArgCount :: Text -> (Int, Text)
parseArgCount txt =
  case T.stripPrefix "[" (T.stripStart txt) of
    Nothing -> (0, txt)
    Just rest ->
      let (digits, afterDigits) = T.span isDigit rest
       in case T.stripPrefix "]" afterDigits of
            Just afterClose
              | not (T.null digits) -> (read (T.unpack digits), afterClose)
            _ -> (0, txt)

hasOptionalDefault :: Text -> Bool
hasOptionalDefault txt =
  case T.stripPrefix "[" (T.stripStart txt) of
    Just _ -> True
    Nothing -> False

synthesizedDisplay :: Text -> Int -> Text
synthesizedDisplay name argCount =
  "$\\" <> name <> T.concat (map placeholder [0 .. argCount - 1]) <> "$"
 where
  placeholder n = "{" <> T.singleton (toEnum (fromEnum 'A' + n)) <> "}"

processDefItem ::
  Env ->
  ([Inline], [[Block]]) ->
  IO ([Inline], [[Block]])
processDefItem env (term, defs) = do
  term' <- mapM (processInline env) term
  defs' <- mapM (processNestedBlockList env) defs
  return (term', defs')

processCaption ::
  Env ->
  Caption ->
  IO Caption
processCaption env (Caption short blocks) = do
  short' <- mapM (processInlineSeqWithComments True env) short
  blocks' <- processNestedBlockList env blocks
  return (Caption short' blocks')

isTexFormat :: Format -> Bool
isTexFormat (Format fmt) = fmt == "tex" || fmt == "latex"

processInline :: Env -> Inline -> IO Inline
processInline = processInlineWithLinks True

processInlineSeqWithComments :: Bool -> Env -> [Inline] -> IO [Inline]
processInlineSeqWithComments allowLinks env = go False
 where
  go _ [] = return []
  go inComment (i : is)
    | inlineEndsTexComment i = do
        i' <- processCurrent inComment i
        (i' :) <$> go False is
    | inComment = do
        i' <- suppressCommentedMarker i
        (i' :) <$> go True is
    | otherwise = do
        i' <- processInlineWithLinks allowLinks env i
        (i' :) <$> go (inlineStartsTexComment i) is

  processCurrent inComment i
    | inComment = suppressCommentedMarker i
    | otherwise = processInlineWithLinks allowLinks env i

  -- Inside a LaTeX line comment, drop both notation and term markers so a
  -- commented-out \define/\termdefine/\termuse neither emits an index entry
  -- nor survives as raw text in the rendered line. The whole RawInline lies
  -- after the % on its line (comments run to the next Soft/LineBreak, which
  -- resets inComment), so blanking it cannot swallow live content.
  suppressCommentedMarker (RawInline fmt txt)
    | isTexFormat fmt
    , Just _ <- parseNotationMarker txt =
        return $ Span nullAttr []
    | isTexFormat fmt
    , hasRawTermMarker txt =
        return $ Span nullAttr []
  suppressCommentedMarker i = return i

inlineEndsTexComment :: Inline -> Bool
inlineEndsTexComment SoftBreak = True
inlineEndsTexComment LineBreak = True
inlineEndsTexComment _ = False

inlineStartsTexComment :: Inline -> Bool
inlineStartsTexComment (RawInline fmt txt)
  | isTexFormat fmt = hasUnescapedPercent txt
inlineStartsTexComment _ = False

hasUnescapedPercent :: Text -> Bool
hasUnescapedPercent txt
  | T.null txt = False
  | Just rest <- T.stripPrefix "\\%" txt = hasUnescapedPercent rest
  | Just _ <- T.stripPrefix "%" txt = True
  | otherwise = hasUnescapedPercent (T.drop 1 txt)

processInlineWithLinks :: Bool -> Env -> Inline -> IO Inline
processInlineWithLinks allowLinks env (Emph ils) =
  Emph <$> processInlineSeqWithComments False env ils
processInlineWithLinks allowLinks env (Underline ils) =
  Underline <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Strong ils) =
  Strong <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Strikeout ils) =
  Strikeout <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Superscript ils) =
  Superscript <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Subscript ils) =
  Subscript <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (SmallCaps ils) =
  SmallCaps <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Quoted quoteType ils) =
  Quoted quoteType <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Cite citations ils) =
  Cite citations <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Link attr ils target) =
  (\ils' -> Link attr ils' target) <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Image attr ils target) =
  (\ils' -> Image attr ils' target) <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Span attr ils) =
  Span attr <$> processInlineSeqWithComments allowLinks env ils
processInlineWithLinks allowLinks env (Note blocks) =
  Note <$> processNestedBlockList env blocks
processInlineWithLinks allowLinks (Env notationData ref declRef termRef pendingDeclRef watchSet) (RawInline fmt txt)
  | isTexFormat fmt
  , Just marker <- parseNotationMarker txt = do
      modifyIORef ref (applyNotationMarker marker)
      let entries = case marker of
            NotationForward _ -> ""
            NotationDefine names -> notationIndexText (notationDisplays notationData) watchSet names
      return $
        if T.null entries
          then Span nullAttr []
          else RawInline (Format "latex") entries
  | isTexFormat fmt
  , hasRawTermMarker txt = do
      entries <- replaceRawTermMarkers termRef txt
      return $
        if T.null (T.strip entries)
          then Span nullAttr []
          else RawInline fmt entries
processInlineWithLinks allowLinks (Env notationData ref declRef termRef pendingDeclRef watchSet) (Math mt content) = do
  (content', refEntries) <-
    linkMathContentChecked allowLinks notationData ref declRef watchSet content
  return $
    if T.null refEntries
      then Math mt content'
      else RawInline (Format "latex") (renderMathWithIndex mt content' refEntries)
processInlineWithLinks _ _ i = return i

renderMathWithIndex :: MathType -> Text -> Text -> Text
renderMathWithIndex InlineMath content indexEntries =
  "\\(" <> content <> "\\)" <> indexEntries
renderMathWithIndex DisplayMath content indexEntries =
  "\\[" <> content <> "\\]" <> indexEntries

tokenizeMath :: Text -> [MathToken]
tokenizeMath txt
  | T.null txt = []
  | Just rest <- T.stripPrefix "\\" txt =
      case T.uncons rest of
        Nothing -> [TokText "\\"]
        Just (c, rest')
          | isLetter c ->
              let (nameTail, tailText) = T.span isLetter rest'
               in TokCommand (T.cons c nameTail) : tokenizeMath tailText
          | otherwise ->
              TokCommand (T.singleton c) : tokenizeMath rest'
  | Just rest <- T.stripPrefix "{" txt = TokLBrace : tokenizeMath rest
  | Just rest <- T.stripPrefix "}" txt = TokRBrace : tokenizeMath rest
  | Just rest <- T.stripPrefix "[" txt = TokLBracket : tokenizeMath rest
  | Just rest <- T.stripPrefix "]" txt = TokRBracket : tokenizeMath rest
  | Just rest <- T.stripPrefix "_" txt = TokSub : tokenizeMath rest
  | Just rest <- T.stripPrefix "^" txt = TokSup : tokenizeMath rest
  | otherwise =
      let (chunk, rest) = T.span (not . isMathSpecial) txt
       in TokText chunk : tokenizeMath rest
 where
  isMathSpecial c = c `elem` ("\\{}[]_^" :: String)

parseMathExpr :: Text -> MathExpr
parseMathExpr = MathSeq . fst . parseMathSeq Nothing . tokenizeMath

parseMathSeq :: Maybe MathToken -> [MathToken] -> ([MathExpr], [MathToken])
parseMathSeq stop = go []
 where
  go acc [] = (reverse acc, [])
  go acc toks@(tok : rest)
    | Just tok == stop = (reverse acc, rest)
    | otherwise =
        let (expr, rest') = parseMathTerm toks
         in go (expr : acc) rest'

parseMathTerm :: [MathToken] -> (MathExpr, [MathToken])
parseMathTerm toks =
  let (base, rest) = parseMathAtom toks
   in parseScripts base rest

parseMathAtom :: [MathToken] -> (MathExpr, [MathToken])
parseMathAtom [] = (MathSeq [], [])
parseMathAtom (TokText txt : rest) = (MathText txt, rest)
parseMathAtom (TokCommand name : rest) =
  let (optionalArg, afterOptional) = parseOptionalMathArg rest
      (args, afterArgs) = parseBracedMathArgs afterOptional
   in (MathCommand name optionalArg args, afterArgs)
parseMathAtom (TokLBrace : rest) =
  let (items, afterGroup) = parseMathSeq (Just TokRBrace) rest
   in (MathGroup (MathSeq items), afterGroup)
parseMathAtom (TokLBracket : rest) = (MathText "[", rest)
parseMathAtom (TokRBrace : rest) = (MathText "}", rest)
parseMathAtom (TokRBracket : rest) = (MathText "]", rest)
parseMathAtom (TokSub : rest) = (MathText "_", rest)
parseMathAtom (TokSup : rest) = (MathText "^", rest)

parseOptionalMathArg :: [MathToken] -> (Maybe MathExpr, [MathToken])
parseOptionalMathArg toks@(TokLBracket : rest) =
  case parseBracketedMathArg rest of
    Just (items, afterArg) -> (Just (MathSeq items), afterArg)
    Nothing -> (Nothing, toks)
parseOptionalMathArg toks = (Nothing, toks)

{- | Parse the body of an optional @[...]@ argument, returning 'Nothing' when no
closing @]@ exists at this level. In that case the @[@ is a literal bracket,
such as the half-open interval in @\\to[0,\\infty)@, and must not be treated
as an optional argument: 'renderMathExpr' always re-emits a closing @]@ for an
optional argument, so accepting an unterminated @[@ would fabricate a stray
@]@ in the rendered math.
-}
parseBracketedMathArg :: [MathToken] -> Maybe ([MathExpr], [MathToken])
parseBracketedMathArg = go []
 where
  go _ [] = Nothing
  go acc (TokRBracket : rest) = Just (reverse acc, rest)
  go acc toks =
    let (expr, rest') = parseMathTerm toks
     in go (expr : acc) rest'

parseBracedMathArgs :: [MathToken] -> ([MathExpr], [MathToken])
parseBracedMathArgs (TokLBrace : rest) =
  let (items, afterArg) = parseMathSeq (Just TokRBrace) rest
      (args, tailText) = parseBracedMathArgs afterArg
   in (MathSeq items : args, tailText)
parseBracedMathArgs toks = ([], toks)

parseScripts :: MathExpr -> [MathToken] -> (MathExpr, [MathToken])
parseScripts base (TokSub : rest) =
  let (arg, afterArg) = parseScriptArg rest
   in parseScripts (MathScript base "_" arg) afterArg
parseScripts base (TokSup : rest) =
  let (arg, afterArg) = parseScriptArg rest
   in parseScripts (MathScript base "^" arg) afterArg
parseScripts base toks = (base, toks)

parseScriptArg :: [MathToken] -> (MathExpr, [MathToken])
parseScriptArg (TokLBrace : rest) =
  let (items, afterArg) = parseMathSeq (Just TokRBrace) rest
   in (MathGroup (MathSeq items), afterArg)
parseScriptArg toks = parseMathAtom toks

renderMathExpr :: MathExpr -> Text
renderMathExpr (MathSeq items) = T.concat (map renderMathExpr items)
renderMathExpr (MathCommand name optionalArg args) =
  "\\" <> name <> renderOptional optionalArg <> T.concat (map renderBraced args)
 where
  renderOptional Nothing = ""
  renderOptional (Just arg) = "[" <> renderMathExpr arg <> "]"
  renderBraced arg = "{" <> renderMathExpr arg <> "}"
renderMathExpr (MathGroup expr) = "{" <> renderMathExpr expr <> "}"
renderMathExpr (MathScript base marker arg) =
  renderMathExpr base <> marker <> renderScriptArg arg
 where
  renderScriptArg (MathGroup expr) = "{" <> renderMathExpr expr <> "}"
  renderScriptArg expr = renderMathExpr expr
renderMathExpr (MathText txt) = txt
renderMathExpr (MathRaw txt) = txt

linkDefinedNotations :: Map Text MacroSpec -> Set Text -> Set Text -> Text -> (Text, Set Text)
linkDefinedNotations specs watchSet defined content =
  let (expr, names) = linkDefinedNotationsExpr specs watchSet defined (parseMathExpr content)
   in (renderMathExpr expr, names)

linkDefinedNotationsExpr :: Map Text MacroSpec -> Set Text -> Set Text -> MathExpr -> (MathExpr, Set Text)
linkDefinedNotationsExpr specs watchSet defined = go
 where
  linkable = watchSet `Set.intersection` defined

  go (MathSeq items) =
    let (items', nameSets) = unzip (map go items)
     in (MathSeq items', Set.unions nameSets)
  go cmd@(MathCommand "hyperlink" _ _) =
    (cmd, Set.empty)
  go cmd@(MathCommand name optionalArg args)
    | name `Set.member` linkable
    , hasRequiredShape (Map.findWithDefault (MacroSpec 0 False) name specs) optionalArg args =
        let nestedNames =
              collectLinkedNotationNames optionalArg args
         in ( MathRaw (notationHyperlink name (renderMathExpr cmd))
            , Set.insert name nestedNames
            )
    | otherwise =
        let (optionalArg', optionalNames) =
              case optionalArg of
                Nothing -> (Nothing, Set.empty)
                Just arg ->
                  let (arg', names) = go arg
                   in (Just arg', names)
            (args', argNameSets) = unzip (map go args)
         in (MathCommand name optionalArg' args', optionalNames `Set.union` Set.unions argNameSets)
  go (MathGroup expr) =
    let (expr', names) = go expr
     in (MathGroup expr', names)
  go (MathScript base marker arg) =
    let (base', baseNames) = go base
        (arg', argNames) = go arg
     in (MathScript base' marker arg', baseNames `Set.union` argNames)
  go expr = (expr, Set.empty)

  collectLinkedNotationNames optionalArg args =
    let optionalNames =
          case optionalArg of
            Nothing -> Set.empty
            Just arg -> snd (go arg)
        argNames = Set.unions (map (snd . go) args)
     in optionalNames `Set.union` argNames

  hasRequiredShape spec optionalArg args =
    (macroHasOptionalArg spec || isNothing optionalArg)
      && length args >= macroMandatoryArgs spec

linkTypedNotations :: Map Text MacroSpec -> IORef DeclState -> Set Text -> Text -> IO (Text, Set Text)
linkTypedNotations specs declRef defined content = do
  (expr, names) <- linkTypedNotationsExpr specs declRef defined (parseMathExpr content)
  return (renderMathExpr expr, names)

linkTypedNotationsExpr :: Map Text MacroSpec -> IORef DeclState -> Set Text -> MathExpr -> IO (MathExpr, Set Text)
linkTypedNotationsExpr specs declRef defined = go
 where
  go (MathSeq items) = processSeq items
  go cmd@(MathCommand name _ (arg : _)) = do
    st <- readIORef declRef
    if isPrefixTypedNotation st name
      then do
        let argText = renderMathExpr arg
        target <- typedNotationTarget st name argText
        checkTypedTargetDefined defined target (renderMathExpr cmd)
        let useText = renderMathExpr cmd
            linked = notationHyperlink target useText
        return (MathRaw linked, Set.singleton target)
      else processMathCommand cmd
  go (MathCommand name optionalArg args) = do
    processMathCommand (MathCommand name optionalArg args)
  go (MathGroup expr) = do
    (expr', names) <- go expr
    return (MathGroup expr', names)
  go (MathScript base marker arg) = do
    (base', baseNames) <- go base
    (arg', argNames) <- go arg
    return (MathScript base' marker arg', baseNames `Set.union` argNames)
  go expr = return (expr, Set.empty)

  processMathCommand (MathCommand name optionalArg args) = do
    (optionalArg', optionalNames) <-
      case optionalArg of
        Nothing -> return (Nothing, Set.empty)
        Just arg -> do
          (arg', names) <- go arg
          return (Just arg', names)
    processedArgs <- mapM go args
    let (args', argNameSets) = unzip processedArgs
    return (MathCommand name optionalArg' args', optionalNames `Set.union` Set.unions argNameSets)
  processMathCommand expr = return (expr, Set.empty)

  processSeq [] = return (MathSeq [], Set.empty)
  processSeq (item : items) = do
    (item', itemNames) <- go item
    st <- readIORef declRef
    case inferPostfixBaseType st (renderMathExpr item) of
      Just ty -> do
        (chainItem, chainNames, rest) <- processPostfixChain ty item' itemNames items
        (MathSeq restItems, restNames) <- processSeq rest
        return (MathSeq (chainItem : restItems), chainNames `Set.union` restNames)
      Nothing -> do
        (MathSeq restItems, restNames) <- processSeq items
        return (MathSeq (item' : restItems), itemNames `Set.union` restNames)

  processPostfixChain ty base baseNames (cmd@(MathCommand name optionalArg args) : rest) =
    do
      st <- readIORef declRef
      if not (isPostfixTypedNotation st name)
        then return (base, baseNames, cmd : rest)
        else case Map.lookup (name, ty) (declNotationTypes st) of
          Nothing -> return (base, baseNames, cmd : rest)
          Just target -> do
            checkTypedTargetDefined defined target (renderMathExpr base <> renderMathExpr cmd)
            (optionalArg', optionalNames) <-
              case optionalArg of
                Nothing -> return (Nothing, Set.empty)
                Just arg -> do
                  (arg', names) <- go arg
                  return (Just arg', names)
            processedArgs <- mapM go args
            let (args', argNameSets) = unzip processedArgs
                cmd' = MathCommand name optionalArg' args'
                useText = renderMathExpr base <> renderMathExpr cmd'
                linked = MathRaw (notationHyperlink target useText)
                names = baseNames `Set.union` optionalNames `Set.union` Set.unions argNameSets `Set.union` Set.singleton target
            processPostfixChain ty linked names rest
  processPostfixChain _ base baseNames rest =
    return (base, baseNames, rest)

  isPrefixTypedNotation :: DeclState -> Text -> Bool
  isPrefixTypedNotation st name =
    any (targetHasArity name) (typedNotationTargetsFor st name)

  isPostfixTypedNotation :: DeclState -> Text -> Bool
  isPostfixTypedNotation st name =
    any (targetHasPostfixArity name) (typedNotationTargetsFor st name)

  typedNotationTargetsFor :: DeclState -> Text -> [Text]
  typedNotationTargetsFor st name =
    [target | ((notation, _), target) <- Map.toList (declNotationTypes st), notation == name]

  targetHasArity :: Text -> Text -> Bool
  targetHasArity name target =
    macroArity target == macroArity name

  targetHasPostfixArity :: Text -> Text -> Bool
  targetHasPostfixArity name target =
    macroArity target == macroArity name + 1

  macroArity :: Text -> Int
  macroArity name =
    macroMandatoryArgs (Map.findWithDefault (MacroSpec 0 False) name specs)

typedNotationTarget :: DeclState -> Text -> Text -> IO Text
typedNotationTarget st notation arg =
  case inferDeclType st arg of
    Just ty ->
      case Map.lookup (notation, ty) (declNotationTypes st) of
        Just target -> return target
        Nothing -> do
          hPutStrLn stderr "[notation-filter] no target declared for typed notation:"
          hPutStrLn stderr ("  notation: " <> T.unpack notation)
          hPutStrLn stderr ("  type: " <> T.unpack ty)
          hPutStrLn stderr ("  add a declaration such as \\DeclNotationType{" <> T.unpack notation <> "}{" <> T.unpack ty <> "}{...}")
          exitWith (ExitFailure 1)
    Nothing -> do
      hPutStrLn stderr "[notation-filter] could not infer the syntactic type of a typed notation argument:"
      hPutStrLn stderr ("  argument: " <> T.unpack arg)
      hPutStrLn stderr "  add a declaration such as \\vars{M,N}{some-type} or a local \\scopebegin block"
      exitWith (ExitFailure 1)

inferPostfixBaseType :: DeclState -> Text -> Maybe DeclType
inferPostfixBaseType st rawArg = do
  guard (isPostfixBaseCandidate rawArg)
  inferDeclType st rawArg

isPostfixBaseCandidate :: Text -> Bool
isPostfixBaseCandidate rawArg =
  let arg = T.strip rawArg
   in not (T.null arg)
        && not ("&" `T.isInfixOf` arg)
        && not (":=" `T.isInfixOf` arg)
        && maybe False (not . isPostfixDelimiter . fst) (T.uncons arg)
 where
  isPostfixDelimiter c = c `elem` (",.;:=" :: String)

checkTypedTargetDefined :: Set Text -> Text -> Text -> IO ()
checkTypedTargetDefined defined target useText =
  unless (target `Set.member` defined) $ do
    hPutStrLn stderr "[notation-filter] typed notation target used before \\define:"
    hPutStrLn stderr ("  target: \\" <> T.unpack target)
    hPutStrLn stderr ("  in math: " <> T.unpack useText)
    exitWith (ExitFailure 1)

inferDeclType :: DeclState -> Text -> Maybe DeclType
inferDeclType st rawArg =
  let arg = normalizeMathExpr rawArg
      base = baseMathName arg
      env = activeDeclEnv st
   in Map.lookup arg env
        <|> inferStructuralDeclType st env rawArg
        <|> Map.lookup base env

inferStructuralDeclType :: DeclState -> Map Text DeclType -> Text -> Maybe DeclType
inferStructuralDeclType st env rawArg =
  inferExprType st env (parseMathExpr rawArg)
    <|> inferPostfix
    <|> inferContains
    <|> inferHead
    <|> inferJuxtaposed
 where
  arg = normalizeMathExpr rawArg

  inferContains =
    fmap snd (find (\(token, _) -> token `T.isInfixOf` arg) (declInferContains st))

  inferPostfix =
    asum
      [ Map.lookup base env <|> inferStructuralDeclType st env base
      | command <- Set.toList (declInferPostfix st)
      , Just base <- [postfixCommandBase ("\\" <> command) arg]
      ]

  inferHead = do
    (headName, _) <- splitHeadApplication arg
    kind <-
      if isUpperHead headName
        then Just DeclHeadUpper
        else
          if isLowerHead headName
            then Just DeclHeadLower
            else Nothing
    Map.lookup kind (declInferHeads st)

  inferJuxtaposed =
    asum
      [ Just ty
      | ty <- Set.toList (declInferJuxtaposed st)
      , allDeclaredAs ty env (T.chunksOf 1 arg)
      ]

inferExprType :: DeclState -> Map Text DeclType -> MathExpr -> Maybe DeclType
inferExprType st env expr =
  inferAtom expr
    <|> inferBinder expr
    <|> inferPrefix expr
    <|> inferInfix expr
 where
  inferAtom (MathCommand name _ []) =
    Map.lookup name (declInferAtoms st)
  inferAtom (MathSeq [item]) =
    inferAtom item
  inferAtom _ =
    Nothing

  inferPrefix (MathCommand name _ _) =
    Map.lookup name (declInferPrefixes st)
  inferPrefix (MathSeq (item : rest))
    | not (null (meaningfulMathItems rest)) =
        case itemOperatorName item of
          Just name -> Map.lookup name (declInferPrefixes st)
          Nothing -> Nothing
  inferPrefix _ =
    Nothing

  inferBinder (MathCommand name _ args)
    | length args >= 2 =
        Map.lookup name (declInferBinders st)
  inferBinder (MathSeq [item]) =
    inferBinder item
  inferBinder (MathSeq (item : rest))
    | hasBinderBody rest =
        case itemOperatorName item of
          Just name -> Map.lookup name (declInferBinders st)
          Nothing -> Nothing
  inferBinder _ =
    Nothing

  inferInfix (MathSeq items) = do
    (leftItems, spec, rightItems) <- splitDeclaredInfix st (meaningfulMathItems items)
    guard (not (null leftItems) && not (null rightItems))
    return (declInfixType spec)
  inferInfix _ =
    Nothing

meaningfulMathItems :: [MathExpr] -> [MathExpr]
meaningfulMathItems =
  filter (not . isBlankMathExpr)

isBlankMathExpr :: MathExpr -> Bool
isBlankMathExpr (MathText txt) = T.null (T.strip txt)
isBlankMathExpr _ = False

hasBinderBody :: [MathExpr] -> Bool
hasBinderBody items =
  let tailText = normalizeBinderTail (renderMathExpr (MathSeq items))
   in not (T.null tailText)

normalizeBinderTail :: Text -> Text
normalizeBinderTail =
  T.filter (not . (`elem` (" \n\t.,;" :: String)))
    . T.replace "\\," ""
    . T.replace "\\;" ""
    . T.replace "\\!" ""
    . T.replace "\\:" ""

splitDeclaredInfix :: DeclState -> [MathExpr] -> Maybe ([MathExpr], DeclInfix, [MathExpr])
splitDeclaredInfix st items = do
  let candidates =
        [ (idx, spec)
        | (idx, item) <- zip [0 ..] items
        , Just name <- [itemOperatorName item]
        , Just spec <- [Map.lookup name (declInferInfixes st)]
        ]
  (_, topSpec) <- maximumByLevel candidates
  let sameLevel = filter ((== declInfixLevel topSpec) . declInfixLevel . snd) candidates
  (idx, spec) <- chooseByAssoc (declInfixAssoc topSpec) sameLevel
  case splitAt idx items of
    (leftItems, _ : rightItems) -> Just (leftItems, spec, rightItems)
    _ -> Nothing

maximumByLevel :: [(Int, DeclInfix)] -> Maybe (Int, DeclInfix)
maximumByLevel [] = Nothing
maximumByLevel (x : xs) =
  Just (foldl pick x xs)
 where
  pick best@(_, bestSpec) candidate@(_, candidateSpec)
    | declInfixLevel candidateSpec > declInfixLevel bestSpec = candidate
    | otherwise = best

-- The operator that governs the split: leftmost for right-associative (so the
-- rest re-associates to the right) and for non-associative, rightmost for
-- left-associative. 'Nothing' for an empty candidate list rather than a crash.
chooseByAssoc :: DeclAssoc -> [(Int, DeclInfix)] -> Maybe (Int, DeclInfix)
chooseByAssoc _ [] = Nothing
chooseByAssoc DeclAssocRight (c : _) = Just c
chooseByAssoc DeclAssocLeft cs = Just (last cs)
chooseByAssoc DeclAssocNon (c : _) = Just c

itemOperatorName :: MathExpr -> Maybe Text
itemOperatorName (MathCommand name _ []) = Just name
itemOperatorName (MathText txt) =
  let stripped = normalizeDeclName txt
   in if T.null stripped then Nothing else Just stripped
itemOperatorName _ = Nothing

postfixCommandBase :: Text -> Text -> Maybe Text
postfixCommandBase command arg =
  case T.breakOn command arg of
    (base, rest)
      | T.null base || T.null rest -> Nothing
      | otherwise -> Just base

normalizeMathExpr :: Text -> Text
normalizeMathExpr =
  T.filter (not . (`elem` (" \n\t" :: String)))
    . T.replace "\\," ""
    . T.replace "\\;" ""
    . T.replace "\\!" ""

baseMathName :: Text -> Text
baseMathName txt =
  let noSub = fst (T.breakOn "_" txt)
      noSup = fst (T.breakOn "^" noSub)
   in if T.null noSup then txt else noSup

splitHeadApplication :: Text -> Maybe (Text, Text)
splitHeadApplication txt = do
  let (headName, rest) = T.span (\c -> isLetter c || c == '\\') txt
  rest' <- T.stripPrefix "(" rest
  _ <- T.stripSuffix ")" rest'
  if T.null headName then Nothing else Just (headName, rest')

isUpperHead :: Text -> Bool
isUpperHead txt =
  case T.uncons txt of
    Just (c, _) -> isAsciiUpper c
    Nothing -> False

isLowerHead :: Text -> Bool
isLowerHead txt =
  case T.uncons txt of
    Just (c, _) -> isAsciiLower c
    Nothing -> False

allDeclaredAs :: DeclType -> Map Text DeclType -> [Text] -> Bool
allDeclaredAs ty env names =
  not (null names) && all (\name -> Map.lookup name env == Just ty) names

parseMandatoryArg :: Text -> Maybe (Text, Text)
parseMandatoryArg txt =
  case T.uncons txt of
    Just ('{', _) -> balancedDelimited '{' '}' txt
    _ -> Nothing

balancedDelimited :: Char -> Char -> Text -> Maybe (Text, Text)
balancedDelimited open close txt =
  case T.uncons txt of
    Just (c, rest) | c == open -> scan 1 (T.singleton open) rest
    _ -> Nothing
 where
  scan :: Int -> Text -> Text -> Maybe (Text, Text)
  scan depth acc rest =
    case T.uncons rest of
      Nothing -> Nothing
      Just (c, tailText)
        | c == open -> scan (depth + 1) (T.snoc acc c) tailText
        | c == close ->
            let acc' = T.snoc acc c
             in if depth == 1
                  then Just (acc', tailText)
                  else scan (depth - 1) acc' tailText
        | c == '\\' ->
            case T.uncons tailText of
              Just (escaped, tailText') ->
                scan depth (T.snoc (T.snoc acc c) escaped) tailText'
              Nothing -> scan depth (T.snoc acc c) tailText
        | otherwise -> scan depth (T.snoc acc c) tailText

-- True iff `{` and `}` are balanced in math content, treating any backslash as
-- escaping the next character (so \{, \}, and \\ never count as group braces).
bracesBalanced :: Text -> Bool
bracesBalanced = go (0 :: Int)
 where
  go depth txt = case T.uncons txt of
    Nothing -> depth == 0
    Just ('\\', rest) -> go depth (T.drop 1 rest)
    Just ('{', rest) -> go (depth + 1) rest
    Just ('}', rest) -> depth > 0 && go (depth - 1) rest
    Just (_, rest) -> go depth rest

-- True iff `\name` appears as a control sequence in `content`: a real command
-- backslash, with a proper right boundary (next char absent or non-letter).
-- The left guard rejects an even run of preceding backslashes, e.g. the \name
-- in \\name is text (the \\ is an escaped backslash / line break), not a use.
isUsedIn :: Text -> Text -> Bool
isUsedIn name = go
 where
  pat = T.cons '\\' name
  plen = T.length pat
  go t = case T.breakOn pat t of
    (before, after)
      | T.null after -> False
      | leftOK before && rightOK after -> True
      | otherwise -> go (T.drop 1 after)
   where
    -- The matched backslash starts a real command only when the run of
    -- backslashes ending at it is odd, i.e. an even number precede it.
    leftOK before = even (T.length (T.takeWhileEnd (== '\\') before))
    rightOK after =
      let after' = T.drop plen after
       in T.null after' || not (isLetter (T.head after'))

-- ----------------------------------------------------------------------------
-- Section reference resolution.
--
-- Source syntax: a section is given a stable id with Pandoc's native
-- attribute syntax, e.g.
--
--     ## Boundary and the mediant-limit map {#sec:boundary-mediant-limit}
--
-- A cross-reference is written `§{sec:boundary-mediant-limit}` and is
-- expanded to `§"<title of that section>"` (as a Link to the section
-- anchor) at filter time. Unknown ids fail the build.
--
-- Raw LaTeX environments are not parsed into normal Pandoc inlines, so the
-- same source syntax is rewritten there as an explicit hyperref.
-- ----------------------------------------------------------------------------

replaceDependencyGraphBlock :: Text -> Block -> Block
replaceDependencyGraphBlock graph (RawBlock fmt txt)
  | isTexFormat fmt
  , "\\DependencyGraph" `T.isInfixOf` txt =
      RawBlock (Format "latex") (T.replace "\\DependencyGraph" graph txt)
replaceDependencyGraphBlock _ block = block

replaceDependencyGraphInline :: Text -> Inline -> Inline
replaceDependencyGraphInline graph (RawInline fmt txt)
  | isTexFormat fmt
  , "\\DependencyGraph" `T.isInfixOf` txt =
      RawInline (Format "latex") (T.replace "\\DependencyGraph" graph txt)
replaceDependencyGraphInline _ inline = inline

-- True when some raw-TeX block or inline contains the \DependencyGraph marker
-- that replaceDependencyGraph* substitutes. Lets processDoc skip the layout
-- solver (and its cache I/O) entirely when no graph is requested.
dependencyGraphReferenced :: [Block] -> Bool
dependencyGraphReferenced blocks =
  any hasMarker (query rawBlockText blocks) || any hasMarker (query rawInlineText blocks)
 where
  hasMarker txt = "\\DependencyGraph" `T.isInfixOf` txt
  rawBlockText (RawBlock fmt txt) | isTexFormat fmt = [txt]
  rawBlockText _ = []
  rawInlineText (RawInline fmt txt) | isTexFormat fmt = [txt]
  rawInlineText _ = []

readMaybeInt :: String -> Maybe Int
readMaybeInt input =
  case reads input of
    [(value, "")] -> Just value
    _ -> Nothing

dependencyLayoutCachePath :: FilePath
dependencyLayoutCachePath = "build/dependency-graph-layout.cache"

collectHeaderMap :: Pandoc -> Map Text [Inline]
collectHeaderMap = Map.fromList . query getHeader
 where
  getHeader :: Block -> [(Text, [Inline])]
  getHeader (Header _ (hid, _, _) inlines)
    | not (T.null hid) = [(hid, inlines)]
  getHeader _ = []

-- Header ids that appear more than once. collectHeaderMap silently keeps the
-- last header for a duplicate id, so §{sec:...} references would resolve to the
-- wrong section; the ref-filter fails the build when this returns non-empty.
duplicateHeaderIds :: Pandoc -> [Text]
duplicateHeaderIds doc =
  [hid | (hid, count) <- Map.toList counts, count > (1 :: Int)]
 where
  counts = foldr (\hid -> Map.insertWith (+) hid 1) Map.empty (query getId doc)
  getId :: Block -> [Text]
  getId (Header _ (hid, _, _) _)
    | not (T.null hid) = [hid]
  getId _ = []

resolveSecRefs :: Map Text [Inline] -> IORef (Set Text) -> [Inline] -> IO [Inline]
resolveSecRefs hmap ref = fmap concat . mapM resolveOne
 where
  resolveOne (Str t) = expandStr hmap ref t
  resolveOne i = return [i]

resolveRawBlockSecRefs :: Map Text [Inline] -> IORef (Set Text) -> Block -> IO Block
resolveRawBlockSecRefs hmap ref (RawBlock fmt txt)
  | isTexFormat fmt = RawBlock fmt <$> expandRawTexSecRefs hmap ref txt
resolveRawBlockSecRefs _ _ block = return block

resolveRawInlineSecRefs :: Map Text [Inline] -> IORef (Set Text) -> Inline -> IO Inline
resolveRawInlineSecRefs hmap ref (RawInline fmt txt)
  | isTexFormat fmt = RawInline fmt <$> expandRawTexSecRefs hmap ref txt
resolveRawInlineSecRefs _ _ inline = return inline

expandStr :: Map Text [Inline] -> IORef (Set Text) -> Text -> IO [Inline]
expandStr hmap ref = go
 where
  go t =
    case nextSectionRef t of
      Nothing -> return [Str t | not (T.null t)]
      Just (before, hid, after) -> do
        sub <- case Map.lookup hid hmap of
          Just title ->
            return
              [ Link
                  nullAttr
                  (Str "\167" : Space : title)
                  ("#" <> hid, "")
              ]
          Nothing -> do
            modifyIORef ref (Set.insert hid)
            return [Str ("\167{" <> hid <> "}")]
        let preInlines = [Str before | not (T.null before)]
        tailInlines <- go after
        return (preInlines ++ sub ++ tailInlines)

expandRawTexSecRefs :: Map Text [Inline] -> IORef (Set Text) -> Text -> IO Text
expandRawTexSecRefs hmap ref = go
 where
  go t =
    case nextSectionRef t of
      Nothing -> return t
      Just (before, hid, after) -> do
        replacement <-
          if Map.member hid hmap
            then return (rawTexSecRef hid)
            else do
              modifyIORef ref (Set.insert hid)
              return ("\167{" <> hid <> "}")
        tailText <- go after
        return (before <> replacement <> tailText)

rawTexSecRef :: Text -> Text
rawTexSecRef hid =
  "\\hyperref[" <> hid <> "]{\167 \\nameref*{" <> hid <> "}}"
