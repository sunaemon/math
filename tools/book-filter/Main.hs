#!/usr/bin/env runhaskell
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Applicative ((<|>))
import Control.Exception (IOException, catch)
import Control.Monad (forM, forM_, guard, unless, when, zipWithM, (>=>))
import Data.Aeson (Value, eitherDecode, parseJSON, withObject, (.:), (.:?))
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Aeson.Types (Parser, parseEither)
import qualified Data.ByteString.Lazy as BL
import Data.Char (isAsciiLower, isAsciiUpper, isDigit, isLetter, isSpace)
import Data.Foldable (asum)
import Data.IORef
import Data.List (find, intercalate, isPrefixOf, sortOn, stripPrefix, zip4)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, mapMaybe)
import Data.Ord (Down (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, getCurrentDirectory, listDirectory)
import System.Environment (getArgs, lookupEnv)
import System.Exit
import System.IO
import System.Process (readProcessWithExitCode)
import Text.Pandoc.JSON
import Text.Pandoc.Walk (query, walk, walkM)

import Correspondence (correspondenceMain)
import DependencyGraph (
  OptimizationConfig (..),
  planCacheNodes,
  planCacheSignature,
  planDependencyGraph,
  readDependencyLayoutCache,
  renderDependencyGraph,
  writeDependencyLayoutCache,
 )
import FormulaAnchors (formulaMarkers)
import MathSyntax
import MathSyntaxCLI (mathSyntaxMain)
import SectionRef (nextSectionRef)

main :: IO ()
main = do
  args <- getArgs
  case args of
    "lint" : rest -> lintMain rest
    "inject-booklinks" : rest -> injectBooklinksMain rest
    ["chapter-correspondence"] -> correspondenceMain
    ["math-syntax"] -> mathSyntaxMain False
    ["math-syntax-located"] -> mathSyntaxMain True
    _ -> toJSONFilter processDoc

data LintConfig = LintConfig
  { lintMaxLineLength :: Int
  , lintMaxReports :: Int
  , lintFix :: Bool
  , lintSortAudit :: Bool
  , lintDslAudit :: Bool
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
    , lintSortAudit = False
    , lintDslAudit = False
    , lintMacros = Nothing
    , lintPaths = []
    }

lintMain :: [String] -> IO ()
lintMain args =
  case parseLintArgs defaultLintConfig args of
    Left message -> do
      hPutStrLn stderr ("book-filter lint: " <> message)
      hPutStrLn stderr "usage: book-filter lint [--fix] [--sort-audit] [--dsl-audit] [--macros=FILE] [--max-line-length=N] [--max-reports=N] FILE..."
      exitWith (ExitFailure 2)
    Right config -> do
      rawNotationRules <- maybe (return []) readRawNotationRules (lintMacros config)
      signatureViolations <- maybe (return []) lintNotationSignatures (lintMacros config)
      when (lintFix config) $
        mapM_ (fixLintSource config rawNotationRules) (lintPaths config)
      headerIds <- collectLintHeaderIds (lintPaths config)
      chapterViolations <- concat <$> mapM (lintSource config rawNotationRules headerIds) (lintPaths config)
      when (lintSortAudit config) $
        case lintMacros config of
          Just macrosPath -> runSortAudit macrosPath (lintPaths config)
          Nothing -> hPutStrLn stderr "[lint] --sort-audit requires --macros=FILE"
      when (lintDslAudit config) $
        case lintMacros config of
          Just macrosPath -> runDslAudit macrosPath (lintPaths config)
          Nothing -> hPutStrLn stderr "[lint] --dsl-audit requires --macros=FILE"
      let violations = signatureViolations ++ chapterViolations
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
  | arg == "--sort-audit" =
      parseLintArgs config{lintSortAudit = True} rest
  | arg == "--dsl-audit" =
      parseLintArgs config{lintDslAudit = True} rest
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

-- Notation-type signature audit. A semantic macro may carry a sort
-- signature in a comment immediately before its definition:
--
--   % notation-type: \NatPair : Nat x Nat -> Nat
--   \newcommand{\NatPair}[2]{...}
--
-- The audit checks that each hint names the macro it precedes, that the
-- signature parses, and that its arity agrees with the definition. Two
-- conventions relax the arity check: a nullary macro with a signature
-- is a juxtaposed function symbol (as \LambdaNumericPair, whose
-- arguments follow it by juxtaposition), and a signature containing
-- "..." is variadic and belongs to a macro taking one comma-list
-- argument (as \Tuple).

lintNotationSignatures :: FilePath -> IO [String]
lintNotationSignatures path = do
  content <- readMacrosFile "lint" path
  return (collectSignatureViolations path (T.lines content))

collectSignatureViolations :: FilePath -> [Text] -> [String]
collectSignatureViolations path ls = finish (foldl step initial (zip [(1 :: Int) ..] ls))
 where
  initial = (Nothing, Map.empty, [], [])

  finish (pending, macros, sigs, violations) =
    reverse violations
      ++ [ report lineNo "notation-type hint is not followed by a \\newcommand"
         | Just (_, lineNo) <- [pending]
         ]
      ++ mapMaybe (checkSignatureArity macros) sigs

  report lineNo message = path <> ":" <> show lineNo <> ": " <> message

  step (pending, macros, sigs, violations) (lineNo, line)
    | Just hint <- parseNotationTypeHint line =
        let violations' =
              case pending of
                Just (_, prevLine) ->
                  report prevLine "notation-type hint is not followed by a \\newcommand" : violations
                Nothing -> violations
         in (Just (hint, lineNo), macros, sigs, violations')
    | Just (name, spec) <- parseNewCommand line =
        let macros' = Map.insert name (macroMandatoryArgs spec) macros
         in case pending of
              Nothing -> (Nothing, macros', sigs, violations)
              Just (hint, hintLine) ->
                case parseSignatureName hint of
                  Just sigName
                    | sigName == name ->
                        (Nothing, macros', (name, hint, hintLine) : sigs, violations)
                    | otherwise ->
                        ( Nothing
                        , macros'
                        , sigs
                        , report hintLine ("notation-type hint names \\" <> T.unpack sigName <> " but precedes \\newcommand{\\" <> T.unpack name <> "}") : violations
                        )
                  Nothing ->
                    (Nothing, macros', sigs, report hintLine "could not parse the name in this notation-type hint" : violations)
    | T.null (T.strip line) || "%" `T.isPrefixOf` T.strip line =
        (pending, macros, sigs, violations)
    | otherwise = (Nothing, macros, sigs, violations)

  checkSignatureArity macros (name, hint, hintLine) =
    case parseSignatureArity hint of
      Nothing ->
        Just (report hintLine ("could not parse notation-type signature: " <> T.unpack hint))
      Just (arity, variadic) ->
        case Map.lookup name macros of
          Nothing ->
            Just (report hintLine ("notation-type signature for undefined macro \\" <> T.unpack name))
          Just macroArity
            | variadic ->
                if macroArity == 1
                  then Nothing
                  else
                    Just
                      ( report
                          hintLine
                          ( "variadic notation-type signature for \\"
                              <> T.unpack name
                              <> " needs a macro taking one comma-list argument, but it takes "
                              <> show macroArity
                          )
                      )
            | macroArity == 0 -> Nothing
            | arity == macroArity -> Nothing
            | otherwise ->
                Just
                  ( report
                      hintLine
                      ( "notation-type signature for \\"
                          <> T.unpack name
                          <> " has arity "
                          <> show arity
                          <> " but the macro takes "
                          <> show macroArity
                          <> " argument(s)"
                      )
                  )

parseSignatureName :: Text -> Maybe Text
parseSignatureName hint = do
  let (rawName, rest) = T.breakOn ":" hint
  guard (not (T.null rest))
  name <- T.stripPrefix "\\" (T.strip rawName)
  guard (not (T.null name))
  return name

-- The arity of a signature: the number of argument sorts on the left of
-- the top-level arrow, and whether the argument list is variadic.
-- Trailing annotations are ignored: a parenthesized note after the
-- result sort, and an arity side condition such as ", n >= 3".
parseSignatureArity :: Text -> Maybe (Int, Bool)
parseSignatureArity hint = do
  let (_, rest) = T.breakOn ":" hint
  guard (not (T.null rest))
  let sig = T.strip (T.drop 1 rest)
      parts = splitTopLevel " -> " sig
  guard (length parts >= 2)
  let lhs = T.intercalate " -> " (init parts)
      rhs = dropTrailingArityNote (dropTrailingParenNote (last parts))
  guard (not (T.null (T.strip rhs)))
  let args = map T.strip (splitTopLevel " x " lhs)
      variadic = any isVariadicPart args
      fixed = filter (not . isVariadicPart) args
  guard (not (null args) && not (any T.null args))
  return (length fixed, variadic)
 where
  isVariadicPart part = part == "..." || part == "…"

dropTrailingParenNote :: Text -> Text
dropTrailingParenNote txt
  | T.isSuffixOf ")" txt && " (" `T.isInfixOf` txt =
      let (before, note) = T.breakOnEnd " (" txt
       in if T.count "(" note == T.count ")" note
            then T.stripEnd before
            else txt
  | otherwise = txt

dropTrailingArityNote :: Text -> Text
dropTrailingArityNote txt =
  case splitTopLevel ", " txt of
    parts
      | length parts >= 2 && isArityNote (last parts) ->
          T.intercalate ", " (init parts)
    _ -> txt
 where
  isArityNote part =
    let p = T.strip part
        (ident, rest) = T.span (\c -> isAsciiLower c || isDigit c) p
     in not (T.null ident)
          && case T.stripPrefix ">=" (T.strip rest) of
            Just digits ->
              let digits' = T.strip digits
               in not (T.null digits') && T.all isDigit digits'
            Nothing -> False

-- Split on a separator occurring at parenthesis depth zero.
splitTopLevel :: Text -> Text -> [Text]
splitTopLevel sep txt =
  case findTopLevel sep txt of
    Nothing -> [txt]
    Just idx ->
      T.take idx txt : splitTopLevel sep (T.drop (idx + T.length sep) txt)

findTopLevel :: Text -> Text -> Maybe Int
findTopLevel sep txt = go 0 0
 where
  go depth idx
    | idx >= T.length txt = Nothing
    | depth == 0 && sep `T.isPrefixOf` T.drop idx txt = Just idx
    | otherwise =
        case T.index txt idx of
          '(' -> go (depth + 1) (idx + 1)
          ')' -> go (max 0 (depth - 1)) (idx + 1)
          _ -> go depth (idx + 1)

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
collectMarkdownHeaderIds contents = Set.fromList (go Nothing (T.lines contents))
 where
  go _ [] = []
  go active (line : rest) =
    let stripped = T.dropWhile (== ' ') line
        fence = do
          (char, _) <- T.uncons stripped
          guard (char == '`' || char == '~')
          guard (T.length line - T.length stripped <= 3)
          let (marks, suffix) = T.span (== char) stripped
          guard (T.length marks >= 3)
          return (char, T.length marks, suffix)
     in case active of
          Just (char, count) -> case fence of
            Just (closing, size, suffix) | char == closing && size >= count && T.all isSpace suffix -> go Nothing rest
            _ -> go active rest
          Nothing -> case fence of
            Just (char, count, _) -> go (Just (char, count)) rest
            Nothing -> maybe id (:) (markdownHeaderId line) (go Nothing rest)

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
  go prefix rest@(char : chars)
    | needle `isPrefixOf` rest =
        Just (reverse prefix, drop (length needle) rest)
    | otherwise =
        go (char : prefix) chars

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
  guard (listToMaybe source == Just open)
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
  cacheOverride <- lookupEnv "DEPENDENCY_GRAPH_CACHE"
  let layoutCachePath =
        fromMaybe
          (maybe dependencyLayoutCachePath T.unpack (lookupMeta "dependency-layout-cache" meta >>= metaText))
          cacheOverride
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
  indexGlossary <- readIndexGlossary meta
  notationRef <- newIORef initialNotationState
  declRef <- newIORef initialDeclState
  termRef <- newIORef initialTermState{termExternal = termForwardExternalFromMeta meta}
  pendingDeclRef <- newIORef []
  let env = Env notationData notationRef declRef termRef pendingDeclRef watchSet
  blocks' <- processBlockList env blocks
  checkDeclStateFinal declRef pendingDeclRef
  checkNotationForwards notationRef watchSet
  checkTermForwards termRef (termForwardExternalFromMeta meta)
  -- Run the dependency-graph layout only when the rendered graph is actually
  -- needed (a \DependencyGraph marker, or the standalone graph-only mode), and
  -- do the layout-cache read/write here in IO rather than through
  -- unsafePerformIO inside the pure layout code.
  dependencyGraph <-
    if graphOnly || dependencyGraphReferenced blocks'
      then do
        let signature = planCacheSignature graphConfig dependencyPlan
            cacheNodes = planCacheNodes dependencyPlan
        cached <- readDependencyLayoutCache layoutCachePath signature cacheNodes
        let (tikz, freshPositions) = renderDependencyGraph debugGraph graphConfig dependencyPlan cached
        forM_ freshPositions (writeDependencyLayoutCache layoutCachePath signature cacheNodes)
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
  -- These passes deliberately retain their order: section-reference diagnostics
  -- see the full source, comments disappear before raw citation parsing, and
  -- index localization collects canonical/display pairs from the original blocks.
  -- Keep the phases explicit rather than fusing stateful traversals blindly.
  let blocksStripped = walk stripHtmlCommentInline (walk stripHtmlCommentBlock blocks'''')
  citationCache <- newIORef Map.empty
  citationInlines <- walkM (expandRawCitationInlineSeq citationCache) blocksStripped
  citationBlocks <- walkM (expandRawCitationBlock citationCache) citationInlines
  return (Pandoc meta (walk (renderHeaderBookmarks (notationBookmarks notationData)) (localizeJapaneseIndex indexGlossary meta blocks citationBlocks)))

readIndexGlossary :: Meta -> IO (Map Text Text)
readIndexGlossary meta = case lookupMeta "index-glossary" meta >>= metaText of
  Nothing -> return Map.empty
  Just path -> do
    yaml <- TIO.readFile (T.unpack path)
    pandoc <- pandocBinary
    (code, out, err) <- readProcessWithExitCode pandoc ["-f", "markdown", "-t", "json"] (T.unpack ("---\n" <> yaml <> "\n---\n"))
    case (code, eitherDecode (BL.fromStrict (TE.encodeUtf8 (T.pack out)))) of
      (ExitSuccess, Right (Pandoc glossaryMeta _)) ->
        return $ Map.fromList $ case lookupMeta "terms" glossaryMeta of
          Just (MetaList terms) -> mapMaybe termPair terms
          _ -> []
      (ExitSuccess, Left decodeError) -> ioError (userError ("book-filter: invalid index glossary parser output: " <> decodeError))
      (ExitFailure _, _) -> ioError (userError ("book-filter: cannot read index glossary: " <> err))
 where
  termPair (MetaMap fields) = do
    english <- Map.lookup "english" fields >>= metaText
    japanese <- Map.lookup "japanese" fields >>= metaText
    return (english, japanese)
  termPair _ = Nothing

-- Keep canonical term keys and hyperlink anchors stable, but display the
-- translated definition followed by its English key in the Japanese index,
-- including references emitted before that definition. Collect from the source
-- before expanding term macros.
localizeJapaneseIndex :: Map Text Text -> Meta -> [Block] -> [Block] -> [Block]
localizeJapaneseIndex glossary meta source output
  | (lookupMeta "index-language" meta >>= metaText) /= Just "ja" = output
  | otherwise = walk localizeBlock (walk localizeInline output)
 where
  translations = Map.union glossary (Map.fromList (concatMap collect (query rawBlock source ++ query rawInline source)))
  rawBlock (RawBlock fmt txt) | isTexFormat fmt = [txt]
  rawBlock _ = []
  rawInline (RawInline fmt txt) | isTexFormat fmt = [txt]
  rawInline _ = []
  collect txt = case nextTermMarker (normalizeTheoremTermHeadings txt) of
    Nothing -> []
    Just (_, marker, rest) ->
      let pair = case marker of
            TermDefine key display | key /= display -> [(key, display)]
            _ -> []
       in pair ++ collect rest
  localizeBlock (RawBlock fmt txt) | isTexFormat fmt = RawBlock fmt (rewrite txt)
  localizeBlock block = block
  localizeInline (RawInline fmt txt) | isTexFormat fmt = RawInline fmt (rewrite txt)
  localizeInline inline = inline
  rewrite txt = case nextIndex txt of
    Nothing -> txt
    Just (prefix, command, payload, rest) ->
      prefix <> command <> localizePayload payload <> "}" <> rewrite rest
  nextIndex txt =
    let candidates =
          [ (prefix, command, body)
          | command <- ["\\index{", "\\BookNotationIndex{"]
          , let (prefix, suffix) = T.breakOn command txt
          , not (T.null suffix)
          , let body = T.drop (T.length command) suffix
          ]
     in case sortOn (T.length . firstOfThree) candidates of
          [] -> Nothing
          (prefix, command, body) : _ -> case takeBalancedArg body of
            Just (payload, rest) -> Just (prefix, command, payload, rest)
            Nothing -> do
              (laterPrefix, laterCommand, payload, rest) <- nextIndex body
              return (prefix <> command <> laterPrefix, laterCommand, payload, rest)
  firstOfThree (a, _, _) = a
  localizePayload payload =
    let (levels, encapsulator) = T.breakOn "|" payload
     in T.intercalate "!" (map localizeLevel (T.splitOn "!" levels)) <> encapsulator
  localizeLevel "0Notation@Notation" = "0Notation@記号"
  localizeLevel "defined in" = "defined in@定義箇所"
  localizeLevel "referenced by" = "referenced by@参照箇所"
  localizeLevel "further reading" = "further reading@関連文献"
  localizeLevel key =
    let canonical = fst (T.breakOn "@" key)
        bilingual display
          | display == canonical = display
          | otherwise = display <> "（" <> canonical <> "）"
     in maybe key (\display -> canonical <> "@" <> bilingual display) (Map.lookup canonical translations)

-- Pandoc's fallback for an unexpanded semantic macro is its literal TeX name.
-- Supply PDF text for header math only; keep the typeset formula and all ordinary
-- math nodes unchanged. Unknown formulas still use Pandoc's normal writer.
renderHeaderBookmarks :: Map Text Text -> Block -> Block
renderHeaderBookmarks labels (Header level attr inlines) =
  Header level attr (walk render inlines)
 where
  render inline@(Math kind formula) =
    case bookmarkMathText labels (parseMathExpr formula) of
      Just plain ->
        Span
          nullAttr
          [ RawInline (Format "latex") ("\\texorpdfstring{" <> renderMathWithIndex kind formula "" <> "}{")
          , Str plain
          , RawInline (Format "latex") "}"
          ]
      Nothing -> inline
  render inline = inline
renderHeaderBookmarks _ block = block

bookmarkMathText :: Map Text Text -> MathExpr -> Maybe Text
bookmarkMathText labels = render
 where
  render (MathSeq xs) = T.concat <$> traverse render xs
  render (MathGroup x) = render x
  render (MathCommand name Nothing []) = Map.lookup name labels
  render (MathText txt)
    | not (T.any (`elem` ("\\{}%$&#_^" :: String)) txt) = Just txt
  render (MathScript base marker arg) = do
    a <- render base
    b <- render arg
    digits <- case marker of
      "_" -> Just "₀₁₂₃₄₅₆₇₈₉"
      "^" -> Just "⁰¹²³⁴⁵⁶⁷⁸⁹"
      _ -> Nothing
    converted <- traverse (convertDigit digits) (T.unpack b)
    return (a <> T.pack converted)
  render _ = Nothing
  convertDigit digits c
    | isDigit c = Just (T.index digits (fromEnum c - fromEnum '0'))
    | otherwise = Nothing

-- Raw theorem/proof environments bypass Pandoc's Markdown citation reader.
-- Expose only bracketed citations as Cite nodes, leaving the surrounding TeX
-- byte-for-byte intact. The normal downstream citeproc then owns numbering,
-- locators, bibliography entries and links, just as for ordinary prose.
type CitationCache = IORef (Map Text (Maybe Inline))

expandRawCitationBlock :: CitationCache -> Block -> IO Block
expandRawCitationBlock cache block@(RawBlock fmt txt)
  | isTexFormat fmt = do
      (changed, inlines) <- rawCitationInlines cache fmt txt
      return $ if changed then Plain inlines else block
expandRawCitationBlock _ block = return block

expandRawCitationInlineSeq :: CitationCache -> [Inline] -> IO [Inline]
expandRawCitationInlineSeq cache = fmap concat . mapM expand
 where
  expand inline@(RawInline fmt txt)
    | isTexFormat fmt = do
        (changed, inlines) <- rawCitationInlines cache fmt txt
        return $ if changed then inlines else [inline]
  expand inline = return [inline]

rawCitationInlines :: CitationCache -> Format -> Text -> IO (Bool, [Inline])
rawCitationInlines cache fmt = go False "" []
 where
  flush raw = [RawInline fmt raw | not (T.null raw)]
  go changed buffer acc txt
    | T.null txt = return (changed, acc ++ flush buffer)
    | Just (literal, rest) <- rawCitationLiteral txt =
        go changed (buffer <> literal) acc rest
    | Just (candidate, rest) <- balancedDelimited '[' ']' txt
    , "@" `T.isInfixOf` candidate = do
        citation <- cachedRawCitation cache candidate
        case citation of
          Just cite -> go True "" (acc ++ flush buffer ++ [cite]) rest
          Nothing -> copyOrdinary changed buffer acc txt
    | otherwise = copyOrdinary changed buffer acc txt

  copyOrdinary changed buffer acc txt =
    let (ordinary, rest) = T.span (`notElem` ("\\[%$" :: String)) (T.drop 1 txt)
     in go changed (buffer <> T.take 1 txt <> ordinary) acc rest

-- Comments, math and literal TeX examples must never become bibliography items.
rawCitationLiteral :: Text -> Maybe (Text, Text)
rawCitationLiteral txt =
  literalEnvironment <|> literalCommand <|> verb <|> math <|> comment <|> escaped
 where
  through open close = do
    rest <- T.stripPrefix open txt
    let (body, end) = T.breakOn close rest
    return $
      if T.null end
        then (txt, "")
        else (open <> body <> close, T.drop (T.length close) end)
  literalEnvironment =
    asum
      [ through ("\\begin{" <> name <> "}") ("\\end{" <> name <> "}")
      | name <-
          [ "verbatim"
          , "verbatim*"
          , "Verbatim"
          , "lstlisting"
          , "minted"
          , "comment"
          , "equation"
          , "equation*"
          , "align"
          , "align*"
          , "gather"
          , "gather*"
          , "multline"
          , "multline*"
          ]
      ]
  literalCommand = asum [commandGroup name | name <- ["texttt", "url", "nolinkurl", "path"]]
  commandGroup name = do
    rest <- T.stripPrefix ("\\" <> name) txt
    let (spaces, body) = T.span isSpace rest
    (group, after) <- balancedDelimited '{' '}' body
    return ("\\" <> name <> spaces <> group, after)
  verb = do
    rest <- T.stripPrefix "\\verb" txt
    let (star, body) = if "*" `T.isPrefixOf` rest then ("*", T.drop 1 rest) else ("", rest)
    (delimiter, _) <- T.uncons body
    guard (not (isLetter delimiter || isSpace delimiter))
    through ("\\verb" <> star <> T.singleton delimiter) (T.singleton delimiter)
  math = asum [mathDelimited "\\(" "\\)", mathDelimited "\\[" "\\]", mathDelimited "$$" "$$", mathDelimited "$" "$"]
  mathDelimited open close = do
    rest <- T.stripPrefix open txt
    return $ case breakRawMath close rest of
      Nothing -> (txt, "")
      Just (body, after) -> (open <> body <> close, after)
  comment = do
    _ <- T.stripPrefix "%" txt
    return (T.breakOn "\n" txt)
  escaped = do
    _ <- T.stripPrefix "\\" txt
    return (T.splitAt 2 txt)

-- Delegate the citation grammar (multiple keys, prefixes and locators) to the
-- same installed Pandoc that reads the book. No filter or citeproc is passed
-- to this small parsing call, so it cannot recurse into this executable.
-- Scoped to one document: environment changes and later invocations cannot
-- reuse another document's parser output. Cache rejected candidates as well.
cachedRawCitation :: CitationCache -> Text -> IO (Maybe Inline)
cachedRawCitation cache candidate = do
  entries <- readIORef cache
  case Map.lookup candidate entries of
    Just citation -> return citation
    Nothing -> do
      citation <- parseRawCitation candidate
      modifyIORef' cache (Map.insert candidate citation)
      return citation

pandocBinary :: IO FilePath
pandocBinary = fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"

parseRawCitation :: Text -> IO (Maybe Inline)
parseRawCitation candidate = do
  pandoc <- pandocBinary
  (code, out, err) <- readProcessWithExitCode pandoc ["-f", "markdown", "-t", "json"] (T.unpack candidate)
  case code of
    ExitFailure _ -> ioError (userError ("book-filter: cannot parse raw citation: " <> err))
    ExitSuccess ->
      case eitherDecode (BL.fromStrict (TE.encodeUtf8 (T.pack out))) of
        Right (Pandoc _ [Para [cite@(Cite _ _)]]) -> return (Just cite)
        Right (Pandoc _ _) -> return Nothing
        Left errMessage -> ioError (userError ("book-filter: invalid citation parser output: " <> errMessage))

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

-- Read the terms whose definitions live outside this build from
-- `term-forward-external:` YAML metadata. A chapter excerpt shares its source
-- with the full book, so a \termforward there may point at a definition in a
-- chapter the excerpt does not include; listing the term here keeps the
-- forwarded-but-never-defined check strict for everything else. Pandoc parses
-- metadata strings as markdown, so smart typography turns the ASCII "--" and
-- "'" of a canonical term key into "–" and "’"; map them back so the listed
-- keys compare equal to the raw keys of \termforward arguments.
termForwardExternalFromMeta :: Meta -> Set Text
termForwardExternalFromMeta = Set.map unsmartifyTermKey . metaNameSet "term-forward-external"

unsmartifyTermKey :: Text -> Text
unsmartifyTermKey =
  T.replace "\8212" "---"
    . T.replace "\8211" "--"
    . T.replace "\8217" "'"
    . T.replace "\8216" "'"
    . T.replace "\8220" "\""
    . T.replace "\8221" "\""

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
emptyNotationData = NotationData Map.empty Map.empty Map.empty defaultBookmarkLabels

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
  , termExternal :: Set Text
  , termAnchors :: Map Text Text
  }

initialTermState :: TermState
initialTermState = TermState Set.empty Set.empty Set.empty Map.empty

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

-- Syntax-class names also feed Sort inference; see the Lean correspondence
-- inventory immediately above data Sort before adding or reusing a name.
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
  "\\begin{mathmeta}" `T.isPrefixOf` T.stripStart raw

-- Pandoc retains a whole theorem/proof environment as one raw block. Split
-- metadata out at its source position, also when an injected BooklinkStart
-- precedes the opener on the same line. Ignore delimiters in TeX comments.
splitEmbeddedMathMeta :: Format -> Text -> Maybe [Block]
splitEmbeddedMathMeta fmt raw = do
  (before, rest) <- breakActiveMarker "\\begin{mathmeta}" raw
  let (body, after) = case breakActiveMarker "\\end{mathmeta}" rest of
        Nothing -> (rest, "")
        Just (contents, remaining) -> (contents <> "\\end{mathmeta}", remaining)
      meta = "\\begin{mathmeta}" <> body
  guard (not (T.null before && T.null after))
  return [RawBlock fmt txt | txt <- [before, meta, after], not (T.null (T.strip txt))]

breakActiveMarker :: Text -> Text -> Maybe (Text, Text)
breakActiveMarker marker = go ""
 where
  go before txt =
    let (line, rest) = T.breakOn "\n" txt
        (code, comment) = breakLatexComment line
        (prefix, found) = T.breakOn marker code
     in if not (T.null found)
          then Just (before <> prefix, T.drop (T.length marker) found <> comment <> rest)
          else
            if T.null rest
              then Nothing
              else go (before <> line <> "\n") (T.drop 1 rest)

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
  , notationSignatures :: Map Text Text
  , notationBookmarks :: Map Text Text
  }

data MacroSpec = MacroSpec
  { macroMandatoryArgs :: Int
  , macroHasOptionalArg :: Bool
  , macroMathClass :: Maybe Text
  }

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

injectBooklinksMain :: [String] -> IO ()
injectBooklinksMain args =
  case parseInjectBooklinksArgs args of
    Just (sourceMapPath, sourcePath, outPath) -> do
      sourceText <- TIO.readFile sourcePath
      mapText <- TIO.readFile sourceMapPath
      (entries, allSkips) <- case parseInjectionMap mapText of
        Left message -> do
          hPutStrLn stderr ("book-filter inject-booklinks: invalid source map: " <> message)
          exitWith (ExitFailure 1)
        Right parsed -> return parsed
      let injections =
            groupBooklinkInjections
              [ pending
              | pending <- entries
              , pendingBooklinkSource pending == Just sourcePath
              ]
          skips =
            [ skip
            | skip <- allSkips
            , skipInjectionSource skip == sourcePath
            ]
      validateBooklinkInjections sourcePath sourceText injections
      validateSkipInjections sourcePath sourceText skips
      root <- getCurrentDirectory
      let sourceIdentity = fromMaybe (T.pack sourcePath) (T.stripPrefix (T.pack root <> "/") (T.pack sourcePath))
      let registry = root <> "/tools/chapter-correspondence/chapters"
      exists <- doesDirectoryExist registry
      configs <- if exists then filter (T.isSuffixOf ".json" . T.pack) <$> listDirectory registry else pure []
      registered <- forM configs $ \name -> do
        contents <- BL.readFile (registry <> "/" <> name)
        case eitherDecode contents >>= parseEither (withObject "chapter configuration" (.: "source")) of
          Right source -> pure (source == sourceIdentity)
          Left err -> ioError (userError ("Invalid formula source configuration: " <> err))
      let formulaInsertions = [Insertion offset 4 marker | or registered, (offset, marker) <- formulaMarkers sourceIdentity sourceText]
      createDirectoryIfMissing True (parentDirectory outPath)
      TIO.writeFile outPath (applyInsertions sourceText (booklinkInsertions sourceText injections <> skipInsertions skips <> formulaInsertions))
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

-- Parse JSON structurally: whitespace, object-key order and nested diagnostics
-- never change entry identity. Even entries without a Lean name consume an
-- array index, as they do in the sourcemap and PDF destinations.
parseInjectionMap :: Text -> Either String ([PendingBooklinkMatch], [SkipInjection])
parseInjectionMap text = do
  value <- eitherDecode (BL.fromStrict (TE.encodeUtf8 text))
  parseEither (withObject "source map" parseRoot) value
 where
  parseRoot root = do
    entries <- root .: "entries"
    skips <- case KeyMap.lookup "skips" root of
      Nothing -> return []
      Just value -> parseJSON value
    matches <- catMaybes <$> zipWithM parseEntry [0 ..] entries
    parsedSkips <- mapM parseSkip skips
    return (matches, parsedSkips)
  parseEntry :: Int -> Value -> Parser (Maybe PendingBooklinkMatch)
  parseEntry index = withObject "entry" $ \entry -> do
    lean <- entry .: "lean"
    name <-
      withObject
        "lean"
        ( \fields -> do
            anchor <- fields .:? "anchorName"
            declaration <- fields .:? "declName"
            return (anchor <|> declaration)
        )
        lean
    booklink <- entry .: "booklink"
    target <- withObject "booklink" (.:? "target") booklink
    match <- entry .: "match"
    withObject
      "match"
      ( \fields -> do
          status <- fields .: "status"
          if status /= ("matched" :: Text)
            then return Nothing
            else do
              source <- fields .: "source"
              start <- fields .: "startOffset"
              end <- fields .: "endOffset"
              let kind = if target == Just ("statement" :: Text) then target else Nothing
              return ((\key -> PendingBooklinkMatch key index kind (Just status) (Just source) (Just start) (Just end)) <$> name)
      )
      match
  parseSkip = withObject "skip" $ \fields ->
    SkipInjection <$> fields .: "key" <*> fields .: "source" <*> fields .: "startOffset" <*> fields .: "endOffset"

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
    , Just parts <- splitEmbeddedMathMeta fmt txt ->
        Div nullAttr <$> processNestedBlockList env parts
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
  Table attr caption columns (TableHead headAttr headRows) bodies (TableFoot footAttr footRows) ->
    Table attr
      <$> processCaption env caption
      <*> pure columns
      <*> (TableHead headAttr <$> mapM (processTableRow env) headRows)
      <*> mapM (processTableBody env) bodies
      <*> (TableFoot footAttr <$> mapM (processTableRow env) footRows)
  DefinitionList items -> DefinitionList <$> mapM (processDefItem env) items
  Plain ils -> Plain <$> processInlineSeqWithComments True env ils
  Para ils -> Para <$> processInlineSeqWithComments True env ils
  Header level attr ils -> do
    enterSection declRef level
    Header level attr <$> processInlineSeqWithComments False env ils
  _ -> walkM (processInline env) b

processTableRow :: Env -> Row -> IO Row
processTableRow env (Row attr cells) = Row attr <$> mapM processCell cells
 where
  processCell (Cell attributes alignment rowSpan colSpan blocks) =
    Cell attributes alignment rowSpan colSpan <$> processNestedBlockList env blocks

processTableBody :: Env -> TableBody -> IO TableBody
processTableBody env (TableBody attr headColumns headRows rows) =
  TableBody attr headColumns <$> mapM (processTableRow env) headRows <*> mapM (processTableRow env) rows

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
    -- The environment already prints this label. Japanese translations use
    -- full-width parentheses and usually omit the space before them.
    labels = headingLabel : maybe [] pure (lookup headingLabel japaneseHeadingLabels)
    parenthesizedHeading =
      asum
        [ do
            afterLabel <- T.stripPrefix label stripped
            innerWithClose <- T.stripPrefix opening (T.stripStart afterLabel)
            T.stripSuffix closing innerWithClose
        | label <- labels
        , (opening, closing) <- [("(", ")"), ("（", "）")]
        ]
    japaneseHeadingLabels =
      [ ("Theorem", "定理")
      , ("Lemma", "補題")
      , ("Proposition", "命題")
      , ("Corollary", "系")
      , ("Claim", "主張")
      , ("Fact", "事実")
      , ("Recall", "復習")
      , ("Definition", "定義")
      , ("Example", "例")
      , ("Construction", "構成")
      , ("Remark", "注意")
      ]

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
termIndexText termRef (TermIndex key)
  | T.null key = return ""
  | isExistingStructuredIndex key = return ("\\index{" <> key <> "}")
  -- A raw \index{A!B} with a subentry separator is a genuine makeindex
  -- locator, not a term definition: pass it through verbatim. Forcing it
  -- through the "defined in" rewrite would append a spurious deepest level
  -- (\index{A!B!defined in}), anchor the page to A's term entry rather than B,
  -- and could overflow makeindex's subsubitem limit on a three-level key.
  | "!" `T.isInfixOf` key = return ("\\index{" <> key <> "}")
  | otherwise = do
      claimTermAnchor termRef key
      return ("\\index{" <> termIndexKey key <> "!defined in|termindexpage{" <> termIndexAnchorName key <> "}}")
termIndexText termRef (TermDefine key rendered)
  | T.null key = return rendered
  | isExistingStructuredIndex key = do
      markTermDefined termRef key
      return ("\\textbf{" <> rendered <> "}\\index{" <> key <> "}")
  | otherwise = do
      st <- readIORef termRef
      markTermDefined termRef key
      let anchor =
            if key `Set.member` termDefined st
              then ""
              else "\\hypertarget{" <> termDefAnchorName key <> "}{}"
      return $
        anchor
          <> "\\hyperlink{"
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
      claimTermAnchor termRef key
      modifyIORef termRef $ \st ->
        st{termForwarded = Set.insert key (termForwarded st)}
      st <- readIORef termRef
      return $
        termLink st key rendered
          <> "\\index{"
          <> termIndexKey key
          <> "!referenced by}"
termIndexText termRef (TermRef key)
  | T.null key = return ""
  | otherwise = do
      claimTermAnchor termRef key
      return ("\\index{" <> termIndexKey key <> "!referenced by}")
termIndexText termRef (TermUse key rendered)
  | T.null key = return rendered
  | otherwise = do
      requireTermAvailable termRef key rendered
      st <- readIORef termRef
      return $
        termLink st key rendered
          <> "\\index{"
          <> termIndexKey key
          <> "!referenced by}"
termIndexText _ (TermMalformed message) = do
  hPutStrLn stderr "[term-filter] malformed term macro:"
  hPutStrLn stderr ("  " <> T.unpack message)
  exitWith (ExitFailure 1)

-- Excerpts may mention a definition belonging to an omitted chapter. Keep
-- the index reference, but do not emit a PDF link with no destination.
termLink :: TermState -> Text -> Text -> Text
termLink st key rendered
  | key `Set.member` termExternal st = rendered
  | otherwise = "\\hyperlink{" <> termIndexAnchorName key <> "}{" <> rendered <> "}"

markTermDefined :: IORef TermState -> Text -> IO ()
markTermDefined termRef key = do
  claimTermAnchor termRef key
  modifyIORef termRef $ \st -> st{termDefined = Set.insert key (termDefined st)}

-- Subentries and explicit display aliases share their canonical index root.
-- Distinct roots must never silently share the lossy hyperlink slug.
claimTermAnchor :: IORef TermState -> Text -> IO ()
claimTermAnchor termRef key
  | isExistingStructuredIndex key = return ()
  | otherwise = do
      st <- readIORef termRef
      let slug = termAnchorSlug key
          root = fst (T.breakOn "@" (fst (T.breakOn "!" key)))
          identity = fromMaybe (T.strip root) (mathTermSortKey root)
      case Map.lookup slug (termAnchors st) of
        Just previous | previous /= identity -> do
          hPutStrLn stderr ("[term-filter] colliding term anchors: " <> T.unpack previous <> " / " <> T.unpack identity <> " -> " <> T.unpack slug)
          exitWith (ExitFailure 1)
        _ -> modifyIORef' termRef $ \current -> current{termAnchors = Map.insert slug identity (termAnchors current)}

requireTermAvailable :: IORef TermState -> Text -> Text -> IO ()
requireTermAvailable termRef key rendered = do
  claimTermAnchor termRef key
  st <- readIORef termRef
  unless (key `Set.member` termDefined st || key `Set.member` termForwarded st) $ do
    hPutStrLn stderr "[term-filter] term used before \\termdefine or \\termforward:"
    hPutStrLn stderr ("  term: " <> T.unpack key)
    hPutStrLn stderr ("  rendered: " <> T.unpack rendered)
    hPutStrLn stderr "  use \\termforward{...} or \\termforwardas{...}{...} for the informal use, or move the \\termdefine{...} earlier"
    exitWith (ExitFailure 1)

checkTermForwards :: IORef TermState -> Set Text -> IO ()
checkTermForwards termRef externalTerms = do
  st <- readIORef termRef
  let missing = (termForwarded st `Set.difference` termDefined st) `Set.difference` externalTerms
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
termIndexAnchorName key = "term-index-" <> termAnchorSlug key

-- A zero-width companion anchor dropped at the definition site itself. The
-- printed book's term links target the index entry (termIndexAnchorName,
-- whose hypertarget the index creates); the formalization viewer prefers
-- jumping straight to the definition, and resolves a term-index-<slug> link
-- to term-def-<slug> when the PDF carries it.
termDefAnchorName :: Text -> Text
termDefAnchorName key = "term-def-" <> termAnchorSlug key

termAnchorSlug :: Text -> Text
termAnchorSlug key = T.map anchorChar (termAnchorKey key)
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
breakRawMath close = go []
 where
  go acc txt
    | T.null txt = Nothing
    | "\\$" `T.isPrefixOf` txt =
        go ("\\$" : acc) (T.drop 2 txt)
    | close `T.isPrefixOf` txt =
        Just (T.concat (reverse acc), T.drop (T.length close) txt)
    | otherwise =
        let (prefix, rest) = T.splitAt 1 txt
         in go (prefix : acc) rest

-- Enforce the first-use gate for watched notation, then (when linking is
-- allowed) hyperlink defined notations and collect their reference index
-- entries. Shared by raw-TeX math and Pandoc Math inlines.

{- | The stage-4 wiring of the DSL angle-bracket resolution: a raw
<a, b> literal in math content is replaced by the notation its
sorts resolve to. When the item sorts are known and the literal is
ambiguous or matches no notation, the build fails; when the sorts
are unknown or the span does not parse, the content is untouched.
-}
resolveDslContent :: NotationData -> IORef DeclState -> Text -> IO Text
resolveDslContent notationData declRef content
  | not ("<" `T.isInfixOf` content || "\\langle" `T.isInfixOf` content) =
      return content
  | otherwise = do
      st <- readIORef declRef
      case parseDslSpan content of
        Nothing -> return content
        Just tree ->
          let (resolved, findings) =
                resolveDslExpr (signatureSorts notationData) st Nothing tree
              bad =
                [ f
                | f <- findings
                , case dslFindingVerdict f of
                    DslVerdictAmbiguous _ -> True
                    DslVerdictNoCandidate -> True
                    _ -> False
                ]
              anyResolved =
                any
                  ( \f -> case dslFindingVerdict f of
                      DslVerdictResolved _ -> True
                      _ -> False
                  )
                  findings
           in if null bad
                then
                  return
                    ( if anyResolved
                        then renderDsl resolved
                        else content
                    )
                else do
                  hPutStrLn
                    stderr
                    "[notation-filter] angle-bracket literal does not resolve uniquely:"
                  forM_ bad $ \f ->
                    hPutStrLn
                      stderr
                      ( "  "
                          <> T.unpack (dslFindingAngle f)
                          <> ": "
                          <> verdictText (dslFindingVerdict f)
                      )
                  hPutStrLn stderr ("  in math: " <> T.unpack content)
                  exitWith (ExitFailure 1)
 where
  verdictText (DslVerdictAmbiguous names) =
    "ambiguous: "
      <> intercalate ", " (map (\n -> '\\' : T.unpack n) names)
  verdictText DslVerdictNoCandidate =
    "no notation matches the known sorts"
  verdictText _ = ""

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
      dslContent <- resolveDslContent notationData declRef content
      -- Linking parses the math to a MathExpr and re-renders it; that round-trip
      -- is the identity only on brace-balanced input. Skip linking on unbalanced
      -- braces (already invalid LaTeX) so the content is passed through verbatim
      -- rather than having a closing brace fabricated for an unclosed group.
      let linkable = allowLinks && bracesBalanced dslContent
      (content', typedNames) <-
        if linkable
          then linkTypedNotations (notationSpecs notationData) declRef active dslContent
          else return (dslContent, Set.empty)
      let (content'', usedNames) =
            if linkable
              then linkDefinedNotations (notationSpecs notationData) watchSet active content'
              else (content', Set.empty)
          refEntries =
            notationReferenceIndexText (notationDisplays notationData) (usedNames `Set.union` typedNames)
      return (protectAlignedLeadingBracket content'', refEntries)
    else do
      hPutStrLn stderr "[notation-filter] notation used before \\define or \\forward:"
      hPutStrLn
        stderr
        ( "  missing: "
            <> intercalate ", " (map (\n -> '\\' : T.unpack n) (Set.toList offenders))
        )
      hPutStrLn stderr ("  in math: " <> T.unpack content)
      exitWith (ExitFailure 1)

-- amsmath reads an initial [T] in aligned as its optional vertical position.
-- It restores unknown positions as formula text, but emits a warning. Make the
-- intended formula start explicit while retaining actual [t], [c], [b] options.
protectAlignedLeadingBracket :: Text -> Text
protectAlignedLeadingBracket input =
  case T.breakOn marker input of
    (_, rest) | T.null rest -> input
    (before, rest) ->
      let after = T.drop (T.length marker) rest
          stripped = T.stripStart after
          positional = case T.stripPrefix "[" stripped of
            Nothing -> False
            Just body ->
              let (position, close) = T.breakOn "]" body
               in not (T.null close) && T.strip position `elem` ["t", "c", "b", ""]
          disambiguator = if "[" `T.isPrefixOf` stripped && not positional then "\\relax" else ""
       in before <> marker <> disambiguator <> protectAlignedLeadingBracket after
 where
  marker = "\\begin{aligned}"

notationIndexText :: Map Text Text -> Set Text -> Set Text -> Text
notationIndexText displays watchSet names =
  let watchedNames = Set.toAscList (names `Set.intersection` watchSet)
      -- Alongside the index entry, drop a zero-width notation-def-<name>
      -- companion anchor at the definition site: the printed notation links
      -- target the index entry, and the formalization viewer resolves them to
      -- this anchor to jump straight to where the notation is introduced.
      entry name =
        "\\hypertarget{notation-def-"
          <> name
          <> "}{}\\BookNotationIndex{0Notation@Notation!"
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
    "\\BookNotationIndex{0Notation@Notation!" <> name <> "@" <> notationIndexDisplayForIndex displays name <> "!referenced by}"

notationIndexAnchorName :: Text -> Text
notationIndexAnchorName name = "notation-index-" <> name

-- A brace group alone is an Ord atom, even when the macro inside is a
-- relation or binary operator. Preserve the macro's outer math class around
-- the link so TeX supplies its normal spacing and operator limits.
notationHyperlink :: Map Text MacroSpec -> Text -> Text -> Text
notationHyperlink specs name body =
  let mathClass = Map.lookup name specs >>= macroMathClass
      wrapper = maybe "" ("\\" <>) mathClass
   in wrapper <> "{\\hyperlink{" <> notationIndexAnchorName name <> "}{" <> body <> "}}"

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
  let (displays, specs, signatures) = collectNotationData Nothing Nothing Map.empty Map.empty Map.empty (T.lines content)
      bookmarks = Map.union (Map.fromList (mapMaybe parseBookmarkHint (T.lines content))) defaultBookmarkLabels
  return (NotationData displays specs signatures bookmarks)

defaultBookmarkLabels :: Map Text Text
defaultBookmarkLabels = Map.fromList [("omega", "ω")]

-- A semantic macro may specify its plain PDF label independently of its math
-- typography, e.g. "% pdf-bookmark: EventualEqualityER = E₀".
parseBookmarkHint :: Text -> Maybe (Text, Text)
parseBookmarkHint line = do
  rest <- T.stripPrefix "% pdf-bookmark:" (T.strip line)
  let (name, suffix) = T.breakOn "=" rest
      label = T.strip (T.drop 1 suffix)
  guard (not (T.null (T.strip name)) && not (T.null label))
  guard (not (T.any (`elem` ("\\{}%$&#_^" :: String)) label))
  return (T.strip name, label)

collectNotationData ::
  Maybe Text ->
  Maybe Text ->
  Map Text Text ->
  Map Text MacroSpec ->
  Map Text Text ->
  [Text] ->
  (Map Text Text, Map Text MacroSpec, Map Text Text)
collectNotationData _ _ displays specs signatures [] = (displays, specs, signatures)
collectNotationData pending pendingSig displays specs signatures (line : rest)
  | Just display <- parseNotationIndexHint line =
      collectNotationData (Just display) pendingSig displays specs signatures rest
  | Just sig <- parseNotationTypeHint line =
      collectNotationData pending (Just sig) displays specs signatures rest
  | Just (name, spec) <- parseNewCommand line =
      let display = fromMaybe (synthesizedDisplay name (macroMandatoryArgs spec)) pending
          signatures' =
            case pendingSig of
              Just sig -> Map.insert name sig signatures
              Nothing -> signatures
       in collectNotationData Nothing Nothing (Map.insert name display displays) (Map.insert name spec specs) signatures' rest
  | T.null (T.strip line) || "%" `T.isPrefixOf` T.strip line =
      collectNotationData pending pendingSig displays specs signatures rest
  | otherwise =
      collectNotationData Nothing Nothing displays specs signatures rest

parseNotationIndexHint :: Text -> Maybe Text
parseNotationIndexHint line =
  T.strip <$> T.stripPrefix "% notation-index:" (T.strip line)

parseNotationTypeHint :: Text -> Maybe Text
parseNotationTypeHint line =
  T.strip <$> T.stripPrefix "% notation-type:" (T.strip line)

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
        , macroMathClass = parseNewCommandReplacement afterName >>= outerMathClass
        }

-- Only a whole replacement consisting of one explicitly classified atom
-- qualifies. A construction such as #1\mathrel{...}#2 includes its operands
-- and must not itself acquire relation spacing. Large operators may append
-- displaylimits, which is also the default of the outer mathop.
outerMathClass :: Text -> Maybe Text
outerMathClass body =
  case parseMathExpr (T.strip body) of
    MathSeq [MathCommand cls Nothing [_]]
      | cls `elem` ["mathrel", "mathbin", "mathop", "mathord", "mathopen", "mathclose", "mathpunct", "mathinner"] ->
          Just cls
    MathSeq [MathCommand "mathop" Nothing [_], MathCommand "displaylimits" Nothing []] ->
      Just "mathop"
    _ -> Nothing

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
  Emph <$> processInlineSeqWithComments allowLinks env ils
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
    , hasRequiredShape (Map.findWithDefault (MacroSpec 0 False Nothing) name specs) optionalArg args =
        let nestedNames =
              collectLinkedNotationNames optionalArg args
         in ( MathRaw (notationHyperlink specs name (renderMathExpr cmd))
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
            linked = notationHyperlink specs target useText
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
                linked = MathRaw (notationHyperlink specs target useText)
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
    macroMandatoryArgs (Map.findWithDefault (MacroSpec 0 False Nothing) name specs)

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

-- ---------------------------------------------------------------------------
-- Notation signature sort audit (validation only)
--
-- The @% notation-type:@ registry signatures describe the sorts of a
-- semantic macro's arguments and its result.  This audit checks every use
-- of a signed macro in a linted source file whose argument sorts can be
-- inferred.  A leaf's sort comes from the existing syntactic inference
-- ('inferDeclType': scoped @\\vars@ declarations, @\\infer*@ rules and the
-- structural rules); a nested signed application contributes its
-- signature's result sort under the argument substitution.  Unknown sorts
-- stay silent: only provable mismatches are reported, and the audit never
-- fails the lint run.  It is enabled with @lint --sort-audit@ and measures
-- how far the signature registry and the declaration substrate agree with
-- the explicit macros in the text, before any generic notation is allowed.

-- Lean correspondence inventory for the canonical English book and the
-- notation-type registry in polish-space/tex/macros.tex. This is documentation,
-- not a translation into Lean's Sort u, an elaborator, or a soundness theorem.
-- Lean source paths below are relative to polish-space/lean/PolishSpaceBook/.
-- Lean examples identify carrier/predicate implementations, not a certified
-- per-occurrence or per-macro correspondence. Some roles have several encodings.
-- Composite declarations are covered recursively by their constructors; sort
-- variables (a, b, i, A, ...) are signature placeholders, not Lean universes.
-- The parser is open-ended: these are the currently used vocabulary, not all
-- admissible names. Test-only vocabulary is not a book/Lean interface.
--
-- Atomic sorts:
--   Nat / Int / Rat / Real / Cplx: intended carriers are Lean's Nat / Int /
--     Rat / Real / Complex. Nat also labels program indices and syntax codes;
--     their validity and computation predicates are erased. The number tower
--     below permits notation coercions, not Lean definitional equalities.
--   Bit: binary letters, represented by Bool in CantorDerivativeRecursion.lean
--     and CantorBaireSpace.lean, or by naturals with a binary-value predicate
--     in internal encodings. The BinaryPair signature supplies this sort;
--     the filter does not prove a code is a finite binary word.
--   Card: cardinality, typically Cardinal in Lean. Finite cardinalities may
--     instead use Nat with a finiteness hypothesis. See Cardinal.mk uses in
--     CantorBendixsonStages.lean. No Card/Nat compatibility is implemented.
--   Prop: a proposition (Lean Prop), not a first-order formula's syntax and
--     not its proof. Relation-shaped text can receive Prop without checking
--     either operand; this is only a syntactic classification.
--   Name: total Nat -> Nat, the Baire-space carrier. ComputesName in
--     LambdaComputablePointAssemblies.lean adds the separate lambda-computation
--     evidence. Membership in a representation's domain is also separate.
--   ZFSet: an explicit set-theoretic object, as in SetTheoryInternalListCodes.lean;
--     distinct from a finite List Nat and its Nat code. No membership or model
--     hypothesis is supplied by this structural annotation.
--   Point: the local carrier X at the computable-point assembly definition;
--     no global Lean Point type. It forgets X's identity and any topology.
--   PCAElement: the carrier A of PartialCombinatoryAlgebra A, defined in
--     LambdaIndexPCA.lean. It forgets the chosen algebra and application law;
--     it is not uniformly Nat (only the numerical instance has that carrier).
--   Stage: the well-founded index carrier iota in CantorDerivativeRecursion.lean
--     (stageTree); neither its relation nor well-foundedness is stored here.
--     It must not be identified automatically with Nat or Ordinal.
--   fo-term: L.Term Nat, or the appropriate variable carrier, in the
--     FirstOrderNamedSyntax.lean development; language and free-variable data
--     are erased. A term variable and a compound term share this syntax class.
--   fo-formula: Formula L / AlphaFormula L in FirstOrderNamedSyntax.lean and
--     FirstOrderAlphaSubstitution.lean. Named syntax and its alpha quotient
--     are not distinguished, nor are closedness, language, or complexity.
--   fo-context: Context L = Finset (AlphaFormula L), defined in
--     FirstOrderDeductionSemantics.lean; distinct from an arbitrary theory.
--   lambda-term: Term in LambdaSyntaxSubstitution.lean / AlphaTerm in
--     LambdaAlphaEquivalence.lean; named representatives, alpha classes,
--     closedness and computational behavior are not distinguished.
--   pca-term: PartialCombinatoryAlgebra.Expression A alpha in PCAAbstraction.lean;
--     algebraic expressions, not their values in Part A, and not numeric codes.
--
-- Constructors and bare-container sorts:
--   Set(a): usually Lean Set A. Bare Set also covers ZFSet objects in the
--     SetTheory*.lean development. These are different representations, not
--     one Lean type; ZFC has no element-type parameter. Set(a) records the
--     intended element role, not a ZFC universe, transitivity or internality.
--   Seq(a), bare Seq: both finite List A (finseq in CantorBaireSpace.lean) and
--     infinite Nat -> A occur in the book. Length and index bounds are erased.
--     In particular this is NOT a faithful Lean sequence type: callableSort
--     reads Seq(a) as Nat -> a even though some declared sequences are finite.
--   Prod(a,b): product data, commonly Lean A x B; set-theoretic
--     ordered pairs instead use ZFSet.pair. Pair is a legacy alias for Prod;
--     nesting preserves association. N-ary products record explicit argument
--     slots without choosing a binary Lean encoding for those slots.
--   Tuple(a1,...,an): fixed tuples, implemented using products, indexed
--     functions or set-theoretic tuple encodings as appropriate. No universal
--     Lean Tuple translation, associativity rule, or dependent typing is given.
--   Fun(a,b): intended total functions A -> B, or their set-theoretic graphs.
--     Topology, computability, graph domain and codomain evidence are omitted.
--     checkSort also accepts a family BODY of sort b in a Fun(a,b) position;
--     that convenience is not Lean function application/type checking.
--   Mor(C,A): C and A are source and target OBJECTS, not category and carrier.
--     Its Lean reading is C --> A in a fixed category (e.g. Assembly maps).
--     The category, universe, map laws and trackers are absent from this sort.
--   Elem(A): a declaration lookup, not a Lean type constructor. For a declared
--     Set(a) or Seq(a), resolveDeclaredSort returns a. It does not construct
--     a subtype or prove membership in A; identity of the container is lost.
--   PartialFun(a,b): descriptive signature for partial functions; currently
--     no callableSort rule or definedness/equality checking. Representation X
--     in CauchyNamesPolishRepresentations.lean stores domain : Set baire_space,
--     toFun : domain -> X and surjectivity; the sort forgets the domain restriction
--     and surjectivity. Numerical partial computation is also expressed
--     relationally by App in LambdaComputablePointAssemblies.lean, not by a
--     single uniform PartialFun Lean type.
--   Assembly(Point): Assembly with a specified intended carrier role. The
--     computablePointAssembly carrier in LambdaComputablePointAssemblies.lean
--     is {x : X // HasComputableName delta x}, with a realizability relation and
--     inhabitation proof. The sort omits that subtype and all realization data.
--
-- Ordinal is NOT currently declared in the book's sort annotations/signatures.
-- Lean has Ordinal and set-theoretic ordinal predicates/constructions (see
-- SetTheoryOrdinalBookBasics.lean), but merely parsing the name Ordinal would
-- not connect them or type ordinal arithmetic.
--
-- Thus this vocabulary is usually coarser than the formalization, but is NOT
-- a uniform quotient of Lean types: Seq/Set merge different representations.
-- Product nesting is preserved; comma-separated function arguments unpack
-- only the outer product and do not reassociate it or curry the function.
-- No Lean declarations, booklinks, or proof certificates are consulted here.
-- A successful audit establishes neither full sort coverage nor Lean typing.

data Sort
  = SortAtom Text
  | SortVar Text
  | SortApp Text [Sort]
  deriving (Eq, Show)

type SortSubst = Map Text Sort

type SignatureSorts = Map Text ([Sort], Sort)

signatureSorts :: NotationData -> SignatureSorts
signatureSorts notationData =
  Map.fromList
    [ (name, sig)
    | (name, hint) <- Map.toList (notationSignatures notationData)
    , Just sig <- [parseSortSignature (signatureBody hint)]
    ]
 where
  signatureBody hint =
    case T.breakOn ":" hint of
      (_, rest)
        | not (T.null rest) -> T.strip (T.drop 1 rest)
      _ -> hint

-- Schematic variables are local to one application of a signature:
-- the registry spells every macro's variable "a", so two nested
-- applications would otherwise share one variable and capture each
-- other (binding a to Seq(a), say). Each use site freshens the
-- signature with a digest of the application's arguments, which is
-- stable for the same application wherever it is computed.
freshSignature :: Text -> Text -> ([Sort], Sort) -> ([Sort], Sort)
freshSignature name digest (argSorts, resultSort) =
  (map fresh argSorts, fresh resultSort)
 where
  fresh (SortVar var) = SortVar (var <> "@" <> name <> "#" <> digest)
  fresh (SortAtom atom) = SortAtom atom
  fresh (SortApp ctor args) = SortApp ctor (map fresh args)

sortDigest :: Text -> Text
sortDigest txt =
  T.pack (show (T.foldl' step 7 txt `mod` 2147483647))
 where
  step h c = (h * 31 + toInteger (fromEnum c)) `mod` 2147483647

parseSortSignature :: Text -> Maybe ([Sort], Sort)
parseSortSignature raw = do
  let body = dropTrailingArityNote (dropTrailingParenNote (T.strip raw))
      parts = splitTopLevel " -> " body
  guard (length parts >= 2)
  let resultText = last parts
      argsText = T.intercalate " -> " (init parts)
      argTexts =
        if T.null (T.strip argsText)
          then []
          else splitTopLevel " x " argsText
  guard (not (any ("..." `T.isInfixOf`) argTexts))
  guard (not ("..." `T.isInfixOf` resultText))
  return (map parseSort argTexts, parseSort resultText)

parseSort :: Text -> Sort
parseSort raw =
  let txt = T.strip raw
      arrowParts = splitTopLevel " -> " txt
   in if length arrowParts >= 2
        then
          SortApp
            "Fun"
            [ parseSort (T.intercalate " -> " (init arrowParts))
            , parseSort (last arrowParts)
            ]
        else case splitTopLevel " x " txt of
          [single] -> parseSortAtom single
          parts -> SortApp "Prod" (map parseSort parts)

parseSortAtom :: Text -> Sort
parseSortAtom raw =
  let txt = T.strip raw
   in if isOuterParenWrapped txt
        then parseSort (T.drop 1 (T.dropEnd 1 txt))
        else case T.breakOn "(" txt of
          (name, rest)
            | not (T.null rest)
            , T.isSuffixOf ")" rest
            , isSortConstructorName name ->
                SortApp (if name == "Pair" then "Prod" else name) (map parseSort (splitTopLevel "," (T.drop 1 (T.dropEnd 1 rest))))
          _
            | txt == "Pair" -> SortAtom "Prod"
            | isSortVarName txt -> SortVar txt
            | otherwise -> SortAtom txt

isOuterParenWrapped :: Text -> Bool
isOuterParenWrapped txt =
  T.length txt >= 2 && T.head txt == '(' && matchingClose == T.length txt - 1
 where
  matchingClose = go 0 0
  go depth idx
    | idx >= T.length txt = -1
    | otherwise =
        case T.index txt idx of
          '(' -> go (depth + 1) (idx + 1)
          ')' -> if depth == 1 then idx else go (depth - 1) (idx + 1)
          _ -> go depth (idx + 1)

isSortConstructorName :: Text -> Bool
isSortConstructorName name =
  case T.uncons name of
    Just (c, _) -> isAsciiUpper c && T.all isLetter name
    Nothing -> False

-- Signature variables are the schematic names: lower-case names and single
-- letters of either case (the @A@, @B@, @C@ in @Mor(C, A)@).  Multi-letter
-- capitalised names are concrete sorts (@Nat@, @Real@, ...) or sort
-- constructors (@Set@, @Seq@, ...).
isSortVarName :: Text -> Bool
isSortVarName txt =
  case T.uncons txt of
    Just (c, rest) ->
      (isAsciiLower c || (T.length txt == 1 && isAsciiUpper c))
        && T.all (\ch -> isLetter ch || isDigit ch) rest
    Nothing -> False

renderSort :: Sort -> Text
renderSort (SortAtom name) = name
renderSort (SortVar name) = name
renderSort (SortApp "Prod" parts) = T.intercalate " x " (map factor parts)
 where
  factor s@(SortApp "Prod" _) = "(" <> renderSort s <> ")"
  factor s = renderSort s
renderSort (SortApp "Fun" [lhs, rhs]) =
  "(" <> renderSort lhs <> " -> " <> renderSort rhs <> ")"
renderSort (SortApp name args) =
  name <> "(" <> T.intercalate ", " (map renderSort args) <> ")"

sortTowerRank :: Text -> Maybe Int
sortTowerRank name = case name of
  "Nat" -> Just 0
  "Int" -> Just 1
  "Rat" -> Just 2
  "Real" -> Just 3
  "Cplx" -> Just 4
  _ -> Nothing

sortConstructorNames :: [Text]
-- Bare/applied compatibility whitelist, NOT the complete constructor registry.
-- Elem, PartialFun and Assembly are parsed too; their semantics differ above.
sortConstructorNames = ["Set", "Seq", "Tuple", "Mor", "Prod", "Fun"]

-- @checkSort subst expected actual@ extends the substitution when the
-- actual sort fits the expected sort: equal sorts, a sort variable on
-- either side, a bare constructor against one of its applications
-- (@Set@ against @Set(Real)@), constructor congruence, or a step up the
-- number tower @Nat < Int < Rat < Real < Cplx@.
checkSort :: SortSubst -> Sort -> Sort -> Maybe SortSubst
checkSort subst expected actual =
  case (expected, actual) of
    (SortVar name, _) ->
      case Map.lookup name subst of
        Nothing
          | sortOccurs name (applySortSubst subst actual) -> Nothing
          | otherwise -> Just (Map.insert name actual subst)
        Just bound -> checkSort subst bound actual
    (_, SortVar name) ->
      case Map.lookup name subst of
        Nothing
          | sortOccurs name (applySortSubst subst expected) -> Nothing
          | otherwise -> Just (Map.insert name expected subst)
        Just bound -> checkSort subst expected bound
    (SortAtom a, SortAtom b)
      | a == b -> Just subst
      | Just rankExpected <- sortTowerRank a
      , Just rankActual <- sortTowerRank b
      , rankActual <= rankExpected ->
          Just subst
      -- A name is a sequence of naturals: Name is a subsort of Seq.
      | a == "Seq" && b == "Name" -> Just subst
      | otherwise -> Nothing
    (SortApp "Seq" [elt], SortAtom "Name") ->
      checkSort subst elt (SortAtom "Nat")
    -- Baire names are exactly total natural-number-valued functions
    -- on Nat. Do not widen their codomain along the number tower.
    (SortAtom "Name", SortApp "Fun" [SortAtom "Nat", SortAtom "Nat"]) -> Just subst
    (SortApp "Fun" [SortAtom "Nat", SortAtom "Nat"], SortAtom "Name") -> Just subst
    (SortAtom a, SortApp b _)
      | a == b && a `elem` sortConstructorNames -> Just subst
    (SortApp a _, SortAtom b)
      | a == b && a `elem` sortConstructorNames -> Just subst
    (SortApp "Fun" [dom, cod], actualSort) ->
      let funReading = case actualSort of
            SortApp "Fun" [dom', cod'] ->
              checkSortList subst [(dom, dom'), (cod, cod')]
            _ -> Nothing
          -- A sequence used as a family: its index sort is Nat.
          sequenceReading = case actualSort of
            SortApp "Seq" [elt] ->
              checkSort subst dom (SortAtom "Nat") >>= \s -> checkSort s cod elt
            _ -> Nothing
          -- A family argument written as a body term: the term's own
          -- sort is the family's codomain sort.
          bodyReading = checkSort subst cod actualSort
       in funReading <|> sequenceReading <|> bodyReading
    (SortApp f fArgs, SortApp g gArgs)
      | f == g && length fArgs == length gArgs ->
          checkSortList subst (zip fArgs gArgs)
    _ -> Nothing

sortOccurs :: Text -> Sort -> Bool
sortOccurs name (SortVar var) = name == var
sortOccurs _ (SortAtom _) = False
sortOccurs name (SortApp _ args) = any (sortOccurs name) args

checkSortList :: SortSubst -> [(Sort, Sort)] -> Maybe SortSubst
checkSortList subst [] = Just subst
checkSortList subst ((expected, actual) : rest) =
  checkSort subst expected actual >>= \subst' -> checkSortList subst' rest

applySortSubst :: SortSubst -> Sort -> Sort
applySortSubst subst = go Set.empty
 where
  go _ (SortAtom name) = SortAtom name
  go seen (SortVar name)
    | name `Set.member` seen = SortVar name
    | otherwise =
        case Map.lookup name subst of
          Nothing -> SortVar name
          Just bound -> go (Set.insert name seen) bound
  go seen (SortApp name args) = SortApp name (map (go seen) args)

checkInferredArgs :: [Sort] -> [Maybe Sort] -> Maybe SortSubst
checkInferredArgs expected inferred = go Map.empty (zip expected inferred)
 where
  go subst [] = Just subst
  go subst ((_, Nothing) : rest) = go subst rest
  go subst ((expectedSort, Just actualSort) : rest) =
    checkSort subst expectedSort actualSort >>= \subst' -> go subst' rest

checkInferredArgsP ::
  [Sort] -> [Maybe (Sort, Bool)] -> Maybe (SortSubst, Bool)
checkInferredArgsP expected inferred = go Map.empty False (zip expected inferred)
 where
  go subst taint [] = Just (subst, taint)
  go subst taint ((_, Nothing) : rest) = go subst taint rest
  go subst taint ((expectedSort, Just (actualSort, t)) : rest) =
    checkSort subst expectedSort actualSort
      >>= \subst' -> go subst' (taint || t) rest

-- The sort of a math expression, when it can be established: a signed
-- application whose known argument sorts fit contributes its result sort;
-- anything else falls back to the syntactic inference substrate, then to
-- the sorts harvested from signed applications in the same section
-- (see 'checkApplication'), and a bare numeral is a natural number.
inferExprSort ::
  SignatureSorts -> DeclState -> Map Text Sort -> MathExpr -> Maybe Sort
inferExprSort sigs st henv expr = fst <$> inferExprSortP sigs st henv expr

-- Commands that only decorate their single argument (accents and
-- rules above or below): the decorated expression keeps the
-- argument's sort.
texAccentCmds :: [Text]
texAccentCmds =
  [ "hat"
  , "check"
  , "tilde"
  , "bar"
  , "vec"
  , "dot"
  , "ddot"
  , "acute"
  , "grave"
  , "breve"
  , "mathring"
  , "overline"
  , "underline"
  ]

-- A sequence with a relation at its top level is a proposition,
-- whatever the operands' sorts are. Sequences that look like set
-- builders (braces, a colon) or that start with a binder are not
-- read this way.
propFormOf :: MathExpr -> Maybe (Sort, Bool)
propFormOf expr = case expr of
  MathGroup inner -> propFormOf inner
  MathSeq [item] -> propFormOf item
  MathSeq items
    | any isRelationItem items
    , not (any isSetBuilderItem items)
    , not (startsWithBinder items) ->
        Just (SortAtom "Prop", False)
  _ -> Nothing
 where
  isRelationItem (MathText txt) = txt `elem` ["=", "<", ">"]
  isRelationItem (MathCommand name _ _) =
    name
      `elem` [ "in"
             , "notin"
             , "subseteq"
             , "subset"
             , "supseteq"
             , "supset"
             , "le"
             , "leq"
             , "ge"
             , "geq"
             , "ne"
             , "neq"
             , "equiv"
             , "approx"
             , "cong"
             , "sim"
             , "simeq"
             , "prec"
             , "succ"
             , "preceq"
             , "succeq"
             , "models"
             , "propto"
             ]
  isRelationItem _ = False
  isSetBuilderItem (MathText txt) = txt `elem` ["\\{", "\\}", ":"]
  isSetBuilderItem (MathCommand name _ _) = name `elem` ["{", "}"]
  isSetBuilderItem _ = False
  startsWithBinder (MathCommand name _ _ : _) =
    name `elem` ["lambda", "forall", "exists"]
  startsWithBinder _ = False

-- Declarations may describe a container, a function, or the entries of an
-- indexed family. A wildcard subscript is local to the same declaration
-- frame as an ordinary variable, and an exact entry overrides the family.
sortDeclarationKey :: MathExpr -> Text
sortDeclarationKey (MathSeq [item]) = sortDeclarationKey item
sortDeclarationKey (MathGroup inner) = sortDeclarationKey inner
sortDeclarationKey (MathScript base marker arg) =
  sortDeclarationKey base <> marker <> sortDeclarationKey arg
sortDeclarationKey expr = normalizeMathExpr (renderMathExpr expr)

resolveDeclaredSort :: DeclState -> Text -> Maybe Sort
resolveDeclaredSort st = resolve [] . parseSort
 where
  resolve seen (SortApp "Elem" [container]) = do
    let name = renderSort container
    guard (name `notElem` seen)
    declared <- Map.lookup name (activeDeclEnv st)
    resolved <- resolve (name : seen) (parseSort declared)
    case resolved of
      SortApp constructor [element]
        | constructor `elem` ["Set", "Seq"] -> Just element
      _ -> Nothing
  resolve seen (SortApp name args) = SortApp name <$> mapM (resolve seen) args
  resolve _ sort = Just sort

explicitExprSort :: DeclState -> MathExpr -> Maybe Sort
explicitExprSort st expr = exact <|> indexed expr
 where
  env = Map.mapKeys (sortDeclarationKey . parseMathExpr) (activeDeclEnv st)
  exact = Map.lookup (sortDeclarationKey expr) env >>= resolveDeclaredSort st
  indexed (MathSeq [item]) = indexed item
  indexed (MathGroup inner) = indexed inner
  indexed (MathScript base "_" _) =
    (Map.lookup (sortDeclarationKey base <> "_*") env >>= resolveDeclaredSort st)
      <|> do
        SortApp "Seq" [element] <- explicitExprSort st base
        return element
  indexed _ = Nothing

callableSort :: Sort -> Maybe (Sort, Sort)
callableSort (SortApp "Fun" [domain, codomain]) = Just (domain, codomain)
callableSort (SortAtom "Name") = Just (SortAtom "Nat", SortAtom "Nat")
callableSort (SortApp "Seq" [element]) = Just (SortAtom "Nat", element)
callableSort _ = Nothing

-- The comma-call notation f(a,b) unpacks only the OUTER product domain.
-- f(pair) still takes one product-valued argument. Nested products retain
-- their grouping; a three-argument call requires an explicit three-component
-- product domain. This notation convention never identifies a curried function
-- with a function on a product.
applicationArgumentSorts :: Sort -> Int -> Maybe [Sort]
applicationArgumentSorts domain 1 = Just [domain]
applicationArgumentSorts (SortApp "Prod" domains) count
  | length domains == count = Just domains
applicationArgumentSorts _ _ = Nothing

namedSortApplication :: DeclState -> MathExpr -> Maybe (Text, [Sort], Sort, [MathExpr])
namedSortApplication st expr = do
  let raw = normalizeMathExpr (renderMathExpr expr)
  (name, rest) <- splitApplication raw
  guard (not (T.null name) && isOuterParenWrapped rest)
  (domain, codomain) <- explicitExprSort st (parseMathExpr name) >>= callableSort
  let arguments = splitArguments (T.drop 1 (T.dropEnd 1 rest))
  domains <- applicationArgumentSorts domain (length arguments)
  return (name, domains, codomain, map parseMathExpr arguments)
 where
  -- Commas in an index, a macro argument, or a nested call do not
  -- separate this call's arguments.
  splitArguments = go 0 [] [] . T.unpack
   where
    go :: Int -> String -> [Text] -> String -> [Text]
    go _ current parts [] = reverse (T.pack (reverse current) : parts)
    go depth current parts (character : rest)
      | character == ',' && depth == 0 = go 0 [] (T.pack (reverse current) : parts) rest
      | character `elem` ("({[" :: String) = go (depth + 1) (character : current) parts rest
      | character `elem` (")}]" :: String) = go (max 0 (depth - 1)) (character : current) parts rest
      | otherwise = go depth (character : current) parts rest
  -- Parentheses inside a braced index belong to the index, as in
  -- a_{s(k)}(n). The outer application may have an indexed head.
  splitApplication raw = search 0 0 (T.unpack raw)
   where
    search :: Int -> Int -> String -> Maybe (Text, Text)
    search _ _ [] = Nothing
    search depth offset (character : rest)
      | character == '(' && depth == 0 = Just (T.splitAt offset raw)
      | character == '{' = search (depth + 1) (offset + 1) rest
      | character == '}' = search (depth - 1) (offset + 1) rest
      | otherwise = search depth (offset + 1) rest

untainted :: Sort -> (Sort, Bool)
untainted s = (s, False)

tainted :: Sort -> (Sort, Bool)
tainted s = (s, True)

-- The same inference, carrying provenance: the flag is True when
-- the derivation used a harvested sort anywhere. A harvested sort
-- is a hypothesis from context, not a declaration, so a conflict
-- it causes retracts the hypothesis instead of reporting a
-- mismatch (see 'checkApplication').
inferExprSortP ::
  SignatureSorts ->
  DeclState ->
  Map Text Sort ->
  MathExpr ->
  Maybe (Sort, Bool)
inferExprSortP sigs st henv expr =
  (untainted <$> explicitExprSort st expr)
    <|> namedResult
    <|> signedResult
    <|> declared
    <|> harvested
    <|> propForm
    <|> literal
 where
  namedResult = do
    (_, domains, codomain, args) <- namedSortApplication st expr
    (subst, provenance) <- checkInferredArgsP domains (map (inferExprSortP sigs st henv) args)
    return (applySortSubst subst codomain, provenance)
  signedResult =
    case expr of
      MathSeq [item] -> inferExprSortP sigs st henv item
      MathGroup inner -> inferExprSortP sigs st henv inner
      MathScript base _ _ -> inferExprSortP sigs st henv base
      MathCommand name _ [arg]
        | name `elem` texAccentCmds -> inferExprSortP sigs st henv arg
      MathCommand name _ args
        | Just sig <- Map.lookup name sigs
        , (argSorts, resultSort) <-
            freshSignature name (sortDigest (T.concat (map renderMathExpr args))) sig
        , length args == length argSorts
        , Just (subst, taint) <-
            checkInferredArgsP
              argSorts
              (map (inferExprSortP sigs st henv) args) ->
            Just (applySortSubst subst resultSort, taint)
      _ -> Nothing
  declared = untainted <$> (inferDeclType st (renderMathExpr expr) >>= resolveDeclaredSort st)
  harvested = lookupHenv expr
  propForm = propFormOf expr
  lookupHenv e = case e of
    MathSeq [item] -> lookupHenv item
    MathGroup inner -> lookupHenv inner
    MathText txt -> tainted <$> Map.lookup txt henv
    _ -> Nothing
  literal =
    case expr of
      MathText txt
        | let digits = T.strip txt
        , not (T.null digits) && T.all isDigit digits ->
            Just (SortAtom "Nat", False)
      _ -> Nothing

-- A sort with no schematic variables in it.
sortIsConcrete :: Sort -> Bool
sortIsConcrete (SortVar _) = False
sortIsConcrete (SortAtom _) = True
sortIsConcrete (SortApp _ args) = all sortIsConcrete args

-- Every bare single letter occurring in an expression.
mathLetters :: MathExpr -> [Text]
mathLetters expr = case expr of
  MathText txt
    | T.length txt == 1 && T.all isLetter txt -> [txt]
    | otherwise -> []
  MathSeq items -> concatMap mathLetters items
  MathGroup inner -> mathLetters inner
  MathScript base _ arg -> mathLetters base ++ mathLetters arg
  MathCommand _ opt args ->
    maybe [] mathLetters opt ++ concatMap mathLetters args
  _ -> []

-- A bare single letter, the form a harvested sort can attach to.
bareLetter :: MathExpr -> Maybe Text
bareLetter expr = case expr of
  MathSeq [item] -> bareLetter item
  MathGroup inner -> bareLetter inner
  MathText txt
    | T.length txt == 1 && T.all isLetter txt -> Just txt
  _ -> Nothing

data SortAuditResult = SortAuditResult
  { sortAuditSeen :: Int
  , sortAuditChecked :: Int
  , sortAuditFindings :: [Text]
  , sortAuditHarvest :: [(Text, Sort)]
  , sortAuditNotes :: [Text]
  , sortAuditRetract :: [Text]
  }

emptySortAudit :: SortAuditResult
emptySortAudit = SortAuditResult 0 0 [] [] [] []

mergeSortAudit :: SortAuditResult -> SortAuditResult -> SortAuditResult
mergeSortAudit a b =
  SortAuditResult
    (sortAuditSeen a + sortAuditSeen b)
    (sortAuditChecked a + sortAuditChecked b)
    (sortAuditFindings a ++ sortAuditFindings b)
    (sortAuditHarvest a ++ sortAuditHarvest b)
    (sortAuditNotes a ++ sortAuditNotes b)
    (sortAuditRetract a ++ sortAuditRetract b)

checkMathExpr ::
  SignatureSorts -> DeclState -> Map Text Sort -> MathExpr -> SortAuditResult
checkMathExpr sigs st henv0 expr = fst (go (henv0, Set.empty) expr)
 where
  -- Applications are visited in textual order, threading a
  -- span-local harvest environment: a sort stated by an earlier
  -- application in the same span (an aligned display, say) is
  -- available to the later ones, exactly as across spans within
  -- a section. Letters whose harvested sorts conflict inside the
  -- span are poisoned for the rest of the span.
  go state expression
    | Just (name, domains, _, args) <- namedSortApplication st expression =
        let (children, state1) = goSeq state args
            appRes = checkApplication (fst state1) (T.dropWhile (== '\\') name) domains args
            (state2, notes) = applyLocalHarvest state1 (sortAuditHarvest appRes) (sortAuditRetract appRes)
         in (mergeSortAudit children (mergeSortAudit appRes emptySortAudit{sortAuditNotes = notes}), state2)
  go state (MathSeq items) = goSeq state items
  go state (MathGroup inner) = go state inner
  go state (MathScript base _ arg) =
    let (res1, state1) = go state base
        (res2, state2) = go state1 arg
     in (mergeSortAudit res1 res2, state2)
  go state (MathCommand name optArg args) =
    let (optRes, state1) = maybe (emptySortAudit, state) (go state) optArg
        (argsRes, state2) = goSeq state1 args
        children = mergeSortAudit optRes argsRes
     in case Map.lookup name sigs of
          Just sig
            | (argSorts, _) <-
                freshSignature name (sortDigest (T.concat (map renderMathExpr args))) sig
            , length argSorts == length args ->
                let appRes = checkApplication (fst state2) name argSorts args
                    (state3, notes) =
                      applyLocalHarvest
                        state2
                        (sortAuditHarvest appRes)
                        (sortAuditRetract appRes)
                    noteRes = emptySortAudit{sortAuditNotes = notes}
                 in ( mergeSortAudit (mergeSortAudit children appRes) noteRes
                    , state3
                    )
          _ -> (children, state2)
  go state _ = (emptySortAudit, state)

  goSeq state = foldl stepSeq (emptySortAudit, state)
   where
    stepSeq (res, s) item =
      let (r, s') = go s item
       in (mergeSortAudit res r, s')

  applyLocalHarvest (env, poisoned) pairs retracts =
    let (env1, poisoned1, notes) = foldl step (env, poisoned, []) pairs
     in (
          ( foldr Map.delete env1 retracts
          , foldr Set.insert poisoned1 retracts
          )
        , notes
        )
   where
    step (e, pz, notes) (letter, sort)
      | letter `Set.member` pz = (e, pz, notes)
      | Just existing <- Map.lookup letter e
      , existing /= sort =
          ( Map.delete letter e
          , Set.insert letter pz
          , notes
              ++ [ "harvest conflict: "
                     <> letter
                     <> " used as both "
                     <> renderSort existing
                     <> " and "
                     <> renderSort sort
                     <> "; left unknown"
                 ]
          )
      | otherwise = (Map.insert letter sort e, pz, notes)

  checkApplication env name argSorts args =
    let inferred = map (inferExprSortP sigs st env) args
        harvestHere =
          [ (letter, expectedSort)
          | (expectedSort, arg) <- zip argSorts args
          , sortIsConcrete expectedSort
          , Just letter <- [bareLetter arg]
          , -- Explicit declarations already participate in the check below.
          -- Do not replace them with an argument's expected supertype.
          isNothing (inferDeclType st letter)
          ]
        retractHere =
          [ letter
          | ((_, arg), (_, _, True)) <- retractMarks
          , letter <- mathLetters arg
          , Map.member letter env
          ]
        retractMarks =
          [ ((idx, arg), (expectedSort, actualSort, taint))
          | (idx, expectedSort, arg, Just (actualSort, taint)) <-
              zip4 [1 :: Int ..] argSorts args inferred
          , isNothing (checkSort Map.empty expectedSort actualSort)
          ]
        checkedHere = if all isJust inferred then 1 else 0
        step (subst, acc) (idx, expectedSort, Just (actualSort, taint)) =
          case checkSort subst expectedSort actualSort of
            Just subst' -> (subst', acc)
            -- A conflict caused by a harvested sort retracts the
            -- hypothesis (recorded in sortAuditRetracted); it is
            -- not a mismatch.
            Nothing
              | taint -> (subst, acc)
              | otherwise ->
                  (subst, acc ++ [mismatchText idx expectedSort actualSort])
        step acc _ = acc
        (_, findings) =
          foldl step (Map.empty, []) (zip3 [1 :: Int ..] argSorts inferred)
     in SortAuditResult 1 checkedHere findings harvestHere [] retractHere
   where
    mismatchText idx expectedSort actualSort =
      "\\"
        <> name
        <> " argument "
        <> T.pack (show idx)
        <> ": expected sort "
        <> renderSort expectedSort
        <> " but inferred "
        <> renderSort actualSort

data SortWalkRefs = SortWalkRefs
  { swDecl :: IORef DeclState
  , swPending :: IORef [DeclCommand]
  , swResult :: IORef SortAuditResult
  , swInFence :: IORef Bool
  , swInComment :: IORef Bool
  , swMathMeta :: IORef (Maybe [Text])
  , swMathSpan :: IORef (Maybe (Text, Int, Text))
  , swHarvest :: IORef [(Int, Map Text Sort)]
  , swHarvestUnion :: IORef (Map Text [Sort])
  }

runSortAudit :: FilePath -> [FilePath] -> IO ()
runSortAudit macrosPath paths = do
  notationData <- readNotationData macrosPath
  let sigs = signatureSorts notationData
  results <- mapM (sortAuditFile sigs) paths
  let total = foldr mergeSortAudit emptySortAudit results
  hPutStrLn stderr "[lint] sort audit (validation only):"
  forM_ (sortAuditFindings total) $ \finding ->
    TIO.hPutStrLn stderr ("  " <> finding)
  forM_ (sortAuditNotes total) $ \note ->
    TIO.hPutStrLn stderr ("  " <> note)
  hPutStrLn
    stderr
    ( "  "
        <> show (sortAuditSeen total)
        <> " signed applications, "
        <> show (sortAuditChecked total)
        <> " fully inferred, "
        <> show (length (sortAuditFindings total))
        <> " mismatch(es), "
        <> show (length (sortAuditRetract total))
        <> " harvest retraction(s)"
    )

sortAuditFile :: SignatureSorts -> FilePath -> IO SortAuditResult
sortAuditFile sigs path = do
  contents <- TIO.readFile path
  -- Two passes over the file: the first collects every harvested
  -- sort in the file, and the second starts from the letters that
  -- were harvested unambiguously, so a sort the text states late
  -- in a chapter is also known at the letter's earlier uses.
  -- Letters harvested with two different sorts are left out.
  (_, union) <- walkFile contents Map.empty
  let prefill = Map.mapMaybe uniqueSort union
  if Map.null prefill
    then fst <$> walkFile contents Map.empty
    else fst <$> walkFile contents prefill
 where
  walkFile contents prefill = do
    refs <-
      SortWalkRefs
        <$> newIORef initialDeclState
        <*> newIORef []
        <*> newIORef emptySortAudit
        <*> newIORef False
        <*> newIORef False
        <*> newIORef Nothing
        <*> newIORef Nothing
        <*> newIORef [(0, prefill)]
        <*> newIORef Map.empty
    forM_ (zip [1 ..] (T.lines contents)) $
      uncurry (sortAuditLine sigs path refs)
    result <- readIORef (swResult refs)
    union <- readIORef (swHarvestUnion refs)
    return (result, union)

uniqueSort :: [Sort] -> Maybe Sort
uniqueSort [s] = Just s
uniqueSort _ = Nothing

addHarvestedSort :: Sort -> Maybe [Sort] -> Maybe [Sort]
addHarvestedSort sort Nothing = Just [sort]
addHarvestedSort sort (Just old)
  | sort `elem` old = Just old
  | otherwise = Just (sort : old)

-- Feed one span's harvested sorts into the current section frame.
-- A letter harvested with two different concrete sorts in one
-- section is a dual use: it is dropped again and reported, so it
-- stays unknown rather than acquiring a sort it may not have.
applySortHarvest ::
  SortWalkRefs -> Text -> Text -> [(Text, Sort)] -> IO ()
applySortHarvest refs prefix context pairs =
  forM_ pairs $ \(letter, sort) -> do
    stack <- readIORef (swHarvest refs)
    case stack of
      ((level, frame) : rest)
        | Just existing <- Map.lookup letter frame
        , existing /= sort -> do
            writeIORef
              (swHarvest refs)
              ((level, Map.delete letter frame) : rest)
            let note =
                  prefix
                    <> "harvest conflict: "
                    <> letter
                    <> " used as both "
                    <> renderSort existing
                    <> " and "
                    <> renderSort sort
                    <> "; left unknown"
                    <> context
            modifyIORef
              (swResult refs)
              ( \current ->
                  mergeSortAudit
                    current
                    emptySortAudit{sortAuditNotes = [note]}
              )
        | otherwise ->
            writeIORef
              (swHarvest refs)
              ((level, Map.insert letter sort frame) : rest)
      [] -> return ()

sortAuditLine :: SignatureSorts -> FilePath -> SortWalkRefs -> Int -> Text -> IO ()
sortAuditLine sigs path refs lineNo rawLine = do
  mathMeta <- readIORef (swMathMeta refs)
  case mathMeta of
    Just acc
      | "\\end{mathmeta}" `T.isInfixOf` rawLine -> do
          applySortMathMeta refs (T.unlines (reverse (rawLine : acc)))
          writeIORef (swMathMeta refs) Nothing
      | otherwise ->
          writeIORef (swMathMeta refs) (Just (rawLine : acc))
    Nothing
      | "\\begin{mathmeta}" `T.isInfixOf` rawLine -> do
          resetSortInline refs
          if "\\end{mathmeta}" `T.isInfixOf` rawLine
            then applySortMathMeta refs rawLine
            else writeIORef (swMathMeta refs) (Just [rawLine])
      | isFenceLine rawLine -> do
          resetSortInline refs
          inFence <- readIORef (swInFence refs)
          writeIORef (swInFence refs) (not inFence)
      | otherwise -> do
          inFence <- readIORef (swInFence refs)
          mathSpan <- readIORef (swMathSpan refs)
          unless inFence $ do
            when (T.null (T.strip rawLine)) (resetSortInline refs)
            let inDisplay = case mathSpan of
                  Just ("$$", _, _) -> True
                  _ -> False
            when (not inDisplay && isHeadingLine rawLine) $ do
              resetSortInline refs
              flushSortPending refs
              enterSection (swDecl refs) (T.length (T.takeWhile (== '#') rawLine))
              let level = T.length (T.takeWhile (== '#') rawLine)
              modifyIORef (swHarvest refs) $ \stack ->
                (level, Map.empty) : dropWhile (\(l, _) -> l >= level) stack
            inComment <- readIORef (swInComment refs)
            let (visible, inComment') = stripHtmlCommentSpan inComment rawLine
            writeIORef (swInComment refs) inComment'
            sortAuditText sigs path refs lineNo (stripLatexComments visible)

applySortMathMeta :: SortWalkRefs -> Text -> IO ()
applySortMathMeta refs blockText =
  case parseMathMetaBlock blockText of
    Just directives -> forM_ directives applyDirective
    Nothing -> return ()
 where
  applyDirective (MathMetaDecl cmd) = applyDeclCommand (swDecl refs) cmd
  applyDirective (MathMetaWith cmds) = modifyIORef (swPending refs) (++ cmds)
  applyDirective _ = return ()

flushSortPending :: SortWalkRefs -> IO ()
flushSortPending refs = do
  cmds <- readIORef (swPending refs)
  writeIORef (swPending refs) []
  mapM_ (applyDeclCommand (swDecl refs)) cmds

stripHtmlCommentSpan :: Bool -> Text -> (Text, Bool)
stripHtmlCommentSpan inComment txt
  | inComment =
      case T.breakOn "-->" txt of
        (_, rest)
          | not (T.null rest) -> stripHtmlCommentSpan False (T.drop 3 rest)
        _ -> ("", True)
  | otherwise =
      case T.breakOn "<!--" txt of
        (before, rest)
          | T.null rest -> (before, False)
          | otherwise ->
              let (after, stillIn) = stripHtmlCommentSpan True (T.drop 4 rest)
               in (before <> after, stillIn)

-- Inline math cannot cross a Markdown block boundary. Display math can.
resetSortInline :: SortWalkRefs -> IO ()
resetSortInline refs = modifyIORef (swMathSpan refs) $ \spanState ->
  case spanState of
    Just ("$", _, _) -> Nothing
    _ -> spanState

-- Find an unescaped dollar, retaining escaped dollars in the span's contents.
breakMathDollar :: Text -> (Text, Text)
breakMathDollar txt =
  case T.breakOn "$" txt of
    (before, rest)
      | not (T.null rest) && odd (T.length (T.takeWhileEnd (== '\\') before)) ->
          let (after, suffix) = breakMathDollar (T.drop 1 rest)
           in (before <> "$" <> after, suffix)
      | otherwise -> (before, rest)

sortAuditText :: SignatureSorts -> FilePath -> SortWalkRefs -> Int -> Text -> IO ()
sortAuditText sigs path refs lineNo txt = do
  modifyIORef (swMathSpan refs) (fmap (\(delimiter, startLine, acc) -> (delimiter, startLine, acc <> "\n")))
  go txt
 where
  go remaining = do
    spanState <- readIORef (swMathSpan refs)
    let (before, rest) = breakMathDollar remaining
        delimiter = if "$$" `T.isPrefixOf` rest then "$$" else "$"
        after = T.drop (T.length delimiter) rest
    case spanState of
      Nothing -> unless (T.null rest) $ do
        writeIORef (swMathSpan refs) (Just (delimiter, lineNo, ""))
        go after
      Just (opening, startLine, acc)
        | T.null rest ->
            writeIORef (swMathSpan refs) (Just (opening, startLine, acc <> before))
        | delimiter == opening -> do
            writeIORef (swMathSpan refs) Nothing
            sortAuditSpan sigs path refs startLine (acc <> before)
            go after
        | opening == "$" -> do
            -- A display opener ends an incomplete inline span.
            writeIORef (swMathSpan refs) (Just (delimiter, lineNo, ""))
            go after
        | otherwise -> do
            writeIORef (swMathSpan refs) (Just (opening, startLine, acc <> before <> delimiter))
            go after

sortAuditSpan :: SignatureSorts -> FilePath -> SortWalkRefs -> Int -> Text -> IO ()
sortAuditSpan sigs path refs lineNo spanText = do
  flushSortPending refs
  st <- readIORef (swDecl refs)
  stack <- readIORef (swHarvest refs)
  let henv = Map.unions (map snd stack)
      res = checkMathExpr sigs st henv (parseMathExpr spanText)
      prefix = T.pack path <> ":" <> T.pack (show lineNo) <> ": sort mismatch: "
      context = "  (in $" <> truncateSpan spanText <> "$)"
      findings' = map (\finding -> prefix <> finding <> context) (sortAuditFindings res)
      plainPrefix = T.pack path <> ":" <> T.pack (show lineNo) <> ": "
      notes' = map (\note -> plainPrefix <> note <> context) (sortAuditNotes res)
  modifyIORef
    (swResult refs)
    ( \current ->
        mergeSortAudit
          current
          res{sortAuditFindings = findings', sortAuditNotes = notes'}
    )
  modifyIORef (swHarvestUnion refs) $ \union ->
    foldl
      (\u (letter, sort) -> Map.alter (addHarvestedSort sort) letter u)
      union
      (sortAuditHarvest res)
  applySortHarvest
    refs
    (T.pack path <> ":" <> T.pack (show lineNo) <> ": ")
    context
    (sortAuditHarvest res)
  unless (null (sortAuditRetract res)) $
    modifyIORef (swHarvest refs) $ \frames ->
      [ (level, foldr Map.delete frame (sortAuditRetract res))
      | (level, frame) <- frames
      ]
 where
  truncateSpan txt =
    let flat = T.replace "\n" " " txt
     in if T.length flat > 80 then T.take 77 flat <> "..." else flat

-- Generic-notation DSL: a table-driven grammar for the math the book
-- writes, in the spirit of Coq's notation system.  Operators are data
-- (dslInfixTable and its companions), so extending the grammar means
-- adding rows, not parser code.  The angle bracket <a, b> is a primary,
-- so it can appear wherever a term can: nested, as an argument, on
-- either side of a relation.  A raw < is read as a bracket when it
-- opens at a primary position, or when a term is followed by a <...>
-- whose interior carries a top-level comma (an application argument);
-- otherwise it is the comparison.  This section parses a math span
-- into DslExpr, and resolves every raw angle bracket to the one
-- registered notation whose argument sorts -- and the sort the
-- surrounding context expects -- it fits, the resolution stage of the
-- generic-notation plan.  Only resolutions the declarations prove are
-- made; when the winner is not unique the bracket stays unresolved.
-- The lint mode --dsl-audit reports the verdicts over the book
-- without changing any output, ahead of wiring the resolution into
-- the filter itself.

data DslAssoc = DslAssocLeft | DslAssocRight | DslAssocNone
  deriving (Eq, Show)

-- A token: the raw text that precedes it (whitespace and spacing
-- commands, folded in so the semantic token stream stays clean) and
-- its own text.  Commands keep their backslash.
data DslTok = DslTok
  { dslTokLead :: Text
  , dslTokText :: Text
  }
  deriving (Eq, Show)

dslTokRender :: DslTok -> Text
dslTokRender tok = dslTokLead tok <> dslTokText tok

dslSpacingTexts :: [Text]
dslSpacingTexts =
  [ "\\,"
  , "\\;"
  , "\\:"
  , "\\!"
  , "\\ "
  , "\\quad"
  , "\\qquad"
  , "\\displaystyle"
  ]

lexDsl :: Text -> [DslTok]
lexDsl = scan ""
 where
  scan lead txt
    | T.null txt = [DslTok lead "" | not (T.null lead)]
    | isSpace (T.head txt) =
        let (ws, rest) = T.span isSpace txt
         in scan (lead <> ws) rest
    | otherwise =
        case lexDslCommand txt of
          Just (core, rest)
            | core `elem` dslSpacingTexts -> scan (lead <> core) rest
            | otherwise -> DslTok lead core : scan "" rest
          Nothing ->
            let (core, rest) = lexDslSymbol txt
             in DslTok lead core : scan "" rest

lexDslCommand :: Text -> Maybe (Text, Text)
lexDslCommand txt = do
  rest <- T.stripPrefix "\\" txt
  case T.uncons rest of
    Just (c, rest')
      | isLetter c ->
          let (tailText, rest'') = T.span isLetter rest'
           in Just ("\\" <> T.cons c tailText, rest'')
      | otherwise -> Just ("\\" <> T.singleton c, rest')
    Nothing -> Just ("\\", "")

lexDslSymbol :: Text -> (Text, Text)
lexDslSymbol txt
  | Just rest <- T.stripPrefix ":=" txt = (":=", rest)
  | otherwise =
      case T.uncons txt of
        Just (c, _)
          | isDigit c ->
              let (digits, rest) = T.span isDigit txt
               in case T.uncons rest of
                    Just ('.', rest')
                      | Just (c', _) <- T.uncons rest'
                      , isDigit c' ->
                          let (frac, rest'') = T.span isDigit rest'
                           in (digits <> "." <> frac, rest'')
                    _ -> (digits, rest)
        Just (c, rest) -> (T.singleton c, rest)
        Nothing -> ("", "")

-- The expression tree.  Nodes keep their tokens so a parsed span
-- renders back byte-for-byte; resolution replaces a raw angle node
-- with a generated DslResolved call.
data DslBraced = DslBraced DslTok [DslItem] DslTok
  deriving (Eq, Show)

-- A list item with the separator token that precedes it (Nothing for
-- the first item).  Separators are commas and semicolons; a relation
-- token also appears here where a list feeds a multi-variable
-- relation (x, y \in X), keeping the rendering faithful.
type DslItem = (Maybe DslTok, DslExpr)

data DslExpr
  = DslAtom DslTok
  | DslSeq [DslExpr]
  | DslApp DslExpr DslExpr
  | DslCmd DslTok (Maybe DslBraced) [DslBraced]
  | DslGroup DslBraced
  | DslInfix DslTok DslExpr DslExpr
  | DslPrefix DslTok DslExpr
  | DslScript DslExpr [DslTok] DslExpr
  | DslBinder DslTok [DslTok] DslExpr
  | DslDelimited DslTok [DslItem] DslTok
  | DslSet DslTok [DslItem] (Maybe (DslTok, [DslItem])) DslTok
  | DslAngle DslTok [DslItem] (Maybe (DslTok, [DslItem])) DslTok Bool
  | DslBars DslTok DslExpr DslTok
  | DslEnv DslTok [DslItem] DslTok
  | DslResolved Text [[DslItem]]
  deriving (Eq, Show)

dslItemsExprs :: [DslItem] -> [DslExpr]
dslItemsExprs = map snd

renderDslItems :: [DslItem] -> Text
renderDslItems items =
  T.concat [maybe "" dslTokRender sep <> renderDsl expr | (sep, expr) <- items]

renderDslBraced :: DslBraced -> Text
renderDslBraced (DslBraced open items close) =
  dslTokRender open <> renderDslItems items <> dslTokRender close

renderDsl :: DslExpr -> Text
renderDsl (DslAtom tok) = dslTokRender tok
renderDsl (DslSeq exprs) = T.concat (map renderDsl exprs)
renderDsl (DslApp fun arg) = renderDsl fun <> renderDsl arg
renderDsl (DslCmd tok opt args) =
  dslTokRender tok
    <> maybe "" renderDslBraced opt
    <> T.concat (map renderDslBraced args)
renderDsl (DslGroup braced) = renderDslBraced braced
renderDsl (DslInfix op lhs rhs) =
  renderDsl lhs <> dslTokRender op <> renderDsl rhs
renderDsl (DslPrefix op expr) = dslTokRender op <> renderDsl expr
renderDsl (DslScript base markers arg) =
  renderDsl base <> T.concat (map dslTokRender markers) <> renderDsl arg
renderDsl (DslBinder kw spec body) =
  dslTokRender kw <> T.concat (map dslTokRender spec) <> renderDsl body
renderDsl (DslDelimited open items close) =
  dslTokRender open <> renderDslItems items <> dslTokRender close
renderDsl (DslSet open items cond close) =
  dslTokRender open
    <> renderDslItems items
    <> maybe "" (\(sep, condItems) -> dslTokRender sep <> renderDslItems condItems) cond
    <> dslTokRender close
renderDsl (DslAngle open items cond close _) =
  dslTokRender open
    <> renderDslItems items
    <> maybe "" (\(sep, condItems) -> dslTokRender sep <> renderDslItems condItems) cond
    <> dslTokRender close
renderDsl (DslBars open expr close) =
  dslTokRender open <> renderDsl expr <> dslTokRender close
renderDsl (DslEnv open items close) =
  dslTokRender open <> renderDslItems items <> dslTokRender close
renderDsl (DslResolved name args) =
  "\\"
    <> name
    <> T.concat ["{" <> renderDslItems items <> "}" | items <- args]

-- Operator table: token text to (level, associativity).  Larger
-- levels bind tighter.  This is the grammar; the parser below only
-- interprets it.
dslInfixTable :: [(Text, (Int, DslAssoc))]
dslInfixTable =
  [ ("\\cdot", (60, DslAssocLeft))
  , ("\\times", (60, DslAssocLeft))
  , ("\\cap", (60, DslAssocLeft))
  , ("\\circ", (60, DslAssocLeft))
  , ("\\concat", (60, DslAssocLeft))
  , ("\\otimes", (60, DslAssocLeft))
  , ("\\ast", (60, DslAssocLeft))
  , ("\\div", (60, DslAssocLeft))
  , ("*", (60, DslAssocLeft))
  , ("/", (60, DslAssocLeft))
  , ("+", (50, DslAssocLeft))
  , ("-", (50, DslAssocLeft))
  , ("\\cup", (50, DslAssocLeft))
  , ("\\sqcup", (50, DslAssocLeft))
  , ("\\setminus", (50, DslAssocLeft))
  , ("\\oplus", (50, DslAssocLeft))
  , ("\\triangle", (50, DslAssocLeft))
  , ("\\pm", (50, DslAssocLeft))
  , ("\\mp", (50, DslAssocLeft))
  , ("=", (40, DslAssocNone))
  , ("\\ne", (40, DslAssocNone))
  , ("<", (40, DslAssocNone))
  , (">", (40, DslAssocNone))
  , ("\\le", (40, DslAssocNone))
  , ("\\ge", (40, DslAssocNone))
  , ("\\in", (40, DslAssocNone))
  , ("\\notin", (40, DslAssocNone))
  , ("\\subseteq", (40, DslAssocNone))
  , ("\\IncludedIn", (40, DslAssocNone))
  , ("\\subset", (40, DslAssocNone))
  , ("\\supseteq", (40, DslAssocNone))
  , ("\\supset", (40, DslAssocNone))
  , ("\\equiv", (40, DslAssocNone))
  , ("\\sim", (40, DslAssocNone))
  , ("\\approx", (40, DslAssocNone))
  , ("\\cong", (40, DslAssocNone))
  , ("\\preceq", (40, DslAssocNone))
  , ("\\prefixOf", (40, DslAssocNone))
  , ("\\sqsubseteq", (40, DslAssocNone))
  , ("\\prec", (40, DslAssocNone))
  , ("\\succeq", (40, DslAssocNone))
  , ("\\mid", (40, DslAssocNone))
  , ("\\perp", (40, DslAssocNone))
  , ("\\models", (40, DslAssocNone))
  , ("\\vdash", (40, DslAssocNone))
  , ("\\nvdash", (40, DslAssocNone))
  , ("\\forces", (40, DslAssocNone))
  , ("\\dashv", (40, DslAssocNone))
  , ("\\parallel", (40, DslAssocNone))
  , ("\\propto", (40, DslAssocNone))
  , ("\\asymp", (40, DslAssocNone))
  , ("\\land", (35, DslAssocLeft))
  , ("\\lor", (30, DslAssocLeft))
  , ("\\to", (20, DslAssocRight))
  , ("\\rightarrow", (20, DslAssocRight))
  , ("\\Rightarrow", (20, DslAssocRight))
  , ("\\leftrightarrow", (20, DslAssocRight))
  , ("\\iff", (20, DslAssocRight))
  , ("\\longrightarrow", (20, DslAssocRight))
  , ("\\implies", (20, DslAssocRight))
  , ("\\impliedby", (20, DslAssocRight))
  , ("\\mapsto", (20, DslAssocRight))
  , (":", (15, DslAssocNone))
  , (":=", (5, DslAssocNone))
  ]

dslInfix :: Text -> Maybe (Int, DslAssoc)
dslInfix tok = lookup tok dslInfixTable

dslInfixLbp :: (Int, DslAssoc) -> Int
dslInfixLbp (level, _) = 2 * level

dslInfixRbp :: (Int, DslAssoc) -> Int
dslInfixRbp (level, DslAssocLeft) = 2 * level + 1
dslInfixRbp (level, _) = 2 * level - 1

-- Unary prefix operators and the binding power of their operand:
-- negation binds above conjunction, unary minus just above addition
-- (so -1/2 and -a + b read as usual).
dslPrefixTable :: [(Text, Int)]
dslPrefixTable =
  [ ("\\neg", 71)
  , ("\\sim", 71)
  , ("-", 101)
  , ("+", 101)
  ]

dslBigops :: [Text]
dslBigops =
  [ "\\sum"
  , "\\prod"
  , "\\bigcup"
  , "\\bigcap"
  , "\\bigvee"
  , "\\bigwedge"
  , "\\bigoplus"
  , "\\bigotimes"
  , "\\bigsqcup"
  , "\\sup"
  , "\\inf"
  , "\\lim"
  , "\\max"
  , "\\min"
  , "\\limsup"
  , "\\liminf"
  ]

dslAccents :: [Text]
dslAccents =
  [ "\\hat"
  , "\\bar"
  , "\\tilde"
  , "\\dot"
  , "\\ddot"
  , "\\vec"
  , "\\widehat"
  , "\\widetilde"
  , "\\overline"
  , "\\underline"
  , "\\check"
  , "\\breve"
  , "\\acute"
  , "\\grave"
  , "\\mathring"
  ]

-- Commands with a fixed number of mandatory arguments, in the
-- TeX sense: when the braces are missing, the next single token
-- is the argument, so \frac12 reads as \frac{1}{2} and
-- \mathcal B as \mathcal{B}. The argument capture in
-- 'parseDslCommand' fills the argument list in order, braced and
-- bare arguments alike.
dslBareArgCmds :: [(Text, Int)]
dslBareArgCmds =
  [ ("\\frac", 2)
  , ("\\dfrac", 2)
  , ("\\tfrac", 2)
  , ("\\binom", 2)
  , ("\\sqrt", 1)
  , ("\\pmod", 1)
  , ("\\mathcal", 1)
  , ("\\mathbb", 1)
  , ("\\mathrm", 1)
  , ("\\mathbf", 1)
  , ("\\mathsf", 1)
  , ("\\mathfrak", 1)
  , ("\\boldsymbol", 1)
  , ("\\operatorname", 1)
  ]

-- Commands whose braced argument is prose, not math: the argument
-- is kept raw. Font commands and the \xrightarrow family are not
-- here; their arguments are math and parse as ordinary groups.
dslOpaqueArgCmds :: [Text]
dslOpaqueArgCmds =
  [ "\\text"
  , "\\textbf"
  , "\\textit"
  , "\\emph"
  , "\\textrm"
  , "\\texttt"
  , "\\textsf"
  ]

-- Size commands that close or separate a delimited construct; when
-- one is followed by a closer it belongs to that closer, not to an
-- application.
dslClosingSizeCmds :: [Text]
dslClosingSizeCmds =
  [ "\\right"
  , "\\bigr"
  , "\\Bigr"
  , "\\biggr"
  , "\\Biggr"
  , "\\middle"
  , "\\bigm"
  , "\\Bigm"
  ]

dslSizeCmds :: [Text]
dslSizeCmds =
  [ "\\left"
  , "\\right"
  , "\\middle"
  , "\\bigl"
  , "\\bigr"
  , "\\Bigl"
  , "\\Bigr"
  , "\\biggl"
  , "\\biggr"
  , "\\Biggl"
  , "\\Biggr"
  , "\\big"
  , "\\Big"
  , "\\bigm"
  , "\\Bigm"
  ]

data DslCtx = DslCtx
  { dslCtxAngle :: Bool
  , dslCtxNoBar :: Bool
  , dslCtxNoRestrict :: Bool
  }

dslCtx0 :: DslCtx
dslCtx0 = DslCtx False False False

dropEnd :: Int -> [a] -> [a]
dropEnd n xs = take (length xs - n) xs

takeDslBracedGroup :: [DslTok] -> Maybe ([DslTok], [DslTok])
takeDslBracedGroup toks@(tok : rest)
  | dslTokText tok == "{" = go 1 [tok] rest
  | otherwise = Nothing
 where
  go depth acc []
    | depth == 0 = Just (reverse acc, [])
    | otherwise = Nothing
  go depth acc (t : r)
    | depth == 0 = Just (reverse acc, t : r)
    | dslTokText t == "{" = go (depth + 1) (t : acc) r
    | dslTokText t == "}" = go (depth - 1) (t : acc) r
    | otherwise = go depth (t : acc) r
takeDslBracedGroup [] = Nothing

isDslAtomTok :: DslTok -> Bool
isDslAtomTok tok =
  case T.uncons (dslTokText tok) of
    Just (c, rest) ->
      (isLetter c || isDigit c) && (T.null rest || T.all isDigit (dslTokText tok))
    Nothing -> False

isDslVarTok :: DslTok -> Bool
isDslVarTok tok =
  case T.uncons (dslTokText tok) of
    Just (c, rest) -> isLetter c && T.null rest
    Nothing -> False

canStartDslPrimary :: DslCtx -> DslTok -> Bool
canStartDslPrimary ctx tok
  | txt `elem` [")", "]", "}", "\\}", "\\rangle"] = False
  | txt `elem` ["|", "\\|"] && dslCtxNoBar ctx = False
  | txt `elem` ["(", "[", "{", "\\{", "|", "\\|", "\\langle", "."] = True
  | T.isPrefixOf "\\" txt =
      txt `notElem` ["\\}", "\\end"]
        && isNothing (dslInfix txt)
        && isNothing (lookup txt dslPrefixTable)
  | otherwise = isDslAtomTok tok
 where
  txt = dslTokText tok

-- Scan for the angle bracket that matches the < at the head of the
-- token stream: its position, and whether its interior carries a
-- comma at its own top level (the application-argument test).
scanDslAngle :: [DslTok] -> Maybe (Int, Bool)
scanDslAngle toks = go 0 0 False 0 toks
 where
  rawMode = case toks of
    (t : _) -> dslTokText t == "<"
    [] -> True
  opensAngle txt = txt == "\\langle" || (rawMode && txt == "<")
  closesAngle txt = txt == "\\rangle" || (rawMode && txt == ">")
  go _ _ _ _ [] = Nothing
  go angleDepth otherDepth comma idx (tok : rest) =
    let txt = dslTokText tok
     in if opensAngle txt && otherDepth == 0
          then go (angleDepth + 1) otherDepth comma (idx + 1) rest
          else
            if closesAngle txt && otherDepth == 0
              then
                if angleDepth == 1
                  then Just (idx, comma)
                  else go (angleDepth - 1) otherDepth comma (idx + 1) rest
              else
                if txt `elem` ["(", "[", "{", "\\{"]
                  then go angleDepth (otherDepth + 1) comma (idx + 1) rest
                  else
                    if txt `elem` [")", "]", "}", "\\}"]
                      then
                        if otherDepth == 0
                          then Nothing
                          else go angleDepth (otherDepth - 1) comma (idx + 1) rest
                      else
                        go
                          angleDepth
                          otherDepth
                          (comma || (txt == "," && otherDepth == 0 && angleDepth == 1))
                          (idx + 1)
                          rest

parseDslExpr :: DslCtx -> Int -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslExpr ctx minBp toks@(tok : _)
  | dslTokText tok `elem` ["&", "\\\\"] = do
      (inner, rest) <- parseDslExpr ctx minBp (drop 1 toks)
      return (DslSeq [DslAtom tok, inner], rest)
parseDslExpr ctx minBp toks = do
  (left, rest) <- parseDslHead ctx toks
  parseDslLoop ctx minBp left rest

{- | Scripts carried by an infix operator itself, as in \sim_1 or
\forces^*: the decoration belongs to the operator, not the rhs.
-}
takeDslOpScripts :: DslCtx -> [DslTok] -> [DslTok] -> ([DslTok], [DslTok])
takeDslOpScripts ctx acc toks@(mark : argToks)
  | dslTokText mark `elem` ["_", "^"]
  , Just (_, rest') <- parseDslScriptArg ctx argToks =
      takeDslOpScripts
        ctx
        (acc ++ take (length toks - length rest') toks)
        rest'
takeDslOpScripts _ acc toks = (acc, toks)

{- | Fold an operator and its scripts into one token; the scripts'
rendered text is kept, so rendering stays byte-exact.
-}
mergeDslOp :: [DslTok] -> DslTok
mergeDslOp [] = DslTok "" ""
mergeDslOp (t : ts) =
  t{dslTokText = dslTokText t <> T.concat (map dslTokRender ts)}

parseDslLoop :: DslCtx -> Int -> DslExpr -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslLoop ctx minBp left rest@(tok : tailToks)
  | dslTokText tok `elem` ["&", "\\\\"] && minBp > 0 = Just (left, rest)
  | dslTokText tok `elem` ["\\right", "\\middle"] = Just (left, rest)
  | dslTokText tok == "<" =
      case scanDslAngle rest of
        Just (_, True)
          | 2 * 90 >= minBp -> do
              (arg, rest') <- parseDslUnit ctx rest
              parseDslLoop ctx minBp (DslApp left arg) rest'
        _
          | Just spec <- dslInfix "<"
          , dslInfixLbp spec >= minBp -> do
              (rhs, rest') <- parseDslExpr ctx (dslInfixRbp spec) tailToks
              parseDslLoop ctx minBp (DslInfix tok left rhs) rest'
          | otherwise -> Just (left, rest)
  | dslTokText tok `elem` ["&", "\\\\"] && minBp == 0 =
      case tailToks of
        [] -> Just (DslSeq [left, DslAtom tok], [])
        (opTok : afterOp)
          | dslTokText opTok /= "<"
          , Just spec <- dslInfix (dslTokText opTok) -> do
              (rhs, rest') <- parseDslExpr ctx (dslInfixRbp spec) afterOp
              parseDslLoop
                ctx
                minBp
                (DslInfix opTok (DslSeq [left, DslAtom tok]) rhs)
                rest'
        _ -> case parseDslExpr ctx 0 tailToks of
          Just (rhs, rest') ->
            parseDslLoop ctx minBp (DslSeq [left, DslAtom tok, rhs]) rest'
          -- Nothing past the separator starts an expression (the
          -- \end of an environment, a closing delimiter): the
          -- separator is a trailing one and the rest belongs to
          -- the enclosing construct.
          Nothing -> Just (DslSeq [left, DslAtom tok], tailToks)
  | Just spec <- dslInfix (dslTokText tok)
  , not (dslTokText tok == ">" && dslCtxAngle ctx)
  , not (dslTokText tok == "|" && dslCtxNoBar ctx)
  , dslInfixLbp spec >= minBp = do
      let (opToks, rhsToks) = takeDslOpScripts ctx [tok] tailToks
      case parseDslExpr ctx (dslInfixRbp spec) rhsToks of
        Just (rhs, rest') ->
          parseDslLoop ctx minBp (DslInfix (mergeDslOp opToks) left rhs) rest'
        -- An operator with nothing after it that could start its
        -- right side is a mention, juxtaposed like the ** of G^{**}.
        Nothing -> case rhsToks of
          [] ->
            parseDslLoop ctx minBp (DslApp left (DslAtom tok)) tailToks
          (t : _)
            | not (canStartDslPrimary ctx t) ->
                parseDslLoop ctx minBp (DslApp left (DslAtom tok)) tailToks
            | otherwise -> Nothing
  | dslTokText tok `elem` dslSizeCmds
  , (barTok : subTok : _) <- tailToks
  , dslTokText barTok == "|"
  , dslTokText subTok == "_" = do
      (arg, rest') <- parseDslScriptArg ctx (drop 2 tailToks)
      parseDslLoop
        ctx
        minBp
        (DslScript left [tok, barTok, subTok] arg)
        rest'
  | dslTokText tok `elem` dslSizeCmds
  , (nextTok : _) <- tailToks
  , dslTokText nextTok
      `elem` [")", "]", "}", "\\}", "\\rangle", "|", "\\|", ">"] =
      Just (left, rest)
  | isJust (lookup (dslTokText tok) dslPrefixTable) && 2 * 90 >= minBp = do
      (arg, rest') <- parseDslHead ctx rest
      parseDslLoop ctx minBp (DslApp left arg) rest'
  | canStartDslPrimary ctx tok && 2 * 90 >= minBp = do
      (arg, rest') <- parseDslUnit ctx rest
      parseDslLoop ctx minBp (DslApp left arg) rest'
  | otherwise = Just (left, rest)
parseDslLoop _ _ left [] = Just (left, [])

parseDslHead :: DslCtx -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslHead ctx toks@(tok : rest)
  | dslTokText tok `elem` ["\\forall", "\\exists"] =
      parseDslBinder ctx toks <|> parseDslUnit ctx toks
  | dslTokText tok == "\\lambda" =
      case rest of
        (v : dot : _)
          | isDslVarTok v && dslTokText dot == "." ->
              parseDslBinder ctx toks
        _ -> parseDslUnit ctx toks
  | Just rbp <- lookup (dslTokText tok) dslPrefixTable =
      case parseDslExpr ctx rbp rest of
        Just (expr, rest') -> Just (DslPrefix tok expr, rest')
        -- A lone operator as a term (the placeholder in A \\times -,
        -- a mentioned \\sim): the operator itself is the atom.
        Nothing -> Just (DslAtom tok, rest)
  | dslTokText tok `elem` dslBigops = do
      (base, rest') <- parseDslPostfixes ctx (DslAtom tok) rest
      case parseDslExpr ctx (2 * 60 + 1) rest' of
        Just (body, rest'') -> return (DslSeq [base, body], rest'')
        -- A mentioned big operator with no body (\\bigcup).
        Nothing -> return (base, rest')
  | dslTokText tok `elem` dslAccents = do
      (unit, rest') <- parseDslUnit ctx rest
      return (DslSeq [DslAtom tok, unit], rest')
  | otherwise = parseDslUnit ctx toks
parseDslHead _ [] = Nothing

parseDslBinder :: DslCtx -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslBinder ctx (kw : rest0) =
  trySpec (parseDslBinderSpec ctx [] rest1)
    <|> trySpec (parseDslBinderSpecMinimal ctx rest1)
 where
  rest1 = case rest0 of
    (t : r) | dslTokText t == "!" -> r
    _ -> rest0
  trySpec spec = do
    bodyStart <- spec
    (body, rest') <- parseDslExpr ctx (2 * 10) bodyStart
    let specToks = take (length rest1 - length bodyStart) rest1
    return (DslBinder kw specToks body, rest')
parseDslBinder _ [] = Nothing

-- One variable (with an optional relation), then the separator: the
-- fallback when the greedy multi-variable specification would
-- swallow the body (\\forall n,\\ x\\in F reads x\\in F as the body).
parseDslBinderSpecMinimal :: DslCtx -> [DslTok] -> Maybe [DslTok]
parseDslBinderSpecMinimal ctx toks = do
  (varExpr, rest1) <- parseDslUnit ctx toks
  case varExpr of
    DslAtom _ -> return ()
    DslScript (DslAtom _) _ _ -> return ()
    DslCmd{} -> return ()
    _ -> Nothing
  rest2 <- case rest1 of
    (opTok : r)
      | Just (40, _) <- dslInfix (dslTokText opTok) -> do
          (_, r') <- parseDslSpecRhs ctx r
          return r'
    _ -> return rest1
  case rest2 of
    (sep : r) | dslTokText sep `elem` [",", "."] -> return r
    _ -> Nothing

parseDslBinderSpec :: DslCtx -> [Text] -> [DslTok] -> Maybe [DslTok]
parseDslBinderSpec ctx bound toks = do
  (varExpr, rest1) <- parseDslUnit ctx toks
  let varName = case varExpr of
        DslAtom t -> dslTokText t
        DslScript (DslAtom t) _ _ -> dslTokText t
        _ -> ""
  rest2 <- case rest1 of
    (opTok : r)
      | Just (40, _) <- dslInfix (dslTokText opTok) -> do
          (_, r') <- parseDslSpecRhs ctx r
          return r'
    _ -> return rest1
  case rest2 of
    (commaTok : r)
      | dslTokText commaTok == "," ->
          case r of
            (v : after)
              | isDslVarTok v
              , dslTokText v `notElem` bound
              , startsDslSpec after ->
                  parseDslBinderSpec ctx (varName : bound) r
            _ -> return r
    (dotTok : r)
      | dslTokText dotTok == "." -> return r
    _ -> return rest2
 where
  startsDslSpec [] = False
  startsDslSpec (t : _) =
    dslTokText t `elem` [",", "."] || isJust (dslInfix (dslTokText t))

parseDslSpecRhs :: DslCtx -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslSpecRhs ctx toks = do
  (unit, rest) <- parseDslUnit ctx toks
  go unit rest
 where
  go acc rest@(tok : tailToks)
    | Just (level, assoc) <- dslInfix (dslTokText tok)
    , level >= 50 = do
        (rhs, rest') <- parseDslUnit ctx tailToks
        go (DslInfix tok acc rhs) rest'
    | otherwise = Just (acc, rest)
  go acc [] = Just (acc, [])

parseDslUnit :: DslCtx -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslUnit ctx toks = do
  (base, rest) <- parseDslPrimary ctx toks
  parseDslPostfixes ctx base rest

parseDslPostfixes :: DslCtx -> DslExpr -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslPostfixes ctx base toks@(tok : rest)
  | dslTokText tok == "|" && nextIsSub && not (dslCtxNoRestrict ctx) = do
      (arg, rest') <- parseDslScriptArg ctx (drop 2 toks)
      parseDslPostfixes ctx (DslScript base [tok, toks !! 1] arg) rest'
  | dslTokText tok `elem` ["^", "_"] = do
      (arg, rest') <- parseDslScriptArg ctx rest
      parseDslPostfixes ctx (DslScript base [tok] arg) rest'
  | dslTokText tok `elem` ["'", "!"] =
      parseDslPostfixes ctx (DslScript base [tok] (DslSeq [])) rest
  | otherwise = Just (base, toks)
 where
  nextIsSub = case rest of
    (t : _) -> dslTokText t == "_"
    [] -> False
parseDslPostfixes _ base [] = Just (base, [])

parseDslScriptArg :: DslCtx -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslScriptArg ctx toks@(tok : _)
  | dslTokText tok == "{" = do
      (braced, rest) <- parseDslBraced ctx toks
      return (DslGroup braced, rest)
  | otherwise =
      parseDslPrimary ctx toks
        <|> case toks of
          (t : rest)
            | dslTokText t
                `notElem` [")", "]", "}", "\\}", "\\rangle", ",", ";", "&", "\\\\"] ->
                Just (DslAtom t, rest)
          _ -> Nothing
parseDslScriptArg _ [] = Nothing

-- Braced groups are grammar: their contents must parse as items.
-- There is no raw fallback; a group outside the grammar fails the
-- span (which then passes through untouched, like any span that
-- does not parse).
parseDslBraced :: DslCtx -> [DslTok] -> Maybe (DslBraced, [DslTok])
parseDslBraced ctx toks@(open : rest)
  | dslTokText open == "{" = do
      (items, rest') <- parseDslItems ctx "}" rest
      (close, rest'') <- expectDslTokEof "}" rest'
      return (DslBraced open items close, rest'')
parseDslBraced _ _ = Nothing

expectDslTok :: Text -> [DslTok] -> Maybe (DslTok, [DslTok])
expectDslTok txt (tok : rest)
  | dslTokText tok == txt = Just (tok, rest)
  | dslTokText tok `elem` dslSizeCmds =
      case rest of
        (close : rest')
          | dslTokText close == txt ->
              Just
                ( close
                    { dslTokLead =
                        dslTokRender tok <> dslTokLead close
                    }
                , rest'
                )
        _ -> Nothing
expectDslTok _ _ = Nothing

{- | 'expectDslTok' that also succeeds at the very end of the span:
TeX does not balance delimiters, and a span may end inside one
(the distribution function in borel-reducibility-synthesis ends
inside an unclosed parenthesis); the closer renders as nothing.
-}
expectDslTokEof :: Text -> [DslTok] -> Maybe (DslTok, [DslTok])
expectDslTokEof txt toks =
  expectDslTok txt toks
    <|> case toks of
      [] -> Just (DslTok "" "", [])
      _ -> Nothing

{- | 'expectDslTokEof' that also accepts a \right<delim> as the
closer: TeX pairs \left with \right whatever the delimiter shapes,
so \left( x \right. closes with an invisible right delimiter. The
\right pair becomes the closing token.
-}
expectDslClose :: Text -> [DslTok] -> Maybe (DslTok, [DslTok])
expectDslClose close toks =
  expectDslTokEof close toks
    <|> case toks of
      (rt : delim : r)
        | dslTokText rt == "\\right" ->
            Just (mergeDslOp [rt, delim], r)
      _ -> Nothing

parseDslItems :: DslCtx -> Text -> [DslTok] -> Maybe ([DslItem], [DslTok])
parseDslItems ctx close toks@(tok : _)
  | dslTokText tok == close = Just ([], toks)
parseDslItems ctx close toks = do
  (first, rest) <- parseDslExpr ctx 0 toks
  go [(Nothing, first)] rest
 where
  go acc rest@(sep : tailToks)
    | dslTokText sep `elem` [",", ";", "&", "\\\\"] =
        case tailToks of
          [] -> Just (acc, rest)
          (nextTok : _)
            | dslTokText nextTok == close -> Just (acc, rest)
          _ -> do
            (item, rest') <- parseDslExpr ctx 0 tailToks
            go (acc ++ [(Just sep, item)]) rest'
    | dslTokText sep == "\\middle"
    , (delim : afterDelim) <- tailToks =
        case afterDelim of
          [] -> Just (acc, rest)
          (nextTok : _)
            | dslTokText nextTok == close -> Just (acc, rest)
          _ -> do
            (item, rest') <- parseDslExpr ctx 0 afterDelim
            go (acc ++ [(Just (mergeDslOp [sep, delim]), item)]) rest'
    | otherwise = Just (acc, rest)
  go acc [] = Just (acc, [])

-- A comma list that may feed one relation applying to all its items
-- (x, y \in X): the relation is kept as the last item's separator.
parseDslItemsWithRelation :: DslCtx -> [DslTok] -> Maybe ([DslItem], [DslTok])
parseDslItemsWithRelation ctx toks = do
  (items, rest) <- parseDslItems ctx "" toks
  case rest of
    (opTok : tailToks)
      | Just spec@(40, _) <- dslInfix (dslTokText opTok)
      , length items > 1 -> do
          (rhs, rest') <- parseDslExpr ctx (dslInfixRbp spec) tailToks
          return (items ++ [(Just opTok, rhs)], rest')
    _ -> return (items, rest)

parseDslPrimary :: DslCtx -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslPrimary ctx toks@(tok : rest)
  | txt == "(" = delimited "(" ")"
  | txt == "[" = delimited "[" "]"
  | txt == "\\{" = parseDslSet ctx tok rest
  | txt == "{" = do
      (braced, rest') <- parseDslBraced ctx toks
      return (DslGroup braced, rest')
  | txt == "<" =
      parseDslAngle ctx tok ">" True toks
        <|> Just (DslAtom tok, rest)
  | txt == "\\langle" = parseDslAngle ctx tok "\\rangle" False toks
  | txt == "|" = parseDslBars ctx tok "|" rest
  | txt == "\\|" = parseDslBars ctx tok "\\|" rest
  | txt == "\\left" =
      parseDslLeftRight ctx tok rest <|> sizePrimary
  | txt `elem` dslSizeCmds = sizePrimary
  | txt == "\\begin" = parseDslEnv ctx tok rest
  | txt == "\\end" = Nothing
  | txt `elem` dslOpaqueArgCmds = case takeDslBracedGroup rest of
      Just (group, rest') ->
        let arg = case group of
              (open : interiorAndClose)
                | not (null interiorAndClose) ->
                    DslBraced
                      open
                      [ (Nothing, DslSeq (map DslAtom (dropEnd 1 interiorAndClose)))
                      | not (null (dropEnd 1 interiorAndClose))
                      ]
                      (last interiorAndClose)
              _ -> DslBraced (DslTok "" "") [] (DslTok "" "")
         in Just (DslCmd tok Nothing [arg], rest')
      Nothing -> Just (DslCmd tok Nothing [], rest)
  | txt `elem` [")", "]", "}", "\\}", "\\rangle", ",", ";", "&", "\\\\"] =
      Nothing
  | T.isPrefixOf "\\" txt = parseDslCommand ctx tok rest
  | isDslAtomTok tok = Just (DslAtom tok, rest)
  | txt `elem` [":", ":=", "*", "=", ">"] = Just (DslAtom tok, rest)
  | isJust (dslInfix txt) = Nothing
  | otherwise = Just (DslAtom tok, rest)
 where
  txt = dslTokText tok
  delimited open close = do
    (items, rest') <- parseDslItems ctx close rest
    (closeTok, rest'') <- expectDslClose close rest'
    return (DslDelimited tok items closeTok, rest'')
  sizePrimary = do
    (inner, rest') <- case rest of
      (dot : r) | dslTokText dot == "." -> return (DslAtom dot, r)
      (closer : r)
        | dslTokText closer `elem` [")", "]", "\\}", "\\rangle", ">"] ->
            return (DslAtom closer, r)
      _ -> parseDslPrimary ctx rest
    return (DslSeq [DslAtom tok, inner], rest')
parseDslPrimary _ [] = Nothing

{- | One bare argument in TeX's sense: the next single token. A
numeric token is split after its first digit, the way TeX reads
\frac12; anything else is one primary. The argument is wrapped
in a brace-less group, so it renders back without braces and is
indistinguishable from a braced argument downstream.
-}
parseDslBareArg :: DslCtx -> [DslTok] -> Maybe (DslBraced, [DslTok])
parseDslBareArg ctx toks@(tok : rest)
  | txt /= "" && T.all isDigit txt && T.length txt > 1 = do
      let (firstDigit, remainder) = T.splitAt 1 txt
          argTok = tok{dslTokText = firstDigit}
          restTok = tok{dslTokLead = "", dslTokText = remainder}
      return (wrapBare (DslAtom argTok), restTok : rest)
  | canStartDslPrimary ctx tok = do
      (unit, rest') <- parseDslPrimary ctx toks
      return (wrapBare unit, rest')
  | otherwise = Nothing
 where
  txt = dslTokText tok
  wrapBare unit =
    DslBraced (DslTok "" "") [(Nothing, unit)] (DslTok "" "")
parseDslBareArg _ [] = Nothing

parseDslCommand :: DslCtx -> DslTok -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslCommand ctx tok rest0 = do
  (opt, rest1) <-
    if dslTokText tok == "\\sqrt"
      then case rest0 of
        (open : r)
          | dslTokText open == "[" -> do
              (items, r') <- parseDslItems ctx "]" r
              (close, r'') <- expectDslTokEof "]" r'
              return (Just (DslBraced open items close), r'')
        _ -> return (Nothing, rest0)
      else return (Nothing, rest0)
  (args, rest2) <- case lookup (dslTokText tok) dslBareArgCmds of
    Just total -> do
      (filled, rest') <- goTableArgs total rest1 []
      (extra, rest'') <- goArgs rest'
      return (filled ++ extra, rest'')
    Nothing -> goArgs rest1
  return (DslCmd tok opt args, rest2)
 where
  goArgs rest@(t : _)
    | dslTokText t == "{" = do
        (braced, rest') <- parseDslBraced ctx rest
        (more, rest'') <- goArgs rest'
        return (braced : more, rest'')
  goArgs rest = return ([], rest)
  goTableArgs 0 rest acc = return (reverse acc, rest)
  goTableArgs n rest@(t : _) acc
    | dslTokText t == "{" = do
        (braced, rest') <- parseDslBraced ctx rest
        goTableArgs (n - 1) rest' (braced : acc)
    | otherwise = case parseDslBareArg ctx rest of
        Just (arg, rest') -> goTableArgs (n - 1) rest' (arg : acc)
        Nothing -> return (reverse acc, rest)
  goTableArgs _ [] acc = return (reverse acc, [])

{- | A \begin{name} ... \end{name} environment as a first-class
construct: the header (with the column spec of an array-like
environment, when present) is folded into the opening token and
the footer into the closing token, and the rows between them are
ordinary items, read through the level-0 row separators.
-}
parseDslEnv :: DslCtx -> DslTok -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslEnv ctx beginTok rest = do
  (nameGroup, rest1) <- takeDslBracedGroup rest
  let envName =
        T.concat (map dslTokText (drop 1 (dropEnd 1 nameGroup)))
  (specGroup, rest2) <-
    if envName `elem` ["array", "tabular", "alignat", "subarray"]
      then case takeDslBracedGroup rest1 of
        Just (group, r) -> return (group, r)
        Nothing -> return ([], rest1)
      else return ([], rest1)
  (items, rest3) <- parseDslItems ctx "\\end" rest2
  -- A separator just before the \end is a trailing separator
  -- with an empty last cell, as TeX reads it.
  let (trailing, rest3') =
        span ((`elem` [",", ";", "&", "\\\\"]) . dslTokText) rest3
      items' = items ++ [(Just sep, DslSeq []) | sep <- trailing]
  (endTok, rest4) <- case rest3' of
    (e : r) | dslTokText e == "\\end" -> return (e, r)
    _ -> Nothing
  (endNameGroup, rest5) <- takeDslBracedGroup rest4
  let open = mergeDslOp (beginTok : nameGroup ++ specGroup)
      close = mergeDslOp (endTok : endNameGroup)
  return (DslEnv open items' close, rest5)

{- | A \left<delim> ... \right<delim> pair as a first-class
delimited construct: the opener is the merged token, the closer is
found by 'expectDslClose', and \middle separators inside are item
separators (see 'parseDslItems'). An invisible left delimiter reads
its items up to the \right. A delimiter outside this grammar falls
back to the plain primary parse of the delimiter construct, with
the \left riding as raw text, as before.
-}
parseDslLeftRight :: DslCtx -> DslTok -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslLeftRight ctx leftTok toks@(delim : rest)
  | d == "(" || d == "[" = do
      (items, rest') <- parseDslItems ctx close rest
      (closeTok, rest'') <- expectDslClose close rest'
      return (DslDelimited merged items closeTok, rest'')
  | d == "\\lfloor" || d == "\\lceil" = do
      let closeCmd = if d == "\\lfloor" then "\\rfloor" else "\\rceil"
      (items, rest') <- parseDslItems ctx closeCmd rest
      (closeTok, rest'') <- expectDslClose closeCmd rest'
      return (DslDelimited merged items closeTok, rest'')
  | d == "\\{" = parseDslSet ctx merged rest
  | d == "|" || d == "\\|" = do
      (expr, rest') <-
        parseDslExpr ctx{dslCtxNoBar = True, dslCtxNoRestrict = True} 0 rest
      (closeTok, rest'') <- expectDslClose d rest'
      return (DslBars merged expr closeTok, rest'')
  | d == "\\langle" =
      parseDslAngle ctx merged "\\rangle" False toks
  | d == "<" =
      parseDslAngle ctx merged ">" True toks
  | d == "." = do
      (items, rest') <- parseDslItems ctx "\\right" rest
      (closeTok, rest'') <- case rest' of
        (rt : delim2 : r)
          | dslTokText rt == "\\right" ->
              return (mergeDslOp [rt, delim2], r)
        _ -> Nothing
      return (DslDelimited merged items closeTok, rest'')
  | otherwise = do
      (inner, rest') <- parseDslPrimary ctx toks
      return (DslSeq [DslAtom leftTok, inner], rest')
 where
  d = dslTokText delim
  merged = mergeDslOp [leftTok, delim]
  close = if d == "(" then ")" else "]"
parseDslLeftRight _ _ [] = Nothing

parseDslSet :: DslCtx -> DslTok -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslSet ctx open rest = do
  (first, rest1) <-
    parseDslExpr ctx{dslCtxNoBar = True} (2 * 15 + 1) rest
  case rest1 of
    (sep : r)
      | dslTokText sep `elem` [":", "\\mid", "|"] -> do
          (condItems, rest2) <- parseDslItemsWithRelation ctx r
          (close, rest3) <- expectDslClose "\\}" rest2
          return (DslSet open [(Nothing, first)] (Just (sep, condItems)) close, rest3)
    (sizeTok : sep : r)
      | dslTokText sizeTok `elem` dslSizeCmds
      , dslTokText sep `elem` [":", "\\mid", "|"] -> do
          let sep' = sep{dslTokLead = dslTokRender sizeTok <> dslTokLead sep}
          (condItems, rest2) <- parseDslItemsWithRelation ctx r
          (close, rest3) <- expectDslClose "\\}" rest2
          return (DslSet open [(Nothing, first)] (Just (sep', condItems)) close, rest3)
    _ -> do
      (items, rest2) <- continueItems [(Nothing, first)] rest1
      (close, rest3) <- expectDslClose "\\}" rest2
      return (DslSet open items Nothing close, rest3)
 where
  continueItems acc rest'@(sep : tailToks)
    | dslTokText sep `elem` [",", ";"] = do
        (item, rest'') <- parseDslExpr ctx 0 tailToks
        continueItems (acc ++ [(Just sep, item)]) rest''
    | otherwise = Just (acc, rest')
  continueItems acc [] = Just (acc, [])

parseDslAngle ::
  DslCtx -> DslTok -> Text -> Bool -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslAngle ctx open close raw toks = do
  _ <- scanDslAngle toks
  (items, rest') <- parseDslItems ctx{dslCtxAngle = True} close (drop 1 toks)
  (cond, rest'') <- case rest' of
    (sep : r)
      | dslTokText sep `elem` [":", "|", "\\mid"] -> do
          (condItems, r') <- parseDslItemsWithRelation ctx r
          return (Just (sep, condItems), r')
    _ -> return (Nothing, rest')
  (closeTok, rest''') <- expectDslClose close rest''
  return (DslAngle open items cond closeTok raw, rest''')

parseDslBars :: DslCtx -> DslTok -> Text -> [DslTok] -> Maybe (DslExpr, [DslTok])
parseDslBars ctx open close rest = do
  (expr, rest') <-
    parseDslExpr ctx{dslCtxNoBar = True, dslCtxNoRestrict = True} 0 rest
  (closeTok, rest'') <- expectDslClose close rest'
  return (DslBars open expr closeTok, rest'')

-- Parse a whole math span: a comma list, optionally feeding one
-- relation, with trailing sentence punctuation kept as atoms.
parseDslSpan :: Text -> Maybe DslExpr
parseDslSpan content = fullParse <|> leadingOp <|> prefixOnly
 where
  toks = lexDsl content
  fullParse = do
    (items, rest) <- parseDslItemsWithRelation dslCtx0 toks
    let (tailToks, rest') =
          span ((`elem` [",", ".", ";"]) . dslTokText) rest
    guard (all (T.null . dslTokText) rest')
    return (DslSeq (map snd items ++ map DslAtom tailToks))
  -- A relation tail used as a prose fragment (class <\\alpha, the
  -- symbol <_W): an operator followed by one expression.
  leadingOp = case toks of
    (opTok : rest)
      | isJust (dslInfix (dslTokText opTok)) -> do
          (rhs, rest') <- parseDslExpr dslCtx0 0 rest
          let (tailToks, rest'') =
                span ((`elem` [",", ".", ";"]) . dslTokText) rest'
          guard (all (T.null . dslTokText) rest'')
          return (DslSeq (DslAtom opTok : rhs : map DslAtom tailToks))
    _ -> Nothing
  -- A mention of prefix operators with no operand (\\neg\\neg), or
  -- with a single unit as the operand.
  prefixOnly =
    let (ops, rest) = span (isDslPrefixTok . dslTokText) toks
     in if null ops
          then Nothing
          else case rest of
            [] -> Just (DslSeq (map DslAtom toks))
            _ -> do
              (unit, rest') <- parseDslUnit dslCtx0 rest
              guard (all (T.null . dslTokText) rest')
              return (DslSeq (map DslAtom ops ++ [unit]))

isDslPrefixTok :: Text -> Bool
isDslPrefixTok txt = isJust (lookup txt dslPrefixTable) || txt `elem` ["-", "+"]

-- Sort inference over DslExpr, mirroring inferExprSort: a signed
-- application whose argument sorts fit contributes its result sort;
-- a declared atom contributes its declared sort (read as a sort when
-- it is one); a numeral is a natural.
inferDslSort :: SignatureSorts -> DeclState -> DslExpr -> Maybe Sort
inferDslSort sigs st expr = case expr of
  DslSeq [single] -> inferDslSort sigs st single
  DslSeq _ -> Nothing
  DslApp fun arg -> do
    (domain, codomain) <- inferDslSort sigs st fun >>= callableSort
    subst <- checkInferredArgs [domain] [inferDslSort sigs st arg]
    return (applySortSubst subst codomain)
  DslEnv{} -> Nothing
  DslAtom tok
    | let txt = dslTokText tok
    , not (T.null txt)
    , T.all isDigit txt ->
        Just (SortAtom "Nat")
    | otherwise -> inferDeclType st (renderDsl expr) >>= resolveDeclaredSort st
  DslGroup braced -> dslBracedSingle braced >>= inferDslSort sigs st
  DslDelimited _ [(_, single)] _ -> inferDslSort sigs st single
  DslDelimited{} -> Nothing
  DslScript base _ _ ->
    explicitExprSort st (parseMathExpr (renderDsl expr)) <|> inferDslSort sigs st base
  DslPrefix op inner
    | dslTokText op == "-" -> inferDslSort sigs st inner
    | otherwise -> Nothing
  DslInfix op _ rhs
    | dslTokText op == ":=" -> inferDslSort sigs st rhs
    | otherwise -> Nothing
  DslCmd tok _ args
    | Just sig <- Map.lookup (dslCmdName tok) sigs
    , (argSorts, resultSort) <-
        freshSignature
          (dslCmdName tok)
          (sortDigest (renderDsl expr))
          sig
    , length args == length argSorts
    , Just subst <-
        checkInferredArgs
          argSorts
          (map (dslBracedSingle >=> inferDslSort sigs st) args) ->
        Just (applySortSubst subst resultSort)
    | otherwise -> inferDeclType st (renderDsl expr) >>= resolveDeclaredSort st
  DslAngle _ items cond _ _
    | isNothing cond ->
        case dslOutcomeWinner (dslAngleOutcome sigs st Nothing items) of
          Just (_, resultSort, _) -> Just resultSort
          Nothing -> Nothing
    | otherwise -> Nothing
  DslResolved name args
    | Just sig <- Map.lookup name sigs
    , (argSorts, resultSort) <-
        freshSignature
          name
          (sortDigest (renderDsl expr))
          sig
    , length args == length argSorts
    , Just subst <-
        checkInferredArgs
          argSorts
          (map (dslItemListSort sigs st) args) ->
        Just (applySortSubst subst resultSort)
    | otherwise -> Nothing
  DslBinder{} -> Nothing
  DslSet{} -> Nothing
  DslBars{} -> Nothing

dslCmdName :: DslTok -> Text
dslCmdName tok = fromMaybe (dslTokText tok) (T.stripPrefix "\\" (dslTokText tok))

dslItemListSort :: SignatureSorts -> DeclState -> [DslItem] -> Maybe Sort
dslItemListSort sigs st [(_, single)] = inferDslSort sigs st single
dslItemListSort _ _ _ = Nothing

dslBracedSingle :: DslBraced -> Maybe DslExpr
dslBracedSingle (DslBraced _ [(_, single)] _) = Just single
dslBracedSingle _ = Nothing

-- Resolution of raw angle brackets.

data DslVerdict
  = DslVerdictResolved Text
  | DslVerdictAmbiguous [Text]
  | DslVerdictNoCandidate
  | DslVerdictUnknownArgs
  deriving (Eq, Show)

data DslAngleFinding = DslAngleFinding
  { dslFindingAngle :: Text
  , dslFindingVerdict :: DslVerdict
  }
  deriving (Eq, Show)

-- The angle-printed notations a raw bracket can mean, by item count.
-- Their sort behaviour comes from the registry signatures; \Tuple is
-- variadic and handled directly.
dslCandidateNames :: Int -> [Text]
dslCandidateNames 1 = ["SingletonSeq"]
dslCandidateNames 2 =
  ["Pair", "NatPair", "NamePair", "PCAPair", "LambdaPair", "BinaryPair"]
dslCandidateNames n
  | n >= 3 = ["Tuple"]
  | otherwise = []

sortHasConcrete :: Sort -> Bool
sortHasConcrete (SortAtom _) = True
sortHasConcrete (SortVar _) = False
sortHasConcrete (SortApp _ args) = any sortHasConcrete args

-- Try one candidate against known item sorts and an expected sort.
-- Returns (name, specificity rank, result sort).  A candidate counts
-- only when every item sort is known and fits; the rank counts the
-- argument positions whose signature mentions a concrete sort, so a
-- specific notation (NamePair) beats the generic Pair, while
-- same-rank collisions (NatPair against LambdaPair) stay ambiguous.
dslTryCandidate ::
  SignatureSorts -> Maybe Sort -> [Maybe Sort] -> Text -> Maybe (Text, Int, Sort)
dslTryCandidate sigs expected sorts name
  | name == "Tuple" = do
      itemSorts <- sequence sorts
      let result = SortApp "Tuple" itemSorts
      case expected of
        Just e -> do
          _ <- checkSort Map.empty e result
          return (name, 0, result)
        Nothing -> return (name, 0, result)
  | otherwise = do
      sig <- Map.lookup name sigs
      let (argSorts, resultSort0) =
            freshSignature
              name
              (sortDigest (T.concat (map (maybe "" renderSort) sorts)))
              sig
      guard (length argSorts == length sorts)
      guard (all isJust sorts)
      subst <- checkInferredArgs argSorts sorts
      let result = applySortSubst subst resultSort0
          rank = length (filter sortHasConcrete argSorts)
      case expected of
        Just e -> do
          _ <- checkSort Map.empty e result
          return (name, rank, result)
        Nothing -> return (name, rank, result)

data DslAngleOutcome = DslAngleOutcome
  { dslOutcomeWinner :: Maybe (Text, Sort, [DslItem])
  , dslOutcomeViable :: [Text]
  , dslOutcomeSortsKnown :: Bool
  , dslOutcomeRefined :: Bool
  }

dslAngleOutcome ::
  SignatureSorts -> DeclState -> Maybe Sort -> [DslItem] -> DslAngleOutcome
dslAngleOutcome sigs st expected items =
  let itemExprs = dslItemsExprs items
      sorts1 = map (inferDslSort sigs st) itemExprs
      names = dslCandidateNames (length items)
      pass1 =
        [ (name, rank, result, items)
        | name <- names
        , Just (name', rank, result) <- [dslTryCandidate sigs expected sorts1 name]
        , name' == name
        ]
      pass2 =
        [ (name, rank, result, items')
        | name <- names
        , Just (argSorts, _) <- [Map.lookup name sigs]
        , length argSorts == length items
        , let items' =
                zipWith
                  ( \(sep, expr) argSort ->
                      ( sep
                      , fst
                          ( resolveDslExpr
                              sigs
                              st
                              (Just argSort)
                              expr
                          )
                      )
                  )
                  items
                  argSorts
        , Just (name', rank, result) <-
            [ dslTryCandidate
                sigs
                expected
                (map (inferDslSort sigs st . snd) items')
                name
            ]
        , name' == name
        ]
      viableByName =
        Map.fromList
          ( [(name, (rank, result, its)) | (name, rank, result, its) <- pass1]
              ++ [(name, (rank, result, its)) | (name, rank, result, its) <- pass2]
          )
      viable =
        [ (name, rank, result, its)
        | (name, (rank, result, its)) <- Map.toList viableByName
        ]
      maxRank = maximum (0 : [rank | (_, rank, _, _) <- viable])
      winners = [v | v@(_, rank, _, _) <- viable, rank == maxRank]
      (winner, refined) = case winners of
        [(name, _, result, its)] ->
          ( Just (name, result, its)
          , any (\(n, _, _, _) -> n == name) pass2
              && not (any (\(n, _, _, _) -> n == name) pass1)
          )
        _ -> (Nothing, False)
   in DslAngleOutcome
        { dslOutcomeWinner = winner
        , dslOutcomeViable = sortOn id [name | (name, _, _, _) <- winners]
        , dslOutcomeSortsKnown = all isJust sorts1
        , dslOutcomeRefined = refined
        }

-- Resolve every raw angle bracket in an expression, propagating the
-- expected sort through the contexts that determine one: signatured
-- arguments, membership (through Set), definitions and relations
-- (through the other side), and transparent groupings.
resolveDslExpr ::
  SignatureSorts -> DeclState -> Maybe Sort -> DslExpr -> (DslExpr, [DslAngleFinding])
resolveDslExpr sigs st expected expr = case expr of
  DslAngle open items cond close raw
    | isNothing cond ->
        resolveDslAngle sigs st expected open items close
    | otherwise ->
        let (items', findings) = resolveDslItems sigs st Nothing items
            (cond', condFindings) = case cond of
              Just (sep, condItems) ->
                let (condItems', fs) = resolveDslItems sigs st Nothing condItems
                 in (Just (sep, condItems'), fs)
              Nothing -> (Nothing, [])
         in (DslAngle open items' cond' close raw, findings ++ condFindings)
  DslAtom _ -> (expr, [])
  DslEnv open items close ->
    let (items', findings) = resolveDslItems sigs st Nothing items
     in (DslEnv open items' close, findings)
  DslSeq exprs ->
    let (exprs', findings) = unzip (map (resolveDslExpr sigs st Nothing) exprs)
     in (DslSeq exprs', concat findings)
  DslApp fun arg ->
    let (fun', funFindings) = resolveDslExpr sigs st Nothing fun
        argExpected = fst <$> (inferDslSort sigs st fun' >>= callableSort)
        (arg', argFindings) = resolveDslExpr sigs st argExpected arg
     in (DslApp fun' arg', funFindings ++ argFindings)
  DslCmd tok opt args ->
    let (opt', optFindings) = case opt of
          Nothing -> (Nothing, [])
          Just braced ->
            let (braced', fs) = resolveDslBraced sigs st Nothing braced
             in (Just braced', fs)
        sig = Map.lookup (dslCmdName tok) sigs
        resolveArg idx braced =
          let argExpected = case sig of
                Just (argSorts, _)
                  | idx < length argSorts -> Just (argSorts !! idx)
                _ -> Nothing
           in resolveDslBraced sigs st argExpected braced
        (args', argFindings) = unzip (zipWith resolveArg [0 ..] args)
     in (DslCmd tok opt' args', optFindings ++ concat argFindings)
  DslGroup braced ->
    let (braced', findings) = resolveDslBraced sigs st expected braced
     in (DslGroup braced', findings)
  DslInfix op lhs rhs
    | dslTokText op `elem` ["\\in", "\\notin"] ->
        let (rhs', rhsFindings) = resolveDslExpr sigs st Nothing rhs
            lhsExpected = case inferDslSort sigs st rhs' of
              Just (SortApp "Set" [tau]) -> Just tau
              _ -> Nothing
            (lhs', lhsFindings) = resolveDslExpr sigs st lhsExpected lhs
         in (DslInfix op lhs' rhs', rhsFindings ++ lhsFindings)
    | isDslRelationTok op || dslTokText op == ":=" ->
        let (lhs', lhsFindings) = resolveDslExpr sigs st Nothing lhs
            (rhs', rhsFindings) =
              resolveDslExpr sigs st (inferDslSort sigs st lhs') rhs
            (lhs'', lhsFindings') =
              case (lhs, inferDslSort sigs st rhs') of
                (DslAngle _ _ Nothing _ _, Just siblingSort) ->
                  resolveDslExpr sigs st (Just siblingSort) lhs
                _ -> (lhs', lhsFindings)
         in (DslInfix op lhs'' rhs', lhsFindings' ++ rhsFindings)
    | otherwise ->
        let (lhs', lhsFindings) = resolveDslExpr sigs st Nothing lhs
            (rhs', rhsFindings) = resolveDslExpr sigs st Nothing rhs
         in (DslInfix op lhs' rhs', lhsFindings ++ rhsFindings)
  DslPrefix op inner ->
    let (inner', findings) = resolveDslExpr sigs st Nothing inner
     in (DslPrefix op inner', findings)
  DslScript base markers arg ->
    let (base', baseFindings) = resolveDslExpr sigs st Nothing base
        (arg', argFindings) = resolveDslExpr sigs st Nothing arg
     in (DslScript base' markers arg', baseFindings ++ argFindings)
  DslBinder kw spec body ->
    let (body', findings) = resolveDslExpr sigs st Nothing body
     in (DslBinder kw spec body', findings)
  DslDelimited open items close ->
    let (items', findings) = case items of
          [item] -> let (item', fs) = resolveDslItems sigs st expected [item] in (item', fs)
          _ -> resolveDslItems sigs st Nothing items
     in (DslDelimited open items' close, findings)
  DslSet open items cond close ->
    let (items', itemFindings) = resolveDslItems sigs st Nothing items
        (cond', condFindings) = case cond of
          Nothing -> (Nothing, [])
          Just (sep, condItems) ->
            let (condItems', fs) = resolveDslItems sigs st Nothing condItems
             in (Just (sep, condItems'), fs)
     in (DslSet open items' cond' close, itemFindings ++ condFindings)
  DslBars open inner close ->
    let (inner', findings) = resolveDslExpr sigs st expected inner
     in (DslBars open inner' close, findings)
  DslResolved _ _ -> (expr, [])

isDslRelationTok :: DslTok -> Bool
isDslRelationTok tok = case dslInfix (dslTokText tok) of
  Just (40, _) -> True
  _ -> False

resolveDslItems ::
  SignatureSorts -> DeclState -> Maybe Sort -> [DslItem] -> ([DslItem], [DslAngleFinding])
resolveDslItems sigs st expected items =
  let itemExpected = case items of
        [_] -> expected
        _ -> Nothing
      resolved =
        [ (sep, resolveDslExpr sigs st itemExpected expr)
        | (sep, expr) <- items
        ]
   in ( [(sep, expr') | (sep, (expr', _)) <- resolved]
      , concat [fs | (_, (_, fs)) <- resolved]
      )

resolveDslItemsEach ::
  SignatureSorts ->
  DeclState ->
  [Maybe Sort] ->
  [DslItem] ->
  ([DslItem], [DslAngleFinding])
resolveDslItemsEach sigs st expecteds items =
  let resolved =
        zipWith
          (\(sep, expr) itemExpected -> (sep, resolveDslExpr sigs st itemExpected expr))
          items
          (expecteds ++ repeat Nothing)
   in ( [(sep, expr') | (sep, (expr', _)) <- resolved]
      , concat [fs | (_, (_, fs)) <- resolved]
      )

resolveDslBraced ::
  SignatureSorts -> DeclState -> Maybe Sort -> DslBraced -> (DslBraced, [DslAngleFinding])
resolveDslBraced sigs st expected (DslBraced open items close) =
  let (items', findings) = resolveDslItems sigs st expected items
   in (DslBraced open items' close, findings)

-- Drop the leading whitespace of an expression's leftmost token, so
-- a resolved bracket renders as a compact macro call.
dslStripLead :: DslExpr -> DslExpr
dslStripLead expr = case expr of
  DslAtom tok -> DslAtom tok{dslTokLead = ""}
  DslEnv open items close -> DslEnv open{dslTokLead = ""} items close
  DslSeq (first : rest) -> DslSeq (dslStripLead first : rest)
  DslSeq [] -> expr
  DslApp fun arg -> DslApp (dslStripLead fun) arg
  DslCmd tok opt args -> DslCmd tok{dslTokLead = ""} opt args
  DslGroup (DslBraced open items close) ->
    DslGroup (DslBraced open{dslTokLead = ""} items close)
  DslInfix op lhs rhs -> DslInfix op (dslStripLead lhs) rhs
  DslPrefix tok inner -> DslPrefix tok{dslTokLead = ""} inner
  DslScript base markers arg -> DslScript (dslStripLead base) markers arg
  DslBinder kw spec body -> DslBinder kw{dslTokLead = ""} spec body
  DslDelimited open items close ->
    DslDelimited open{dslTokLead = ""} items close
  DslSet open items cond close ->
    DslSet open{dslTokLead = ""} items cond close
  DslAngle open items cond close raw ->
    DslAngle open{dslTokLead = ""} items cond close raw
  DslBars open inner close -> DslBars open{dslTokLead = ""} inner close
  DslResolved _ _ -> expr

resolveDslAngle ::
  SignatureSorts ->
  DeclState ->
  Maybe Sort ->
  DslTok ->
  [DslItem] ->
  DslTok ->
  (DslExpr, [DslAngleFinding])
resolveDslAngle sigs st expected open items close =
  let (items1, itemFindings) = resolveDslItems sigs st Nothing items
      outcome = dslAngleOutcome sigs st expected items1
      angleText = renderDsl (DslAngle open items Nothing close True)
   in case dslOutcomeWinner outcome of
        Just (name, _, _) ->
          let winnerExpecteds = case Map.lookup name sigs of
                Just (argSorts, _)
                  | length argSorts == length items ->
                      map Just argSorts
                _ -> replicate (length items) Nothing
              (winnerItems, winnerFindings) =
                resolveDslItemsEach sigs st winnerExpecteds items
              args = case name of
                "Tuple" -> [stripFirstLead winnerItems]
                _ ->
                  [ [(Nothing, dslStripLead expr)]
                  | (_, expr) <- winnerItems
                  ]
              stripFirstLead [] = []
              stripFirstLead ((sep, expr) : rest) =
                (sep, dslStripLead expr) : rest
           in ( DslResolved name args
              , winnerFindings
                  ++ [DslAngleFinding angleText (DslVerdictResolved name)]
              )
        Nothing ->
          let verdict = case dslOutcomeViable outcome of
                [] ->
                  if dslOutcomeSortsKnown outcome
                    then DslVerdictNoCandidate
                    else DslVerdictUnknownArgs
                names -> DslVerdictAmbiguous names
           in ( DslAngle open items1 Nothing close True
              , itemFindings ++ [DslAngleFinding angleText verdict]
              )

-- The --dsl-audit lint mode: parse every math span in the book with
-- the DSL grammar and report the resolution verdicts, without
-- changing any output.
data DslAuditResult = DslAuditResult
  { dslAuditSpans :: Int
  , dslAuditParsed :: Int
  , dslAuditAngles :: Int
  , dslAuditResolved :: Int
  , dslAuditAmbiguous :: Int
  , dslAuditNoCandidate :: Int
  , dslAuditUnknown :: Int
  , dslAuditFindings :: [Text]
  }

emptyDslAudit :: DslAuditResult
emptyDslAudit = DslAuditResult 0 0 0 0 0 0 0 []

mergeDslAudit :: DslAuditResult -> DslAuditResult -> DslAuditResult
mergeDslAudit a b =
  DslAuditResult
    (dslAuditSpans a + dslAuditSpans b)
    (dslAuditParsed a + dslAuditParsed b)
    (dslAuditAngles a + dslAuditAngles b)
    (dslAuditResolved a + dslAuditResolved b)
    (dslAuditAmbiguous a + dslAuditAmbiguous b)
    (dslAuditNoCandidate a + dslAuditNoCandidate b)
    (dslAuditUnknown a + dslAuditUnknown b)
    (dslAuditFindings a ++ dslAuditFindings b)

data DslWalkRefs = DslWalkRefs
  { dwDecl :: IORef DeclState
  , dwPending :: IORef [DeclCommand]
  , dwResult :: IORef DslAuditResult
  , dwInFence :: IORef Bool
  , dwInComment :: IORef Bool
  , dwMathMeta :: IORef (Maybe [Text])
  , dwDisplay :: IORef (Maybe (Int, Text))
  , dwInline :: IORef (Maybe (Int, Text))
  }

runDslAudit :: FilePath -> [FilePath] -> IO ()
runDslAudit macrosPath paths = do
  notationData <- readNotationData macrosPath
  let sigs = signatureSorts notationData
  results <- mapM (dslAuditFile sigs) paths
  let total = foldr mergeDslAudit emptyDslAudit results
  hPutStrLn stderr "[lint] dsl audit (validation only):"
  forM_ (dslAuditFindings total) $ \finding ->
    TIO.hPutStrLn stderr ("  " <> finding)
  hPutStrLn
    stderr
    ( "  "
        <> show (dslAuditSpans total)
        <> " spans, "
        <> show (dslAuditParsed total)
        <> " parsed, "
        <> show (dslAuditAngles total)
        <> " angle brackets: "
        <> show (dslAuditResolved total)
        <> " resolved, "
        <> show (dslAuditAmbiguous total)
        <> " ambiguous, "
        <> show (dslAuditNoCandidate total)
        <> " no candidate, "
        <> show (dslAuditUnknown total)
        <> " unknown arguments"
    )

dslAuditFile :: SignatureSorts -> FilePath -> IO DslAuditResult
dslAuditFile sigs path = do
  contents <- TIO.readFile path
  refs <-
    DslWalkRefs
      <$> newIORef initialDeclState
      <*> newIORef []
      <*> newIORef emptyDslAudit
      <*> newIORef False
      <*> newIORef False
      <*> newIORef Nothing
      <*> newIORef Nothing
      <*> newIORef Nothing
  forM_ (zip [1 ..] (T.lines contents)) $
    uncurry (dslAuditLine sigs path refs)
  readIORef (dwResult refs)

dslAuditLine :: SignatureSorts -> FilePath -> DslWalkRefs -> Int -> Text -> IO ()
dslAuditLine sigs path refs lineNo rawLine = do
  mathMeta <- readIORef (dwMathMeta refs)
  case mathMeta of
    Just acc
      | "\\end{mathmeta}" `T.isInfixOf` rawLine -> do
          applyDslMathMeta refs (T.unlines (reverse (rawLine : acc)))
          writeIORef (dwMathMeta refs) Nothing
      | otherwise ->
          writeIORef (dwMathMeta refs) (Just (rawLine : acc))
    Nothing
      | "\\begin{mathmeta}" `T.isInfixOf` rawLine ->
          if "\\end{mathmeta}" `T.isInfixOf` rawLine
            then applyDslMathMeta refs rawLine
            else writeIORef (dwMathMeta refs) (Just [rawLine])
      | isFenceLine rawLine -> do
          inFence <- readIORef (dwInFence refs)
          writeIORef (dwInFence refs) (not inFence)
      | otherwise -> do
          inFence <- readIORef (dwInFence refs)
          display <- readIORef (dwDisplay refs)
          unless inFence $ do
            when (isNothing display && isHeadingLine rawLine) $ do
              flushDslPending refs
              enterSection (dwDecl refs) (T.length (T.takeWhile (== '#') rawLine))
            inComment <- readIORef (dwInComment refs)
            let (visible, inComment') = stripHtmlCommentSpan inComment rawLine
            writeIORef (dwInComment refs) inComment'
            dslAuditText sigs path refs lineNo (stripLatexComments visible)

applyDslMathMeta :: DslWalkRefs -> Text -> IO ()
applyDslMathMeta refs blockText =
  case parseMathMetaBlock blockText of
    Just directives -> forM_ directives applyDirective
    Nothing -> return ()
 where
  applyDirective (MathMetaDecl cmd) = applyDeclCommand (dwDecl refs) cmd
  applyDirective (MathMetaWith cmds) = modifyIORef (dwPending refs) (++ cmds)
  applyDirective _ = return ()

flushDslPending :: DslWalkRefs -> IO ()
flushDslPending refs = do
  cmds <- readIORef (dwPending refs)
  writeIORef (dwPending refs) []
  mapM_ (applyDeclCommand (dwDecl refs)) cmds

dslAuditText :: SignatureSorts -> FilePath -> DslWalkRefs -> Int -> Text -> IO ()
dslAuditText sigs path refs lineNo txt = do
  display <- readIORef (dwDisplay refs)
  case display of
    Just (startLine, acc) ->
      case T.breakOn "$$" txt of
        (before, rest)
          | T.null rest ->
              writeIORef (dwDisplay refs) (Just (startLine, acc <> "\n" <> txt))
          | otherwise -> do
              writeIORef (dwDisplay refs) Nothing
              dslAuditSpan sigs path refs startLine (acc <> "\n" <> before)
              dslAuditText sigs path refs lineNo (T.drop 2 rest)
    Nothing ->
      case T.breakOn "$$" txt of
        (before, rest)
          | T.null rest -> dslAuditInline sigs path refs lineNo txt
          | otherwise -> do
              dslAuditInline sigs path refs lineNo before
              let inner = T.drop 2 rest
              case T.breakOn "$$" inner of
                (spanText, rest')
                  | T.null rest' ->
                      writeIORef (dwDisplay refs) (Just (lineNo, inner))
                  | otherwise -> do
                      dslAuditSpan sigs path refs lineNo spanText
                      dslAuditText sigs path refs lineNo (T.drop 2 rest')

-- Inline spans may wrap across source lines; a pending span is
-- carried in dwInline until its closing $ arrives.
dslAuditInline :: SignatureSorts -> FilePath -> DslWalkRefs -> Int -> Text -> IO ()
dslAuditInline sigs path refs lineNo txt = do
  pending <- readIORef (dwInline refs)
  case pending of
    Just (startLine, acc) ->
      case T.breakOn "$" txt of
        (before, rest)
          | T.null rest ->
              writeIORef (dwInline refs) (Just (startLine, acc <> "\n" <> txt))
          | otherwise -> do
              writeIORef (dwInline refs) Nothing
              dslAuditSpan sigs path refs startLine (acc <> "\n" <> before)
              dslAuditInline sigs path refs lineNo (T.drop 1 rest)
    Nothing -> go txt
 where
  go t = case T.breakOn "$" t of
    (_, rest)
      | T.null rest -> return ()
      | otherwise -> do
          let inner = T.drop 1 rest
          case T.breakOn "$" inner of
            (spanText, rest')
              | T.null rest' ->
                  writeIORef (dwInline refs) (Just (lineNo, inner))
              | otherwise -> do
                  dslAuditSpan sigs path refs lineNo spanText
                  go (T.drop 1 rest')

dslAuditSpan :: SignatureSorts -> FilePath -> DslWalkRefs -> Int -> Text -> IO ()
dslAuditSpan sigs path refs lineNo spanText = do
  flushDslPending refs
  st <- readIORef (dwDecl refs)
  let result = case parseDslSpan spanText of
        Nothing ->
          emptyDslAudit
            { dslAuditSpans = 1
            , dslAuditFindings =
                [ T.pack path
                    <> ":"
                    <> T.pack (show lineNo)
                    <> ": does not parse: $"
                    <> T.map (\c -> if c == '\n' then ' ' else c) spanText
                    <> "$"
                ]
            }
        Just expr ->
          let (_, findings) = resolveDslExpr sigs st Nothing expr
              base =
                emptyDslAudit
                  { dslAuditSpans = 1
                  , dslAuditParsed = 1
                  , dslAuditAngles = length findings
                  }
              step acc finding =
                let verdictText = case dslFindingVerdict finding of
                      DslVerdictResolved name ->
                        "would resolve "
                          <> dslFindingAngle finding
                          <> " to \\"
                          <> name
                      DslVerdictAmbiguous names ->
                        "ambiguous "
                          <> dslFindingAngle finding
                          <> ": could be "
                          <> T.intercalate ", " (map ("\\" <>) names)
                      DslVerdictNoCandidate ->
                        "no notation fits " <> dslFindingAngle finding
                      DslVerdictUnknownArgs -> ""
                    line =
                      T.pack path
                        <> ":"
                        <> T.pack (show lineNo)
                        <> ": "
                        <> verdictText
                        <> "  (in $"
                        <> truncateSpan spanText
                        <> "$)"
                 in case dslFindingVerdict finding of
                      DslVerdictResolved _ ->
                        acc
                          { dslAuditResolved = dslAuditResolved acc + 1
                          , dslAuditFindings = dslAuditFindings acc ++ [line]
                          }
                      DslVerdictAmbiguous _ ->
                        acc
                          { dslAuditAmbiguous = dslAuditAmbiguous acc + 1
                          , dslAuditFindings = dslAuditFindings acc ++ [line]
                          }
                      DslVerdictNoCandidate ->
                        acc
                          { dslAuditNoCandidate = dslAuditNoCandidate acc + 1
                          , dslAuditFindings = dslAuditFindings acc ++ [line]
                          }
                      DslVerdictUnknownArgs ->
                        acc{dslAuditUnknown = dslAuditUnknown acc + 1}
           in foldl step base findings
  modifyIORef (dwResult refs) (mergeDslAudit result)
 where
  truncateSpan txt =
    let flat = T.replace "\n" " " txt
     in if T.length flat > 80 then T.take 77 flat <> "..." else flat

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
-- expanded to `§<section number>` (as a Link to the section
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

-- Standalone default. Make supplies a per-book DEPENDENCY_GRAPH_CACHE; direct
-- callers may instead set dependency-layout-cache metadata.
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
          Just _ ->
            return
              [ Link
                  nullAttr
                  [Str "\167", Space, RawInline (Format "latex") ("\\ref*{" <> hid <> "}")]
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
  "\\hyperref[" <> hid <> "]{\167 \\ref*{" <> hid <> "}}"
