{-# LANGUAGE OverloadedStrings #-}

-- | Lossless mathematical syntax shared by rendering and correspondence.
module MathSyntax where

import Data.Char (isLetter, isSpace)
import Data.Text (Text)
import qualified Data.Text as T

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
parseScriptArg (TokText txt : rest) =
  let (spaces, body) = T.span isSpace txt
   in case T.uncons body of
        Just (character, tailText) ->
          ( MathText (spaces <> T.singleton character)
          , [TokText tailText | not (T.null tailText)] ++ rest
          )
        Nothing -> parseScriptArg rest
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
