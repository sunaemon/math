{-# LANGUAGE OverloadedStrings #-}

module ProofContexts (proofRequest, definitionRequest, quote, contextBridgeRequest, contextReference) where

import ContextTemplates
import Control.Monad (unless, when)
import Data.Aeson (FromJSON (..), Value (..), object, withObject, (.:), (.:?), (.=))
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser)
import Data.Char (isAlphaNum, isDigit, ord)
import Data.List (mapAccumL)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Numeric (showHex)

-- Single-pass substitution: source strings containing marker words are data.
substitute :: [(Text, Text)] -> Text -> Text
substitute entries = go
 where
  replacements = Map.fromList entries
  word c = isAlphaNum c || c == '_'
  go text = case T.uncons text of
    Nothing -> ""
    Just (c, rest)
      | word c ->
          let (token, tailText) = T.span word text
           in Map.findWithDefault token token replacements <> go tailText
      | otherwise -> T.cons c (go rest)

quote :: Bool -> Text -> Text
quote ascii text = "\"" <> T.concatMap escape text <> "\""
 where
  escape '"' = "\\\""
  escape '\\' = "\\\\"
  escape '\b' = "\\b"
  escape '\f' = "\\f"
  escape '\n' = "\\n"
  escape '\r' = "\\r"
  escape '\t' = "\\t"
  escape c
    | ord c < 32 || (ascii && ord c > 126) = unicode (ord c)
    | otherwise = T.singleton c
  unicode n
    | n > 65535 = unicode (55296 + (n - 65536) `div` 1024) <> unicode (56320 + (n - 65536) `mod` 1024)
    | otherwise = let digits = T.pack (showHex n "") in "\\u" <> T.replicate (4 - T.length digits) "0" <> digits

prelude :: Text
prelude =
  substitute
    [ ("FRESH_DEFINITION", substitute [("FRESH", "freshContextName")] freshTemplate)
    , ("UNFOLD_DEFINITION", substitute [("UNFOLD", "unfoldContextStep")] unfoldTemplate)
    ]
    inspectionTemplate

data Step = Body | ValueStep | Function | Argument | Metadata | Projection | Unfold

newtype ProofPath = ProofPath [Step]

parsePath :: Text -> Parser ProofPath
parsePath path = case T.splitOn "." path of
  "root" : steps -> ProofPath <$> mapM step steps
  _ -> fail "Invalid proof-context path"
 where
  step "body" = pure Body
  step "value" = pure ValueStep
  step "fn" = pure Function
  step "arg" = pure Argument
  step "metadata" = pure Metadata
  step "projection" = pure Projection
  step "unfold" = pure Unfold
  step _ = fail "Invalid proof-context path"

stepText :: Step -> Text
stepText Body = "body"
stepText ValueStep = "value"
stepText Function = "fn"
stepText Argument = "arg"
stepText Metadata = "metadata"
stepText Projection = "projection"
stepText Unfold = "unfold"

contextExpression :: Text -> ProofPath -> Text -> Text -> Text -> Parser Text
contextExpression declaration (ProofPath steps) term name helper = do
  unless (not (T.null helper) && T.all (\c -> isAlphaNum c || c == '_') helper) $
    fail "Invalid proof-context helper name"
  pure $
    substitute
      [ ("HELPER", helper)
      , ("FRESH", helper <> "_fresh")
      , ("UNFOLD", helper <> "_unfold")
      , ("FRESH_DEFINITION", substitute [("FRESH", helper <> "_fresh")] freshTemplate)
      , ("UNFOLD_DEFINITION", substitute [("UNFOLD", helper <> "_unfold")] unfoldTemplate)
      , ("ROOT", quote True declaration)
      , ("STEPS", "[" <> T.intercalate ", " (map (quote True . stepText) steps) <> "]")
      , ("TERM", quote False term)
      , ("OUTPUT", quote True name)
      ]
      expressionTemplate

proofRequest :: Text -> Value -> Parser Value
proofRequest action = withObject "proof context request" $ \fields -> do
  source <- case action of
    "proofPrelude" -> pure prelude
    "inspectContexts" -> do
      imports <- fields .: "imports"
      requests <- fields .: "requests" :: Parser [(Text, Text)]
      let grouped = Map.fromListWith Set.union [(decl, Set.singleton wanted) | (decl, wanted) <- requests]
          command (decl, wanted) =
            substitute
              [("ROOT", quote True decl), ("WANTED", T.intercalate ", " (map (quote True) (Set.toAscList wanted)))]
              inspectionCommandTemplate
      pure (imports <> prelude <> T.concat (map command (Map.toAscList grouped)))
    "contextExpression" -> do
      declaration <- fields .: "declaration"
      path <- fields .: "path" >>= parsePath
      term <- fields .: "term"
      name <- fields .: "name"
      helper <- fields .: "helper"
      contextExpression declaration path term name helper
    _ -> fail "Unknown proof-context action"
  pure (object ["source" .= source])

data Binder = Binder {binderName :: Text, binderType :: Text, binderInstance :: Maybe Bool, binderValue :: Maybe Text}

instance FromJSON Binder where
  parseJSON = withObject "binder" $ \fields -> Binder <$> fields .: "name" <*> fields .: "type" <*> fields .:? "instance" <*> fields .:? "value"

-- Match the exported schematic universe names, without changing named universes.
eraseUniverses :: Text -> Text
eraseUniverses text = case T.uncons text of
  Nothing -> ""
  Just (c, rest) -> case prefix text of
    Just suffix ->
      let (digits, tailText) = T.span isDigit suffix
       in if T.null digits then T.cons c (eraseUniverses rest) else "Type" <> eraseUniverses tailText
    Nothing -> T.cons c (eraseUniverses rest)
 where
  prefix input = case T.stripPrefix "Type u_" input of
    Just rest -> Just rest
    Nothing -> T.stripPrefix "Sort u_" input

definitionRequest :: Value -> Parser Value
definitionRequest = withObject "expression definition" $ \fields -> do
  name <- fields .: "name"
  term <- fields .: "term"
  context <- fields .: "binders"
  let names = map binderName context
  unless (Set.size (Set.fromList names) == length names) $
    fail "Shadowed Lean binder names require explicit renaming before re-elaboration."
  proof <- fields .:? "proof"
  source <- case proof of
    Just input ->
      withObject
        "proof reference"
        ( \p -> do
            declaration <- p .: "declaration"
            path <- p .: "path" >>= parsePath
            helper <- p .: "helper"
            contextExpression declaration path term name helper
        )
        input
    Nothing -> do
      unless (all (\b -> not (T.isInfixOf "⋯" (binderType b)) && maybe True (not . T.isInfixOf "⋯") (binderValue b)) context) $
        fail "Elided proof context cannot be replayed from pretty-printed text; use the original Lean expression."
      unless (all (isJust . binderInstance) context) $
        fail "Missing binder instance annotation"
      let render inBody binder =
            let ty = eraseUniverses (binderType binder)
                (opening, closing) = if binderInstance binder == Just True then ("[", "]") else ("(", ")")
                parameter = opening <> "«" <> binderName binder <> "» : " <> ty <> closing
             in case binderValue binder of
                  Just value -> (True, (Nothing, Just ("let «" <> binderName binder <> "» : " <> ty <> " := " <> value <> ";")))
                  Nothing
                    | inBody -> (True, (Nothing, Just ("fun " <> parameter <> " =>")))
                    | otherwise -> (False, (Just parameter, Nothing))
          (_, pieces) = mapAccumL render False context
          params = [p | (Just p, _) <- pieces]
          steps = [s | (_, Just s) <- pieces]
      pure ("noncomputable abbrev " <> name <> " " <> T.intercalate " " params <> " :=\n  " <> T.intercalate "\n  " (steps <> [term]) <> "\n")
  pure (object ["source" .= source])

{- | Share only an actual prefix of the original kernel context, including lets.
Aliases used for printing cannot establish lexical binder identity.
-}
contextBridgeRequest :: Value -> Parser Value
contextBridgeRequest = withObject "context bridge" $ \fields -> do
  names <- fields .: "names" :: Parser [Text]
  chosen <- case names of
    [] -> pure Nothing
    [name] -> pure (Just name)
    first : rest -> do
      unless (all ((== T.takeWhile (/= '@') first) . T.takeWhile (/= '@')) rest) (fail "Different Lean declarations require an explicit context bridge.")
      records <- fields .: "records" :: Parser (Maybe (Map.Map Text Value))
      source <- maybe (fail "Different Lean declarations require an explicit context bridge.") pure records
      contexts <- mapM (\name -> maybe (fail "Missing Lean context") (withObject "context" (.: "binders")) (Map.lookup name source)) names :: Parser [[BridgeBinder]]
      let choices = zip names contexts
          selected = foldl (\best item -> if length (snd item) > length (snd best) then item else best) (first, fromMaybe [] (Map.lookup first (Map.fromList choices))) choices
      mapM_ (check selected) choices
      pure (Just (fst selected))
  pure (object ["context" .= chosen])
 where
  check (selected, target) (name, old) = do
    unless (not ("@" `T.isInfixOf` name) || selected == name || (name <> ".") `T.isPrefixOf` selected) (fail "Sibling proof contexts cannot share binder identities.")
    unless (and (zipWith (==) old target)) (fail "Proof context prefix changed a binder or local definition.")

data BridgeBinder = BridgeBinder Text (Maybe Value) (Maybe Value) (Maybe Value)
  deriving (Eq)

instance FromJSON BridgeBinder where
  parseJSON = withObject "context binder identity" $ \fields -> do
    name <- fields .: "name"
    original <- maybe (pure name) parseJSON (KM.lookup "originalName" fields)
    BridgeBinder original <$> fields .:? "type" <*> fields .:? "instance" <*> fields .:? "value"

contextReference :: Value -> Parser Text
contextReference = withObject "source proof context" $ \fields -> do
  unless (KM.size fields == 2 && KM.member "declaration" fields && KM.member "path" fields) (fail "A local context needs declaration and path")
  raw <- fields .: "path" :: Parser Value
  path <- case raw of
    String value -> pure value
    _ -> do
      segments <- parseJSON raw :: Parser [Text]
      unless (not (null segments) && not (any T.null segments)) (fail "A context path needs nonempty string segments")
      pure (T.intercalate "." segments)
  _ <- parsePath path
  declaration <- fields .: "declaration"
  when (T.null declaration) (fail "A context needs a declaration name")
  pure (declaration <> "@" <> path)
