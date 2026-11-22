{-# LANGUAGE OverloadedStrings #-}

{- | One chapter transaction: shared parser, source normalization, lexical
identities and expression boundaries. Lean execution stays with the caller.
-}
module ChapterPreparation (chapterRequest, preparationRequest, occurrencesRequest, formulasRequest, formulaLocations) where

import Control.Monad (foldM, unless, zipWithM)
import Data.Aeson (Value (..), object, toJSON, withObject, (.!=), (.:), (.:?), (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import MathSyntaxCLI (syntaxRecord)
import ProofContexts (contextReference)
import SemanticTranslation (translationRequest)
import SourceNormalization (normalizationRequest)
import StructuralSyntax (alignedRows, expressionList, extractBindings)
import VariableResolution (resolutionRequest)

field :: Text -> Value -> Value
field key (Object fields) = fromMaybe Null (KM.lookup (K.fromText key) fields)
field _ _ = Null

label :: Text -> Value -> Text
label key value = case field key value of String text -> text; _ -> ""

array :: Value -> [Value]
array (Array values) = toList values
array _ = []

patch :: Value -> [(Text, Value)] -> Value
patch (Object fields) changes = Object (foldr (uncurry (KM.insert . K.fromText)) fields changes)
patch value _ = value

position :: Text -> Value -> Parser Int
position key = withObject "source position" (.: K.fromText key)

-- All offsets count Unicode characters. Delimiter scanning treats comments,
-- fenced code and escaped characters exactly as opaque source spans.
occurrences :: Text -> [Value]
occurrences = scan 0 1 0
 where
  scan :: Int -> Int -> Int -> Text -> [Value]
  scan offset line index source
    | T.null source = []
    | "<!--" `T.isPrefixOf` source = skip "<!--" "-->"
    | "```" `T.isPrefixOf` source = skip "```" "```"
    | "\\" `T.isPrefixOf` source = advance (T.take 2 source) (T.drop 2 source)
    | "$" `T.isPrefixOf` source =
        let delimiter = if "$$" `T.isPrefixOf` source then "$$" else "$"
            width = T.length delimiter
            (book, remaining, closed) = seek delimiter [] (T.drop width source)
            bodyStart = offset + width
            bodyEnd = bodyStart + T.length book
            end = bodyEnd + if closed then width else 0
            consumed = delimiter <> book <> if closed then delimiter else ""
            next = if closed then T.drop width remaining else remaining
            row = object ["index" .= index, "start" .= offset, "end" .= end, "bodyStart" .= bodyStart, "bodyEnd" .= bodyEnd, "line" .= line, "book" .= book, "closed" .= closed]
         in row : scan end (line + T.count "\n" consumed) (index + 1) next
    | otherwise = advance (T.take 1 source) (T.drop 1 source)
   where
    advance consumed = scan (offset + T.length consumed) (line + T.count "\n" consumed) index
    skip opening closing =
      let (body, suffix) = T.breakOn closing (T.drop (T.length opening) source)
          consumed = opening <> body <> if T.null suffix then "" else closing
       in advance consumed (T.drop (T.length closing) suffix)
  seek delimiter previous source
    | T.null source = (T.pack (reverse previous), source, False)
    | delimiter `T.isPrefixOf` source = (T.pack (reverse previous), source, True)
    | delimiter == "$" && "\n\n" `T.isPrefixOf` source = (T.pack (reverse previous), source, False)
    | "\\" `T.isPrefixOf` source = seek delimiter (reverse (T.unpack (T.take 2 source)) <> previous) (T.drop 2 source)
    | Just (char, rest) <- T.uncons source = seek delimiter (char : previous) rest
    | otherwise = (T.pack (reverse previous), source, False)

occurrencesRequest :: Value -> Parser Value
occurrencesRequest = withObject "source math occurrences" $ \fields -> do
  source <- fields .: "text"
  pure (object ["occurrences" .= occurrences source])

-- Closed formula bodies, in the same Unicode offsets used by correspondence.
formulaLocations :: Text -> [(Int, Int)]
formulaLocations = mapMaybe (parseMaybe parse) . occurrences
 where
  parse = withObject "formula location" $ \fields -> do
    closed <- fields .: "closed"
    if closed then (,) <$> fields .: "bodyStart" <*> fields .: "bodyEnd" else fail "Unclosed formula"

formulasRequest :: Value -> Parser Value
formulasRequest = withObject "shared located parser batch" $ \fields -> do
  formulas <- fields .: "formulas"
  pure (object ["formulas" .= map (syntaxRecord True) formulas])

-- The production boundary accepts source text, not a Python-managed meaning AST.
-- Intermediate located syntax and lexical identities stay inside this transaction.
chapterRequest :: Value -> Parser Value
chapterRequest value =
  withObject
    "chapter interpretation"
    ( \fields -> do
        prepared <- preparationRequest value
        interpret <- fields .:? "interpret" .!= True
        if not interpret
          then pure (patch prepared [("translations", toJSON ([] :: [Value]))])
          else do
            records <- fields .: "records" :: Parser Value
            constants <- fields .:? "constants" .!= object []
            conventions <- fields .:? "conventions" .!= object []
            occupied <- fields .:? "occupied" .!= ([] :: [Text])
            includeAST <- fields .:? "includeAST" .!= False
            let environment = object ["records" .= records, "bridgeRecords" .= records, "constants" .= constants, "conventions" .= conventions, "occupied" .= occupied, "standalone" .= True, "resolveContext" .= True, "includeAST" .= includeAST]
            translated <- translationRequest (object ["environment" .= environment, "expressions" .= field "expressions" prepared])
            pure (patch prepared [("translations", field "results" translated)])
    )
    value

preparationRequest :: Value -> Parser Value
preparationRequest = withObject "chapter preparation" $ \fields -> do
  source <- fields .: "text"
  scopes <- fields .: "scopes" :: Parser [Value]
  records <- fields .: "records"
  let rows = occurrences source
  parsed <- fields .:? "parsed" .!= map (syntaxRecord True . label "book") rows
  unless (length rows == length parsed) (fail "Syntax export lost occurrences")
  prepared <- zipWithM (prepare scopes records) rows parsed
  contexts <- mapM (scopeContext records) [scope | scope@(Object values) <- scopes, KM.member "context" values]
  pure (object ["rows" .= map fst prepared, "expressions" .= concatMap snd prepared, "scopeContexts" .= contexts])

prepare :: [Value] -> Value -> Value -> Value -> Parser (Value, [Value])
prepare scopes records row parsed
  | field "closed" row /= Bool True || field "roundtrip" parsed /= Bool True || not (null (array (field "problems" parsed))) =
      pure (patch initial [("syntaxReason", String "Unclosed delimiter or non-lossless shared parse"), ("variables", toJSON ([] :: [Value])), ("bindingEffects", toJSON ([] :: [Value]))], [])
  | otherwise = do
      let tree = field "tree" parsed
      start <- position "start" tree
      end <- position "end" tree
      unless (start == 0 && end == T.length (label "book" row)) (fail "Syntax positions did not consume the source")
      normalized <- foldM normalize tree ["rational", "numeric", "prefix", "restrictions"]
      (variables, effects) <- either fail pure (extractBindings normalized)
      resolved <- resolutionRequest (object ["variables" .= variables, "effects" .= effects, "row" .= row, "scopes" .= scopes, "records" .= records])
      finalVariables <- withObject "resolved variables" (.: "variables") resolved :: Parser [Value]
      finalEffects <- withObject "resolved effects" (.: "effects") resolved :: Parser [Value]
      offset <- position "bodyStart" row
      absolute <- mapM (shiftEffect offset) finalEffects
      literal <- normalize normalized "literal"
      fragments <- either fail pure (expressionList literal)
      aligned <- either fail pure (alignedRows literal)
      let parts = array fragments
          prepared = patch initial [("syntaxStatus", String "parsed"), ("syntax", literal), ("variables", toJSON finalVariables), ("bindingEffects", toJSON absolute), ("syntaxOffsetConvention", String "Syntax nodes are relative to bodyStart; variables and bindingEffects use absolute source offsets.")]
          expressionKind
            | label "kind" literal == "contextual-interpretations" = "contextual-interpretations"
            | aligned /= Null = "aligned-rows"
            | otherwise = "expression-list"
          makeJob fragment node = object ["formulaIndex" .= field "index" row, "fragmentIndex" .= fragment, "tree" .= node, "variables" .= [variable | variable <- finalVariables, inside node variable]]
          inside node variable = case (field "start" node, field "end" node, field "formulaOffset" variable) of (Number begin, Number stop, Number current) -> begin <= current && current < stop; _ -> False
      if null parts
        then pure (prepared, [makeJob Null literal])
        else do
          evidence <- mapM (fragmentEvidence offset) parts
          pure (patch prepared [("expressionKind", String expressionKind), ("typeReason", String "Separate source expressions are checked individually, not collapsed into one Lean term."), ("expressionFragments", toJSON evidence)], zipWith (makeJob . toJSON) [0 :: Int ..] parts)
 where
  initial = patch row [("typeStatus", String "unresolved"), ("typeReason", String "No reviewed interpretation"), ("syntaxStatus", String "unsupported")]
  normalize tree stage = normalizationRequest (object ["stage" .= (stage :: Text), "tree" .= tree, "row" .= row, "scopes" .= scopes]) >>= withObject "normalized source" (.: "tree")

fragmentEvidence :: Int -> Value -> Parser Value
fragmentEvidence offset node = do
  begin <- position "start" node
  end <- position "end" node
  pure (object (["start" .= (offset + begin), "end" .= (offset + end), "typeStatus" .= ("unresolved" :: Text)] <> ["interpretationId" .= field "interpretationId" node | field "interpretationId" node /= Null]))

shiftEffect :: Int -> Value -> Parser Value
shiftEffect offset effect = do
  shifted <- shiftFields offset ["start", "end"] effect
  case field "binder" effect of
    Null -> pure shifted
    binder -> do
      positioned <- shiftFields offset ["declarationOffset", "domainOffset", "carrierOffset", "familyOffset", "bodyStart"] binder
      components <- mapM (shiftFields offset ["start", "end"]) (array (field "components" binder))
      offsets <- mapM (\value -> do original <- withObject "family offset" (.: "offset") (object ["offset" .= value]); pure (offset + original :: Int)) (array (field "familyOffsets" binder))
      let changes = [("components", toJSON components)] <> [("familyOffsets", toJSON offsets) | field "familyOffsets" binder /= Null]
      pure (patch shifted [("binder", patch positioned changes)])

shiftFields :: Int -> [Text] -> Value -> Parser Value
shiftFields offset keys value = do
  changes <- mapM (\key -> do original <- position key value; pure (key, toJSON (offset + original))) [key | key <- keys, field key value /= Null]
  pure (patch value changes)

scopeContext :: Value -> Value -> Parser Value
scopeContext records scope = do
  reference <- contextReference (field "context" scope)
  pure (object ["scope" .= field "scope" scope, "start" .= field "start" scope, "end" .= field "end" scope, "context" .= reference, "status" .= (if field reference records /= Null then "matched" else "unresolved" :: Text)])
