{-# LANGUAGE OverloadedStrings #-}

-- | Normalize explicit source-owned scope bindings, without guessing targets.
module SourceScopes (scopeBindingsRequest, referenceRequest, scopeDeclarationsRequest, scopeMetadataRequest, sourceScopesRequest) where

import Control.Monad (foldM, foldM_, unless, when)
import Data.Aeson (FromJSON (parseJSON), Object, Value (..), object, toJSON, withObject, (.!=), (.:), (.:?), (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser)
import Data.Char (isAscii, isDigit, isLetter, isNumber, isSpace)
import Data.Foldable (for_)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import ProofContexts (contextReference)
import SourceJSON (decodeSourceJSON)

referenceRequest :: Value -> Parser Value
referenceRequest = withObject "context reference request" $ \fields -> do
  reference <- fields .: "context" >>= contextReference
  pure (object ["reference" .= reference])

scopeBindingsRequest :: Value -> Parser Value
scopeBindingsRequest = withObject "scope normalization request" $ \fields -> do
  data' <- fields .: "scope" :: Parser Object
  unless
    (KM.member "scope" data' && KM.member "bindings" data' && all (`elem` ["scope", "bindings", "context", "numerals", "predicates", "restrictions", "rationalSingletons", "literalInterpretations"]) (KM.keys data'))
    (fail "A scope has scope, bindings and optional context/numerals/predicates/restrictions")
  scope <- data' .: "scope"
  context <- data' .:? "context" >>= traverse contextReference
  bindings <- data' .: "bindings" :: Parser Object
  (_, normalized) <- foldM (binding scope context) (Map.empty, KM.empty) (KM.toList bindings)
  pure (object ["scope" .= Object (KM.insert "bindings" (Object normalized) data')])
 where
  binding scope context (seen, normalized) (identity, value) =
    withObject
      "source binding"
      ( \fields -> do
          origin <- fields .:? "indexOrigin" :: Parser (Maybe Value)
          offset <- fields .:? "indexOffset" :: Parser (Maybe Value)
          when (maybe False (not . positive) origin) (fail "indexOrigin must be a positive integer")
          when (maybe False (not . positive) offset || isJust offset && isJust origin) (fail "indexOffset must be a positive integer on a scalar binding")
          when (KM.member "projection" fields && (KM.lookup "projection" fields /= Just (String "Subtype.val") || isJust origin || isJust offset)) (fail "Only scalar Subtype.val projection is supported")
          occurrence <- fields .:? "occurrence" .!= "any"
          unless (occurrence `elem` ["any", "subscript-base", "superscript-base", "unsubscripted"]) (fail ("Unknown occurrence selector: " <> T.unpack occurrence))
          symbol <- fields .: "symbol" :: Parser Text
          let previous = Map.findWithDefault [] symbol seen
          when (not (null previous) && (occurrence == "any" || "any" `elem` previous || occurrence `elem` previous)) (fail ("Colliding symbols in " <> T.unpack scope))
          target <- case KM.lookup "target" fields of
            Just (Object structured) -> Just <$> structuredTarget structured
            Just value' -> Just <$> parseText value'
            Nothing -> pure Nothing
          qualified <- traverse (\name -> if "/" `T.isInfixOf` name then pure name else maybe (fail "A short binder target requires a source-owned context") (\prefix -> pure (prefix <> "/" <> name)) context) target
          when (isJust qualified == KM.member "reason" fields) (fail "Binding needs exactly a Lean target or unresolved reason")
          let named = KM.insert "id" (String (scope <> "/" <> K.toText identity)) fields
              output = maybe named (\name -> KM.insert "target" (String name) named) qualified
          pure (Map.insert symbol (occurrence : previous) seen, KM.insert identity (Object output) normalized)
      )
      value
  positive (Number n) = n >= 1 && n == fromInteger (floor n)
  positive _ = False
  parseText (String value) = pure value
  parseText _ = fail "A source target needs a string or structured target"
  structuredTarget fields
    | KM.size fields == 1, Just (String name) <- KM.lookup "constant" fields, not (T.null name) = pure (name <> "/@constant")
    | otherwise = do
        unless (KM.size fields == 3 && all (`KM.member` fields) ["declaration", "path", "binder"]) (fail "A structured target needs declaration, path and binder")
        binder <- fields .: "binder"
        reference <- contextReference (Object (KM.delete "binder" fields))
        pure (reference <> "/" <> binder)

scopeDeclarationsRequest :: Value -> Parser Value
scopeDeclarationsRequest = withObject "scope declaration inventory" $ \fields -> do
  scopes <- fields .: "scopes" :: Parser [Object]
  names <- concat <$> mapM declarations scopes
  pure (object ["declarations" .= Set.toList (Set.fromList names)])
 where
  declarations scope = do
    bindings <- scope .: "bindings" :: Parser Object
    targets <-
      concat
        <$> mapM
          ( withObject
              "source binding"
              ( \binding -> case KM.lookup "target" binding of
                  Nothing -> pure []
                  Just value -> do target <- parseJSON value; pure [T.dropEnd 1 (fst (T.breakOnEnd "/" target))]
              )
          )
          (KM.elems bindings)
    contexts <- case KM.lookup "context" scope of Nothing -> pure []; Just value -> (: []) <$> contextReference value
    interpretations <- scope .:? "literalInterpretations" .!= [] :: Parser [Object]
    literals <-
      concat
        <$> mapM
          ( \interpretation -> do
              constant <- interpretation .: "constant"
              consumer <- interpretation .: "consumer" :: Parser Object
              declaration <- consumer .: "declaration"
              callee <- consumer .: "callee"
              pure [constant, declaration, callee]
          )
          interpretations
    pure (targets <> contexts <> literals)

-- Validate the explicit interpretation metadata and retain premise source spans.
scopeMetadataRequest :: Value -> Parser Value
scopeMetadataRequest = withObject "scope metadata" $ \fields -> do
  scopes <- fields .: "scopes" :: Parser [Object]
  text <- fields .: "text"
  normalized <- mapM (validate text) scopes
  names <- mapM (.: "scope") normalized :: Parser [Text]
  unless (Set.size (Set.fromList names) == length names) (fail "Duplicate scope")
  intervals <- mapM (\scope -> (,) <$> scope .: "start" <*> scope .: "end") normalized :: Parser [(Int, Int)]
  when (or [a < c && c < b && b < d | (a, b) <- intervals, (c, d) <- intervals]) (fail "Crossing scopes")
  pure (object ["scopes" .= normalized])
 where
  exact keys fields = KM.size fields == length keys && all (`KM.member` fields) keys
  resolvedBinding bindings name = case KM.lookup (K.fromText name) bindings of Just (Object binding) -> KM.member "target" binding; _ -> False
  identifier value = not (T.null value) && all segment (T.splitOn "." value)
   where
    letter c = c == '_' || isAscii c && isLetter c
    segment part = case T.uncons part of Just (c, rest) -> letter c && T.all (\x -> letter x || isDigit x) rest; Nothing -> False
  validate text scope = do
    bindings <- scope .: "bindings" :: Parser Object
    case KM.lookup "literalInterpretations" scope of
      Nothing -> pure ()
      Just value -> do
        interpretations <- parseJSON value :: Parser [Object]
        unless (length interpretations >= 2) (fail "Shared literals need at least two explicit interpretations")
        foldM_ literal Set.empty interpretations
    case KM.lookup "rationalSingletons" scope of
      Nothing -> pure ()
      Just value -> unless (value == object ["ambient" .= ("Real" :: Text)]) (fail "Rational singleton families require an explicit Real ambient")
    for_ (KM.lookup "numerals" scope) $
      withObject
        "numeral domain"
        ( \domain -> do
            unless (exact ["type", "from"] domain) (fail "Numerals need a supported type and a resolved witness binding")
            ty <- domain .: "type" :: Parser Text
            witness <- domain .: "from"
            unless (ty == "Real" && resolvedBinding bindings witness) (fail "Numerals need a supported type and a resolved witness binding")
        )
    for_ (KM.lookup "predicates" scope) $
      withObject
        "predicate domain"
        ( \domain -> do
            unless (exact ["type", "witness"] domain) (fail "Predicates need Real and a local witness in a source-owned context")
            ty <- domain .: "type" :: Parser Text
            witness <- domain .: "witness"
            unless (ty == "Real" && maybe False (/= Null) (KM.lookup "context" scope) && not (T.null witness) && not ("/" `T.isInfixOf` witness)) (fail "Predicates need Real and a local witness in a source-owned context")
        )
    restrictions <- maybe (pure []) parseJSON (KM.lookup "restrictions" scope) :: Parser [Object]
    (_, updated) <- foldM (restriction text scope bindings) (Set.empty, []) restrictions
    pure (if KM.member "restrictions" scope then KM.insert "restrictions" (toJSON updated) scope else scope)
  literal seen interpretation = do
    unless (exact ["id", "constant", "consumer"] interpretation) (fail "A literal interpretation needs id, constant and consumer")
    name <- interpretation .: "id"
    unless (not (T.null name) && Set.notMember name seen) (fail "Literal interpretation identities must be nonempty and distinct")
    constant <- interpretation .: "constant"
    unless (identifier constant) (fail "A literal interpretation needs a named Lean constant")
    consumer <- interpretation .: "consumer"
    unless (exact ["declaration", "callee", "argumentPosition"] consumer) (fail "A consumer needs declaration, callee and argumentPosition")
    declaration <- consumer .: "declaration"
    callee <- consumer .: "callee"
    unless (identifier declaration && identifier callee) (fail "A consumer needs named Lean declarations")
    position <- consumer .: "argumentPosition" :: Parser Int
    unless (position >= 0) (fail "A consumer argument position must be a nonnegative integer")
    pure (Set.insert name seen)
  restriction text scope bindings (seen, updated) entry = do
    let message = "A bounded-trace restriction needs a unique premise and resolved metric/subset bindings"
    unless (exact ["kind", "premise", "metric", "subset"] entry) (fail message)
    kind <- entry .: "kind" :: Parser Text
    premise <- entry .: "premise"
    metric <- entry .: "metric"
    subset <- entry .: "subset"
    unless
      ( kind == "bounded-trace"
          && not (T.null premise)
          && T.all (\c -> isLetter c || isNumber c || c `elem` ['_', '-']) premise
          && Set.notMember premise seen
          && resolvedBinding bindings metric
          && resolvedBinding bindings subset
      )
      (fail message)
    begin <- scope .: "start"
    end <- scope .: "end"
    let opening = "<!-- chapter-correspondence-premise: " <> premise <> " -->"
        closing = "<!-- chapter-correspondence-premise-end: " <> premise <> " -->"
        occurrences needle = [(T.length prefix, T.length prefix + T.length needle) | (prefix, _) <- T.breakOnAll needle text]
    case (occurrences opening, occurrences closing) of
      ([(a, b)], [(c, d)])
        | begin <= a
        , a < b
        , b < c
        , c < d
        , d <= end
        , let body = T.take (c - b) (T.drop b text)
        , not (T.null (T.dropAround whitespace body)) ->
            pure (Set.insert premise seen, updated <> [KM.insert "source" (object ["start" .= b, "end" .= c, "text" .= body]) entry])
      _ -> fail ("Missing, duplicate, empty, or out-of-scope premise: " <> T.unpack premise)
  whitespace c = isSpace c || c `elem` ['\x1c', '\x1d', '\x1e', '\x1f', '\x85']

-- Annotation regions retain Python-compatible zero-based Unicode offsets.
sourceScopesRequest :: Value -> Parser Value
sourceScopesRequest = withObject "source scopes" $ \fields -> do
  text <- fields .: "text"
  scopes <- scan text 0 text
  scopeMetadataRequest (object ["scopes" .= scopes, "text" .= text])
 where
  header = "<!-- chapter-correspondence"
  scan complete offset remaining = case T.breakOn header remaining of
    (_, rest) | T.null rest -> pure ([] :: [Value])
    (prefix, rest) ->
      let opening = offset + T.length prefix
          afterHeader = T.drop (T.length header) rest
          jsonStart = T.dropWhile whitespace afterHeader
       in if not ("{" `T.isPrefixOf` jsonStart)
            then scan complete (opening + T.length header) afterHeader
            else case endAnnotation jsonStart of
              Nothing -> pure []
              Just (raw, after, width) -> do
                decoded <- either fail pure (decodeSourceJSON raw)
                normalized <- scopeBindingsRequest (object ["scope" .= decoded]) >>= withObject "normalized scope" (.: "scope")
                name <- withObject "scope name" (.: "scope") normalized
                let begin = opening + T.length header + T.length afterHeader - T.length jsonStart + width
                    closeTag = "<!-- chapter-correspondence-end: " <> name <> " -->"
                    allowedName = not (T.null name) && T.all (\c -> isLetter c || isNumber c || c `elem` ['_', '-']) name
                    ends = [T.length before | allowedName, (before, _) <- T.breakOnAll closeTag complete]
                closing <- case ends of [position] | position >= begin -> pure position; _ -> fail ("Missing/duplicate/misplaced scope end: " <> T.unpack name)
                scope <- withObject "scope region" (pure . Object . KM.insert "start" (toJSON begin) . KM.insert "end" (toJSON closing)) normalized
                restScopes <- scan complete begin after
                pure (scope : restScopes)
  endAnnotation input = search 0 input
   where
    search offset remaining = case T.breakOn "}" remaining of
      (_, rest) | T.null rest -> Nothing
      (prefix, rest) ->
        let count = offset + T.length prefix + 1
            afterBrace = T.drop 1 rest
            trimmed = T.dropWhile whitespace afterBrace
         in case T.stripPrefix "-->" trimmed of
              Just after -> Just (T.take count input, after, count + T.length afterBrace - T.length trimmed + 3)
              Nothing -> search count afterBrace
  whitespace c = isSpace c || c `elem` ['\x1c', '\x1d', '\x1e', '\x1f', '\x85']
