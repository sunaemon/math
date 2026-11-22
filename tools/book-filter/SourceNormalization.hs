{-# LANGUAGE OverloadedStrings #-}

-- | Source-owned evidence attached before construction-specific interpretation.
module SourceNormalization (normalizationRequest, comparisonRequest, scalarRequest) where

import Control.Monad (unless)
import Data.Aeson (Value (..), object, toJSON, withObject, (.:), (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser)
import Data.Char (isDigit, isSpace)
import Data.Foldable (toList)
import Data.List (dropWhileEnd, sortOn)
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Text (Text)
import qualified Data.Text as T
import ProofContexts (contextReference)
import StructuralSyntax (ballFamilies, expressionTokens, indexedSingletons, normalTokens)

field :: Text -> Value -> Value
field key (Object fields) = fromMaybe Null (KM.lookup (K.fromText key) fields)
field _ _ = Null

label :: Text -> Value -> Text
label key value = case field key value of String text -> text; _ -> ""

patch :: Value -> [(Text, Value)] -> Value
patch (Object fields) changes = Object (foldr (uncurry (KM.insert . K.fromText)) fields changes)
patch value _ = value

integer :: Text -> Value -> Parser Int
integer key = withObject "normalization source position" (.: K.fromText key)

normalizationRequest :: Value -> Parser Value
normalizationRequest = withObject "source normalization" $ \fields -> do
  stage <- fields .: "stage" :: Parser Text
  tree <- fields .: "tree"
  row <- fields .: "row"
  scopes <- fields .: "scopes" :: Parser [Value]
  rowStart <- integer "start" row
  applicable <- filterM (active rowStart) scopes
  normalized <- case stage of
    "literal" -> literal tree row (select "literalInterpretations" applicable)
    "rational" -> do
      shapes <- either fail pure (indexedSingletons tree)
      let rational = case shapes of Array values -> any ((== "ℚ") . label "indexType") values; _ -> False
      pure $ case select "rationalSingletons" applicable of
        [] -> tree
        choices | rational -> let scope = innermost choices in patch tree [("rationalAmbient", object ["type" .= ("Real" :: Text), "scope" .= field "scope" scope, "start" .= field "start" scope, "end" .= field "end" scope])]
        _ -> tree
    "restrictions" -> generatorRestrictions tree row applicable
    "numeric" -> numeric tree row (select "numerals" applicable)
    "prefix" -> prefix tree (select "predicates" applicable)
    _ -> fail "Unknown source normalization stage"
  pure (object ["tree" .= normalized])
 where
  filterM _ [] = pure []
  filterM predicate (value : rest) = do yes <- predicate value; remaining <- filterM predicate rest; pure ([value | yes] <> remaining)
  active offset scope = do begin <- integer "start" scope; end <- integer "end" scope; pure (begin <= offset && offset < end)
  select key = filter (hasField key)
  hasField key (Object fields) = KM.member (K.fromText key) fields
  hasField _ _ = False
  innermost [] = Null
  innermost (first : rest) = foldl (\best candidate -> if field "start" candidate > field "start" best then candidate else best) first rest
  literal tree _ [] = pure tree
  literal tree row scopes = do
    unless (length scopes == 1) (fail "Shared literal interpretation scopes must be unambiguous")
    let book = label "book" row
    unless (not (T.null book) && T.all isDigit book) (fail "Shared literal interpretations require one bare natural numeral")
    let scope = innermost scopes
        interpretations = case field "literalInterpretations" scope of Array values -> toList values; _ -> []
        part interpretation =
          object
            [ "kind" .= ("interpreted-literal" :: Text)
            , "start" .= field "start" tree
            , "end" .= field "end" tree
            , "args" .= ([] :: [Value])
            , "operatorStart" .= field "start" tree
            , "operatorEnd" .= field "end" tree
            , "interpretationId" .= (label "scope" scope <> "/" <> label "id" interpretation)
            , "expectedConstant" .= field "constant" interpretation
            , "consumer" .= field "consumer" interpretation
            , "lowering" .= object ["kind" .= ("contextual-literal" :: Text), "sourceLiteral" .= book]
            ]
    pure (patch tree [("kind", String "contextual-interpretations"), ("sourceSyntax", tree), ("interpretations", toJSON (map part interpretations))])
  numeric tree _ [] = pure tree
  numeric tree row choices = do
    let scope = innermost choices
        domain = field "numerals" scope
        witness = field (label "from" domain) (field "bindings" scope)
        evidence = object ["type" .= field "type" domain, "target" .= field "target" witness, "binding" .= field "id" witness]
        book = label "book" row
        stripped = T.dropAround whitespace book
    if T.null stripped || not (T.all isDigit stripped)
      then pure (patch tree [("numericContext", evidence), ("numericExpression", Bool (not (T.null book) && T.all (\c -> isDigit c || whitespace c || c `elem` ['+', '*', '/', '(', ')', '-']) book))])
      else do
        start <- integer "start" tree
        pure
          ( patch
              tree
              [ ("numericDomain", evidence)
              , ("numeral", String stripped)
              , ("numericStart", toJSON (start + T.length book - T.length (T.dropWhile whitespace book)))
              , ("numericEnd", toJSON (start + T.length (T.dropWhileEnd whitespace book)))
              ]
          )
  prefix tree [] = pure tree
  prefix tree choices
    | label "kind" tree /= "sequence" = pure tree
    | otherwise = do
        tokens <- either fail pure (normalTokens tree)
        case tokens of
          operator : digits@(first : _)
            | label "text" operator == "<"
            , all (\t -> label "kind" t == "text" && T.length (label "text" t) == 1 && T.all isDigit (label "text" t)) digits -> do
                positions <- mapM (integer "start") digits
                if not (and (zipWith (\a b -> b == a + 1) positions (drop 1 positions)))
                  then pure tree
                  else do
                    let scope = innermost choices
                        domain = field "predicates" scope
                    context <- contextReference (field "context" scope)
                    final <- integer "start" (last digits)
                    let evidence = object ["type" .= field "type" domain, "target" .= (context <> "/" <> label "witness" domain), "binding" .= (label "scope" scope <> "/predicates")]
                        body =
                          object
                            [ "kind" .= ("sequence" :: Text)
                            , "items" .= digits
                            , "start" .= field "start" first
                            , "end" .= (final + 1)
                            , "numericDomain" .= evidence
                            , "numeral" .= T.concat (map (label "text") digits)
                            , "numericStart" .= field "start" first
                            , "numericEnd" .= (final + 1)
                            ]
                    pure (patch tree [("prefixPredicate", object ["domain" .= evidence, "operator" .= operator, "bound" .= body])])
          _ -> pure tree
  generatorRestrictions tree row applicable = do
    shapes <- either fail pure (ballFamilies tree)
    ordered <- mapM (\scope -> do begin <- integer "start" scope; pure (begin, scope)) [scope | scope <- applicable, not (null (array (field "restrictions" scope)))]
    let scopes = map snd (sortOn (Down . fst) ordered)
    end <- integer "end" row
    attached <- concat <$> mapM (attach end scopes) (array shapes)
    pure (if null attached then tree else patch tree [("generatorRestrictions", toJSON attached)])
  attach end scopes shape = do
    let diameter = firstItem (array (field "traceCondition" shape))
        arguments = array (field "args" diameter)
    case arguments of
      [metric, traceBody] -> do
        trace <- sourceTokens traceBody
        case trace of
          [value, intersection, subset]
            | label "name" intersection == "cap"
            , null (array (field "args" intersection))
            , field "optional" intersection == Null -> do
                lhs <- identity value
                rhs <- identity (field "value" shape)
                if lhs /= rhs
                  then pure []
                  else do
                    metricSymbol <- symbol metric
                    subsetSymbol <- symbol subset
                    choosePremise end shape traceBody metricSymbol subsetSymbol scopes
          _ -> pure []
      _ -> pure []
  choosePremise _ _ _ _ _ [] = pure []
  choosePremise end shape trace metricSymbol subsetSymbol (scope : scopes) = do
    candidates <-
      filterM
        ( \restriction -> do
            begin <- integer "start" (field "source" restriction)
            let bindings = field "bindings" scope
            pure (begin >= end && field "symbol" (field (label "metric" restriction) bindings) == metricSymbol && field "symbol" (field (label "subset" restriction) bindings) == subsetSymbol)
        )
        (array (field "restrictions" scope))
    case candidates of
      [] -> choosePremise end shape trace metricSymbol subsetSymbol scopes
      [restriction] ->
        let binding key = field (label key restriction) (field "bindings" scope)
            reference key = object ["id" .= field "id" (binding key), "target" .= field "target" (binding key)]
         in pure
              [ object
                  [ "kind" .= ("bounded-trace" :: Text)
                  , "generatorOffset" .= field "start" (field "opening" shape)
                  , "premise" .= field "premise" restriction
                  , "source" .= field "source" restriction
                  , "metric" .= reference "metric"
                  , "subset" .= reference "subset"
                  , "trace" .= trace
                  ]
              ]
      _ -> fail "Ambiguous bounded-trace premise"
  sourceTokens node =
    if label "kind" node == "sequence"
      then either fail pure (normalTokens node)
      else do
        parts <- either fail pure (expressionTokens node)
        pure [t | t <- parts, let text = label "text" t, T.null text || not (T.all whitespace text)]
  symbol node = do
    parts <- sourceTokens node
    pure $ case parts of
      [part] -> if label "kind" part == "text" then field "text" part else String ("\\" <> label "name" part)
      _ -> Null
  identity node
    | label "kind" node == "sequence" = toJSON <$> (sourceTokens node >>= mapM identity)
    | Object fields <- node = Object <$> traverse childIdentity (KM.delete "start" (KM.delete "end" fields))
    | otherwise = pure node
  childIdentity (Array values) = toJSON <$> mapM identity (toList values)
  childIdentity value@(Object _) = identity value
  childIdentity value = pure value
  array (Array values) = toList values
  array _ = []
  firstItem (value : _) = value
  firstItem [] = Null
  whitespace c = isSpace c || c `elem` ['\x1c', '\x1d', '\x1e', '\x1f', '\x85']

-- Numeric comparison operands inherit only an explicit source-domain witness.
comparisonRequest :: Value -> Parser Value
comparisonRequest = withObject "comparison operand" $ \fields -> do
  tokens <- fields .: "tokens" :: Parser [Value]
  domain <- fields .: "domain"
  converted <- if domain == Null || domain == object [] || not (all scalarToken tokens) then pure tokens else numbers domain tokens
  let trimmed = dropWhileEnd blank (dropWhile blank converted)
  case trimmed of
    [] -> fail "Empty expression operand."
    first : _ -> do
      begin <- integer "start" first
      final <- integer "start" (last trimmed)
      let lastToken = last trimmed
          end = case field "end" lastToken of Null -> toJSON (final + T.length (label "text" lastToken)); value -> value
      pure (object ["tree" .= object ["kind" .= ("sequence" :: Text), "items" .= trimmed, "start" .= begin, "end" .= end]])
 where
  whitespace c = isSpace c || c `elem` ['\x1c', '\x1d', '\x1e', '\x1f', '\x85']
  blank node = not (T.null (label "text" node)) && T.all whitespace (label "text" node)
  scalarToken node = label "kind" node == "text" && not (T.null (label "text" node)) && T.all (\c -> isDigit c || whitespace c || c `elem` ['+', '*', '/', '(', ')', '-']) (label "text" node)
  digits node = not (T.null (label "text" node)) && T.all isDigit (label "text" node)
  numbers _ [] = pure []
  numbers domain (token : rest)
    | not (digits token) = (token :) <$> numbers domain rest
    | otherwise = do
        begin <- integer "start" token
        (value, remaining) <- collect begin (label "text" token) rest
        subsequent <- numbers domain remaining
        pure
          ( object
              [ "kind" .= ("source-numeral" :: Text)
              , "start" .= begin
              , "end" .= (begin + T.length value)
              , "numericDomain" .= domain
              , "numeral" .= value
              , "numericStart" .= begin
              , "numericEnd" .= (begin + T.length value)
              ]
              : subsequent
          )
  collect begin value (token : rest) | digits token = do
    next <- integer "start" token
    if next == begin + T.length value then collect begin (value <> label "text" token) rest else pure (value, token : rest)
  collect _ value rest = pure (value, rest)

-- | Scalar coercion candidates use source-resolved types, never observed calls.
scalarRequest :: Value -> Parser Value
scalarRequest = withObject "scalar operands" $ \fields -> do
  stage <- fields .: "stage" :: Parser Text
  variables <- fields .: "variables" :: Parser [Value]
  let variable node = fromMaybe Null (lookup (field "start" node) [(field "formulaOffset" v, v) | v <- variables])
  case stage of
    "real" -> do
      node <- fields .: "tree"
      tokens <- if label "kind" node == "sequence" then concat <$> mapM (either fail pure . expressionTokens) (array (field "items" node)) else either fail pure (expressionTokens node)
      converted <- realTokens variable tokens
      result <- case converted of Nothing -> pure Null; Just parts -> sequenceTree parts
      pure (object ["tree" .= result])
    "ennreal" -> do
      operands <- fields .: "operands" :: Parser [Value]
      let isExtended operand = let v = variable (atomic operand) in label "status" v == "resolved" && label "leanType" v `elem` ["ENNReal", "ℝ≥0∞"]
      pure (object ["operands" .= if any isExtended operands then map extended operands else operands])
    _ -> fail "Unknown scalar normalization stage"
 where
  array (Array values) = toList values
  array _ = []
  whitespace c = isSpace c || c `elem` ['\x1c', '\x1d', '\x1e', '\x1f', '\x85']
  digits value = not (T.null value) && T.all isDigit value
  blank node = let value = label "text" node in not (T.null value) && T.all whitespace value
  sequenceTree tokens = case dropWhileEnd blank (dropWhile blank tokens) of
    [] -> fail "Empty expression operand."
    parts@(first : _) -> do
      begin <- integer "start" first
      final <- integer "start" (last parts)
      let end = case field "end" (last parts) of Null -> toJSON (final + T.length (label "text" (last parts))); value -> value
      pure (object ["kind" .= ("sequence" :: Text), "items" .= parts, "start" .= begin, "end" .= end])
  realTokens _ [] = pure (Just [])
  realTokens variable (token : rest)
    | label "kind" token /= "text" = pure Nothing
    | otherwise = do
        begin <- integer "start" token
        let value = label "text" token
        (merged, remaining) <- if digits value then collect begin value rest else pure (value, rest)
        let node = if digits value then patch token [("text", String merged), ("end", toJSON (begin + T.length merged))] else token
            numeric = digits merged || label "leanType" (variable node) `elem` ["Nat", "ℕ", "Int", "ℤ", "Real", "ℝ"]
            converted = if numeric then patch node [("kind", String "real-scalar-atom"), ("body", node)] else node
            allowed = numeric || (not (T.null merged) && T.all whitespace merged) || merged `elem` ["+", "-", "*", "/", "(", ")"]
        if allowed then fmap (converted :) <$> realTokens variable remaining else pure Nothing
  collect begin value (token : rest)
    | digits (label "text" token) = do
        next <- integer "start" token
        if next == begin + T.length value then collect begin (value <> label "text" token) rest else pure (value, token : rest)
  collect _ value rest = pure (value, rest)
  atomic node
    | label "kind" node == "sequence" = case filter (\n -> not (label "kind" n == "text" && blank n)) (array (field "items" node)) of [child] -> atomic child; _ -> node
    | label "kind" node == "text" =
        let value = label "text" node
            stripped = T.dropAround whitespace value
            begin = case field "start" node of Number n -> n; _ -> 0
         in patch node [("text", String stripped), ("start", toJSON (begin + fromIntegral (T.length value - T.length (T.dropWhile whitespace value))))]
    | otherwise = node
  extended operand =
    let node = atomic operand
     in if label "kind" node == "command" && label "name" node == "infty"
          then patch node [("kind", String "ennreal-top")]
          else
            if label "kind" node == "text" && digits (label "text" node)
              then
                let begin = field "start" node
                    end = case field "end" node of
                      Null -> case begin of
                        Number n -> toJSON (n + fromIntegral (T.length (label "text" node)))
                        _ -> Null
                      value -> value
                 in patch node [("kind", String "ennreal-numeral"), ("end", end), ("operatorStart", begin), ("operatorEnd", end)]
              else operand
