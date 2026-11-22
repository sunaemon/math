{-# LANGUAGE OverloadedStrings #-}

-- Original-source locations are a separate, conservative view of validated
-- correspondence. Matching a function name alone can never authorize a range.
module LeanSourceRanges (sourceTargetsRequest, sourceRangesRequest) where

import Data.Aeson (Value (..), object, withObject, (.:), (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser)
import Data.Foldable (toList)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

field :: Text -> Value -> Value
field key (Object values) = fromMaybe Null (KM.lookup (K.fromText key) values)
field _ _ = Null

array :: Value -> [Value]
array (Array values) = toList values
array _ = []

canonical :: Value -> Value
canonical (Object values) = Object (fmap canonical (if KM.lookup "kind" values == Just (String "variable") then KM.delete "id" values else values))
canonical (Array values) = Array (fmap canonical values)
canonical value = value

complete :: Value -> Bool
complete value@(Object values) = field "kind" value /= String "truncated" && all complete (KM.elems values)
complete (Array values) = all complete values
complete _ = True

names :: Value -> [Text]
names value@(Object values) = case field "kind" value of
  String "variable" -> case field "name" value of String name -> [name]; _ -> []
  _ -> concatMap names (KM.elems values)
names (Array values) = concatMap names values
names _ = []

sourceTargetsRequest :: Value -> Parser Value
sourceTargetsRequest = withObject "source-range targets" $ \fields -> do
  formulas <- fields .: "formulas" :: Parser Value
  operators <- fields .: "operators" :: Parser Value
  let records = field "leanEvidence" formulas
      roots = Map.fromList [(show (field "index" row), row) | row <- array (field "formulas" formulas)]
      make row operator kernel = do
        let candidates = row : array (field "expressionFragments" row)
            contains part =
              field "context" part /= Null && case (field "start" part, field "end" part, field "start" operator, field "end" operator) of
                (Number a, Number b, Number c, Number d) -> a <= c && d <= b
                _ -> False
        context <- case filter contains candidates of
          first : _ -> case field "context" first of String name -> Just name; _ -> Nothing
          _ -> Nothing
        let binders = case records of Object values -> maybe [] (array . field "binders") (KM.lookup (K.fromText context) values); _ -> []
        pure (object ["formulaIndex" .= field "index" row, "operatorStart" .= field "operatorStart" operator, "declaration" .= T.takeWhile (/= '@') context, "kernel" .= canonical kernel, "binders" .= binders])
      operatorsFor rowIndex = fromMaybe Null (Map.lookup (show rowIndex) roots)
      targets = [target | entry <- array (field "formulas" operators), let row = operatorsFor (field "formulaIndex" entry), node <- array (field "nodes" entry), call <- case array (field "calls" node) of [] -> [node]; calls -> calls, let kernel = field "kernel" (field "elaborated" call), kernel /= Null, Just target <- [make row node kernel]]
      text fieldName = Set.toList (Set.fromList [name | target <- targets, String name <- [field fieldName target]])
      headName kernel = let root = if field "kind" kernel == String "application" then field "function" kernel else kernel in case (field "kind" root, field "name" root) of (String "constant", String name) -> [name]; _ -> []
  pure (object ["targets" .= targets, "declarations" .= text "declaration", "heads" .= Set.toList (Set.fromList (concatMap (headName . field "kernel") targets)), "variables" .= Set.toList (Set.fromList (concatMap (names . field "kernel") targets))])

sourceRangesRequest :: Value -> Parser Value
sourceRangesRequest = withObject "original Lean source ranges" $ \fields -> do
  targets <- fields .: "targets" :: Parser [Value]
  ranges <- fields .: "ranges" :: Parser [Value]
  let index = Map.fromListWith (<>) [(name, [range]) | range <- ranges, String name <- [field "declaration" range]]
      contextMatches target range = all check (Set.toList (Set.fromList (names (field "kernel" target))))
       where
        check name = case (filter ((== String name) . field "name") (array (field "binders" target)), filter ((== String name) . field "name") (array (field "locals" range))) of
          ([expected], [actual]) -> field "type" expected == field "type" actual && field "value" expected == field "value" actual
          _ -> False
      matched target =
        let possible = case field "declaration" target of
              String name -> Map.findWithDefault [] name index
              _ -> []
            matches = filter (\range -> field "kernel" target /= Null && complete (field "kernel" target) && canonical (field "kernel" range) == field "kernel" target && contextMatches target range) possible
         in [object ["formulaIndex" .= field "formulaIndex" target, "operatorStart" .= field "operatorStart" target, "source" .= field "source" range, "startOffset" .= field "startOffset" range, "endOffset" .= field "endOffset" range, "startLine" .= field "startLine" range, "declaration" .= field "declaration" range, "match" .= ("kernel-and-context" :: Text)] | range <- matches]
  pure (object ["ranges" .= nub (concatMap matched targets)])
