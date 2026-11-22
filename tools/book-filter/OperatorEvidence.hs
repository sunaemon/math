{-# LANGUAGE OverloadedStrings #-}

{- | Check all observed calls against their source-owned expectations. Coverage
is computed from the observed Lean telescope, never from a list of known heads.
-}
module OperatorEvidence (coverageRequest, checkProbeRequest, mergeCallRequest) where

import Control.Monad (unless)
import Data.Aeson (Object, Value (..), object, withObject, (.!=), (.:), (.:?), (.=))
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser)
import Data.Maybe (fromMaybe, isNothing)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

statusOf :: Object -> Parser Text
statusOf o = o .: "status"

coverage :: Object -> [Object] -> Maybe [Object] -> Parser Value
coverage elaborated expectations checks = do
  arguments <- elaborated .:? "arguments" :: Parser (Maybe [Object])
  case arguments of
    Nothing -> pure missing
    Just args | not (all (KM.member "implicit") args) -> pure missing
    Just args -> do
      implicit <- mapM (.: "implicit") args
      positions <- mapM (.: "argumentPosition") expectations :: Parser [Int]
      checksMatch <- maybe (pure False) (fmap (all (== "matched")) . mapM statusOf) checks
      let actual = Set.fromList [i | (i, True) <- zip [0 :: Int ..] implicit]
          expected = Set.fromList positions
          absent = actual Set.\\ expected
          unexpected = expected Set.\\ actual
          status
            | length positions /= Set.size expected || not (Set.null unexpected) = "mismatch"
            | isNothing checks = "unreviewed"
            | maybe 0 length checks /= length positions || not checksMatch = "mismatch"
            | not (Set.null absent) = "unreviewed"
            | Set.null actual = "not-required"
            | otherwise = "matched" :: Text
      pure $
        object
          [ "actualPositions" .= Set.toAscList actual
          , "expectedPositions" .= Set.toAscList expected
          , "missingPositions" .= Set.toAscList absent
          , "unexpectedPositions" .= Set.toAscList unexpected
          , "status" .= status
          ]
 where
  missing = object ["status" .= ("unreviewed" :: Text), "reason" .= ("Missing elaborated argument telescope" :: Text)]

coverageRequest :: Value -> Parser Value
coverageRequest = withObject "implicit coverage" $ \o -> do
  elaborated <- o .: "elaborated"
  expectations <- o .: "expectations"
  checks <- o .:? "checks"
  result <- coverage elaborated expectations checks
  pure (object ["coverage" .= result])

-- Source metadata remains an extensible object on the wire; all decisions below
-- parse the required observed evidence and preserve unrelated metadata verbatim.
overlay :: Object -> Value -> Object
overlay old (Object new) = KM.union new old
overlay old _ = old

requirement :: Maybe Int -> Text -> Object -> Value
requirement operand kind value = Object (overlay value (object ["sourceOperand" .= operand, "kind" .= kind]))

requirements :: Object -> Object -> Parser ([Value], Text)
requirements mapping observed = do
  rule <- mapping .: "rule" :: Parser Text
  distance <- observed .: "distanceRequirement" :: Parser (Maybe Object)
  (base, baseStatus) <-
    maybe
      (pure ([], "not-required"))
      ( \r -> do
          status <- statusOf r
          pure ([requirement (Just 1) "nonempty-set" r], status)
      )
      distance
  let choose key operand kind required = do
        entry <- if required then Just <$> observed .: key else observed .: key
        case entry of
          Nothing -> pure (base, baseStatus)
          Just r -> do
            status <- statusOf r
            pure ([requirement operand kind r], status)
  case rule of
    "map:inclusion" -> choose "inclusionRequirement" Nothing "subset-inclusion" True
    "application:subtype-argument" -> choose "subtypeArgumentRequirement" (Just 0) "subtype-membership" False
    "relation:sequence-limit" -> choose "convergenceInclusionRequirement" (Just 0) "convergence-subspace-inclusion" False
    "macro:MetricDiameter" -> do
      (entries, status) <- choose "diameterRequirement" (Just 1) "bounded-set" True
      subset <- observed .: "metricSetRequirement"
      pure (entries <> maybe [] (\r -> [requirement (Just 1) "metric-subspace-containment" r]) subset, status)
    "definition:=" -> choose "equalityRequirement" Nothing "defining-equality" True
    "operation:infimum" -> choose "infimumRequirement" (Just 0) "nonempty-bounded-below" True
    r | r `elem` ["sum:infinite", "sum:tail"] -> do
      operands <- mapping .: "operandSpans" :: Parser [Value]
      choose "summabilityRequirement" (Just (length operands - 1)) "summable" True
    _ -> pure (base, baseStatus)

checkCall :: Object -> Object -> Object -> Object -> Parser Value
checkCall heads consumers mapping observed = do
  elaborated <- observed .: "elaborated"
  operands <- observed .: "operands" :: Parser (Maybe [Object])
  operandChecksMatch <- maybe (pure False) (fmap (all (== "matched")) . mapM statusOf) operands
  implicitChecks <- observed .: "implicitArguments"
  implicitExpectations <- mapping .:? "expectedImplicitArguments" .!= []
  coverageValue <- coverage elaborated implicitExpectations implicitChecks
  implicitStatus <- withObject "coverage" statusOf coverageValue
  (semantic, requirementStatus) <- requirements mapping observed
  let operandStatus
        | implicitStatus == "mismatch" = "mismatch"
        | isNothing operands = "unreviewed"
        | operandChecksMatch = "matched"
        | otherwise = "mismatch" :: Text
  rule <- mapping .: "rule"
  expected <- if KM.member "expectedConstant" mapping then mapping .:? "expectedConstant" else heads .:? Key.fromText rule
  observedHead <- elaborated .: "head" :: Parser Value
  let headStatus = maybe "unreviewed" (\e -> if observedHead == e then "matched" else "mismatch") expected :: Text
  kernel <- elaborated .: "kernel"
  kernelKind <- kernel .: "kind" :: Parser Text
  targetVariable <- case KM.lookup "expectedVariable" mapping of
    Nothing -> pure headStatus
    Just variable -> do
      headNode <- if kernelKind == "application" then kernel .: "function" else pure kernel
      kind <- headNode .: "kind" :: Parser Text
      pure (if kind == "variable" && KM.lookup "name" headNode == Just variable then "matched" else "mismatch")
  (targetCallee, calleeFields) <-
    if KM.member "expectedCallee" mapping
      then do
        callee <- observed .: "callee"
        status <- statusOf callee
        pure (status, object ["calleeCheck" .= callee])
      else pure (targetVariable, object [])
  target <- case KM.lookup "expectedBinderName" mapping of
    Nothing -> pure targetCallee
    Just binder -> do
      binderKind <- mapping .:? "expectedBinderKind" .!= ("lambda" :: Text)
      typeMatches <- case KM.lookup "expectedBinderTypeName" mapping of
        Nothing -> pure True
        Just typeName -> do
          domain <- kernel .: "domain"
          pure (KM.lookup "name" domain == Just typeName)
      pure (if kernelKind == binderKind && KM.lookup "name" kernel == Just binder && typeMatches then "matched" else "mismatch")
  (consumerFields, finalSemantic, finalRequirement) <-
    if KM.member "consumer" mapping
      then do
        key <- mapping .:? "consumerKey"
        consumerObject <- maybe (pure Nothing) ((consumers .:?) . Key.fromText) key :: Parser (Maybe Object)
        evidence <- maybe (pure Nothing) (.:? "evidence") consumerObject :: Parser (Maybe Object)
        consumerStatus <- case evidence of
          Nothing -> pure ("unreviewed" :: Text)
          Just e -> do
            h <- e .: "headStatus"
            argument <- e .: "argument"
            a <- statusOf argument
            pure (if h == ("matched" :: Text) && a == "matched" then "matched" else "mismatch")
        pure
          ( object ["consumerEvidence" .= evidence, "consumerStatus" .= consumerStatus]
          , semantic <> [object ["kind" .= ("literal-consumer-argument" :: Text), "status" .= consumerStatus]]
          , if consumerStatus == "matched" then "proved" else "unresolved"
          )
      else pure (object [], semantic, requirementStatus)
  pure
    $ Object
    $ overlay (overlay (overlay mapping calleeFields) consumerFields)
    $ object
      [ "elaborated" .= elaborated
      , "operandChecks" .= operands
      , "operandStatus" .= operandStatus
      , "implicitArgumentChecks" .= implicitChecks
      , "implicitArgumentCoverage" .= coverageValue
      , "implicitArgumentStatus" .= implicitStatus
      , "semanticRequirements" .= finalSemantic
      , "requirementStatus" .= finalRequirement
      , "expectedHead" .= expected
      , "headStatus" .= headStatus
      , "targetStatus" .= target
      ]

checkProbeRequest :: Value -> Parser Value
checkProbeRequest = withObject "operator evidence request" $ \fields -> do
  mappings <- fields .: "mappings" :: Parser [Object]
  nodes <- fields .: "nodes" :: Parser [Object]
  consumers <- fields .:? "consumers" .!= KM.empty
  heads <- fields .: "heads"
  checked <-
    mapM
      ( \mapping -> do
          marker <- mapping .: "marker" :: Parser Text
          multiple <- mapping .:? "allowMultipleCalls" .!= False
          let matched = filter (\n -> KM.lookup "marker" n == Just (String marker)) nodes
          unless (not (null matched) && (length matched == 1 || multiple)) $
            fail ("Operator marker missing or duplicated: " <> T.unpack marker <> " (" <> show (length matched) <> " occurrences)")
          mapM (checkCall heads consumers mapping) matched
      )
      mappings
  pure (object ["mappings" .= concat checked])

mergeCallRequest :: Value -> Parser Value
mergeCallRequest = withObject "merge operator calls" $ \fields -> do
  mapping <- fields .: "mapping" :: Parser Object
  existing <- fields .:? "existing" :: Parser (Maybe Object)
  prior <- maybe (pure []) (.: "calls") existing :: Parser [Object]
  let calls = prior <> [mapping]
      original = fromMaybe mapping existing
  combined <-
    mapM
      ( \field -> do
          statuses <- Set.fromList <$> mapM (\o -> o .:? field .!= ("unreviewed" :: Text)) calls
          let status
                | Set.member "mismatch" statuses = "mismatch"
                | Set.member "unreviewed" statuses = "unreviewed"
                | statuses == Set.singleton "not-required" = "not-required"
                | otherwise = "matched" :: Text
          pure (field .= status)
      )
      ["headStatus", "targetStatus", "operandStatus", "implicitArgumentStatus"]
  requirementsSeen <- Set.fromList <$> mapM (\o -> o .:? "requirementStatus" .!= ("not-required" :: Text)) calls
  let requirementStatus
        | Set.member "unresolved" requirementsSeen = "unresolved"
        | Set.member "proved" requirementsSeen = "proved"
        | otherwise = "not-required" :: Text
  pure (object ["node" .= Object (overlay original (object (combined <> ["calls" .= calls, "requirementStatus" .= requirementStatus])))])
