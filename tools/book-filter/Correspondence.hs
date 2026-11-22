{-# LANGUAGE OverloadedStrings #-}

{- | Shared semantic macro lowering. The caller supplies already resolved Lean
operands; Lean remains responsible for elaboration and kernel validation.
-}
module Correspondence (correspondenceMain) where

import ChapterPreparation (chapterRequest, formulasRequest, occurrencesRequest, preparationRequest)
import Control.Monad (unless)
import Data.Aeson (Value, eitherDecode, encode, object, withObject, (.:), (.=))
import Data.Aeson.Types (Parser, parseEither)
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Text (Text)
import FormulaAnchors (formulaAnchorsRequest)
import LeanSourceRanges (sourceRangesRequest, sourceTargetsRequest)
import OperatorEvidence (checkProbeRequest, coverageRequest, mergeCallRequest)
import OperatorProbe (preludeRequest, probeRequest)
import ProofContexts (contextBridgeRequest, definitionRequest, proofRequest)
import SemanticExpr
import SemanticTranslation (translationRequest)
import SourceNormalization (comparisonRequest, normalizationRequest, scalarRequest)
import SourceScopes (referenceRequest, scopeBindingsRequest, scopeDeclarationsRequest, scopeMetadataRequest, sourceScopesRequest)
import StructuralSyntax (structuralRequest)
import System.IO (hFlush, isEOF, stdout)
import VariableResolution (domainResolutionRequest, lexicalResolutionRequest, outerResolutionRequest, resolutionRequest)

reviewBasis :: Value -> Parser ReviewBasis
reviewBasis = withObject "review basis" $ \fields ->
  ReviewBasis <$> fields .: "sourceHash" <*> fields .: "rulesHash" <*> fields .: "leanFingerprints"

request :: Value -> Parser Value
request value =
  withObject
    "correspondence request"
    ( \fields -> do
        action <- fields .: "action"
        case action :: Text of
          "reviewMatches" -> do
            recorded <- fields .: "recorded" >>= reviewBasis
            current <- fields .: "current" >>= reviewBasis
            pure (object ["matched" .= either (const False) (const True) (review recorded current (candidate ()))])
          "contextReference" -> referenceRequest value
          "sourceOccurrences" -> occurrencesRequest value
          "parseFormulas" -> formulasRequest value
          "prepareChapter" -> preparationRequest value
          "analyzeChapter" -> chapterRequest value
          "formulaAnchors" -> formulaAnchorsRequest value
          "leanSourceTargets" -> sourceTargetsRequest value
          "leanSourceRanges" -> sourceRangesRequest value
          "scalarOperands" -> scalarRequest value
          "comparisonOperand" -> comparisonRequest value
          "normalizeSource" -> normalizationRequest value
          "sourceScopes" -> sourceScopesRequest value
          "scopeMetadata" -> scopeMetadataRequest value
          "scopeDeclarations" -> scopeDeclarationsRequest value
          "scopeBindings" -> scopeBindingsRequest value
          "resolveVariables" -> resolutionRequest value
          "resolveDomains" -> domainResolutionRequest value
          "resolveLexical" -> lexicalResolutionRequest value
          "resolveOuter" -> outerResolutionRequest value
          "contextBridge" -> contextBridgeRequest value
          "translateBatch" -> translationRequest value
          "structural" -> structuralRequest value
          "macros" -> pure (object ["macros" .= macroNames])
          "lowerMacro" -> do
            name <- fields .: "name"
            arguments <- fields .: "arguments"
            case operation name (map ExplicitLean arguments) of
              Left message -> fail message
              Right op -> pure (object ["term" .= renderCandidate (candidate (Macro Nothing op))])
          "operatorProbe" -> probeRequest value
          name | name `elem` ["metricPrelude", "operatorLean", "operatorHeader"] -> preludeRequest name value
          "implicitCoverage" -> coverageRequest value
          "mergeOperatorCall" -> mergeCallRequest value
          "checkOperatorProbe" -> checkProbeRequest value
          "expressionDefinition" -> definitionRequest value
          actionName | actionName `elem` ["proofPrelude", "inspectContexts", "contextExpression"] -> proofRequest actionName value
          _ -> fail "Unknown correspondence action"
    )
    value

-- One JSON request and response per line. Keep the process alive to amortize
-- startup; malformed input is an explicit error, never an untyped fallback.
correspondenceMain :: IO ()
correspondenceMain = do
  done <- isEOF
  unless done $ do
    line <- BL.fromStrict <$> BS.getLine
    let result = eitherDecode line >>= parseEither request
        response = either (\message -> object ["error" .= message]) id result
    BL.putStrLn (encode response)
    hFlush stdout
    correspondenceMain
