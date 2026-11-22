{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}

{- | Source derivation evidence is orthogonal to mathematical operations.
It may annotate an existing operator trace, but cannot replace its operands,
expected Lean head, type, instance or kernel obligations.
-}
module SemanticTrace (SourceDerivation (..), RestrictionEvidence (..), derivationValue, restrictionValue, annotateRoot) where

import Data.Aeson (Value (..), object, (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Data (Data)
import Data.Text (Text)
import LocatedMath (LocatedMath, SourceSpan (..), locatedValue)

-- Premise provenance records named source bindings and syntax. In particular,
-- metric/subset roles are selected by the chapter rule, not fields in the AST.
data RestrictionEvidence = RestrictionEvidence
  { restrictionKind :: Text
  , restrictionOffset :: Int
  , restrictionPremise :: Text
  , restrictionSource :: SourceSpan
  , restrictionText :: Text
  , restrictionReferences :: [(Text, (Text, Text))]
  , restrictionSyntax :: [(Text, LocatedMath)]
  }
  deriving (Eq, Show, Data)

restrictionValue :: RestrictionEvidence -> Value
restrictionValue evidence =
  let reference (identity, target) = object ["id" .= identity, "target" .= target]
      source = restrictionSource evidence
   in object $
        [ "kind" .= restrictionKind evidence
        , "generatorOffset" .= restrictionOffset evidence
        , "premise" .= restrictionPremise evidence
        , "source" .= object ["start" .= spanStart source, "end" .= spanEnd source, "text" .= restrictionText evidence]
        ]
          <> [K.fromText role .= reference binding | (role, binding) <- restrictionReferences evidence]
          <> [K.fromText role .= locatedValue syntax | (role, syntax) <- restrictionSyntax evidence]

data SourceDerivation
  = SharedOperand Text Int
  | ExpandedNotation Text
  | WitnessedOperation Text Text
  | SourceInterpretation Text
  deriving (Eq, Show, Data)

derivationValue :: SourceDerivation -> Value
derivationValue (SharedOperand kind index) = object ["kind" .= kind, "member" .= index]
derivationValue (ExpandedNotation kind) = String kind
derivationValue (WitnessedOperation kind witness) = object ["kind" .= kind, "witness" .= witness]
derivationValue (SourceInterpretation kind) = object ["kind" .= kind]

annotateRoot :: SourceDerivation -> [Value] -> [Value]
annotateRoot origin values = case reverse values of
  Object fields : previous -> reverse (Object (KM.insert "lowering" (derivationValue origin) fields) : previous)
  _ -> values
