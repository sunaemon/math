{-# LANGUAGE OverloadedStrings #-}

{- | Explicit realizers selected by the Polish Spaces source recognizers.
Common AST/rendering code must not decide that an index is rational, a
conditional is real-valued, or a shared source operand denotes membership.
-}
module ChapterMappingRules (
  rationalReal,
  rationalSingletonFamily,
  rationalUnion,
  realConditional,
  sharedMembership,
  listedComparison,
  realScalarComparison,
  radiusSection,
  extendedNumeral,
  dimensionNumeral,
  dimensionOrigin,
) where

import SemanticAST (AggregationRule (..), CoercionRule (..), Comparison (..), ConditionalRule (..), LambdaRule (..), LiteralRule (..), SectionRule (..))
import SemanticTrace (SourceDerivation (..))

rationalReal :: CoercionRule
rationalReal = CoercionRule "Rat" "ℚ" "Real" "ℝ" "Rat.cast" "RatCast" "coercion:rational-real" "set:embedded-rationals"

rationalSingletonFamily :: LambdaRule
rationalSingletonFamily = LambdaRule "Rat" "Set Real"

rationalUnion :: AggregationRule
rationalUnion = AggregationRule "Rat" "iSup" "SupSet" "set:indexed-union"

realConditional :: ConditionalRule
realConditional = ConditionalRule "ℝ" "cases:real"

sharedMembership :: Int -> SourceDerivation
sharedMembership = SharedOperand "shared-membership-domain"

listedComparison :: SourceDerivation
listedComparison = ExpandedNotation "variable-list-conjunction"

realScalarComparison :: SourceDerivation
realScalarComparison = WitnessedOperation "real-scalar-comparison" "MetricDiameter"

radiusSection :: SectionRule
radiusSection = SectionRule Less "Real" "LT.lt" "predicate:<" "binder:radius" "implicit-radius" "radius-type" "radius-order" "LT" "implicit-radius-predicate"

extendedNumeral :: LiteralRule
extendedNumeral = LiteralRule "ENNReal" "literal:ennreal-numeral" "exponent-type" "exponent-numeral"

dimensionNumeral :: LiteralRule
dimensionNumeral = LiteralRule "Nat" "literal:dimension-level" "nonnegative-dimension-level-type" "dimension-level-numeral"

dimensionOrigin :: SourceDerivation
dimensionOrigin = SourceInterpretation "nonnegative-dimension-level"
