{-# LANGUAGE OverloadedStrings #-}

module SemanticExprTests (semanticExprFailures) where

import Data.Aeson (Value (..))
import qualified Data.Aeson.KeyMap as KM
import Data.Either (isLeft)
import qualified Data.Map.Strict as Map
import LocatedMath (SourceSpan (..))
import SemanticExpr
import SemanticTrace (SourceDerivation (..))

semanticExprFailures :: [String]
semanticExprFailures =
  ["recursive semantic lowering changed operand order" | renderCandidate proposed /= "((|x|) / (y))"]
    <> ["stale source approved" | not (isLeft (review basis (basis{sourceFingerprint = "changed"}) proposed))]
    <> ["stale rules approved" | not (isLeft (review basis (basis{rulesFingerprint = "changed"}) proposed))]
    <> ["missing Lean evidence approved" | not (isLeft (review basis (basis{leanFingerprints = Map.empty}) proposed))]
    <> ["review changed the semantic expression" | either (const True) ((/= "((|x|) / (y))") . renderReviewed) (review basis basis proposed)]
    <> ["wrong operation arity accepted" | not (isLeft (operation "Ball" [ExplicitLean "x"]))]
    <> ["subtraction ellipsis guessed associativity" | not (isLeft (foldPlan (ScalarBinary Subtract) AssociativeFold))]
    <> ["intersection silently changed grouping" | not (isLeft (foldPlan (SetBinary Intersection) LeftFold))]
    <> ["registered intersection fold missing" | isLeft (foldPlan (SetBinary Intersection) AssociativeFold)]
    <> ["registered union fold missing" | isLeft (foldPlan (SetBinary Union) AssociativeFold)]
    <> ["coercion kept the rational/real default" | render coercion /= "(Int.ofNat (2) : ℤ)"]
    <> ["coercion function lost its explicit domain" | render (CoercionFunction source natInt) /= "((↑) : Nat → ℤ)"]
    <> ["range kept the real ambient" | render (TypedRange source natInt (CoercionFunction source natInt)) /= "(Set.range (((↑) : Nat → ℤ)) : Set ℤ)"]
    <> ["conditional kept a real result type" | render boolCases /= "(@dite Bool (True) (Classical.propDecidable _) ((fun «h» : (True) => (true : Bool))) ((fun «h» : (True) => (false : Bool))))"]
    <> ["typed numeral kept the ENNReal domain" | render naturalLiteral /= "(2 : Nat)"]
    <> ["source derivation changed the mathematical expression" | ordinaryTerm annotated /= ordinaryTerm unannotated || instrumentedTerm annotated /= instrumentedTerm unannotated]
    <> ["source derivation changed operator evidence" | stripOrigin (operatorTraces annotated) /= operatorTraces unannotated]
    <> ["source derivation lost its root evidence" | lastOrigin (operatorTraces annotated) /= Just (String "explicit-list")]
    <> ["operator section kept a real/radius default" | render naturalSection /= "(fun «n» : Nat => («n» ≤ ((2 : Nat))))"]
 where
  basis = ReviewBasis "source" "rules" (Map.singleton "D" "body")
  proposed = candidate (Macro Nothing (Fraction (Macro Nothing (Absolute (ExplicitLean "x"))) (ExplicitLean "y")))
  source = SourceSpan 0 1
  render = renderCandidate . candidate
  natInt = CoercionRule "Nat" "Nat" "Int" "ℤ" "Int.ofNat" "NatCast" "coercion:nat-int" "set:natural-image"
  coercion = Coerce source natInt (Literal source source InferredLiteral "2")
  boolCases = DependentConditional source source (ConditionalRule "Bool" "cases:bool") (ExplicitLean "True") (branch "true") (branch "false")
  branch value = CaseBranch source source "h" "Bool" (ExplicitLean "True") (ExplicitLean value)
  naturalLiteral = Literal source source (InstanceLiteral (LiteralRule "Nat" "literal:natural" "domain" "instance")) "2"
  comparison = Compare source source Less coercion naturalLiteral
  unannotated = renderPair [] 0 (candidate comparison)
  annotated = renderPair [] 0 (candidate (Derived (ExpandedNotation "explicit-list") comparison))
  stripOrigin values = case reverse values of
    Object fields : previous -> reverse (Object (KM.delete "lowering" fields) : previous)
    _ -> values
  lastOrigin values = case reverse values of Object fields : _ -> KM.lookup "lowering" fields; _ -> Nothing
  naturalSection = OperatorSection source source (SectionRule AtMost "Nat" "LE.le" "predicate:≤" "binder:section" "implicit-argument" "domain" "order" "LE" "typed-section") "n" (NumericDomain "Nat" "D/n" Nothing "D" (Just "n")) naturalLiteral
