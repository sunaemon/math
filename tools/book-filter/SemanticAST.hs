{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}

{- | Shared semantic types. No JSON encoding, source recognizers, chapter
defaults or rendering logic belongs in this module. Interpretation plans
carry explicit types and registered Lean realizers selected by mapping rules.
-}
module SemanticAST (
  Expr (..),
  Operation (..),
  Arithmetic (..),
  Comparison (..),
  BindingIdentity (..),
  ReferenceAdaptation (..),
  IndexKind (..),
  NameDecoration (..),
  MetricDomain (..),
  MetricEvaluation (..),
  SetOperator (..),
  Binder (..),
  BinderNotation (..),
  UpperRayKind (..),
  CoordinateKind (..),
  FamilyBinding (..),
  FamilyNotation (..),
  FamilyCarrier (..),
  SetAggregation (..),
  SubspaceNotation (..),
  SequenceWitness (..),
  SummationKind (..),
  DistanceKind (..),
  BoundBodyKind (..),
  NumericDomain (..),
  LiteralEvidence (..),
  LiteralRule (..),
  CoercionRule (..),
  LambdaRule (..),
  AggregationRule (..),
  ConditionalRule (..),
  SectionRule (..),
  LiteralConsumer (..),
  FamilyRange (..),
  BinaryOperation (..),
  FoldGrouping (..),
  FoldPlan (..),
  foldPlan,
  AmbientEvidence (..),
  RestrictionEvidence (..),
) where

import Data.Data (Data)
import Data.Text (Text)
import LocatedMath (LocatedMath, SourceSpan)
import SemanticTrace (RestrictionEvidence (..), SourceDerivation)

-- Operands have a fixed order and arity in the type, including ambient carriers.
data Operation a
  = Difference a a
  | Fraction a a
  | Absolute a
  | Closure a
  | AmbientClosure a a
  | Ball a a
  | ClosedInterval a a
  | OpenInterval a a
  | LeftClosedInterval a a
  deriving (Eq, Show, Functor, Foldable, Traversable, Data)

-- ExplicitLean is a migration boundary for already constructed operand text,
-- not a claim that the remaining Python interpreter has a semantic AST.
data Expr
  = ExplicitLean Text
  | Macro (Maybe SourceSpan) (Operation Expr)
  | Reference SourceSpan BindingIdentity
  | Literal SourceSpan SourceSpan LiteralEvidence Text
  | Scoped SourceSpan Expr
  | Parenthesized SourceSpan Expr
  | Scalar SourceSpan SourceSpan Arithmetic Expr Expr
  | Compare SourceSpan SourceSpan Comparison Expr Expr
  | Derived SourceDerivation Expr
  | Comparisons [Expr]
  | Negate SourceSpan SourceSpan Expr
  | Index SourceSpan SourceSpan IndexKind Expr Expr
  | ShiftIndex SourceSpan Integer Expr
  | NamedReference SourceSpan SourceSpan NameDecoration BindingIdentity
  | Application SourceSpan SourceSpan BindingIdentity Expr [Expr]
  | MetricApplication SourceSpan SourceSpan MetricDomain MetricEvaluation (Maybe Text) Expr Expr Expr
  | SubtypeRange SourceSpan SourceSpan Text Expr Expr
  | SubtypeApplication SourceSpan SourceSpan BindingIdentity Expr Expr
  | UniversalSet SourceSpan Expr
  | SetExpression SourceSpan SourceSpan SetOperator Expr Expr
  | SourceConstant SourceSpan Text
  | RationalImage SourceSpan
  | EmbeddedRationalComplement SourceSpan SourceSpan Expr Expr
  | BinaryAlphabet SourceSpan
  | Lambda SourceSpan SourceSpan Binder Expr
  | DefiningEquality SourceSpan SourceSpan Expr Expr
  | EmptySet SourceSpan Expr
  | UpperRay SourceSpan SourceSpan UpperRayKind Expr SourceSpan
  | IntegerCast SourceSpan Expr
  | IntegerNegate SourceSpan SourceSpan Expr
  | RealIntegerPower SourceSpan SourceSpan Expr Expr
  | ExtendedTop SourceSpan
  | RealSequenceSpace SourceSpan SourceSpan SourceSpan Expr
  | FunctionType SourceSpan SourceSpan Text Expr Expr
  | TypeDeclaration SourceSpan SourceSpan Expr Expr
  | HomeomorphismType SourceSpan SourceSpan Expr Expr
  | NonemptyType SourceSpan SourceSpan Expr
  | FiniteIndex SourceSpan Expr
  | CoordinateSpace SourceSpan SourceSpan CoordinateKind Expr Expr
  | BinarySequenceAlphabet SourceSpan SourceSpan (Maybe Text)
  | SubtypeType SourceSpan SourceSpan SubspaceNotation Expr
  | TypedMapForall SourceSpan SourceSpan BindingIdentity Expr Expr
  | MultipleCalls Expr
  | FamilyLambda SourceSpan SourceSpan FamilyBinding Expr
  | DependentSum SourceSpan SourceSpan Expr
  | IndexedSet SourceSpan SourceSpan SetAggregation (Maybe Text) Expr
  | RepeatedTuple SourceSpan SourceSpan Expr [Expr]
  | ConvergenceSequence SourceSpan SequenceWitness Expr
  | SequenceConvergence SourceSpan SourceSpan [(SourceSpan, Text)] (Maybe Integer) Expr Expr
  | SumFunction SourceSpan BindingIdentity (Maybe Expr) Expr
  | Summation SourceSpan SourceSpan [(SourceSpan, Text)] SummationKind (Maybe Expr) Expr
  | ImplicitMultiply SourceSpan SourceSpan Expr Expr
  | RealScalar SourceSpan Expr
  | AmbientSetClosure SourceSpan Expr Expr
  | ExplicitMetricBall SourceSpan MetricDomain (Maybe Text) Expr Expr Expr
  | ExplicitMetricDiameter SourceSpan MetricDomain Expr Expr
  | DistanceFunction SourceSpan DistanceKind Expr
  | Restriction SourceSpan Expr Expr
  | Composition SourceSpan SourceSpan Expr Expr
  | PointwiseComparison SourceSpan SourceSpan DistanceKind Expr Expr Expr
  | BoundFunction SourceSpan BoundBodyKind BindingIdentity Expr
  | SetComprehension SourceSpan SourceSpan [(SourceSpan, Text)] BindingIdentity (Maybe Expr) Expr
  | ImageSet SourceSpan SourceSpan [(SourceSpan, Text)] Expr Expr
  | Infimum SourceSpan SourceSpan Expr
  | RepeatedEvaluation Expr
  | CaseBranch SourceSpan SourceSpan Text Text Expr Expr
  | DependentConditional SourceSpan SourceSpan ConditionalRule Expr Expr Expr
  | SigmaPair SourceSpan Text Expr Expr
  | OperatorSection SourceSpan SourceSpan SectionRule Text NumericDomain Expr
  | ContextualLiteral SourceSpan SourceSpan Text Text LiteralConsumer Text
  | Conjunction SourceSpan SourceSpan Expr Expr
  | SingletonSet SourceSpan SourceSpan SourceSpan (Maybe Text) Expr
  | PropositionPair Expr Expr
  | MembershipEquality SourceSpan SourceSpan Expr Expr Expr
  | InclusionMap SourceSpan SourceSpan Expr Expr
  | RangeFamily SourceSpan Text BindingIdentity FamilyRange
  | DecreasingFamily SourceSpan SourceSpan [(SourceSpan, Text)] Integer Integer Expr
  | RepeatedBinary SourceSpan SourceSpan [(SourceSpan, Text)] BindingIdentity FamilyRange FoldPlan Expr
  | CoercionFunction SourceSpan CoercionRule
  | TypedRange SourceSpan CoercionRule Expr
  | Coerce SourceSpan CoercionRule Expr
  | TypedLambda SourceSpan LambdaRule BindingIdentity [LocatedMath] SourceSpan Expr
  | Aggregate SourceSpan AggregationRule AmbientEvidence Expr
  | SetIdentity SourceSpan SourceSpan Expr Expr
  | MetricBoundedSet SourceSpan Expr Expr
  | ExistentialSetPredicate SourceSpan Text Expr [(Text, Expr)] Expr Expr
  | GuardedSet SourceSpan SourceSpan [(SourceSpan, Text)] Expr RestrictionEvidence Expr
  | GeneratedUnion SourceSpan SourceSpan Expr RestrictionEvidence Expr
  deriving (Eq, Show, Data)

-- Rules describe elaboration parameters; no source recognizer belongs here.
data CoercionRule = CoercionRule
  { coercionSource :: Text
  , coercionSourceDisplay :: Text
  , coercionTarget :: Text
  , coercionTargetDisplay :: Text
  , coercionHead :: Text
  , coercionClass :: Text
  , coercionTraceRule :: Text
  , coercionRangeRule :: Text
  }
  deriving (Eq, Show, Data)

data LambdaRule = LambdaRule
  { lambdaDomain :: Text
  , lambdaResult :: Text
  }
  deriving (Eq, Show, Data)

data AggregationRule = AggregationRule
  { aggregationIndex :: Text
  , aggregationHead :: Text
  , aggregationLattice :: Text
  , aggregationTraceRule :: Text
  }
  deriving (Eq, Show, Data)

data ConditionalRule = ConditionalRule
  { conditionalResult :: Text
  , conditionalTraceRule :: Text
  }
  deriving (Eq, Show, Data)

-- A typed operator section introduces one implicit source argument. Its
-- domain, realizer and trace roles come from an explicit notation rule.
data SectionRule = SectionRule
  { sectionComparison :: Comparison
  , sectionDomain :: Text
  , sectionHead :: Text
  , sectionTraceRule :: Text
  , sectionBinderRule :: Text
  , sectionOperandRole :: Text
  , sectionTypeRole :: Text
  , sectionOrderRole :: Text
  , sectionOrderClass :: Text
  , sectionLowering :: Text
  }
  deriving (Eq, Show, Data)

data SubspaceNotation = ExplicitSubspace | SetAsSubspace
  deriving (Eq, Show, Data)

data SequenceWitness = SequenceWitness BindingIdentity Expr
  deriving (Eq, Show, Data)

data SummationKind = FiniteSum | InfiniteSum | TailSum
  deriving (Eq, Show, Data)

data DistanceKind = MetricDistance MetricDomain | BinaryDistance Text
  deriving (Eq, Show, Data)

data BoundBodyKind = PredicateBody | ImageBody
  deriving (Eq, Show, Data)

data NumericDomain = NumericDomain
  { numericType :: Text
  , numericTarget :: Text
  , numericBinding :: Maybe Text
  , numericContext :: Text
  , numericWitness :: Maybe Text
  }
  deriving (Eq, Show, Data)

-- The value of a literal is independent of the evidence selecting its type.
-- Witness and sequence cases keep the original context rather than inferring
-- a domain from the generated Lean term.
data LiteralEvidence
  = InferredLiteral
  | FixedLiteral Text
  | InstanceLiteral LiteralRule
  | SourceLiteral LiteralRule SourceSpan SourceDerivation
  | WitnessLiteral NumericDomain
  | SequenceLiteral SequenceWitness
  deriving (Eq, Show, Data)

data LiteralRule = LiteralRule
  { literalDomain :: Text
  , literalTraceRule :: Text
  , literalTypeRole :: Text
  , literalInstanceRole :: Text
  }
  deriving (Eq, Show, Data)

data LiteralConsumer = LiteralConsumer Text Text Int
  deriving (Eq, Show, Data)

data FamilyRange = NaturalTail Integer Integer | FiniteNaturalInterval Integer Integer Expr
  deriving (Eq, Show, Data)

data BinaryOperation = SetBinary SetOperator | ScalarBinary Arithmetic
  deriving (Eq, Show, Data)

data FoldGrouping = AssociativeFold | LeftFold | RightFold
  deriving (Eq, Show, Data)

-- A mapping rule must select the binary operation, grouping and Lean realizer
-- together. An ellipsis alone cannot authorize associativity or an empty fold.
data FoldPlan = FoldPlan BinaryOperation FoldGrouping Text Text Text
  deriving (Eq, Show, Data)

foldPlan :: BinaryOperation -> FoldGrouping -> Either String FoldPlan
foldPlan binary grouping = case (binary, grouping) of
  (SetBinary Intersection, AssociativeFold) -> Right (FoldPlan binary grouping "iInf" "set:indexed-intersection" "InfSet")
  (SetBinary Union, AssociativeFold) -> Right (FoldPlan binary grouping "iSup" "set:indexed-union" "SupSet")
  _ -> Left "Repeated binary operator needs an explicit registered fold rule and grouping"

data AmbientEvidence = AmbientEvidence Text Text SourceSpan
  deriving (Eq, Show, Data)

data FamilyNotation = ProductFamily | FunctionFamily
  deriving (Eq, Show, Data)

data FamilyCarrier = DirectCarrier Expr | IndexedPredicateCarrier Expr
  deriving (Eq, Show, Data)

data SetAggregation = IndexedIntersection | IndexedUnion
  deriving (Eq, Show, Data)

data FamilyBinding = FamilyBinding
  { familyNotation :: FamilyNotation
  , familyIdentity :: BindingIdentity
  , familyDomain :: Text
  , familyDomainName :: Maybe Text
  , familyComponents :: [(SourceSpan, Text)]
  , familyCarrier :: Maybe FamilyCarrier
  , familyMultipleCalls :: Bool
  }
  deriving (Eq, Show, Data)

data Arithmetic = Add | Subtract | Multiply | Divide
  deriving (Eq, Show, Data)

data Comparison = Equal | Unequal | Less | AtMost | Greater | AtLeast
  deriving (Eq, Show, Data)

data BindingIdentity = BindingIdentity
  { bindingSourceId :: Text
  , bindingContext :: Maybe Text
  , bindingName :: Text
  , bindingType :: Text
  , bindingConstant :: Maybe Text
  , bindingAdaptation :: ReferenceAdaptation
  , bindingIndexOrigin :: Maybe Integer
  , bindingIndexLowerBound :: Maybe Integer
  , bindingOccurrenceSelector :: Maybe Text
  , bindingNamedSubscript :: Bool
  , bindingSourceSymbol :: Maybe Text
  , bindingSourceWidth :: Maybe Int
  , bindingLocalBinder :: Bool
  , bindingBinderContext :: Maybe Text
  , bindingRole :: Maybe Text
  }
  deriving (Eq, Show, Data)

-- A view of the same source binder; its lexical/context identity is unchanged.
data ReferenceAdaptation = DirectReference | SubtypeValue | NaturalOffset Integer
  deriving (Eq, Show, Data)

data IndexKind = Subscript | Superscript
  deriving (Eq, Show, Data)

data NameDecoration = SubscriptName | StarredName
  deriving (Eq, Show, Data)

data MetricEvaluation = PointDistance | SetDistance
  deriving (Eq, Show, Data)

data MetricDomain = SourceMetricCarrier Text | AppliedMetricCarrier
  deriving (Eq, Show, Data)

data SetOperator = Member | Included | Intersection | Union | Product | DifferenceSet | EqualSet | UnequalSet
  deriving (Eq, Show, Data)

data UpperRayKind = OpenUpperRay | ClosedUpperRay
  deriving (Eq, Show, Data)

data CoordinateKind = FiniteCoordinates | IndexedCoordinates
  deriving (Eq, Show, Data)

data BinderNotation = SequenceBinder | MapstoBinder
  deriving (Eq, Show, Data)

data Binder = Binder
  { binderNotation :: BinderNotation
  , binderIdentity :: BindingIdentity
  , binderDomain :: Text
  , binderDomainSpan :: Maybe SourceSpan
  , binderContext :: Maybe Text
  , binderComponents :: [(SourceSpan, Text)]
  , binderIndexOrigin :: Integer
  }
  deriving (Eq, Show, Data)
