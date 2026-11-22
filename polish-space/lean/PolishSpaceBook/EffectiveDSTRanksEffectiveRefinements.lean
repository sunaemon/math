module

public import PolishSpaceBook.LambdaFinitePowerRepresentations
public import PolishSpaceBook.LambdaWellFoundedCompleteness
public import PolishSpaceBook.LambdaSeparationIteration
public import PolishSpaceBook.EffectiveRankProse
public import PolishSpaceBook.LambdaLusinSuslinImages
public import PolishSpaceBook.LambdaRankComparisons
public import PolishSpaceBook.LambdaEffectiveBoundedness
public import PolishSpaceBook.LambdaBorelCodeCompleteness
public import PolishSpaceBook.LambdaRankLabelComputation
public import PolishSpaceBook.BorelRankLabels
public import PolishSpaceBook.LambdaBorelConstructors
public import PolishSpaceBook.LambdaArithmeticNormalForm
public import PolishSpaceBook.LambdaBorelIndexValidity
public import PolishSpaceBook.LambdaBaireQuantifiers
public import PolishSpaceBook.LambdaBorelSyntax
public import PolishSpaceBook.LambdaProgramTotality
public import PolishSpaceBook.LambdaBairePreimages
public import PolishSpaceBook.LambdaBorelEvaluation
public import PolishSpaceBook.LambdaHKLFusion
public import PolishSpaceBook.LambdaKernelComplexity
public import PolishSpaceBook.LambdaEffectiveSeparation
public import PolishSpaceBook.LambdaCatalogProjections
public import PolishSpaceBook.WellFoundedRankMaps
public import PolishSpaceBook.EffectiveDSTLightfaceHierarchies
public import PolishSpaceBook.EffectiveClosedTreeRepresentation
public import PolishSpaceBook.BorelExpressionValidity
public import PolishSpaceBook.LambdaKernelConditions
public import PolishSpaceBook.LambdaTreeRefinement
public import PolishSpaceBook.LambdaCatalogTreeRefinement
public import PolishSpaceBook.LambdaHKLRefinement
public import PolishSpaceBook.LambdaHKLComponents
public import PolishSpaceBook.LambdaHKLStages
public import PolishSpaceBook.LambdaHKLLevels
public import PolishSpaceBook.LambdaHKLScheduling
public import PolishSpaceBook.LambdaGenericTests
public import PolishSpaceBook.LambdaHKLCommonRight
public import PolishSpaceBook.LambdaHKLSplitting
public import PolishSpaceBook.LambdaGenericFilters
public import PolishSpaceBook.LambdaRectangleFilters
public import PolishSpaceBook.LambdaGenericFilterConstruction
public import PolishSpaceBook.BorelForcingTruth
public import PolishSpaceBook.LambdaBorelTruth
public import PolishSpaceBook.LambdaHKLDichotomy
public import PolishSpaceBook.HKLPolishTransport
public import PolishSpaceBook.ZeroDimensionalClosedPresentation
public import PolishSpaceBook.ZeroDimensionalPolishRefinement
public import PolishSpaceBook.LambdaCoanalyticTruth
public import PolishSpaceBook.EquivalenceRelationSeparation
public import PolishSpaceBook.HKLCrucialPairs
public import PolishSpaceBook.HKLTreeRefinement
public import PolishSpaceBook.HKLDenseRefinements
public import PolishSpaceBook.HKLCompatibleRefinements
public import PolishSpaceBook.HKLLevelConstruction
public import PolishSpaceBook.AnalyticConditionFusion
public import PolishSpaceBook.HKLBranchFusion
public import PolishSpaceBook.HKLEdgeFusion
public import PolishSpaceBook.HKLDenseScheduling
public import PolishSpaceBook.SilverFusion
public import PolishSpaceBook.AnalyticConditionCatalog
public import PolishSpaceBook.AnalyticCatalogConstruction
public import PolishSpaceBook.AnalyticFusionDiameter
public import PolishSpaceBook.SilverKernel
public import PolishSpaceBook.HKLKernel

@[expose] public section

/-!
# Effective descriptive set theory: ranks and refinements

The canonical computational infrastructure is the closed lambda calculus.
`LambdaRelativePredicates`, `LambdaPairTrees`, and `LambdaAnalyticCatalog`
construct relative decision programs, tree presentations, and the countable
condition order. `LambdaFinitePowerConditions` constructs recursive finite-power
codes, coordinate programs, and closed presentations with refinements.
`LambdaFinitePowerRepresentations` builds the actual product representations
and countable inclusion orders on represented sets, retaining pair correlations.
`LambdaIndexedOperations` and `LambdaEffectiveSeparation`
supply the numerical index transformations used by separation and saturation.
`LambdaBoundedPrefixTests` and `LambdaBorelEvaluation` turn finite evaluation
certificates into two tree presentations at the original parameter; their
label programs and word coding use the same calculus.

`LambdaKernelComplexity`, `LambdaInvariantClosure`, and `LambdaKernelConditions`
construct the Silver and HKL kernels and hereditary failure. The Silver proof
uses the countable GH basis and coanalytic local truth in `LambdaGHTopology`
and `LambdaCoanalyticTruth`. The HKL proof uses exact finite-tree refinements,
node/edge fusion, and restricted-product Borel truth in the `LambdaHKL`
modules and `LambdaBorelTruth`. `SilverDichotomy` and `HKLPolishTransport`
transfer these constructions to general Polish spaces. The actual generic
points are obtained by witness fusion, without set-theoretic generic extensions.
Shared tree, saturation, order-filter, and Borel-code arguments remain in
model-independent geometric modules.

`LambdaBorelCodeCompleteness` proves recursive Borel separation and
completeness via the joint-tree rank bound and the rank-label programs.
`LambdaEffectiveBoundedness` constructs a single recursive well-order bound
for analytic families of well-founded trees, preserving the parameter.
`LambdaWellFoundedCompleteness` constructs the continuous, lambda-computed
section-code reductions to the well-founded tree codes.
`LambdaSeparationIteration` constructs jointly decidable separator families
from recursive state updates preserving disjointness.
`LambdaRankComparisons` supplies the starred comparisons, countability of
section ranks, Borel layers, and bounded Borel layers for analytic subfamilies.
`EffectiveRankProse` packages the general and effective coanalytic-norm
definitions and realizes them with the actual section-tree ranks.
`LambdaLusinSuslinImages` constructs uniform indices for images and inverse
prefix images from the supplied map and closed-domain indices.
`LambdaKleeneNotations` and `LambdaIteratedJump` implement ordinal notations
and their jump hierarchy. The coverage audit and `todo.md` track the remaining
passage-level correspondence and proof work. Kondo--Addison and
Spector--Gandy remain explicitly cited external inputs. Completing the
Silver/HKL constructions does not discharge these separate obligations.
-/
