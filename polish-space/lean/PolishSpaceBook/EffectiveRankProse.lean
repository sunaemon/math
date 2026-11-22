module

public import PolishSpaceBook.LambdaRankComparisons
public import PolishSpaceBook.BorelOrdinalRankLayers
public import PolishSpaceBook.LusinRankSeparation

@[expose] public section

namespace PolishSpaceBook
open Set MeasureTheory LambdaTree

/-- Agreement is required on the whole left ambient space, with only the
right argument restricted to the coanalytic domain. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Agreement is required only when the right-hand
    parameter lies in $A$;
-/
def NormComparison (A : Set (ℕ → ℕ)) (value : A → Ordinal)
    (r : Ordinal → Ordinal → Prop) (R : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  ∀ y (hy : y ∈ A) x, R x y ↔ ∃ hx : x ∈ A, r (value ⟨x, hx⟩) (value ⟨y, hy⟩)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    A \termdefine{coanalytic norm} on a $\bPi^1_1$ set $A\IncludedIn\BaireSpace$ is an ordinal-valued map
    $\varphi:A\to\omegaOneOrd$ whose initial segments
    $$
    A_{\le\alpha}:=\{x\in A:\varphi(x)\le\alpha\}
    $$
    are Borel and whose comparisons admit starred analytic and coanalytic extensions. Thus there are relations
    $\leq_\Sigma,\leq_\Pi$ on the ambient space such that, for every fixed $y\in A$,
    $$
    x\leq_\Sigma y
    \quad\Longleftrightarrow\quad
    x\leq_\Pi y
    \quad\Longleftrightarrow\quad
    x\in A\text{ and }\varphi(x)\leq\varphi(y),
    $$
    with $\leq_\Sigma$ in $\bSigma^1_1$ and $\leq_\Pi$ in $\bPi^1_1$.
-/
/-- A coanalytic norm, including Borel layers and both starred comparisons.
Ambient pairs use the chapter's entrywise pairing of Baire sequences. -/
structure CoanalyticNorm (A : Set (ℕ → ℕ)) where
  coanalytic : AnalyticSet Aᶜ
  value : A → Ordinal
  countable_value : ∀ x, value x < Ordinal.omega 1
  borel_layer : ∀ α < Ordinal.omega 1,
    MeasurableSet {x | ∃ hx : x ∈ A, value ⟨x, hx⟩ ≤ α}
  leSigma : (ℕ → ℕ) → (ℕ → ℕ) → Prop
  lePi : (ℕ → ℕ) → (ℕ → ℕ) → Prop
  ltSigma : (ℕ → ℕ) → (ℕ → ℕ) → Prop
  ltPi : (ℕ → ℕ) → (ℕ → ℕ) → Prop
  analytic_le : AnalyticSet {p | leSigma (leftBaire p) (rightBaire p)}
  coanalytic_le : AnalyticSet {p | ¬ lePi (leftBaire p) (rightBaire p)}
  analytic_lt : AnalyticSet {p | ltSigma (leftBaire p) (rightBaire p)}
  coanalytic_lt : AnalyticSet {p | ¬ ltPi (leftBaire p) (rightBaire p)}
  leSigma_spec : NormComparison A value (· ≤ ·) leSigma
  lePi_spec : NormComparison A value (· ≤ ·) lePi
  ltSigma_spec : NormComparison A value (· < ·) ltSigma
  ltPi_spec : NormComparison A value (· < ·) ltPi

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Analogous starred relations represent strict comparison.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For a fixed $\varepsilon$, the effective version requires $A$ to be $\lPi^1_1(\varepsilon)$ and the two
    comparison extensions to be $\lSigma^1_1(\varepsilon)$ and $\lPi^1_1(\varepsilon)$, respectively.
-/
/-- All domain and comparison presentations retain the same real parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Let $A \IncludedIn X$ be $\lPi^1_1$. A \termdefineas{lightface Pi11 rank}{$\lPi^1_1$ rank} on $A$ is a map
    $$\varphi:A\to\omegaOneOrd$$
    such that, for each countable ordinal $\alpha$, the section
    $$A_{\le\alpha}:=\{x\in A:\varphi(x)\le\alpha\}$$
    is Borel. In addition, there are starred relations $\leq_\Sigma$ in $\lSigma^1_1$ and $\leq_\Pi$ in $\lPi^1_1$ such
    that, whenever $y\in A$,
    $$
    x\leq_\Sigma y
    \quad\Longleftrightarrow\quad
    x\leq_\Pi y
    \quad\Longleftrightarrow\quad
    x\in A\text{ and }\varphi(x)\leq\varphi(y),
    $$
    and similarly for strict comparison.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    The rank background for \termuse{Silver's dichotomy} in §{sec:silver-dichotomy} is supplied by
    \termdefineas{coanalytic rank}{coanalytic ranks}. These are ordinal-valued measurements on
    $\lPi^1_1$ sets whose initial segments are Borel in a uniform way.
-/
structure EffectiveCoanalyticNorm (ε : ℕ → ℕ) (A : Set (ℕ → ℕ))
    extends CoanalyticNorm A where
  domain_projected : Projected ε Aᶜ
  le_projected : ProjectedRelation ε leSigma
  le_complement_projected : ProjectedRelation ε (fun x y => ¬ lePi x y)
  lt_projected : ProjectedRelation ε ltSigma
  lt_complement_projected : ProjectedRelation ε (fun x y => ¬ ltPi x y)

/-- The section-tree rank is an actual instance, rather than an assumed norm
specification supplied to later boundedness arguments. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    We construct this stronger version for tree ranks below.
-/
noncomputable def treeRankNorm {ε : ℕ → ℕ} (T : PairTree ε) :
    EffectiveCoanalyticNorm ε (sectionDomain T) where
  coanalytic := by
    rw [sectionDomain_complement]
    exact (show Projected ε (pairTreeProjection T.tree) from ⟨T, rfl⟩).analyticSet
  value := fun x => sectionRank T x.val x.property
  countable_value := fun x => sectionRank_countable T x.val x.property
  borel_layer := fun α hα => sectionRankLayer_measurable T α hα
  leSigma := sectionLe T
  lePi := sectionLePi T
  ltSigma := sectionLt T
  ltPi := sectionLtPi T
  analytic_le := (sectionLe_projected T).analyticSet
  coanalytic_le := (sectionLePi_complement_projected T).analyticSet
  analytic_lt := (sectionLt_projected T).analyticSet
  coanalytic_lt := (sectionLtPi_complement_projected T).analyticSet
  leSigma_spec := fun y hy x => sectionLe_iff_rank T x y hy
  lePi_spec := fun y hy x =>
    (sectionLe_agreement T x y hy).symm.trans (sectionLe_iff_rank T x y hy)
  ltSigma_spec := fun y hy x => sectionLt_iff_rank T x y hy
  ltPi_spec := fun y hy x =>
    (sectionLt_agreement T x y hy).symm.trans (sectionLt_iff_rank T x y hy)
  domain_projected := by rw [sectionDomain_complement]; exact ⟨T, rfl⟩
  le_projected := sectionLe_projected T
  le_complement_projected := sectionLePi_complement_projected T
  lt_projected := sectionLt_projected T
  lt_complement_projected := sectionLtPi_complement_projected T

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The same recursion gives a precise local computation step. Fix $x$ and $a$, and write
    $$L_a(t,b)\quad\Longleftrightarrow\quad R(b,a)\mathbin{\wedge}x\in\RankLayer{b}{t}.$$
-/
/-- The lower-stage truth predicate retains both the predecessor test and
local accessibility; it does not assign ranks above an infinite chain. -/
def LowerRankTruth (R : ℕ → ℕ → Prop) (hR : WellFounded R)
    (E : (ℕ → ℕ) → ℕ → ℕ → Prop) (x : ℕ → ℕ) (a t b : ℕ) : Prop :=
  R b a ∧ OrdinalRankLayer.Holds (E x) (hR.apply b).rank t

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For a well-founded rooted tree $T$, write $\rho_T(t)$ for the rank of its node $t$ under strict extension,
    and put $\rho(T):=\rho_T(\emptySeq)$. Thus terminal nodes have rank zero. The countability argument in
    §{sec:borel-codes-rank} shows $\rho(T)<\omegaOneOrd$ for every individual tree.
-/
/-- The strict-extension root rank is countable, and a terminal root has rank zero. -/
theorem rootRank_spec (T : RootedPrefixTree)
    (hT : WellFounded (strictTreeExtension T.tree)) :
    (hT.apply T.root).rank < Ordinal.omega 1 ∧
      ((∀ t, ¬ strictTreeExtension T.tree t T.root) → (hT.apply T.root).rank = 0) := by
  refine ⟨T.root_rank_countable hT, ?_⟩
  intro hterminal
  rw [Acc.rank_eq]
  apply le_antisymm
  · apply Ordinal.iSup_le
    rintro ⟨t, ht⟩
    exact (hterminal t ht).elim
  · exact bot_le

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For a specified countable family of downward-closed dense sets, call a point generic when it belongs to a condition
    from each set in the family. The same convention applies to pairs and rectangle conditions.
-/
/-- Genericity for specified tests means actual membership in a condition
from each test. A carrier can describe points, coded pairs, or rectangles. -/
def PointGeneric {X C : Type*} (carrier : C → Set X)
    (tests : Set (Set C)) (x : X) : Prop :=
  ∀ D ∈ tests, ∃ q ∈ D, x ∈ carrier q

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    whereas arbitrary Borel maps preserve Borel
    measurability under preimages.
-/
/-- Borel measurability preserves Borel inverse images. -/
theorem borelMap_preimage {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) {U : Set Y} (hU : MeasurableSet U) :
    MeasurableSet (f ⁻¹' U) := hU.preimage hf

end PolishSpaceBook
