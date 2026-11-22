module

public import PolishSpaceBook.EffectiveRankProse
public import PolishSpaceBook.LambdaWellFoundedCompleteness
public import PolishSpaceBook.LambdaHomogeneousHulls
public import PolishSpaceBook.LambdaKernelComplexity

@[expose] public section

namespace PolishSpaceBook
open Set MeasureTheory TopologicalSpace LambdaTree

/-- The norm is the root rank of the same section tree used by the
recursive reduction, with its domain transported by literal set equality. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Then set $\varphi(x):=\rho(T_x)$, the well-founded rank of $T_x$. The assertion $\rho(T_x)\le\alpha$ is Borel once
    $\alpha$ is fixed, because it is checked by induction through a fixed countable well-order coding $\alpha$. The
    starred comparison relations are obtained from strict-extension maps between trees and their well-founded duals, as in
    the tree-rank comparison lemma.
-/
theorem exists_effective_tree_rank {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε Aᶜ) :
    ∃ (T : PairTree ε) (hdom : A = sectionDomain T) (N : EffectiveCoanalyticNorm ε A),
      ∀ x (hx : x ∈ A), N.value ⟨x, hx⟩ = sectionRank T x (by change x ∈ sectionDomain T; rwa [← hdom]) := by
  obtain ⟨T, hT⟩ := hA
  have hdom : A = sectionDomain T := by
    apply compl_injective
    rw [sectionDomain_complement]
    exact hT
  cases hdom
  exact ⟨T, rfl, treeRankNorm T, fun _ _ => rfl⟩

/-- Pull back the rank of the supplied tree through the supplied coding map.
Every layer and every bound refers to that same norm. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For equivalence relations, the rank is applied to the graph. If $E\IncludedIn X\times X$ is $\lPi^1_1$, fix
    the tree-rank $\lPi^1_1$
    norm $\varphi$ on $E$ and write
    $$E_{\le\alpha}:=\{(x,y):x\mathrel E y\text{ and }\varphi(x,y)\le\alpha\}.$$
    Each $E_{\le\alpha}$ is Borel, and $E=\bigcup_{\alpha<\omegaOneOrd}E_{\le\alpha}$. Rank boundedness says that
    every analytic subset of $E$ is already contained in some Borel approximation $E_{\le\alpha}$.
-/
theorem tree_rank_layers_pullback {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {ε : ℕ → ℕ}
    (T : PairTree ε) (f : X → (ℕ → ℕ)) (hf : Measurable f) :
    (∀ α < Ordinal.omega 1, MeasurableSet (f ⁻¹' sectionRankLayer T α)) ∧
      f ⁻¹' sectionDomain T = ⋃ (α : Ordinal.{0}) (_ : α < Ordinal.omega 1),
        f ⁻¹' sectionRankLayer T α ∧
      ∀ B : Set X, AnalyticSet B → B ⊆ f ⁻¹' sectionDomain T →
        ∃ α < Ordinal.omega 1, B ⊆ f ⁻¹' sectionRankLayer T α := by
  refine ⟨fun α hα => (sectionRankLayer_measurable T α hα).preimage hf, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      let α := sectionRank T (f x) hx
      exact mem_iUnion.mpr ⟨α, mem_iUnion.mpr ⟨sectionRank_countable T (f x) hx,
        (show f x ∈ sectionRankLayer T α from ⟨hx, le_rfl⟩)⟩⟩
    · intro hx
      obtain ⟨α, hxα⟩ := mem_iUnion.mp hx
      obtain ⟨_, hw, _⟩ := mem_iUnion.mp hxα
      exact hw
  · intro B hB hBA
    have hi := analyticSet_image_via_baire_parametrization hB hf
    have hw : ∀ y ∈ f '' B, WellFounded (strictTreeExtension (rootedSection T y).tree) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hBA hx
    obtain ⟨α, hα, _, hb⟩ := analytic_subset_borel_rank_layer T hi hw
    exact ⟨α, hα, fun x hx => hb ⟨x, hx, rfl⟩⟩

/-- Empty Silver kernel means the actual countable homogeneous family covers
all points, hence all quotient classes. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    There are only countably many sets in the union. If $H=\emptyset$, then $E$ has at most countably many classes.
-/
theorem silverKernel_empty_countable (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hH : silverKernel ε E = ∅) : Countable (Quotient E) := by
  classical
  let : Countable (HomogeneousSet ε E) := countable_homogeneousSet ε E
  apply countable_quotient_of_homogeneous_cover E
    (fun D : HomogeneousSet ε E => D.val) (fun D => D.property.2)
  intro x
  by_contra hx
  push Not at hx
  have hxH : x ∈ silverKernel ε E :=
    fun h => by obtain ⟨D, hxD⟩ := mem_iUnion.mp h; exact hx D hxD
  simp only [hH, mem_empty_iff_false] at hxH

/-- The set-indexed kernel is exactly the kernel defined through valid effective codes. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Let $E$ be a $\lPi^1_1$ equivalence relation on the closed presentation $X$. A set is $E$-homogeneous if all its
    points are $E$-equivalent. With the effective codes from §{sec:edst-generic-conditions}, define
    $$
    H=\SetDifference{X}{\bigcup\{W_e:e\in C,\ W_e\text{ is }E\text{-homogeneous}\}}.
    $$
-/
theorem mem_silverKernel_codes (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (C : ComplementedCodes ε) (x : ℕ → ℕ) :
    x ∈ silverKernel ε E ↔ ∀ e, ValidComplementedIndex ε e →
      ERHomogeneous E (C.negativeSet e)ᶜ → x ∉ (C.negativeSet e)ᶜ := by
  rw [mem_silverKernel_iff]
  constructor
  · intro h e he hh
    rw [← C.complementary he] at hh ⊢
    exact h _ (C.sound he) hh
  · intro h D hD hh hx
    obtain ⟨e, he, hDe⟩ := C.complete hD
    rw [← hDe, C.complementary he] at hh hx
    exact h e he hh hx

/-- The ergodic kernel retains the fixed parameter and both invariance statements. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    It is lightface analytic and invariant under $\EffectiveClosureER{E}$, hence also under $E$.
-/
theorem ergodicKernel_properties (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hE : ProjectedRelation ε E.r) (hne : ProjectedRelation ε (fun x y => ¬ E.r x y)) :
    Projected ε (equivalenceGapKernel E (invariantSetoid ε E)) ∧
      ERInvariant (invariantSetoid ε E) (equivalenceGapKernel E (invariantSetoid ε E)) ∧
      ERInvariant E (equivalenceGapKernel E (invariantSetoid ε E)) := by
  have hi := equivalenceGapKernel_invariant E (invariantSetoid ε E)
  exact ⟨projected_hklKernel ε E hE hne, hi,
    fun {_ _} hxy => hi (relation_le_invariantSetoid ε E hxy)⟩

end PolishSpaceBook
