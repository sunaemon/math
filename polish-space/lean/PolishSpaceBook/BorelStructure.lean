module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import PolishSpaceBook.PolishSpaces

@[expose] public section

/-!
# Borel structure

Formalization targets for `polish-space/src/polish-space-book/borel-structure.md`.

Formalized so far: the `Fσ`/`Gδ` duality and the book's explicit metric proof that
closed sets are `Gδ`; the transfinite Borel hierarchy with its first three levels,
successor inclusions, monotonicity, and continuous-preimage closure; stabilization
at `ω₁`, the `Σ⁰_{ω₁} = Π⁰_{ω₁}` collapse, and closure of the common Borel class
under complements and countable unions; the inductive `BorelCode` representation,
decoding and coding completeness relative to a countable basis, and the tree-rank
bound; and `Δ⁰_1 = clopen` together with the two concrete Baire-space level
computations.

Finite-level universal sets and their diagonal strictness proof are formalized
in `FiniteBorelUniversal.lean`, using the hierarchy developed here.
External real-coded syntax and truth assignments are developed in
`BorelExpressionEvaluation.lean`; coanalytic validity is proved in
`BorelExpressionValidity.lean`. `BorelExpressionBorelEvaluation.lean` gives
the relative analytic/coanalytic evaluation descriptions for arbitrary
Borel leaves. The stronger completeness classification is cited externally.

The concrete `Σ⁰_ω` set of no finite rank, including the alternating clopen
normal form, the `P_k` hardness/completeness proof, and the isolating slice
maps, is proved in `FiniteBorelNormalForm.lean`.
-/

namespace PolishSpaceBook

open Set
open scoped Ordinal

variable {Y : Type*} [TopologicalSpace Y]

/-- The complement of a `Gδ` set is `Fσ`: dual to `IsFsigma.isGdelta_compl`. -/
theorem IsGδ.isFsigma_compl {s : Set Y} (hs : IsGδ s) : IsFsigma sᶜ := by
  rcases hs with ⟨S, hSopen, hScount, rfl⟩
  refine ⟨compl '' S, hScount.image _, ?_, ?_⟩
  · rintro t ⟨u, hu, rfl⟩
    exact (hSopen u hu).isClosed_compl
  · rw [compl_sInter]

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Recall from Alexandrov's theorem in §{sec:alexandrov-theorem} that $\Fsigma$ means a countable union of closed sets and
    $\Gdelta$ means a countable intersection of open sets. The two classes are dual:
    $$A \text{ is } \Fsigma \quad\Longleftrightarrow\quad \SetDifference{X}{A} \text{ is } \Gdelta.$$
-/
/-- A set is `Fσ` iff its complement is `Gδ` (the book's `Fσ`/`Gδ` duality). -/
theorem isFsigma_iff_isGδ_compl {s : Set Y} : IsFsigma s ↔ IsGδ sᶜ := by
  refine ⟨IsFsigma.isGdelta_compl, fun h => ?_⟩
  simpa using IsGδ.isFsigma_compl h

/-- A set is `Gδ` iff its complement is `Fσ`. -/
theorem isGδ_iff_isFsigma_compl {s : Set Y} : IsGδ s ↔ IsFsigma sᶜ := by
  refine ⟨IsGδ.isFsigma_compl, fun h => ?_⟩
  simpa using IsFsigma.isGdelta_compl h

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    In metric spaces, every closed set $C$ is $\Gdelta$. The empty set is open and hence $\Gdelta$; for $C\ne\emptyset$,
    $$C = \bigcap_{n \ge 1} \{x : d(x,C) < 1/n\}.$$
    This is the basic reason the finite Borel levels line up with the classical $\Fsigma/\Gdelta$ notation.
-/
/-- Closed sets are `Gδ` via the explicit metric neighborhoods used in Alexandrov's theorem. -/
theorem isGδ_of_isClosed_metric {Z : Type*} [MetricSpace Z] {s : Set Z}
    (hs : IsClosed s) : IsGδ s :=
  isGδ_of_isClosed_metric_neighborhoods hs

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Longer strings record iterated operations from inside out:

    *   **$\GdeltaSigma$** means a countable union of $\Gdelta$ sets, i.e. a set of the form
        $$\bigcup_{n \in \omega}\bigcap_{m \in \omega} U_{n,m}$$
        with each $U_{n,m}$ open.
    *   **$\FsigmaDelta$** means a countable intersection of $\Fsigma$ sets, i.e. a set of the form
        $$\bigcap_{n \in \omega}\bigcup_{m \in \omega} C_{n,m}$$
        with each $C_{n,m}$ closed.

    The same convention continues: the final symbol is the outermost operation, and the initial letter tells whether the
    construction starts from closed sets ($F$) or open sets ($G$).
-/
/-- `GδΣ`: a countable union of `Gδ` sets. -/
def IsGδSigma (s : Set Y) : Prop :=
  ∃ S : Set (Set Y), S.Countable ∧ (∀ t ∈ S, IsGδ t) ∧ s = ⋃₀ S

/-- `FσΔ`: a countable intersection of `Fσ` sets. -/
def IsFsigmaDelta (s : Set Y) : Prop :=
  ∃ S : Set (Set Y), S.Countable ∧ (∀ t ∈ S, IsFsigma t) ∧ s = ⋂₀ S

/-- The complement of a `GδΣ` set is `FσΔ` (the duality continues to the higher levels). -/
theorem IsGδSigma.isFsigmaDelta_compl {s : Set Y} (hs : IsGδSigma s) : IsFsigmaDelta sᶜ := by
  rcases hs with ⟨S, hcount, hG, rfl⟩
  refine ⟨compl '' S, hcount.image _, ?_, ?_⟩
  · rintro t ⟨u, hu, rfl⟩
    exact IsGδ.isFsigma_compl (hG u hu)
  · rw [compl_sUnion]

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Limit levels are where the recursion stops being merely notational. The tempting but wrong simplification of the limit
    clause is
    $$
    \bSigma^0_\lambda \stackrel{?}{=} \bigcup_{\alpha<\lambda}\bSigma^0_\alpha,
    $$
    which would only keep sets already appearing at one fixed earlier level. It would miss countable unions whose $n$-th
    term has complexity increasing with $n$ — exactly the sets the recursive definition was designed to admit.
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    A \termdefine{pointclass} is a class of sets of points, usually sets of reals or subsets of a fixed Polish space. The
    \termdefine{Borel hierarchy} on a metric space $X$ is the transfinite sequence of pointclasses $\bSigma^0_\alpha(X)$ and
    $\bPi^0_\alpha(X)$ defined by recursion on ordinals $\alpha \ge 1$. Pointclass indices in this recursion range over
    these positive levels. In the rest of this definition, and whenever the ambient space is clear, we suppress $X$ and
    write $\bSigma^0_\alpha$, $\bPi^0_\alpha$, and $\bDelta^0_\alpha$.

    *   $\bSigma^0_1$ = open sets;  $\bPi^0_1$ = closed sets.
    *   For $\alpha > 1$,
        $$
        \bSigma^0_\alpha
        =
        \left\{\bigcup_{n \in \omega} A_n :
        A_n \in \bPi^0_{\beta_n}
        \text{ for some } \beta_n < \alpha
        \text{, for each } n
        \right\}.
        $$
    *   $\bPi^0_\alpha = \{\SetDifference{X}{A} : A \in \bSigma^0_\alpha\}$.
    *   $\bDelta^0_\alpha := \bSigma^0_\alpha \cap \bPi^0_\alpha$.

    The quantifier "for some $\beta_n < \alpha$, for each $n$" is essential. At a limit level it permits a countable union
    whose terms have ranks climbing toward the limit; it does not require all terms to come from one fixed earlier level.
-/
/-- The additive Borel pointclass `Σ⁰_α` on `Y`, by transfinite recursion on the
ordinal `α ≥ 1`: `Σ⁰_1` is the open sets, and for `α > 1`, `Σ⁰_α` is the class of
countable unions `⋃ₙ Aₙ` where each `Aₙ` is `Π⁰_{βₙ}` for some `1 ≤ βₙ < α`
(equivalently `(Aₙ)ᶜ ∈ Σ⁰_{βₙ}`). -/
def borelSigma (α : Ordinal) : Set (Set Y) :=
  if α ≤ 1 then {s | IsOpen s}
  else
    {s | ∃ f : ℕ → Set Y,
        (∀ n, ∃ β : {β : Ordinal // 1 ≤ β ∧ β < α}, (f n)ᶜ ∈ borelSigma β.1) ∧ s = ⋃ n, f n}
termination_by α
decreasing_by exact β.2.2

/-- The multiplicative Borel pointclass `Π⁰_α`: complements of `Σ⁰_α` sets. -/
def borelPi (α : Ordinal) : Set (Set Y) := {s | sᶜ ∈ borelSigma (Y := Y) α}

/-- The ambiguous Borel pointclass `Δ⁰_α := Σ⁰_α ∩ Π⁰_α`. -/
def borelDelta (α : Ordinal) : Set (Set Y) := borelSigma (Y := Y) α ∩ borelPi (Y := Y) α

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Continuous preimages preserve every Borel level. If $f:Y\to X$ is continuous and
    $A\in\bSigma^0_\alpha(X)$, then $f^{-1}(A)\in\bSigma^0_\alpha(Y)$, and likewise for $\bPi^0_\alpha$ and
    $\bDelta^0_\alpha$. This follows by induction on $\alpha$, since continuous preimages send open sets to open sets and
    commute with complements and countable unions.
-/
/-- Continuous preimages preserve every additive Borel level. -/
theorem borelSigma_preimage {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z) (hf : Continuous f) (α : Ordinal) {A : Set Z}
    (hA : A ∈ borelSigma (Y := Z) α) : f ⁻¹' A ∈ borelSigma (Y := X) α := by
  revert A
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro A hA
    by_cases hα : α ≤ 1
    · rw [borelSigma, ite_eq_left hα] at hA ⊢
      exact hA.preimage hf
    · rw [borelSigma, ite_eq_right hα] at hA ⊢
      obtain ⟨g, hg, rfl⟩ := hA
      refine ⟨fun n => f ⁻¹' g n, fun n => ?_, by simp⟩
      obtain ⟨β, hβ⟩ := hg n
      refine ⟨β, ?_⟩
      simpa only [preimage_compl] using ih β.1 β.2.2 hβ

/-- Continuous preimages preserve every multiplicative Borel level. -/
theorem borelPi_preimage {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z) (hf : Continuous f) (α : Ordinal) {A : Set Z}
    (hA : A ∈ borelPi (Y := Z) α) : f ⁻¹' A ∈ borelPi (Y := X) α := by
  show (f ⁻¹' A)ᶜ ∈ borelSigma (Y := X) α
  rw [← preimage_compl]
  exact borelSigma_preimage f hf α hA

/-- Continuous preimages preserve every ambiguous Borel level. -/
theorem borelDelta_preimage {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z) (hf : Continuous f) (α : Ordinal) {A : Set Z}
    (hA : A ∈ borelDelta (Y := Z) α) : f ⁻¹' A ∈ borelDelta (Y := X) α := by
  change A ∈ borelSigma (Y := Z) α ∧ A ∈ borelPi (Y := Z) α at hA
  change f ⁻¹' A ∈ borelSigma (Y := X) α ∧ f ⁻¹' A ∈ borelPi (Y := X) α
  exact ⟨borelSigma_preimage f hf α hA.1, borelPi_preimage f hf α hA.2⟩

/-- A boldface pointclass: a family assigning to each topological space a collection
of its subsets (e.g. `fun X => borelSigma (Y := X) α`). The hardness/completeness
notions below use its Baire-space component for sources and its target-space
component for membership. -/
def Pointclass : Type 1 := (X : Type) → [TopologicalSpace X] → Set (Set X)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    For a pointclass $\Gamma$ and a set $P\IncludedIn Z$, say that $P$ is
    \termdefineas{Gamma-hard}{$\Gamma$-hard} with respect to Baire-space reductions if every
    $B\in\Gamma(\BaireSpace)$ is the continuous preimage of $P$ under some continuous map $\BaireSpace\to Z$. The set
    $P$ is \termdefineas{Gamma-complete}{$\Gamma$-complete} if, in addition, $P\in\Gamma(Z)$. This convention makes both
    the source of the reductions and the ambient space of $P$ explicit.
-/
/-- `P ⊆ Z` is `Γ`-hard for Baire-space reductions: every
`B ∈ Γ(baire_space)` is a continuous preimage of `P`. -/
def IsGammaHard (Γ : Pointclass) {Z : Type} [TopologicalSpace Z] (P : Set Z) : Prop :=
  ∀ B : Set baire_space, B ∈ Γ baire_space →
    ∃ f : baire_space → Z, Continuous f ∧ B = f ⁻¹' P

/-- `P ⊆ Z` is `Γ`-complete for Baire-space reductions: it is `Γ`-hard and
itself lies in `Γ(Z)`. -/
def IsGammaComplete (Γ : Pointclass) {Z : Type} [TopologicalSpace Z] (P : Set Z) : Prop :=
  IsGammaHard Γ P ∧ P ∈ Γ Z

/-- `Σ⁰_1` is exactly the open sets. -/
theorem borelSigma_one : borelSigma (1 : Ordinal) = {s : Set Y | IsOpen s} := by
  rw [borelSigma]; simp

/-- `Π⁰_1` is exactly the closed sets. -/
theorem borelPi_one : borelPi (1 : Ordinal) = {s : Set Y | IsClosed s} := by
  ext s
  simp only [borelPi, mem_ofPred_eq, borelSigma_one, isOpen_compl_iff]

/-- The only ordinal `β` with `1 ≤ β < 2` is `1`. -/
private theorem ordinal_eq_one_of_le_lt_two {β : Ordinal} (h1 : 1 ≤ β) (h2 : β < 2) : β = 1 := by
  refine le_antisymm ?_ h1
  have h : (2 : Ordinal) = Order.succ 1 := by rw [Order.succ_eq_add_one, one_add_one_eq_two]
  exact Order.lt_succ_iff.1 (h ▸ h2)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    At the first nontrivial stage the recursive definition recovers the classical notation. Since the only ordinal below $2$
    and at least $1$ is $1$,
    $$
    \begin{aligned}
    \bSigma^0_2
    &= \left\{\bigcup_{n \in \omega} A_n : A_n \in \bPi^0_1
    \text{ for each } n\right\} \\
    &= \left\{\bigcup_{n \in \omega} F_n : F_n \text{ is closed for each } n\right\}
    = \Fsigma.
    \end{aligned}
    $$
    Taking complements,
    $$
    \SetDifference{X}{\bigcup_n C_n}=\bigcap_n(\SetDifference{X}{C_n}),
    $$
    and hence
    $$
    \begin{aligned}
    \bPi^0_2
    &= \{\SetDifference{X}{A} : A \in \bSigma^0_2\} \\
    &= \left\{\bigcap_{n \in \omega} U_n : U_n \text{ is open for each } n\right\}
    = \Gdelta.
    \end{aligned}
    $$
-/
/-- `Σ⁰_2` is exactly the `Fσ` sets: at `α = 2` the only lower level is `Π⁰_1`
(closed sets), so `Σ⁰_2` is the countable unions of closed sets. -/
theorem borelSigma_two : borelSigma (2 : Ordinal) = {s : Set Y | IsFsigma s} := by
  ext s
  rw [borelSigma, ite_eq_right (not_le.2 one_lt_two)]
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨Set.range f, Set.countable_range f, ?_, (Set.sUnion_range f).symm⟩
    rintro t ⟨n, rfl⟩
    obtain ⟨β, hβmem⟩ := hf n
    rw [ordinal_eq_one_of_le_lt_two β.2.1 β.2.2, borelSigma_one] at hβmem
    exact isOpen_compl_iff.1 hβmem
  · rintro ⟨S, hScount, hSclosed, rfl⟩
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · refine ⟨fun _ => ∅, fun n => ⟨⟨1, le_refl 1, one_lt_two⟩, ?_⟩, by simp⟩
      rw [borelSigma_one]; simp
    · obtain ⟨f, rfl⟩ := hScount.exists_eq_range hSne
      refine ⟨f, fun n => ⟨⟨1, le_refl 1, one_lt_two⟩, ?_⟩, (Set.sUnion_range f).symm⟩
      rw [borelSigma_one]
      exact (hSclosed (f n) ⟨n, rfl⟩).isOpen_compl

private theorem ord_not_three_le_one : ¬ (3 : Ordinal) ≤ 1 :=
  not_le.2 (by exact_mod_cast (by norm_num : (1 : ℕ) < 3))

private theorem ord_lt_three_le_two {β : Ordinal} (h : β < 3) : β ≤ 2 := by
  have h3 : (3 : Ordinal) = Order.succ 2 := by
    rw [Order.succ_eq_add_one]; exact_mod_cast (by norm_num : (2 : ℕ) + 1 = 3)
  exact Order.lt_succ_iff.1 (h3 ▸ h)

private theorem ord_one_le_two : (1 : Ordinal) ≤ 2 := by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
private theorem ord_two_lt_three : (2 : Ordinal) < 3 := by exact_mod_cast (by norm_num : (2 : ℕ) < 3)

/-- `Π⁰_2` is exactly the `Gδ` sets. -/
theorem borelPi_two : borelPi (2 : Ordinal) = {s : Set Y | IsGδ s} := by
  ext s
  simp only [borelPi, mem_ofPred_eq, borelSigma_two]
  exact (isGδ_iff_isFsigma_compl).symm

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    At $\alpha=3$ the union pieces may come from $\bPi^0_1$ or $\bPi^0_2$:
    $$
    \bSigma^0_3
    = \left\{\bigcup_{n \in \omega} A_n :
    A_n \in \bPi^0_1 \cup \bPi^0_2
    \text{ for each } n\right\}.
    $$
    Because closed sets are $\Gdelta$ in metric spaces, $\bPi^0_1 \IncludedIn \bPi^0_2$, so this is the class of countable
    unions of $\Gdelta$ sets: $\GdeltaSigma$. Complementing gives $\FsigmaDelta$.
-/
/-- `Σ⁰_3` is exactly the `GδΣ` sets in a metric space: the only lower levels are
`Π⁰_1` (closed) and `Π⁰_2` (Gδ), and closed sets are `Gδ` in a metric space, so the
pieces of the countable union are exactly the `Gδ` sets. -/
theorem borelSigma_three {Z : Type*} [MetricSpace Z] :
    borelSigma (Y := Z) (3 : Ordinal) = {s : Set Z | IsGδSigma s} := by
  ext s
  rw [borelSigma, ite_eq_right ord_not_three_le_one]
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨Set.range f, Set.countable_range f, ?_, (Set.sUnion_range f).symm⟩
    rintro t ⟨n, rfl⟩
    obtain ⟨β, hβmem⟩ := hf n
    rcases lt_or_eq_of_le (ord_lt_three_le_two β.2.2) with hlt | heq
    · -- `1 ≤ β < 2` forces `β = 1`: the piece is closed, hence `Gδ` in a metric space.
      rw [ordinal_eq_one_of_le_lt_two β.2.1 hlt, borelSigma_one] at hβmem
      exact isGδ_of_isClosed_metric (isOpen_compl_iff.1 hβmem)
    · -- `β = 2`: the complement is `Fσ`, so the piece itself is `Gδ`.
      rw [heq, borelSigma_two] at hβmem
      simpa using IsFsigma.isGdelta_compl hβmem
  · rintro ⟨S, hScount, hSGδ, rfl⟩
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · refine ⟨fun _ => ∅, fun n => ⟨⟨2, ord_one_le_two, ord_two_lt_three⟩, ?_⟩, by simp⟩
      rw [borelSigma_two]
      exact ⟨{Set.univ}, Set.countable_singleton _, by simp [isClosed_univ], by simp⟩
    · obtain ⟨f, rfl⟩ := hScount.exists_eq_range hSne
      refine ⟨f, fun n => ⟨⟨2, ord_one_le_two, ord_two_lt_three⟩, ?_⟩, (Set.sUnion_range f).symm⟩
      rw [borelSigma_two]
      exact IsGδ.isFsigma_compl (hSGδ (f n) ⟨n, rfl⟩)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    In a metric space the hierarchy is monotone: whenever $1\leq\beta\leq\gamma$,
    $$
    \bSigma^0_\beta\IncludedIn\bSigma^0_\gamma,
    \qquad
    \bPi^0_\beta\IncludedIn\bPi^0_\gamma.
    $$
    Moreover, for every $\alpha\geq 1$,
    $$
    \bSigma^0_\alpha\IncludedIn\bPi^0_{\alpha+1},
    \qquad
    \bPi^0_\alpha\IncludedIn\bSigma^0_{\alpha+1}.
    $$
    Above level $1$ these facts follow directly from the union and complement clauses. The metric-space base case uses that
    open sets are $\Fsigma$ and closed sets are $\Gdelta$.
-/
/-- Monotone embedding `Σ⁰_α ⊆ Π⁰_{α+1}` for `1 ≤ α`: a `Σ⁰_α` set, viewed as the
constant countable union of itself, has its complement at level `α`, so the set
itself is `Π⁰_{α+1}`. This is the first half of the book's `Σ⁰_α ⊆ Σ⁰_{α+2}` chain
used in the stabilization argument at `ω₁`. -/
theorem borelSigma_subset_borelPi_succ {α : Ordinal} (hα : 1 ≤ α) :
    borelSigma (Y := Y) α ⊆ borelPi (α + 1) := by
  intro A hA
  have hlt : α < α + 1 := by rw [← Order.succ_eq_add_one]; exact Order.lt_succ α
  have h1lt : (1 : Ordinal) < α + 1 := lt_of_le_of_lt hα hlt
  show Aᶜ ∈ borelSigma (α + 1)
  rw [borelSigma, ite_eq_right (not_le.2 h1lt)]
  exact ⟨fun _ => Aᶜ, fun _ => ⟨⟨α, hα, hlt⟩, by simpa using hA⟩, (Set.iUnion_const Aᶜ).symm⟩

/-- Monotone embedding `Π⁰_α ⊆ Σ⁰_{α+1}` for `1 ≤ α`: a `Π⁰_α` set has its
complement at level `α`, so as the constant countable union of itself it is
`Σ⁰_{α+1}`. This is the dual half of the `Σ⁰_α ⊆ Σ⁰_{α+2}` chain. -/
theorem borelPi_subset_borelSigma_succ {α : Ordinal} (hα : 1 ≤ α) :
    borelPi (Y := Y) α ⊆ borelSigma (α + 1) := by
  intro A hA
  have hlt : α < α + 1 := by rw [← Order.succ_eq_add_one]; exact Order.lt_succ α
  have h1lt : (1 : Ordinal) < α + 1 := lt_of_le_of_lt hα hlt
  rw [borelSigma, ite_eq_right (not_le.2 h1lt)]
  exact ⟨fun _ => A, fun _ => ⟨⟨α, hα, hlt⟩, hA⟩, (Set.iUnion_const A).symm⟩

/-- The book's monotonicity step `Σ⁰_α ⊆ Σ⁰_{α+2}` for `1 ≤ α`, obtained by
composing the two embeddings through `Π⁰_{α+1}`. -/
theorem borelSigma_subset_borelSigma_add_two {α : Ordinal} (hα : 1 ≤ α) :
    borelSigma (Y := Y) α ⊆ borelSigma (α + 2) := by
  intro A hA
  have hlt : α < α + 1 := by rw [← Order.succ_eq_add_one]; exact Order.lt_succ α
  have h1 : (1 : Ordinal) ≤ α + 1 := le_trans hα hlt.le
  have hmem := borelPi_subset_borelSigma_succ h1 (borelSigma_subset_borelPi_succ hα hA)
  rwa [add_assoc, one_add_one_eq_two] at hmem

/-- For `1 < β ≤ γ` the hierarchy is monotone: both levels use the union form, and
the index bound `δ < β ≤ γ` transfers term by term. No metric is needed here. -/
theorem borelSigma_mono_of_one_lt {β γ : Ordinal} (hβ : 1 < β) (h : β ≤ γ) :
    borelSigma (Y := Y) β ⊆ borelSigma γ := by
  have hγ : 1 < γ := lt_of_lt_of_le hβ h
  intro s hs
  rw [borelSigma, ite_eq_right (not_le.2 hβ)] at hs
  rw [borelSigma, ite_eq_right (not_le.2 hγ)]
  obtain ⟨f, hf, rfl⟩ := hs
  refine ⟨f, fun n => ?_, rfl⟩
  obtain ⟨⟨δ, hδ1, hδβ⟩, hδmem⟩ := hf n
  exact ⟨⟨δ, hδ1, lt_of_lt_of_le hδβ h⟩, hδmem⟩

/-- In a metric space `Σ⁰_1 ⊆ Σ⁰_2`: every open set is `Fσ`, because its closed
complement is `Gδ` (the book's `infDist` construction) and complements of `Gδ`
sets are `Fσ`. -/
theorem borelSigma_one_subset_two {Z : Type*} [MetricSpace Z] :
    borelSigma (Y := Z) 1 ⊆ borelSigma 2 := by
  intro U hU
  rw [borelSigma_one] at hU
  rw [borelSigma_two]
  simpa using IsGδ.isFsigma_compl (isGδ_of_isClosed_metric hU.isClosed_compl)

/-- General monotonicity of the Borel hierarchy in a metric space: `Σ⁰_β ⊆ Σ⁰_γ`
whenever `1 ≤ β ≤ γ`. The union-form case is handled by
`borelSigma_mono_of_one_lt`; the base level `β = 1` (open sets) climbs to `γ ≥ 2`
through `Σ⁰_2 = Fσ`. -/
theorem borelSigma_mono {Z : Type*} [MetricSpace Z] {β γ : Ordinal}
    (hβ : 1 ≤ β) (h : β ≤ γ) : borelSigma (Y := Z) β ⊆ borelSigma γ := by
  rcases eq_or_lt_of_le hβ with hβ1 | hβ1
  · -- `β = 1`
    subst hβ1
    rcases eq_or_lt_of_le h with hγ1 | hγ1
    · rw [← hγ1]
    · have h2γ : (2 : Ordinal) ≤ γ := by
        rw [show (2 : Ordinal) = Order.succ 1 by rw [Order.succ_eq_add_one, one_add_one_eq_two]]
        exact Order.succ_le_of_lt hγ1
      exact borelSigma_one_subset_two.trans (borelSigma_mono_of_one_lt one_lt_two h2γ)
  · exact borelSigma_mono_of_one_lt hβ1 h

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Structural induction shows that $\rho(c)$ is countable for every code $c$: each constructor takes a successor
    or the supremum of countably many countable successors. Regularity of $\omegaOneOrd$ keeps the result countable.
    This explains why the recursive data suffice for the Borel hierarchy up to its stabilization at $\omegaOneOrd$.
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The recursion may be written for all ordinals, but no new sets appear after $\omegaOneOrd$. At the first
    uncountable stage,
    $$
    \bSigma^0_{\omegaOneOrd}
    = \left\{\bigcup_n A_n : A_n \in \bPi^0_{\beta_n}
    \text{ for some } \beta_n < \omegaOneOrd
    \text{, for each } n\right\}.
    $$
    By the regularity of $\omegaOneOrd$ proved in §{sec:ordinals-cofinality}, the countable set of indices
    $\{\beta_n:n\in\omega\}$ has a supremum $\gamma<\omegaOneOrd$. Hence all terms already lie below one countable bound,
    and the union lies in
    $\bSigma^0_{\gamma+1}$. Therefore
    $$
    \bSigma^0_{\omegaOneOrd}
    = \bigcup_{\alpha < \omegaOneOrd}\bSigma^0_\alpha.
    $$
    The reverse inclusion follows from monotonicity.
-/
/-- Stabilization of the Borel hierarchy at `ω₁` (metric space): no new sets
appear at the first uncountable level, `Σ⁰_{ω₁} = ⋃_{α < ω₁} Σ⁰_α`.

This is the book's regularity argument. The `⊇` inclusion is monotonicity. For
`⊆`, a `Σ⁰_{ω₁}` set is a countable union `⋃ₙ Aₙ` whose pieces have complements
at levels `βₙ < ω₁`; regularity of `ℵ₁` (`Ordinal.iSup_lt_omega_one`) gives a
single countable bound `γ := ⨆ₙ βₙ < ω₁`, monotonicity pushes every piece to
level `γ`, and the union then sits at `γ + 1 < ω₁`. -/
theorem borelSigma_omega1_eq {Z : Type*} [MetricSpace Z] :
    borelSigma (Y := Z) (ω₁ : Ordinal.{0}) =
      {s : Set Z | ∃ α : Ordinal.{0}, α < ω₁ ∧ s ∈ borelSigma α} := by
  have h1ltω1 : (1 : Ordinal) < ω₁ := lt_trans Ordinal.one_lt_omega0 Ordinal.omega0_lt_omega_one
  have hlim : Order.IsSuccLimit (ω₁ : Ordinal) := by
    have := Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)
    rwa [Cardinal.ord_aleph] at this
  ext s
  simp only [mem_ofPred_eq]
  constructor
  · -- A `Σ⁰_{ω₁}` set lands at some countable level `γ + 1`.
    intro hs
    rw [borelSigma, ite_eq_right (not_le.2 h1ltω1)] at hs
    obtain ⟨f, hf, rfl⟩ := hs
    choose β hβ using hf
    -- `β n` is the level of the `n`-th piece's complement; `γ` is their supremum.
    have hγω1 : (⨆ n, (β n).1) < ω₁ := Ordinal.iSup_lt_omega_one fun n => (β n).2.2
    have hγ1 : (1 : Ordinal) ≤ ⨆ n, (β n).1 :=
      le_trans (β 0).2.1 (Ordinal.le_iSup (fun n => (β n).1) 0)
    have hpiece : ∀ n, (f n)ᶜ ∈ borelSigma (⨆ n, (β n).1) := fun n =>
      borelSigma_mono (β n).2.1 (Ordinal.le_iSup (fun n => (β n).1) n) (hβ n)
    have hlt : (⨆ n, (β n).1) < (⨆ n, (β n).1) + 1 := by
      rw [← Order.succ_eq_add_one]; exact Order.lt_succ _
    have hsucc : (⨆ n, (β n).1) + 1 < ω₁ := by
      have h := hlim.succ_lt hγω1; rwa [Order.succ_eq_add_one] at h
    refine ⟨(⨆ n, (β n).1) + 1, hsucc, ?_⟩
    rw [borelSigma, ite_eq_right (not_le.2 (lt_of_le_of_lt hγ1 hlt))]
    exact ⟨f, fun n => ⟨⟨⨆ n, (β n).1, hγ1, hlt⟩, hpiece n⟩, rfl⟩
  · -- Every set appearing below `ω₁` is, by monotonicity, in `Σ⁰_{ω₁}`.
    rintro ⟨α, hαω1, hαmem⟩
    rcases le_total α 1 with hα1 | hα1
    · have hopen : s ∈ borelSigma (Y := Z) 1 := by
        rw [borelSigma_one]; rw [borelSigma, ite_eq_left hα1] at hαmem; exact hαmem
      exact borelSigma_mono (le_refl 1) h1ltω1.le hopen
    · exact borelSigma_mono hα1 hαω1.le hαmem

/-- Monotonicity of the `Π` hierarchy in a metric space, dual to `borelSigma_mono`
by complementation: for `1 ≤ β ≤ γ`, `Π⁰_β ⊆ Π⁰_γ`. -/
theorem borelPi_mono {Z : Type*} [MetricSpace Z] {β γ : Ordinal}
    (hβ : 1 ≤ β) (h : β ≤ γ) : borelPi (Y := Z) β ⊆ borelPi γ :=
  fun _ hs => borelSigma_mono hβ h hs

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The class $\bSigma^0_{\omegaOneOrd}$ is closed under countable unions: if $A_n \in \bSigma^0_{\alpha_n}$ with
    $\alpha_n < \omegaOneOrd$, then $\beta := \sup_n\alpha_n < \omegaOneOrd$ by regularity, hence $A_n \in
    \bSigma^0_{\alpha_n}\IncludedIn\bPi^0_{\alpha_n+1}\IncludedIn\bPi^0_{\beta+1}$, and so $\bigcup_n A_n \in
    \bSigma^0_{\beta+2} \IncludedIn \bSigma^0_{\omegaOneOrd}$.

    To prove closure under complement, take $A\in\bSigma^0_{\omegaOneOrd}$. Stabilization gives
    $A\in\bSigma^0_\alpha$ for some $1\leq\alpha<\omegaOneOrd$, so
    $\SetDifference{X}{A}\in\bPi^0_\alpha$. Viewing this set as a one-term countable union places it in
    $\bSigma^0_{\alpha+1}\IncludedIn\bSigma^0_{\omegaOneOrd}$. Thus
    $\bSigma^0_{\omegaOneOrd}$ is complement-closed. Since $\bPi^0_{\omegaOneOrd}$ consists of complements of
    $\bSigma^0_{\omegaOneOrd}$ sets, this closure forces
    $$\bSigma^0_{\omegaOneOrd} \;=\; \bPi^0_{\omegaOneOrd};$$
    the members of this common class are the \termdefineas{Borel set}{Borel sets} of $X$, and the common class is the Borel
    $\sigma$-algebra of $X$.
-/
/-- The Borel hierarchy collapses at `ω₁`: `Σ⁰_{ω₁} = Π⁰_{ω₁}`, the common class
being the Borel σ-algebra. Forward: a `Σ⁰_{ω₁}` set sits at some level `1 ≤ δ < ω₁`
(stabilization), hence in `Π⁰_{δ+1} ⊆ Π⁰_{ω₁}` through the embedding and
`Π`-monotonicity; the reverse follows by complementation. -/
theorem borelSigma_omega1_eq_borelPi {Z : Type*} [MetricSpace Z] :
    borelSigma (Y := Z) (ω₁ : Ordinal.{0}) = borelPi (Y := Z) (ω₁ : Ordinal.{0}) := by
  have h1ltω1 : (1 : Ordinal) < ω₁ := lt_trans Ordinal.one_lt_omega0 Ordinal.omega0_lt_omega_one
  have hlim : Order.IsSuccLimit (ω₁ : Ordinal) := by
    have := Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)
    rwa [Cardinal.ord_aleph] at this
  have key : borelSigma (Y := Z) (ω₁ : Ordinal.{0}) ⊆ borelPi ω₁ := by
    intro A hA
    rw [borelSigma_omega1_eq] at hA
    obtain ⟨α, hauto, hαmem⟩ := hA
    -- normalize the level to some `1 ≤ δ < ω₁`
    obtain ⟨δ, hδ1, hδω1, hδmem⟩ :
        ∃ δ, 1 ≤ δ ∧ δ < ω₁ ∧ A ∈ borelSigma (Y := Z) δ := by
      rcases le_total α 1 with hα1 | hα1
      · refine ⟨1, le_refl 1, h1ltω1, ?_⟩
        rw [borelSigma_one]; rw [borelSigma, ite_eq_left hα1] at hαmem; exact hαmem
      · exact ⟨α, hα1, hauto, hαmem⟩
    have hδ1ω1 : δ + 1 ≤ ω₁ := by
      have := hlim.succ_lt hδω1; rw [Order.succ_eq_add_one] at this; exact this.le
    have h1δ1 : (1 : Ordinal) ≤ δ + 1 :=
      le_trans hδ1 (by rw [← Order.succ_eq_add_one]; exact (Order.lt_succ δ).le)
    exact borelPi_mono h1δ1 hδ1ω1 (borelSigma_subset_borelPi_succ hδ1 hδmem)
  refine Set.Subset.antisymm key fun A hA => ?_
  -- `A ∈ Π⁰_{ω₁}` means `Aᶜ ∈ Σ⁰_{ω₁}`; apply `key` to `Aᶜ` and uncomplement.
  have h := key (show Aᶜ ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0}) from hA)
  simp only [borelPi, Set.mem_ofPred_eq, compl_compl] at h
  exact h

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Taking complements gives the analogous identity
    $$
    \bPi^0_{\omegaOneOrd}
    = \bigcup_{\alpha < \omegaOneOrd}\bPi^0_\alpha.
    $$
-/
/-- The dual stabilization identity for the `Π` hierarchy: `Π⁰_{ω₁} = ⋃_{α<ω₁} Π⁰_α`,
obtained from `borelSigma_omega1_eq` by complementation. -/
theorem borelPi_omega1_eq {Z : Type*} [MetricSpace Z] :
    borelPi (Y := Z) (ω₁ : Ordinal.{0}) =
      {s : Set Z | ∃ α : Ordinal.{0}, α < ω₁ ∧ s ∈ borelPi α} := by
  ext s
  constructor
  · intro hs
    have hc : sᶜ ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0}) := hs
    rw [borelSigma_omega1_eq] at hc
    obtain ⟨α, hα, hmem⟩ := hc
    exact ⟨α, hα, hmem⟩
  · rintro ⟨α, hα, hmem⟩
    show sᶜ ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0})
    rw [borelSigma_omega1_eq]
    exact ⟨α, hα, hmem⟩

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    A map $f:X\to Y$ between topological spaces is a \termdefine{Borel-measurable map} if $f^{-1}(V)$ is Borel in $X$ for
    every open set $V\IncludedIn Y$. This open-set criterion is equivalent to requiring $f^{-1}(B)$ to be Borel in $X$ for
    every Borel set $B\IncludedIn Y$: the family
    $$
    \{B\IncludedIn Y:f^{-1}(B)\text{ is Borel in }X\}
    $$
    is a $\sigma$-algebra because inverse images commute with complements and countable unions, and a $\sigma$-algebra that
    contains the open sets contains the Borel $\sigma$-algebra.
-/
/-- A map is Borel measurable when it is measurable between the Borel
measurable spaces generated by the source and target topologies. -/
def IsBorelMeasurable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  @Measurable X Y (borel X) (borel Y) f

/-- The open-set criterion for Borel measurability: because the target Borel
σ-algebra is generated by its open sets, it suffices to check their preimages. -/
theorem isBorelMeasurable_iff_preimage_open {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} :
    IsBorelMeasurable f ↔
      ∀ V : Set Y, IsOpen V → @MeasurableSet X (borel X) (f ⁻¹' V) := by
  constructor
  · intro hf V hV
    exact hf (MeasurableSpace.GenerateMeasurable.basic V hV)
  · intro h
    exact @measurable_generateFrom X Y (borel X) {V : Set Y | IsOpen V} f
      (fun V hV => h V hV)

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Beyond these first levels, the construction in §{sec:borel-codes} records the required countable unions and
    complements as inductive constructor data.
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Fix a Polish space $X$ and a countable open base $\IndexedFamily{U_n}{n\in\omega}$ for its topology.
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The third rule takes an arbitrary countable sequence of previously constructed codes as its argument.
    It need not be a finite list or a computable sequence.

    The set $A_c\IncludedIn X$ interpreted by a code is defined by structural recursion:
    $$
    \begin{aligned}
    A_{\BorelLeafCode{n}}&:=U_n,\\
    A_{\BorelComplementCode{c}}&:=\SetDifference{X}{A_c},\\
    A_{\BorelUnionCode{\Sequence{c_k}{k\in\omega}}}&:=\bigcup_{k\in\omega}A_{c_k}.
    \end{aligned}
    $$
    In particular, different codes can have the same interpretation.

    By structural induction, $A_c$ is Borel for every code $c$: basic open sets are Borel, and Borel sets are
    closed under complements and countable unions.
-/
/-- Borel codes are inductively generated by basic opens, complementation, and countable union.
The union argument is an arbitrary sequence of codes. Structural recursion is
well-founded even though subcode depths need not have a common finite bound. -/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: definition
  excerpt: |
    The formal expressions generated inductively by the following rules are called \termdefineas{Borel code}{Borel codes}: \begin{enumerate} \item For each
-/
inductive BorelCode : Type
  | leaf : ℕ → BorelCode
  | union : (ℕ → BorelCode) → BorelCode
  | compl : BorelCode → BorelCode

/-- Decoding a Borel code against a countable family `U` of basic sets: a leaf
decodes to its basic set, a union node to the countable union of its children's
decodings, a complement node to the complement of its child's decoding. This is
the book's three equations for `A_c` (borel-structure §borel-codes),
realized here as structural recursion on the code. -/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    A \termforward{Borel code} records how a set is built from basic open sets by complements and countable unions.
    We first define these records as inductive data, just as terms and formulas are defined by constructors in
    §{sec:appendix-logic}. Their interpretation is then given by structural recursion. Later we encode the same data
    as real parameters, so that statements about Borel sets can be expressed as statements about reals.
-/
def BorelCode.decode {X : Type*} (U : ℕ → Set X) : BorelCode → Set X
  | .leaf n => U n
  | .union f => ⋃ n, (f n).decode U
  | .compl c => (c.decode U)ᶜ

/-- `Σ⁰_{ω₁}` (the Borel σ-algebra) is closed under complement: immediate from the
collapse `Σ⁰_{ω₁} = Π⁰_{ω₁}`. -/
theorem borelSigma_omega1_compl {Z : Type*} [MetricSpace Z] {A : Set Z}
    (h : A ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0})) :
    Aᶜ ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0}) := by
  rw [borelSigma_omega1_eq_borelPi] at h; exact h

/-- `Σ⁰_{ω₁}` is closed under countable unions (the book's L154 closure property):
each piece's complement sits at some level `< ω₁` by stabilization and the
collapse, so the union is again a `Σ⁰_{ω₁}` set in union form. -/
theorem borelSigma_omega1_iUnion {Z : Type*} [MetricSpace Z] {A : ℕ → Set Z}
    (h : ∀ n, A n ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0})) :
    (⋃ n, A n) ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0}) := by
  have h1ltω1 : (1 : Ordinal) < ω₁ := lt_trans Ordinal.one_lt_omega0 Ordinal.omega0_lt_omega_one
  rw [borelSigma, ite_eq_right (not_le.2 h1ltω1)]
  refine ⟨A, fun n => ?_, rfl⟩
  have hcompl : (A n)ᶜ ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0}) :=
    borelSigma_omega1_compl (h n)
  rw [borelSigma_omega1_eq] at hcompl
  obtain ⟨α, hαω1, hαmem⟩ := hcompl
  rcases le_total α 1 with hα1 | hα1
  · refine ⟨⟨1, le_refl 1, h1ltω1⟩, ?_⟩
    rw [borelSigma_one]; rw [borelSigma, ite_eq_left hα1] at hαmem; exact hαmem
  · exact ⟨⟨α, hα1, hαω1⟩, hαmem⟩

/-- Every decoded Borel code is a Borel set: if the basis `U` consists of open
sets, then `c.decode U ∈ Σ⁰_{ω₁}` for every code `c`. This is the easy direction
of the code↔set correspondence (borel-structure §borel-codes), by structural
induction on the code using closure of `Σ⁰_{ω₁}` under countable union and
complement, with leaves landing in `Σ⁰_1 ⊆ Σ⁰_{ω₁}`. -/
theorem BorelCode.decode_mem_borel {Z : Type*} [MetricSpace Z] {U : ℕ → Set Z}
    (hU : ∀ n, IsOpen (U n)) (c : BorelCode) :
    c.decode U ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0}) := by
  have h1ltω1 : (1 : Ordinal) < ω₁ := lt_trans Ordinal.one_lt_omega0 Ordinal.omega0_lt_omega_one
  induction c with
  | leaf n => exact borelSigma_mono (le_refl 1) h1ltω1.le (by rw [borelSigma_one]; exact hU n)
  | union f ih => exact borelSigma_omega1_iUnion ih
  | compl c ih => exact borelSigma_omega1_compl ih

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Conversely, the recursive construction in the previous subsection gives inductive constructor data for every
    Borel set. Neither the code level nor the structural rank need be the least Borel level of the decoded set:
    redundant complements can increase both without changing that set.
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    By the rank stabilization at $\omegaOneOrd$ from §{sec:borel-hierarchy}, every Borel set $A\IncludedIn X$ lies in
    $\bSigma^0_\alpha(X)$ or $\bPi^0_\alpha(X)$ for some $\alpha<\omegaOneOrd$. Construct a code by recursion on $\alpha$:

    *   $\alpha=1$: let $e$ be the empty-set code constructed above. For each $n$, put $c_n:=\BorelLeafCode{n}$ if
        $U_n\IncludedIn A$, and $c_n:=e$ otherwise. Then $\BorelUnionCode{\Sequence{c_n}{n\in\omega}}$ codes the open set
        $A$,
        including $A=\emptyset$.
    *   $\alpha>1$, $A\in\bSigma^0_\alpha$: write $A=\bigcup_n B_n$ with $B_n\in\bPi^0_{\beta_n}(X)$ and
        $\beta_n<\alpha$. Recursively choose a code $c_n$ for each $B_n$; then
        $\BorelUnionCode{\Sequence{c_n}{n\in\omega}}$ codes $A$.
    *   $A\in\bPi^0_\alpha$: first construct a code $c$ for $\complement A\in\bSigma^0_\alpha$, then use
        $\BorelComplementCode{c}$.

    At a limit ordinal $\lambda$, no extra constructor is needed. The definition of $\bSigma^0_\lambda$ already expresses
    its members as countable unions of sets from classes $\bPi^0_{\beta_n}$ with $\beta_n<\lambda$.
    Thus the same union constructor handles the limit step in the \termuse{Borel hierarchy}.
-/
/-- Every Borel set has a code: given a countable open basis `U`, every set in
`Σ⁰_{ω₁}` is `c.decode U` for some code `c` (borel-structure §borel-codes, "every
Borel set has a code"). The proof is the book's induction on the Borel level: an
open set is the union of the basis sets it contains (coded by union of leaves,
with `∅` coded as the complement of the covering union); at higher levels a set
is a countable union whose pieces' complements live at lower levels, so the
inductive hypothesis codes each complement and the set is coded by a union of
complement nodes. -/
theorem BorelCode.exists_decode_eq {Z : Type*} [MetricSpace Z]
    (U : ℕ → Set Z) (hUbasis : TopologicalSpace.IsTopologicalBasis (Set.range U))
    {A : Set Z} (hA : A ∈ borelSigma (Y := Z) (ω₁ : Ordinal.{0})) :
    ∃ c : BorelCode, c.decode U = A := by
  classical
  have hcov : (⋃ n, U n) = Set.univ := by rw [← Set.sUnion_range]; exact hUbasis.sUnion_eq
  suffices key : ∀ α : Ordinal.{0}, ∀ B : Set Z,
      B ∈ borelSigma (Y := Z) α → ∃ c : BorelCode, c.decode U = B by
    rw [borelSigma_omega1_eq] at hA
    obtain ⟨α, -, hAα⟩ := hA
    exact key α A hAα
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro B hB
    by_cases hα1 : α ≤ 1
    · -- open base level: `B = ⋃ {Uₙ : Uₙ ⊆ B}`
      rw [borelSigma, ite_eq_left hα1, Set.mem_ofPred_eq] at hB
      refine ⟨BorelCode.union fun n =>
        if U n ⊆ B then BorelCode.leaf n
        else BorelCode.compl (BorelCode.union BorelCode.leaf), ?_⟩
      have hdec : (BorelCode.union fun n =>
          if U n ⊆ B then BorelCode.leaf n
          else BorelCode.compl (BorelCode.union BorelCode.leaf)).decode U
          = ⋃ n, (if U n ⊆ B then U n else (∅ : Set Z)) := by
        simp only [BorelCode.decode]
        refine Set.iUnion_congr fun n => ?_
        by_cases hP : U n ⊆ B
        · simp only [ite_eq_left hP, BorelCode.decode]
        · simp only [ite_eq_right hP, BorelCode.decode]; rw [hcov, Set.compl_univ]
      rw [hdec]
      refine Set.Subset.antisymm (Set.iUnion_subset fun n => ?_) (fun x hx => ?_)
      · by_cases hP : U n ⊆ B
        · rw [ite_eq_left hP]; exact hP
        · rw [ite_eq_right hP]; exact Set.empty_subset _
      · obtain ⟨v, hvrange, hxv, hvB⟩ := hUbasis.exists_subset_of_mem_open hx hB
        obtain ⟨n, rfl⟩ := hvrange
        exact Set.mem_iUnion.2 ⟨n, by rw [ite_eq_left hvB]; exact hxv⟩
    · -- higher level: code each piece's complement by the inductive hypothesis
      rw [borelSigma, ite_eq_right hα1] at hB
      obtain ⟨f, hf, rfl⟩ := hB
      choose β hβmem using hf
      choose c hc using fun n => IH (β n).1 (β n).2.2 (f n)ᶜ (hβmem n)
      refine ⟨BorelCode.union fun n => BorelCode.compl (c n), ?_⟩
      simp only [BorelCode.decode, hc, compl_compl]

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    Allowing only complement and countable union suffices because countable intersection is recoverable as
    $$\bigcap_n B_n = \SetDifference{X}{\bigcup_n (\SetDifference{X}{B_n})}.$$
    Finite nonempty unions and intersections are obtained by repeating terms in a countable sequence.
    The whole space is coded by $\BorelUnionCode{\Sequence{\BorelLeafCode{n}}{n\in\omega}}$, since $\bigcup_nU_n=X$;
    its complement codes the empty set. Thus the three constructors suffice for the whole Borel $\sigma$-algebra.
-/
/-- The Borel-code label set (leaf, countable union, complement) needs no
intersection node: countable intersection is recoverable from complement and
countable union by De Morgan, `⋂ₙ Bₙ = (⋃ₙ Bₙᶜ)ᶜ` (borel-structure §borel-codes).
Together with `BorelCode.decode_mem_borel` and `BorelCode.exists_decode_eq`, this
is why the three labels generate exactly the Borel σ-algebra. -/
theorem iInter_eq_compl_iUnion_compl {Z : Type*} (B : ℕ → Set Z) :
    (⋂ n, B n) = (⋃ n, (B n)ᶜ)ᶜ := by
  rw [Set.compl_iUnion]; simp only [compl_compl]

/-- Each level `Σ⁰_γ` is closed under countable unions. At `γ ≤ 1` this is closure
of open sets under unions; at `γ > 1` a countable union of union-form sets is again
a union of the same lower-level pieces, reindexed through `ℕ ≃ ℕ × ℕ`. -/
theorem borelSigma_iUnion {Z : Type*} [MetricSpace Z] {γ : Ordinal}
    {A : ℕ → Set Z} (h : ∀ n, A n ∈ borelSigma (Y := Z) γ) :
    (⋃ n, A n) ∈ borelSigma (Y := Z) γ := by
  by_cases hγ1 : γ ≤ 1
  · rw [borelSigma, ite_eq_left hγ1]
    refine isOpen_iUnion fun n => ?_
    have hn := h n; rwa [borelSigma, ite_eq_left hγ1] at hn
  · rw [borelSigma, ite_eq_right hγ1] at h ⊢
    choose f hf using h
    let e : ℕ ≃ ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ)).symm
    refine ⟨fun k => f (e k).1 (e k).2, fun k => (hf (e k).1).1 (e k).2, ?_⟩
    rw [Set.iUnion_congr fun n => (hf n).2]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, m, hx⟩
      exact ⟨e.symm (n, m), by simpa using hx⟩
    · rintro ⟨k, hx⟩
      exact ⟨(e k).1, (e k).2, hx⟩

/-- The Borel code level `ℓ(c)`, distinct from the ordinary node rank `ρ_c`:
a leaf sits at level `1`, a complement raises the level by one, and a union
takes the supremum of its children's levels. Thus a union need not strictly
increase this measure. See `borel-structure §borel-codes-rank`. -/
noncomputable def BorelCode.lvl : BorelCode → Ordinal.{0}
  | .leaf _ => 1
  | .union f => ⨆ n, (f n).lvl
  | .compl c => c.lvl + 1

/-- Every code's level is at least `1`. -/
theorem BorelCode.one_le_lvl (c : BorelCode) : 1 ≤ c.lvl := by
  induction c with
  | leaf n => exact le_rfl
  | union f ih => exact le_trans (ih 0) (Ordinal.le_iSup (fun n => (f n).lvl) 0)
  | compl c ih => exact le_trans ih le_self_add

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    To bound the Borel rank of $A_c$, use an ordinal measure adapted to the decoding operations. Define the
    \termdefine{Borel code level} $\ell(c)$ by structural recursion on the code:
    $$
    \begin{aligned}
    \ell(\BorelLeafCode{n}) &= 1,\\
    \ell(\BorelComplementCode{c'}) &= \ell(c') + 1,\\
    \ell(\BorelUnionCode{\Sequence{c_k}{k\in\omega}}) &= \sup_k \ell(c_k).
    \end{aligned}
    $$
    This differs from $\rho$: a union need not increase the code level above the levels of its subcodes.
    The code level gives an upper bound on the Borel rank of the decoded set:
    $$
    A_c \in \bSigma^0_{\ell(c)}(X).
    $$
    The proof is induction on the code, following the three clauses. A leaf decodes to a basic open set, so $A_c \in
    \bSigma^0_1$. A complement decodes to $\SetDifference{X}{A_{c'}}$ with $A_{c'} \in \bSigma^0_{\ell(c')}$; this
    set is $\bPi^0_{\ell(c')}$, hence $\bSigma^0_{\ell(c')+1}$. A union decodes to $\bigcup_k A_{c_k}$ with each
    $A_{c_k} \in \bSigma^0_{\ell(c_k)} \IncludedIn \bSigma^0_{\sup_k \ell(c_k)}$, and each level $\bSigma^0_\gamma$ is
    closed under countable unions, so the union stays at level $\sup_k \ell(c_k)$. Since every $\ell(c)$ is a countable
    ordinal, a countable-rank code always decodes to a Borel set of countable Borel rank.
-/
/-- Borel rank is bounded by the Borel code level: for an open basis `U`, the set decoded by
`c` lies in `Σ⁰_{lvl c}` (borel-structure §borel-codes-rank). The proof is the
book's structural induction on the code — leaves are open
(`Σ⁰_1`), a complement raises `Π⁰_α ⊆ Σ⁰_{α+1}`, and a union of children at levels
`≤ γ := ⨆ lvl` stays in `Σ⁰_γ` by closure under countable unions. -/
theorem BorelCode.decode_mem_borelSigma_lvl {Z : Type*} [MetricSpace Z] {U : ℕ → Set Z}
    (hU : ∀ n, IsOpen (U n)) (c : BorelCode) :
    c.decode U ∈ borelSigma (Y := Z) c.lvl := by
  induction c with
  | leaf n =>
    show U n ∈ borelSigma (Y := Z) 1
    rw [borelSigma_one]; exact hU n
  | union f ih =>
    refine borelSigma_iUnion fun n => ?_
    exact borelSigma_mono (BorelCode.one_le_lvl (f n)) (Ordinal.le_iSup (fun n => (f n).lvl) n) (ih n)
  | compl c ih =>
    have hpi : (c.decode U)ᶜ ∈ borelPi (Y := Z) c.lvl := by
      show ((c.decode U)ᶜ)ᶜ ∈ borelSigma (Y := Z) c.lvl
      rw [compl_compl]; exact ih
    exact borelPi_subset_borelSigma_succ (BorelCode.one_le_lvl c) hpi

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    A $\bDelta^0_1$ set is both open and closed, so finite prefix information decides the answer either way.
-/
/-- `Δ⁰_1` is exactly the clopen sets: a set is both `Σ⁰_1` (open) and `Π⁰_1`
(closed) iff it is clopen (borel-structure §borel-hierarchy-baire, "a `Δ⁰_1` set
is both open and closed"). -/
theorem borelDelta_one : borelDelta (Y := Y) 1 = {s : Set Y | IsClopen s} := by
  ext s
  simp only [borelDelta, Set.mem_inter_iff, borelSigma_one, borelPi, Set.mem_ofPred_eq,
    isOpen_compl_iff]
  constructor
  · rintro ⟨ho, hc⟩; exact ⟨hc, ho⟩
  · rintro ⟨hc, ho⟩; exact ⟨ho, hc⟩

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    For example, in $\BaireSpace$ the set
    $$
    \{x : x(n)=0 \text{ for infinitely many } n\}
    =
    \bigcap_{m\in\omega}\bigcup_{n\ge m}\{x:x(n)=0\}
    $$
    is $\Gdelta$, hence $\bPi^0_2$: after every finite stage there must be a later zero. Its complement, the set of
    sequences eventually avoiding $0$, is $\Fsigma$:
    $$
    \{x : \exists m\,\forall n\ge m\,x(n)\ne 0\}
    =
    \bigcup_{m\in\omega}\bigcap_{n\ge m}\{x:x(n)\ne 0\}.
    $$
    This is the typical Baire-space reading of the hierarchy: existential countable choices appear as countable unions,
    universal countable requirements as countable intersections, and closed conditions as infinite branches through trees.
-/
/-- A concrete level computation in Baire space `ℕ → ℕ`: the set of sequences that
are `0` infinitely often is `Gδ`, hence `Π⁰_2` (borel-structure
§borel-hierarchy-baire). It is `⋂_m ⋃_{n ≥ m} {x : x n = 0}`, a countable
intersection of open sets, since each `{x : x n = 0}` is clopen. -/
theorem baire_infinitelyOftenZero_mem_borelPi_two :
    {x : ℕ → ℕ | ∀ m, ∃ n, m ≤ n ∧ x n = 0} ∈ borelPi (Y := ℕ → ℕ) 2 := by
  rw [borelPi_two]
  show IsGδ {x : ℕ → ℕ | ∀ m, ∃ n, m ≤ n ∧ x n = 0}
  have hset : {x : ℕ → ℕ | ∀ m, ∃ n, m ≤ n ∧ x n = 0}
      = ⋂ m, ⋃ n, {x : ℕ → ℕ | m ≤ n ∧ x n = 0} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
  rw [hset]
  refine IsGδ.iInter_of_isOpen fun m => isOpen_iUnion fun n => ?_
  by_cases h : m ≤ n
  · simp only [h, true_and]
    exact (continuous_apply n).isOpen_preimage {0} (isOpen_discrete _)
  · simp only [h, false_and, Set.ofPred_false]
    exact isOpen_empty

/-- The complement of the previous example — sequences that are eventually nonzero
— is `Fσ` (`Σ⁰_2`), by `Fσ`/`Gδ` duality. This is the book's companion
computation (borel-structure §borel-hierarchy-baire). -/
theorem baire_eventuallyNonzero_mem_borelSigma_two :
    {x : ℕ → ℕ | ∃ m, ∀ n, m ≤ n → x n ≠ 0} ∈ borelSigma (Y := ℕ → ℕ) 2 := by
  have hset : {x : ℕ → ℕ | ∃ m, ∀ n, m ≤ n → x n ≠ 0}
      = {x : ℕ → ℕ | ∀ m, ∃ n, m ≤ n ∧ x n = 0}ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_exists, not_and, ne_eq]
  rw [hset]
  have h := baire_infinitelyOftenZero_mem_borelPi_two
  rwa [borelPi, Set.mem_ofPred_eq] at h

end PolishSpaceBook
