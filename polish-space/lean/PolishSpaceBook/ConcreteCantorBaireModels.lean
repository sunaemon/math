module

public import PolishSpaceBook.CantorBaireSpace
public import PolishSpaceBook.MediantIntervals
public import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.List.TakeWhile
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete models of Cantor and Baire space

Formalization targets for
`polish-space/src/polish-space-book/concrete-cantor-baire-models.md`.
-/

namespace PolishSpaceBook

open Set TopologicalSpace Topology

/-!
## Concrete Cantor-space models

| Book notation | Lean name |
| --- | --- |
| `\PowerSet{\omega}` | `powersetOmega` |
| characteristic function `\chi_E` | `subsetCharacteristic E` |
| finite membership-decision clopen set | `membershipDecisionSet F G` |
| middle-thirds Cantor set | mathlib `cantorSet` |
-/

theorem isClopen_cantor_immediate_subcylinder (s : finseq Bool) (ε : Bool) :
    IsClopen (cyl (concat s [ε]) : Set cantor_space) :=
  cantor_cyl_clopen (concat s [ε])

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For $s\in\finseq{2}$, the usual cylinder in $\CantorSpace$ is
    $\cyl{s}=\{x\in\CantorSpace:s\prefixOf x\}$. These cylinders split into two immediate
    subcylinders at each node and form the standard clopen basis.
-/
/-- A Cantor-space cylinder is the union of its two immediate subcylinders. -/
theorem cantor_cyl_eq_union_immediate_subcylinders (s : finseq Bool) :
    (cyl s : Set cantor_space) =
      cyl (concat s [false]) ∪ cyl (concat s [true]) := by
  ext x
  constructor
  · intro hx
    cases h : x s.length
    · left
      exact (mem_cyl_concat_iff (s := s) (t := [false])).2
        ⟨hx, by simp [h]⟩
    · right
      exact (mem_cyl_concat_iff (s := s) (t := [true])).2
        ⟨hx, by simp [h]⟩
  · rintro (hx | hx)
    · exact cyl_concat_subset s [false] hx
    · exact cyl_concat_subset s [true] hx

/-- The two immediate Cantor subcylinders are disjoint. -/
theorem disjoint_cantor_immediate_subcylinders (s : finseq Bool) :
    Disjoint (cyl (concat s [false]) : Set cantor_space) (cyl (concat s [true])) := by
  rw [Set.disjoint_left]
  intro x hxfalse hxtrue
  have htail_false :=
    (mem_cyl_concat_iff (s := s) (t := [false]) (x := x)).1 hxfalse
  have htail_true :=
    (mem_cyl_concat_iff (s := s) (t := [true]) (x := x)).1 hxtrue
  have hfalse : x s.length = false := by
    simpa using (prefixOfSeq_singleton.1 htail_false.2)
  have htrue : x s.length = true := by
    simpa using (prefixOfSeq_singleton.1 htail_true.2)
  exact Bool.noConfusion (hfalse.symm.trans htrue)

theorem isTopologicalBasis_cantor_cyl :
    IsTopologicalBasis ({U : Set cantor_space | ∃ s : finseq Bool, U = cyl s}) :=
  isTopologicalBasis_cyl (A := Bool)

/-- Book notation `\PowerSet{\omega}` as a topological model of Cantor space. -/
abbrev powersetOmega : Type :=
  Set ℕ

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Identify a subset $E\IncludedIn\omega$ with its characteristic function:
    $$
    \chi:\PowerSet{\omega}\longrightarrow 2^\omega,
    \qquad
    \chi(E)(n)=
    \begin{cases}
    1,&n\in E,\\
    0,&n\notin E.
    \end{cases}
    $$
    The inverse sends $x\in2^\omega$ to $\{n\in\omega:x(n)=1\}$.
-/
/-- The characteristic function of a subset of `ω`, as a point of Cantor space. -/
noncomputable def subsetCharacteristic (E : powersetOmega) : cantor_space := by
  classical
  exact fun n => if n ∈ (E : Set ℕ) then true else false

/-- The subset of `ω` coded by a binary sequence. -/
def characteristicSubset (x : cantor_space) : powersetOmega :=
  {n | x n = true}

noncomputable instance : TopologicalSpace powersetOmega :=
  TopologicalSpace.induced subsetCharacteristic inferInstance

theorem subsetCharacteristic_characteristicSubset (x : cantor_space) :
    subsetCharacteristic (characteristicSubset x) = x := by
  classical
  ext n
  by_cases hx : x n = true
  · simp [subsetCharacteristic, characteristicSubset, hx]
  · simp [subsetCharacteristic, characteristicSubset, hx]

theorem characteristicSubset_subsetCharacteristic (E : powersetOmega) :
    characteristicSubset (subsetCharacteristic E) = E := by
  classical
  ext n
  simp [subsetCharacteristic, characteristicSubset]

/-- Identifying a subset of `ω` with its characteristic function. -/
noncomputable def powersetOmegaEquivCantorSpace : powersetOmega ≃ cantor_space where
  toFun := subsetCharacteristic
  invFun := characteristicSubset
  left_inv := characteristicSubset_subsetCharacteristic
  right_inv := subsetCharacteristic_characteristicSubset

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The inverse image of a cylinder is
    $$
    \chi^{-1}(\cyl{s})=
    \left\{E\IncludedIn\omega:\forall n<|s|,\quad
    \begin{aligned}
    s(n)=1&\implies n\in E,\\
    s(n)=0&\implies n\notin E
    \end{aligned}
    \right\}.
    $$
-/
/-- Pulling a binary cylinder back along the characteristic-function bijection. -/
theorem subsetCharacteristic_preimage_cyl (s : finseq Bool) :
    subsetCharacteristic ⁻¹' (cyl s : Set cantor_space) =
      {E : powersetOmega | ∀ n, ∀ hn : n < s.length,
        n ∈ E ↔ s.get ⟨n, hn⟩ = true} := by
  classical
  ext E
  change (∀ n, ∀ hn : n < s.length, subsetCharacteristic E n = s.get ⟨n, hn⟩) ↔ _
  constructor
  · intro h n hn
    rw [← h n hn]
    simp [subsetCharacteristic]
  · intro h n hn
    have := h n hn
    cases hs : s.get ⟨n, hn⟩ <;> simp_all [subsetCharacteristic]

/-- The product topology on `\PowerSet{\omega}` is the one transported from `2^ω`. -/
noncomputable def powersetOmegaHomeomorphCantorSpace : powersetOmega ≃ₜ cantor_space :=
  powersetOmegaEquivCantorSpace.toHomeomorphOfIsInducing ⟨rfl⟩

theorem powersetOmegaHomeomorphCantorSpace_apply (E : powersetOmega) :
    powersetOmegaHomeomorphCantorSpace E = subsetCharacteristic E :=
  rfl

/-- The power-set model is compact because it is homeomorphic to Cantor space. -/
theorem powersetOmega_compact :
    CompactSpace powersetOmega := by
  have : CompactSpace cantor_space := cantor_space_compact
  exact powersetOmegaHomeomorphCantorSpace.symm.compactSpace

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    More generally, a \termuse{cylinder} is a set obtained by prescribing values at finitely many positions of a sequence.
    Under the characteristic-function identification, for finite sets $F,G\IncludedIn\omega$, define the cylinder
    $$
    \relax[F;G]:=
    \left\{E\IncludedIn\omega:\forall n\in\omega,\quad
    \begin{aligned}
    n\in F&\implies n\in E,\\
    n\in G&\implies n\notin E
    \end{aligned}
    \right\}.
    $$
-/
/-- Finite membership decisions: contain every member of `F` and avoid every member of `G`. -/
def membershipDecisionSet (F G : Finset ℕ) : Set powersetOmega :=
  {E | (∀ n, n ∈ F → n ∈ (E : Set ℕ)) ∧ (∀ n, n ∈ G → n ∉ (E : Set ℕ))}

theorem membershipDecisionSet_disjoint_form (F G : Finset ℕ) :
    membershipDecisionSet F G =
      {E : powersetOmega | (F : Set ℕ) ⊆ (E : Set ℕ) ∧ Disjoint (G : Set ℕ) (E : Set ℕ)} := by
  ext E
  constructor
  · rintro ⟨hF, hG⟩
    refine ⟨?_, ?_⟩
    · intro n hn
      exact hF n hn
    · rw [Set.disjoint_left]
      intro n hnG hnE
      exact hG n hnG hnE
  · rintro ⟨hF, hG⟩
    refine ⟨fun n hn => hF hn, ?_⟩
    intro n hnG hnE
    exact (Set.disjoint_left.mp hG) hnG hnE

theorem membershipDecisionSet_nonempty_iff_disjoint (F G : Finset ℕ) :
    (membershipDecisionSet F G).Nonempty ↔ Disjoint (F : Set ℕ) (G : Set ℕ) := by
  constructor
  · rintro ⟨E, hF, hG⟩
    rw [Set.disjoint_left]
    intro n hnF hnG
    exact hG n hnG (hF n hnF)
  · intro hdisj
    refine ⟨(F : Set ℕ), ?_⟩
    constructor
    · intro n hnF
      exact hnF
    · intro n hnG hnF
      exact (Set.disjoint_left.mp hdisj) hnF hnG

theorem membershipDecisionSet_eq_empty_of_not_disjoint {F G : Finset ℕ}
    (h : ¬ Disjoint (F : Set ℕ) (G : Set ℕ)) :
    membershipDecisionSet F G = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  exact fun hnonempty => h ((membershipDecisionSet_nonempty_iff_disjoint F G).1 hnonempty)

theorem isClopen_cantor_membershipDecisions (F G : Finset ℕ) :
    IsClopen {x : cantor_space | (∀ n, n ∈ F → x n = true) ∧ (∀ n, n ∈ G → x n = false)} := by
  classical
  have hF : IsClopen {x : cantor_space | ∀ n, n ∈ F → x n = true} := by
    rw [show {x : cantor_space | ∀ n, n ∈ F → x n = true} =
        ⋂ n : {n : ℕ // n ∈ F}, {x : cantor_space | x n.1 = true} by
      ext x
      simp]
    exact isClopen_iInter_of_finite fun n =>
      (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply n.1)
  have hG : IsClopen {x : cantor_space | ∀ n, n ∈ G → x n = false} := by
    rw [show {x : cantor_space | ∀ n, n ∈ G → x n = false} =
        ⋂ n : {n : ℕ // n ∈ G}, {x : cantor_space | x n.1 = false} by
      ext x
      simp]
    exact isClopen_iInter_of_finite fun n =>
      (isClopen_discrete ({false} : Set Bool)).preimage (continuous_apply n.1)
  rw [show {x : cantor_space | (∀ n, n ∈ F → x n = true) ∧ (∀ n, n ∈ G → x n = false)} =
      {x : cantor_space | ∀ n, n ∈ F → x n = true} ∩
        {x : cantor_space | ∀ n, n ∈ G → x n = false} by
    ext x
    rfl]
  exact hF.inter hG

theorem membershipDecisionSet_isClopen (F G : Finset ℕ) :
    IsClopen (membershipDecisionSet F G) := by
  classical
  have htarget := isClopen_cantor_membershipDecisions F G
  have hpre := htarget.preimage powersetOmegaHomeomorphCantorSpace.continuous
  convert hpre using 1
  ext E
  simp [membershipDecisionSet, powersetOmegaHomeomorphCantorSpace_apply, subsetCharacteristic]

theorem exists_membershipDecisionSet_subset_of_mem_open {U : Set powersetOmega} {E : powersetOmega}
    (hE : E ∈ U) (hU : IsOpen U) :
    ∃ F G : Finset ℕ, E ∈ membershipDecisionSet F G ∧ membershipDecisionSet F G ⊆ U := by
  classical
  let H := powersetOmegaHomeomorphCantorSpace
  have hHU : IsOpen (H '' U) := H.isOpenMap U hU
  have hHE : H E ∈ H '' U := ⟨E, hE, rfl⟩
  obtain ⟨s, hHs, hsHU⟩ := exists_cyl_subset_of_mem_open (A := Bool) hHE hHU
  let F : Finset ℕ := (Finset.range s.length).filter fun n => n ∈ (E : Set ℕ)
  let G : Finset ℕ := (Finset.range s.length).filter fun n => n ∉ (E : Set ℕ)
  refine ⟨F, G, ?_, ?_⟩
  · simp [membershipDecisionSet, F, G]
  · intro E' hE'
    have hprefix : H E' ∈ cyl s := by
      intro i hi
      have hirange : i ∈ Finset.range s.length := by
        simpa using hi
      have hcoord : H E' i = H E i := by
        by_cases hiE : i ∈ (E : Set ℕ)
        · have hiF : i ∈ F := by
            simp [F, hirange, hiE]
          have hiE' : i ∈ (E' : Set ℕ) := hE'.1 i hiF
          simp [H, powersetOmegaHomeomorphCantorSpace_apply, subsetCharacteristic, hiE, hiE']
        · have hiG : i ∈ G := by
            simp [G, hirange, hiE]
          have hiE' : i ∉ (E' : Set ℕ) := hE'.2 i hiG
          simp [H, powersetOmegaHomeomorphCantorSpace_apply, subsetCharacteristic, hiE, hiE']
      exact hcoord.trans (hHs i hi)
    rcases hsHU hprefix with ⟨E₀, hE₀, hE₀eq⟩
    have hEq : E' = E₀ := H.injective hE₀eq.symm
    simpa [hEq] using hE₀

theorem isTopologicalBasis_membershipDecisionSet :
    IsTopologicalBasis {U : Set powersetOmega | ∃ F G : Finset ℕ, U = membershipDecisionSet F G} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨F, G, rfl⟩
    exact (membershipDecisionSet_isClopen F G).isOpen
  · intro E U hE hU
    rcases exists_membershipDecisionSet_subset_of_mem_open hE hU with ⟨F, G, hEFG, hsub⟩
    exact ⟨membershipDecisionSet F G, ⟨F, G, rfl⟩, hEFG, hsub⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Conversely, choose $k$ such that $F\cup G\IncludedIn\{0,\ldots,k-1\}$.
    Then
    $$
    \relax[F;G]=\bigcup\left\{\chi^{-1}(\cyl{s}):
    s\in\funcspace{k}{2},\;F\IncludedIn F_s,\;G\IncludedIn G_s\right\}.
    $$
    The right-hand side is a finite union, so the sets $[F;G]$ also form a clopen basis.
    If $F\cap G\ne\emptyset$, then $[F;G]=\emptyset$.
-/
/-- Book-facing package for the power-set Cantor model: characteristic functions
give a homeomorphism with Cantor space, finite positive and negative membership
requirements are clopen basic neighborhoods, and such a neighborhood is nonempty
exactly when the positive and negative requirements are disjoint. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Equip $\PowerSet{\omega}$ with the topology
    that makes this bijection $\chi$ a homeomorphism onto $2^\omega$ with its product topology.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    These inverse images form a clopen basis.
-/
theorem concretePowerSetModelFacts :
    Nonempty (powersetOmega ≃ₜ cantor_space) ∧
      (∀ E : powersetOmega,
        powersetOmegaHomeomorphCantorSpace E = subsetCharacteristic E) ∧
      (∀ x : cantor_space,
        powersetOmegaHomeomorphCantorSpace.symm x = characteristicSubset x) ∧
      (∀ F G : Finset ℕ,
        membershipDecisionSet F G =
            {E : powersetOmega |
              (F : Set ℕ) ⊆ (E : Set ℕ) ∧ Disjoint (G : Set ℕ) (E : Set ℕ)} ∧
          ((membershipDecisionSet F G).Nonempty ↔ Disjoint (F : Set ℕ) (G : Set ℕ)) ∧
          (¬ Disjoint (F : Set ℕ) (G : Set ℕ) → membershipDecisionSet F G = ∅) ∧
          IsClopen (membershipDecisionSet F G)) ∧
      IsTopologicalBasis {U : Set powersetOmega | ∃ F G : Finset ℕ, U = membershipDecisionSet F G} ∧
      CompactSpace powersetOmega := by
  refine ⟨⟨powersetOmegaHomeomorphCantorSpace⟩, ?_, ?_, ?_, ?_, powersetOmega_compact⟩
  · exact powersetOmegaHomeomorphCantorSpace_apply
  · intro x
    rfl
  · intro F G
    exact ⟨membershipDecisionSet_disjoint_form F G,
      membershipDecisionSet_nonempty_iff_disjoint F G,
      fun h => membershipDecisionSet_eq_empty_of_not_disjoint h,
      membershipDecisionSet_isClopen F G⟩
  · exact isTopologicalBasis_membershipDecisionSet

theorem membershipDecisionSet_agree_below {A E : powersetOmega} {N : ℕ}
    [DecidablePred fun n => n ∈ (A : Set ℕ)]
    [DecidablePred fun n => n ∉ (A : Set ℕ)]
    (hE : E ∈ membershipDecisionSet
      ((Finset.range N).filter fun n => n ∈ (A : Set ℕ))
      ((Finset.range N).filter fun n => n ∉ (A : Set ℕ))) :
    ∀ m, m < N → (m ∈ (E : Set ℕ) ↔ m ∈ (A : Set ℕ)) := by
  intro m hmN
  constructor
  · intro hmE
    by_contra hmA
    have hmG : m ∈ (Finset.range N).filter fun n => n ∉ (A : Set ℕ) := by
      simp [hmN, hmA]
    exact hE.2 m hmG hmE
  · intro hmA
    have hmF : m ∈ (Finset.range N).filter fun n => n ∈ (A : Set ℕ) := by
      simp [hmN, hmA]
    exact hE.1 m hmF

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \item \emph{Middle-thirds Cantor set.} Let $C\IncludedIn[0,1]$ be the set of reals with a ternary expansion using only
    the digits $0$ and $2$.
-/
/-- The classical middle-thirds Cantor set. This is mathlib's ternary Cantor set. -/
abbrev middleThirdsCantorSet : Set ℝ :=
  cantorSet

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Define
    $$
    h:2^\omega\longrightarrow C,
    \qquad
    h(x)=\sum_{n=0}^{\infty}\frac{2x_n}{3^{n+1}}
    $$
    by reading a binary sequence as ternary digits $2x_0,2x_1,\ldots$. This map is onto by the definition of $C$.
    If two sequences first differ at position $k$, the contribution $2/3^{k+1}$ there exceeds the sum
    $1/3^{k+1}$ of all possible later differences, so their images differ. If they agree at the first $k$ positions,
    their images differ by at most $3^{-k}$, proving continuity. Thus $h$ is a continuous bijection from a compact
    space to a Hausdorff space, and hence a homeomorphism.
-/
/-- The middle-thirds Cantor set is homeomorphic to Cantor space. -/
noncomputable def middleThirdsCantorHomeomorph : cantor_space ≃ₜ middleThirdsCantorSet :=
  cantorSetHomeomorphNatToBool.symm

/-- The middle-thirds Cantor-set model is compact because it is homeomorphic to
Cantor space. -/
theorem middleThirdsCantorSet_compact :
    CompactSpace middleThirdsCantorSet := by
  have : CompactSpace cantor_space := cantor_space_compact
  exact middleThirdsCantorHomeomorph.compactSpace

theorem middleThirdsCantorHomeomorph_apply (x : cantor_space) :
    (middleThirdsCantorHomeomorph x : ℝ) =
      Real.ofDigits (fun n => cond (x n) (2 : Fin 3) 0) :=
  rfl

theorem middleThirdsCantorSet_eq_zero_two_ofDigits :
    middleThirdsCantorSet =
      {x | ∃ a : ℕ → Fin 3, (∀ n, a n ≠ 1) ∧ Real.ofDigits a = x} :=
  cantorSet_eq_zero_two_ofDigits

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The interval $I_s$ is the corresponding stage-$k$ interval of the middle-third construction, and
    $$h(\cyl{s})=C\cap I_s.$$
-/
/-- The part of the middle-thirds Cantor set whose ternary expansion has the finite
prefix determined by the binary word `s`. -/
def middleThirdsTernaryPrefixSet (s : finseq Bool) : Set middleThirdsCantorSet :=
  {y | ∃ a : ℕ → Fin 3,
    (∀ n, a n ≠ 1) ∧
      Real.ofDigits a = y.1 ∧
        ∀ i (hi : i < s.length), a i = cond (s.get ⟨i, hi⟩) (2 : Fin 3) 0}

/-- Binary cylinders become exactly the Cantor-set pieces with the matching finite
ternary prefix. This is the formal version of the book's stage-`k` middle-thirds
interval statement. -/
theorem middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet (s : finseq Bool) :
    middleThirdsCantorHomeomorph '' cyl s = middleThirdsTernaryPrefixSet s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun n => cond (x n) (2 : Fin 3) 0, ?_, ?_, ?_⟩
    · intro n
      cases hxn : x n <;> simp [hxn]
    · exact (middleThirdsCantorHomeomorph_apply x).symm
    · intro i hi
      have hxi : x i = s.get ⟨i, hi⟩ := hx i hi
      simp [hxi]
  · rintro ⟨a, ha_no_one, ha_value, ha_prefix⟩
    let x : cantor_space := middleThirdsCantorHomeomorph.symm y
    let b : ℕ → Fin 3 := fun n => cond (x n) (2 : Fin 3) 0
    have hxy : middleThirdsCantorHomeomorph x = y := by
      simp [x]
    have hb_no_one : ∀ n, b n ≠ 1 := by
      intro n
      cases hxn : x n <;> simp [b, hxn]
    have hb_value : Real.ofDigits b = y.1 := by
      calc
        Real.ofDigits b = (middleThirdsCantorHomeomorph x : ℝ) := by
          simpa [b] using (middleThirdsCantorHomeomorph_apply x).symm
        _ = y.1 := congrArg Subtype.val hxy
    have hba : b = a :=
      ofDigits_zero_two_sequence_unique hb_no_one ha_no_one (hb_value.trans ha_value.symm)
    refine ⟨x, ?_, hxy⟩
    intro i hi
    have hdigit := congrFun hba i
    let si : Bool := s.get ⟨i, hi⟩
    have hprefix := ha_prefix i hi
    have hdigits_eq :
        cond (x i) (2 : Fin 3) 0 = cond si (2 : Fin 3) 0 := by
      simpa [b, si] using hdigit.trans hprefix
    change x i = si
    cases hxi : x i <;> cases hsi : si <;>
      simp [hxi, hsi] at hdigits_eq ⊢

/-- Finite middle-thirds prefix pieces are nested under extension of the binary
prefix. -/
theorem middleThirdsTernaryPrefixSet_subset_of_prefix {s t : finseq Bool}
    (hst : prefixOf s t) :
    middleThirdsTernaryPrefixSet t ⊆ middleThirdsTernaryPrefixSet s := by
  rw [← middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet t,
    ← middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet s]
  exact Set.image_mono (cyl_subset_of_prefix hst)

/-- Ternary-prefix pieces form a topological basis for the middle-thirds Cantor set. -/
theorem isTopologicalBasis_middleThirdsTernaryPrefixSet :
    IsTopologicalBasis {U : Set middleThirdsCantorSet |
      ∃ s : finseq Bool, U = middleThirdsTernaryPrefixSet s} := by
  let H := middleThirdsCantorHomeomorph
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨s, rfl⟩
    have himage : IsClopen (H '' cyl s) :=
      ⟨H.isClosedMap _ (isClopen_cyl s).isClosed,
        H.isOpenMap _ (isClopen_cyl s).isOpen⟩
    simpa [H, middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet s] using
      himage.isOpen
  · intro y U hyU hU
    have hpreOpen : IsOpen (H ⁻¹' U) := hU.preimage H.continuous
    have hyPre : H.symm y ∈ H ⁻¹' U := by
      simpa [H] using hyU
    obtain ⟨s, hys, hsU⟩ := exists_cyl_subset_of_mem_open (A := Bool) hyPre hpreOpen
    refine ⟨middleThirdsTernaryPrefixSet s, ⟨s, rfl⟩, ?_, ?_⟩
    · rw [← middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet]
      exact ⟨H.symm y, hys, by simp [H]⟩
    · intro z hz
      rw [← middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet] at hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hsU hx

/-- Book-facing package for the middle-thirds Cantor model: the Cantor set is the
zero/two ternary-digit set, the homeomorphism sends a binary sequence to the
corresponding ternary digit sequence, finite binary cylinders map to finite
ternary-prefix pieces, those pieces are nested under prefix extension, and those
pieces are clopen. -/
theorem concreteMiddleThirdsCantorModelFacts :
    Nonempty (cantor_space ≃ₜ middleThirdsCantorSet) ∧
      (∀ x : cantor_space,
        (middleThirdsCantorHomeomorph x : ℝ) =
          Real.ofDigits (fun n => cond (x n) (2 : Fin 3) 0)) ∧
      middleThirdsCantorSet =
        {x | ∃ a : ℕ → Fin 3, (∀ n, a n ≠ 1) ∧ Real.ofDigits a = x} ∧
      (∀ s : finseq Bool,
        middleThirdsCantorHomeomorph '' (cyl s : Set cantor_space) =
            middleThirdsTernaryPrefixSet s ∧
          IsClopen (middleThirdsTernaryPrefixSet s)) ∧
      (∀ s t : finseq Bool,
        prefixOf s t →
          middleThirdsTernaryPrefixSet t ⊆ middleThirdsTernaryPrefixSet s) ∧
      CompactSpace middleThirdsCantorSet := by
  refine ⟨⟨middleThirdsCantorHomeomorph⟩, ?_, middleThirdsCantorSet_eq_zero_two_ofDigits,
    ?_, ?_, middleThirdsCantorSet_compact⟩
  · exact middleThirdsCantorHomeomorph_apply
  · intro s
    have hprefix : middleThirdsCantorHomeomorph '' (cyl s : Set cantor_space) =
        middleThirdsTernaryPrefixSet s :=
      middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet s
    refine ⟨hprefix, ?_⟩
    have himage : IsClopen (middleThirdsCantorHomeomorph '' (cyl s : Set cantor_space)) :=
      ⟨middleThirdsCantorHomeomorph.isClosedMap _ (isClopen_cyl s).isClosed,
        middleThirdsCantorHomeomorph.isOpenMap _ (isClopen_cyl s).isOpen⟩
    simpa [hprefix] using himage
  · intro s t hst
    exact middleThirdsTernaryPrefixSet_subset_of_prefix hst

/-!
## Basic Baire-space cylinders
-/

theorem isClopen_baire_immediate_subcylinder (s : finseq ℕ) (n : ℕ) :
    IsClopen (cyl (concat s [n]) : Set baire_space) :=
  baire_cyl_clopen (concat s [n])

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \item \emph{Baire-space cylinders.} The reference model is $\BaireSpace$ with its usual cylinders
    $\cyl{s}=\{x\in\BaireSpace:s\prefixOf x\}$ for $s\in\finseq{\omega}$. Each cylinder splits into countably many
    immediate subcylinders $\cyl{s\concat(n)}$, giving the standard coding tree for open and closed subsets of
    $\BaireSpace$.
-/
/-- A Baire-space cylinder is the union of its countably many immediate
subcylinders. -/
theorem baire_cyl_eq_iUnion_immediate_subcylinders (s : finseq ℕ) :
    (cyl s : Set baire_space) = ⋃ n : ℕ, cyl (concat s [n]) := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.2 ⟨x s.length, ?_⟩
    exact (mem_cyl_concat_iff (s := s) (t := [x s.length])).2
      ⟨hx, by simp⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
    exact cyl_concat_subset s [n] hxn

/-- Distinct immediate Baire subcylinders are disjoint. -/
theorem disjoint_baire_immediate_subcylinders (s : finseq ℕ) {m n : ℕ}
    (hmn : m ≠ n) :
    Disjoint (cyl (concat s [m]) : Set baire_space) (cyl (concat s [n])) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  have htail_m := (mem_cyl_concat_iff (s := s) (t := [m]) (x := x)).1 hxm
  have htail_n := (mem_cyl_concat_iff (s := s) (t := [n]) (x := x)).1 hxn
  have hm : x s.length = m := by
    simpa using (prefixOfSeq_singleton.1 htail_m.2)
  have hn : x s.length = n := by
    simpa using (prefixOfSeq_singleton.1 htail_n.2)
  exact hmn (hm.symm.trans hn)

theorem isTopologicalBasis_baire_cyl :
    IsTopologicalBasis ({U : Set baire_space | ∃ s : finseq ℕ, U = cyl s}) :=
  isTopologicalBasis_cyl (A := ℕ)

/-- The two reference cylinder models have the structure described in the book:
Cantor cylinders are clopen, split into two disjoint immediate subcylinders, and
form a basis; Baire cylinders are clopen, split into countably many pairwise
disjoint immediate subcylinders, and form a basis. -/
theorem concreteReferenceCylinderModelFacts :
    (∀ s : finseq Bool, IsClopen (cyl s : Set cantor_space)) ∧
      (∀ s : finseq Bool,
        (cyl s : Set cantor_space) =
            cyl (concat s [false]) ∪ cyl (concat s [true]) ∧
          Disjoint (cyl (concat s [false]) : Set cantor_space)
            (cyl (concat s [true]))) ∧
      IsTopologicalBasis ({U : Set cantor_space | ∃ s : finseq Bool, U = cyl s}) ∧
      (∀ s : finseq ℕ, IsClopen (cyl s : Set baire_space)) ∧
      (∀ s : finseq ℕ,
        (cyl s : Set baire_space) = ⋃ n : ℕ, cyl (concat s [n]) ∧
          ∀ m n : ℕ, m ≠ n →
            Disjoint (cyl (concat s [m]) : Set baire_space)
              (cyl (concat s [n]))) ∧
      IsTopologicalBasis ({U : Set baire_space | ∃ s : finseq ℕ, U = cyl s}) := by
  refine ⟨?_, ?_, isTopologicalBasis_cantor_cyl, ?_, ?_, isTopologicalBasis_baire_cyl⟩
  · intro s
    exact isClopen_cyl s
  · intro s
    exact ⟨cantor_cyl_eq_union_immediate_subcylinders s,
      disjoint_cantor_immediate_subcylinders s⟩
  · intro s
    exact isClopen_cyl s
  · intro s
    exact ⟨baire_cyl_eq_iUnion_immediate_subcylinders s,
      fun m n hmn => disjoint_baire_immediate_subcylinders s hmn⟩

/-!
## Simple continued fractions

The book uses the same continuant indexing as this file:
`simpleCFNum a 0 = 1`, `simpleCFDen a 0 = 0`, `simpleCFNum a 1 = 0`,
and `simpleCFDen a 1 = 1`. Thus `simpleCFNum a (n+1)` and
`simpleCFDen a (n+1)` are the numerator and denominator of the prefix
of length `n`.
-/

open scoped Topology

def simpleCFNum (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | n + 2 => a (n + 1) * simpleCFNum a (n + 1) + simpleCFNum a n

def simpleCFDen (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 1) * simpleCFDen a (n + 1) + simpleCFDen a n

@[simp]
theorem simpleCFNum_zero (a : ℕ → ℤ) :
    simpleCFNum a 0 = 1 :=
  rfl

@[simp]
theorem simpleCFNum_one (a : ℕ → ℤ) :
    simpleCFNum a 1 = 0 :=
  rfl

@[simp]
theorem simpleCFDen_zero (a : ℕ → ℤ) :
    simpleCFDen a 0 = 0 :=
  rfl

@[simp]
theorem simpleCFDen_one (a : ℕ → ℤ) :
    simpleCFDen a 1 = 1 :=
  rfl

theorem simpleCFNum_succ_succ (a : ℕ → ℤ) (n : ℕ) :
    simpleCFNum a (n + 2) = a (n + 1) * simpleCFNum a (n + 1) + simpleCFNum a n :=
  rfl

theorem simpleCFDen_succ_succ (a : ℕ → ℤ) (n : ℕ) :
    simpleCFDen a (n + 2) = a (n + 1) * simpleCFDen a (n + 1) + simpleCFDen a n :=
  rfl

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    For $n \ge 0$,
    \begin{equation*}
    p_{n+1} q_n - p_n q_{n+1} = (-1)^{n+1}. \tag{ii}
    \end{equation*}
    \emph{Base $n = 0$:} $p_1 q_0 - p_0 q_1 = -1$, from the seed values. \emph{Inductive step:}
    $$\begin{aligned}
    p_{n+2} q_{n+1} - p_{n+1} q_{n+2}
    &\;\overset{(*)}{=}\; (a_{n+1} p_{n+1} + p_n) q_{n+1} - p_{n+1} (a_{n+1} q_{n+1} + q_n) \\
    &\;=\; -(p_{n+1} q_n - p_n q_{n+1}) \\
    &\;\overset{\text{(ii)}}{=}\; (-1)^{n+2}.
    \end{aligned}$$
-/
theorem simpleCF_determinant (a : ℕ → ℤ) (n : ℕ) :
    simpleCFNum a (n + 1) * simpleCFDen a n -
        simpleCFNum a n * simpleCFDen a (n + 1) =
      (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [simpleCFNum_succ_succ, simpleCFDen_succ_succ]
      calc
        (a (n + 1) * simpleCFNum a (n + 1) + simpleCFNum a n) * simpleCFDen a (n + 1) -
            simpleCFNum a (n + 1) *
              (a (n + 1) * simpleCFDen a (n + 1) + simpleCFDen a n)
            = - (simpleCFNum a (n + 1) * simpleCFDen a n -
                simpleCFNum a n * simpleCFDen a (n + 1)) := by
              ring
        _ = -((-1 : ℤ) ^ (n + 1)) := by rw [ih]
        _ = (-1 : ℤ) ^ (n + 2) := by
              rw [pow_succ]
              ring

theorem simpleCF_common_divisor_dvd_one (a : ℕ → ℤ) (n : ℕ) {d : ℤ}
    (hp : d ∣ simpleCFNum a (n + 1)) (hq : d ∣ simpleCFDen a (n + 1)) :
    d ∣ (1 : ℤ) := by
  have hdiff :
      d ∣ simpleCFNum a (n + 1) * simpleCFDen a n -
          simpleCFNum a n * simpleCFDen a (n + 1) :=
    dvd_sub (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hq _)
  rw [simpleCF_determinant] at hdiff
  have hunit : IsUnit ((-1 : ℤ) ^ (n + 1)) := by
    rw [Int.isUnit_iff]
    exact neg_one_pow_eq_or ℤ (n + 1)
  exact dvd_trans hdiff (isUnit_iff_dvd_one.mp hunit)

def SimpleCFPositivePartials (a : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ a (n + 1)

theorem simpleCFDen_nonneg_of_positive {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, 0 ≤ simpleCFDen a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simp
      · simp
      · rw [simpleCFDen_succ_succ]
        exact add_nonneg
          (mul_nonneg (le_trans zero_le_one (ha n)) (ih (n + 1) (by omega)))
          (ih n (by omega))

theorem simpleCFDen_pos_of_positive {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, 0 < simpleCFDen a (n + 1) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, simpleCFDen_succ_succ]
      exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_lt_of_le zero_lt_one (ha n)) ih)
        (simpleCFDen_nonneg_of_positive ha n)

theorem simpleCFDen_ge_index_of_positive {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, (n : ℤ) ≤ simpleCFDen a (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simp
      · rw [show 1 + 1 = 2 by norm_num, simpleCFDen_succ_succ]
        simpa using ha 0
      · rw [show n + 2 + 1 = n + 3 by omega, show n + 3 = (n + 1) + 2 by omega,
          simpleCFDen_succ_succ]
        have hden₁ : (n + 1 : ℤ) ≤ simpleCFDen a (n + 2) := by
          simpa [show n + 1 + 1 = n + 2 by omega] using ih (n + 1) (by omega)
        have hden₀ : (1 : ℤ) ≤ simpleCFDen a (n + 1) := by
          have hpos : 0 < simpleCFDen a (n + 1) := simpleCFDen_pos_of_positive ha n
          omega
        have hmul :
            simpleCFDen a (n + 2) ≤ a (n + 2) * simpleCFDen a (n + 2) := by
          calc
            simpleCFDen a (n + 2) = (1 : ℤ) * simpleCFDen a (n + 2) := by ring
            _ ≤ a (n + 2) * simpleCFDen a (n + 2) := by
              exact mul_le_mul_of_nonneg_right (ha (n + 1))
                (simpleCFDen_nonneg_of_positive ha (n + 2))
        calc
          ((n + 2 : ℕ) : ℤ) ≤ (n + 1 : ℤ) + 1 := by omega
          _ ≤ simpleCFDen a (n + 2) + simpleCFDen a (n + 1) := add_le_add hden₁ hden₀
          _ ≤ a (n + 2) * simpleCFDen a (n + 2) + simpleCFDen a (n + 1) := by
            linarith

theorem simpleCFDen_tendsto_atTop_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) :
    Filter.Tendsto (fun n : ℕ => (simpleCFDen a (n + 1) : ℝ)) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono
    (fun n : ℕ => by exact_mod_cast simpleCFDen_ge_index_of_positive ha n)
    tendsto_natCast_atTop_atTop

theorem simpleCFNum_nonneg_of_positive {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, 0 ≤ simpleCFNum a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simp
      · simp
      · rw [simpleCFNum_succ_succ]
        exact add_nonneg
          (mul_nonneg (le_trans zero_le_one (ha n)) (ih (n + 1) (by omega)))
          (ih n (by omega))

theorem simpleCFNum_pos_of_positive {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, 0 < simpleCFNum a (n + 2) := by
  intro n
  induction n with
  | zero =>
      rw [show 0 + 2 = 2 by norm_num, simpleCFNum_succ_succ]
      simp
  | succ n ih =>
      rw [show n + 1 + 2 = n + 3 by omega, show n + 3 = (n + 1) + 2 by omega,
        simpleCFNum_succ_succ]
      exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_lt_of_le zero_lt_one (ha (n + 1))) ih)
        (simpleCFNum_nonneg_of_positive ha (n + 1))

theorem simpleCFNum_le_den_of_positive {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, simpleCFNum a (n + 1) ≤ simpleCFDen a (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simp
      · rw [show 1 + 1 = 2 by norm_num, simpleCFNum_succ_succ, simpleCFDen_succ_succ]
        simpa using ha 0
      · rw [show n + 2 + 1 = n + 3 by omega, show n + 3 = (n + 1) + 2 by omega,
          simpleCFNum_succ_succ, simpleCFDen_succ_succ]
        have h₁ : simpleCFNum a (n + 2) ≤ simpleCFDen a (n + 2) := by
          simpa [show n + 1 + 1 = n + 2 by omega] using ih (n + 1) (by omega)
        have h₀ : simpleCFNum a (n + 1) ≤ simpleCFDen a (n + 1) := by
          simpa [show n + 1 = n + 1 by rfl] using ih n (by omega)
        exact add_le_add (mul_le_mul_of_nonneg_left h₁ (le_trans zero_le_one (ha (n + 1)))) h₀

theorem simpleCFConvergent_num_den_pos_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    0 < simpleCFNum a (n + 2) ∧ 0 < simpleCFDen a (n + 2) :=
  ⟨simpleCFNum_pos_of_positive ha n,
    by simpa [show n + 2 = (n + 1) + 1 by omega] using
      simpleCFDen_pos_of_positive ha (n + 1)⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For $n \ge 1$, the recurrence gives $p_{n+1}, q_{n+1} \in \RestrictedSet{\NN}{\ge 1}$. By (ii), any common divisor of
    $p_{n+1}$ and $q_{n+1}$ divides $\pm 1$, so $p_{n+1}/q_{n+1}$ is in lowest terms.
-/
theorem simpleCFConvergent_num_den_lowestTerms {a : ℕ → ℤ} (n : ℕ) {d : ℤ}
    (hp : d ∣ simpleCFNum a (n + 2)) (hq : d ∣ simpleCFDen a (n + 2)) :
    d ∣ (1 : ℤ) :=
  simpleCF_common_divisor_dvd_one a (n + 1) hp hq

theorem simpleCFConvergent_den_ne_zero_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (simpleCFDen a (n + 1) : ℚ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (simpleCFDen_pos_of_positive ha n))

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    We claim that for $n \ge 1$,
    $$[0; a_1, \ldots, a_n] \;=\; \frac{p_{n+1}}{q_{n+1}};$$
    call $p_{n+1}/q_{n+1}$ the $n$-th \termdefine{convergent} of $\alpha_0$. Direct induction on this fails: the
    inductive step needs the last slot of the continued fraction to range over the reals, not just
    $\RestrictedSet{\NN}{\ge 1}$:
-/
def simpleCFConvergent (a : ℕ → ℤ) (n : ℕ) : ℚ :=
  (simpleCFNum a (n + 1) : ℚ) / (simpleCFDen a (n + 1) : ℚ)

theorem simpleCFConvergent_eq_divInt (a : ℕ → ℤ) (n : ℕ) :
    simpleCFConvergent a n =
      Rat.divInt (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1)) := by
  unfold simpleCFConvergent
  exact Rat.intCast_div_eq_divInt (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))

theorem simpleCFConvergent_den_le_den_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    ((simpleCFConvergent a n).den : ℝ) ≤
      (simpleCFDen a (n + 1) : ℝ) := by
  have hq_pos : 0 < simpleCFDen a (n + 1) := simpleCFDen_pos_of_positive ha n
  have hq_ne : simpleCFDen a (n + 1) ≠ 0 := ne_of_gt hq_pos
  have hdvd : ((simpleCFConvergent a n).den : ℤ) ∣ simpleCFDen a (n + 1) := by
    rw [simpleCFConvergent_eq_divInt]
    exact Rat.den_dvd (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
  have hle_nat :
      (((simpleCFConvergent a n).den : ℤ).natAbs) ≤
        (simpleCFDen a (n + 1)).natAbs :=
    Int.natAbs_le_of_dvd_ne_zero hdvd hq_ne
  have hle_int :
      ((simpleCFConvergent a n).den : ℤ) ≤ simpleCFDen a (n + 1) := by
    have hle_int' :
        (((simpleCFConvergent a n).den : ℤ).natAbs : ℤ) ≤
          ((simpleCFDen a (n + 1)).natAbs : ℤ) := by
      exact_mod_cast hle_nat
    rw [Int.natAbs_of_nonneg (by exact_mod_cast Nat.zero_le (simpleCFConvergent a n).den),
      Int.natAbs_of_nonneg (le_of_lt hq_pos)] at hle_int'
    exact hle_int'
  exact_mod_cast hle_int

theorem simpleCFConvergent_mem_Icc_zero_one_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    ((simpleCFConvergent a n : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hp_nonneg : (0 : ℚ) ≤ (simpleCFNum a (n + 1) : ℚ) := by
    exact_mod_cast simpleCFNum_nonneg_of_positive ha (n + 1)
  have hp_le_q : (simpleCFNum a (n + 1) : ℚ) ≤ (simpleCFDen a (n + 1) : ℚ) := by
    exact_mod_cast simpleCFNum_le_den_of_positive ha n
  have hq_pos : (0 : ℚ) < (simpleCFDen a (n + 1) : ℚ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hnonnegQ : (0 : ℚ) ≤ simpleCFConvergent a n := by
    unfold simpleCFConvergent
    exact div_nonneg hp_nonneg hq_pos.le
  have hleQ : simpleCFConvergent a n ≤ (1 : ℚ) := by
    unfold simpleCFConvergent
    exact (div_le_one hq_pos).2 hp_le_q
  constructor
  · exact_mod_cast hnonnegQ
  · exact_mod_cast hleQ

theorem simpleCFConvergent_succ_sub {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) (n : ℕ) :
    ((simpleCFConvergent a (n + 1) : ℝ) - (simpleCFConvergent a n : ℝ)) =
      ((-1 : ℝ) ^ (n + 2)) /
        ((simpleCFDen a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
  have hden₁ : (simpleCFDen a (n + 1) : ℚ) ≠ 0 :=
    simpleCFConvergent_den_ne_zero_of_positive ha n
  have hden₂ : (simpleCFDen a (n + 2) : ℚ) ≠ 0 :=
    simpleCFConvergent_den_ne_zero_of_positive ha (n + 1)
  have hdet := simpleCF_determinant a (n + 1)
  unfold simpleCFConvergent
  norm_num [Rat.cast_div, hden₁, hden₂]
  field_simp [show (simpleCFDen a (n + 1) : ℝ) ≠ 0 by exact_mod_cast hden₁,
    show (simpleCFDen a (n + 2) : ℝ) ≠ 0 by exact_mod_cast hden₂]
  ring_nf
  ring_nf at hdet
  have hdetR :
      (simpleCFNum a (2 + n) : ℝ) * (simpleCFDen a (1 + n) : ℝ) -
          (simpleCFNum a (1 + n) : ℝ) * (simpleCFDen a (2 + n) : ℝ) =
        ((-1 : ℤ) ^ n : ℝ) := by
    exact_mod_cast hdet
  ring_nf at hdetR
  simpa [mul_comm, mul_left_comm, mul_assoc] using hdetR

theorem simpleCFConvergent_succ_succ_sub {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    ((simpleCFConvergent a (n + 2) : ℝ) - (simpleCFConvergent a n : ℝ)) =
      ((a (n + 2) : ℝ) * ((-1 : ℝ) ^ (n + 2))) /
        ((simpleCFDen a (n + 3) : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
  have hden₁ : (simpleCFDen a (n + 1) : ℚ) ≠ 0 :=
    simpleCFConvergent_den_ne_zero_of_positive ha n
  have hden₃ : (simpleCFDen a (n + 3) : ℚ) ≠ 0 :=
    simpleCFConvergent_den_ne_zero_of_positive ha (n + 2)
  have hdet := simpleCF_determinant a (n + 1)
  unfold simpleCFConvergent
  norm_num [Rat.cast_div, hden₁, hden₃]
  field_simp [show (simpleCFDen a (n + 1) : ℝ) ≠ 0 by exact_mod_cast hden₁,
    show (simpleCFDen a (n + 3) : ℝ) ≠ 0 by exact_mod_cast hden₃]
  rw [show n + 3 = (n + 1) + 2 by omega, simpleCFNum_succ_succ,
    simpleCFDen_succ_succ]
  norm_num [Int.cast_add, Int.cast_mul]
  ring_nf
  have hdetR :
      (simpleCFNum a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a (n + 2) : ℝ) =
        ((-1 : ℤ) ^ (n + 2) : ℝ) := by
    exact_mod_cast hdet
  ring_nf at hdetR ⊢
  linear_combination (a (2 + n) : ℝ) * hdetR

theorem abs_simpleCFConvergent_succ_sub {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a)
    (n : ℕ) :
    |(simpleCFConvergent a (n + 1) : ℝ) - (simpleCFConvergent a n : ℝ)| =
      1 / ((simpleCFDen a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
  have hq₂ : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have hq₁ : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  rw [simpleCFConvergent_succ_sub ha n, abs_div, abs_of_pos (mul_pos hq₂ hq₁)]
  simp

theorem abs_simpleCFConvergent_succ_succ_sub {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    |(simpleCFConvergent a (n + 2) : ℝ) - (simpleCFConvergent a n : ℝ)| =
      (a (n + 2) : ℝ) /
        ((simpleCFDen a (n + 3) : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
  have ha₂ : 0 < (a (n + 2) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (ha (n + 1))
  have hq₃ : 0 < (simpleCFDen a (n + 3) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 2)
  have hq₁ : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  rw [simpleCFConvergent_succ_succ_sub ha n, abs_div,
    abs_of_pos (mul_pos hq₃ hq₁), abs_mul, abs_of_pos ha₂]
  simp

theorem abs_simpleCFConvergent_succ_succ_sub_lt_succ_sub {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    |(simpleCFConvergent a (n + 2) : ℝ) - (simpleCFConvergent a n : ℝ)| <
      |(simpleCFConvergent a (n + 1) : ℝ) - (simpleCFConvergent a n : ℝ)| := by
  have ha₂ : 0 < (a (n + 2) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (ha (n + 1))
  have hq₁ : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hq₂ : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have hq₃ : 0 < (simpleCFDen a (n + 3) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 2)
  have hq₃_eq :
      (simpleCFDen a (n + 3) : ℝ) =
        (a (n + 2) : ℝ) * (simpleCFDen a (n + 2) : ℝ) +
          (simpleCFDen a (n + 1) : ℝ) := by
    rw [show n + 3 = (n + 1) + 2 by omega, simpleCFDen_succ_succ]
    norm_num [Int.cast_add, Int.cast_mul]
  rw [abs_simpleCFConvergent_succ_succ_sub ha n, abs_simpleCFConvergent_succ_sub ha n]
  rw [div_lt_div_iff₀ (mul_pos hq₃ hq₁) (mul_pos hq₂ hq₁)]
  rw [hq₃_eq]
  nlinarith

theorem simpleCFConvergent_succ_ne {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (simpleCFConvergent a (n + 1) : ℝ) ≠ (simpleCFConvergent a n : ℝ) := by
  intro h
  have hq₂ : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have hq₁ : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hpos :
      0 < 1 / ((simpleCFDen a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ)) :=
    one_div_pos.mpr (mul_pos hq₂ hq₁)
  have hdist := abs_simpleCFConvergent_succ_sub ha n
  rw [h, sub_self, abs_zero] at hdist
  linarith

theorem simpleCFConvergent_succ_succ_mem_uIoo {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (simpleCFConvergent a (n + 2) : ℝ) ∈
      Set.uIoo (simpleCFConvergent a n : ℝ) (simpleCFConvergent a (n + 1) : ℝ) := by
  have hq₁ : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hq₂ : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have hq₃ : 0 < (simpleCFDen a (n + 3) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 2)
  have ha₂ : 0 < (a (n + 2) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (ha (n + 1))
  have hden₁ :
      0 < (simpleCFDen a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ) :=
    mul_pos hq₂ hq₁
  have hden₂ :
      0 < (simpleCFDen a (n + 3) : ℝ) * (simpleCFDen a (n + 1) : ℝ) :=
    mul_pos hq₃ hq₁
  have hstep := simpleCFConvergent_succ_sub ha n
  have hskip := simpleCFConvergent_succ_succ_sub ha n
  rcases neg_one_pow_eq_or ℝ (n + 2) with hpow | hpow
  · have h01 :
        (simpleCFConvergent a n : ℝ) < (simpleCFConvergent a (n + 1) : ℝ) := by
      have hdiff :
          0 < (simpleCFConvergent a (n + 1) : ℝ) - simpleCFConvergent a n := by
        rw [hstep, hpow]
        exact one_div_pos.mpr hden₁
      exact sub_pos.mp hdiff
    have h02 :
        (simpleCFConvergent a n : ℝ) < (simpleCFConvergent a (n + 2) : ℝ) := by
      have hdiff :
          0 < (simpleCFConvergent a (n + 2) : ℝ) - simpleCFConvergent a n := by
        rw [hskip, hpow, mul_one]
        exact div_pos ha₂ hden₂
      exact sub_pos.mp hdiff
    have h21 :
        (simpleCFConvergent a (n + 2) : ℝ) < simpleCFConvergent a (n + 1) := by
      have hlt := abs_simpleCFConvergent_succ_succ_sub_lt_succ_sub ha n
      rw [abs_of_pos (sub_pos.mpr h02), abs_of_pos (sub_pos.mpr h01)] at hlt
      linarith
    exact Set.mem_uIoo_of_lt h02 h21
  · have h10 :
        (simpleCFConvergent a (n + 1) : ℝ) < simpleCFConvergent a n := by
      have hdiff :
          (simpleCFConvergent a (n + 1) : ℝ) - simpleCFConvergent a n < 0 := by
        rw [hstep, hpow]
        exact div_neg_of_neg_of_pos (by norm_num) hden₁
      exact sub_neg.mp hdiff
    have h20 :
        (simpleCFConvergent a (n + 2) : ℝ) < simpleCFConvergent a n := by
      have hdiff :
          (simpleCFConvergent a (n + 2) : ℝ) - simpleCFConvergent a n < 0 := by
        rw [hskip, hpow]
        simpa using div_neg_of_neg_of_pos (neg_neg_of_pos ha₂) hden₂
      exact sub_neg.mp hdiff
    have h12 :
        (simpleCFConvergent a (n + 1) : ℝ) < simpleCFConvergent a (n + 2) := by
      have hlt := abs_simpleCFConvergent_succ_succ_sub_lt_succ_sub ha n
      rw [abs_of_neg (sub_neg.mpr h20), abs_of_neg (sub_neg.mpr h10)] at hlt
      linarith
    exact Set.mem_uIoo_of_gt h12 h20

theorem simpleCFConvergent_succ_succ_mem_uIcc {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (simpleCFConvergent a (n + 2) : ℝ) ∈
      Set.uIcc (simpleCFConvergent a n : ℝ) (simpleCFConvergent a (n + 1) : ℝ) :=
  Set.uIoo_subset_uIcc_self (simpleCFConvergent_succ_succ_mem_uIoo ha n)

theorem simpleCFConvergent_mem_uIcc_from {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n d : ℕ) :
    (simpleCFConvergent a (n + d) : ℝ) ∈
      Set.uIcc (simpleCFConvergent a n : ℝ) (simpleCFConvergent a (n + 1) : ℝ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      rcases d with _ | _ | d
      · simp
      · simp
      · have hbetween :
            (simpleCFConvergent a ((n + d) + 2) : ℝ) ∈
              Set.uIcc (simpleCFConvergent a (n + d) : ℝ)
                (simpleCFConvergent a ((n + d) + 1) : ℝ) :=
          simpleCFConvergent_succ_succ_mem_uIcc ha (n + d)
        have hleft :
            (simpleCFConvergent a (n + d) : ℝ) ∈
              Set.uIcc (simpleCFConvergent a n : ℝ)
                (simpleCFConvergent a (n + 1) : ℝ) :=
          ih d (by omega)
        have hright :
            (simpleCFConvergent a (n + (d + 1)) : ℝ) ∈
              Set.uIcc (simpleCFConvergent a n : ℝ)
                (simpleCFConvergent a (n + 1) : ℝ) :=
          ih (d + 1) (by omega)
        have hsub :=
          Set.uIcc_subset_uIcc hleft
            (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright)
        exact hsub (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbetween)

theorem simpleCFConvergent_limit_mem_uIcc {a : ℕ → ℤ} {β : ℝ}
    (ha : SimpleCFPositivePartials a)
    (hβ : Filter.Tendsto
      (fun n : ℕ => ((simpleCFConvergent a n : ℚ) : ℝ)) Filter.atTop (𝓝 β))
    (n : ℕ) :
    β ∈ Set.uIcc (simpleCFConvergent a n : ℝ) (simpleCFConvergent a (n + 1) : ℝ) := by
  have hclosed :
      IsClosed (Set.uIcc (simpleCFConvergent a n : ℝ)
        (simpleCFConvergent a (n + 1) : ℝ)) := by
    simpa [Set.uIcc] using
      (isClosed_Icc :
        IsClosed (Set.Icc
          ((simpleCFConvergent a n : ℝ) ⊓ (simpleCFConvergent a (n + 1) : ℝ))
          ((simpleCFConvergent a n : ℝ) ⊔ (simpleCFConvergent a (n + 1) : ℝ))))
  refine hclosed.mem_of_tendsto hβ ?_
  refine Filter.eventually_atTop.2 ⟨n, ?_⟩
  intro m hnm
  rcases exists_add_of_le hnm with ⟨d, rfl⟩
  exact simpleCFConvergent_mem_uIcc_from ha n d

theorem uIcc_subset_uIoo_of_mem_uIoo {a b x y : ℝ}
    (hx : x ∈ Set.uIoo a b) (hy : y ∈ Set.uIoo a b) :
    Set.uIcc x y ⊆ Set.uIoo a b := by
  change x ∈ Set.Ioo (a ⊓ b) (a ⊔ b) at hx
  change y ∈ Set.Ioo (a ⊓ b) (a ⊔ b) at hy
  change Set.Icc (x ⊓ y) (x ⊔ y) ⊆ Set.Ioo (a ⊓ b) (a ⊔ b)
  exact Set.Icc_subset_Ioo ((lt_inf_iff).2 ⟨hx.1, hy.1⟩)
    ((sup_lt_iff).2 ⟨hx.2, hy.2⟩)

theorem uIoo_subset_uIoo_of_mem_uIcc_of_mem_uIoo {a b x y : ℝ}
    (hx : x ∈ Set.uIcc a b) (hy : y ∈ Set.uIoo a b) :
    Set.uIoo x y ⊆ Set.uIoo a b := by
  intro z hz
  change x ∈ Set.Icc (a ⊓ b) (a ⊔ b) at hx
  change y ∈ Set.Ioo (a ⊓ b) (a ⊔ b) at hy
  change z ∈ Set.Ioo (x ⊓ y) (x ⊔ y) at hz
  change z ∈ Set.Ioo (a ⊓ b) (a ⊔ b)
  exact ⟨lt_of_le_of_lt (le_inf hx.1 hy.1.le) hz.1,
    lt_of_lt_of_le hz.2 (sup_le hx.2 hy.2.le)⟩

theorem simpleCFConvergent_limit_mem_uIoo {a : ℕ → ℤ} {β : ℝ}
    (ha : SimpleCFPositivePartials a)
    (hβ : Filter.Tendsto
      (fun n : ℕ => ((simpleCFConvergent a n : ℚ) : ℝ)) Filter.atTop (𝓝 β))
    (n : ℕ) :
    β ∈ Set.uIoo (simpleCFConvergent a n : ℝ)
      (simpleCFConvergent a (n + 1) : ℝ) := by
  have hc₂ :
      (simpleCFConvergent a (n + 2) : ℝ) ∈
        Set.uIoo (simpleCFConvergent a n : ℝ)
          (simpleCFConvergent a (n + 1) : ℝ) :=
    simpleCFConvergent_succ_succ_mem_uIoo ha n
  have hc₁ :
      (simpleCFConvergent a (n + 1) : ℝ) ∈
        Set.uIcc (simpleCFConvergent a n : ℝ)
          (simpleCFConvergent a (n + 1) : ℝ) :=
    Set.right_mem_uIcc
  have hc₃ :
      (simpleCFConvergent a (n + 3) : ℝ) ∈
        Set.uIoo (simpleCFConvergent a n : ℝ)
          (simpleCFConvergent a (n + 1) : ℝ) := by
    exact
      (uIoo_subset_uIoo_of_mem_uIcc_of_mem_uIoo hc₁ hc₂)
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            simpleCFConvergent_succ_succ_mem_uIoo ha (n + 1))
  exact
    (uIcc_subset_uIoo_of_mem_uIoo hc₂ hc₃)
      (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          simpleCFConvergent_limit_mem_uIcc ha hβ (n + 2))

theorem abs_sub_left_lt_of_mem_uIoo {a b c : ℝ}
    (h : c ∈ Set.uIoo a b) :
    |c - a| < |b - a| := by
  have hne : a ≠ b := by
    intro hab
    subst b
    rw [Set.uIoo_self] at h
    exact h
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hI : c ∈ Set.Ioo a b := by
      simpa [Set.uIoo_of_lt hab] using h
    calc
      |c - a| = c - a := abs_of_nonneg (sub_nonneg.mpr hI.1.le)
      _ < b - a := sub_lt_sub_right hI.2 a
      _ = |b - a| := (abs_of_nonneg (sub_nonneg.mpr hab.le)).symm
  · have hI : c ∈ Set.Ioo b a := by
      simpa [Set.uIoo_of_gt hba] using h
    calc
      |c - a| = -(c - a) := abs_of_nonpos (sub_nonpos.mpr hI.2.le)
      _ = a - c := by ring
      _ < a - b := sub_lt_sub_left hI.1 a
      _ = -(b - a) := by ring
      _ = |b - a| := (abs_of_nonpos (sub_nonpos.mpr hba.le)).symm

theorem rat_one_div_den_le_abs {q : ℚ} (hq : q ≠ 0) :
    (1 : ℚ) / (q.den : ℚ) ≤ |q| := by
  have hden_pos : (0 : ℚ) < q.den := Nat.cast_pos.mpr q.den_pos
  have hnum : (1 : ℚ) ≤ |(q.num : ℚ)| := by
    exact_mod_cast Int.one_le_abs (Rat.num_ne_zero.mpr hq)
  calc
    (1 : ℚ) / (q.den : ℚ) ≤ |(q.num : ℚ)| / (q.den : ℚ) :=
      div_le_div_of_nonneg_right hnum hden_pos.le
    _ = |(q.num : ℚ) / (q.den : ℚ)| := by
      rw [abs_div, abs_of_pos hden_pos]
    _ = |q| := by
      rw [Rat.num_div_den q]

theorem rat_one_div_den_mul_den_le_abs_sub {r s : ℚ} (hrs : r ≠ s) :
    (1 : ℚ) / ((r.den : ℚ) * (s.den : ℚ)) ≤ |r - s| := by
  have hdiff : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have hbasic := rat_one_div_den_le_abs hdiff
  have hden_dvd : (r - s).den ∣ r.den * s.den := Rat.sub_den_dvd r s
  have hprod_pos_nat : 0 < r.den * s.den := Nat.mul_pos r.den_pos s.den_pos
  have hden_le_prod_nat : (r - s).den ≤ r.den * s.den :=
    Nat.le_of_dvd hprod_pos_nat hden_dvd
  have hden_pos : (0 : ℚ) < ((r - s).den : ℚ) :=
    Nat.cast_pos.mpr (r - s).den_pos
  have hden_le_prod :
      ((r - s).den : ℚ) ≤ (r.den : ℚ) * (s.den : ℚ) := by
    exact_mod_cast hden_le_prod_nat
  exact (one_div_le_one_div_of_le hden_pos hden_le_prod).trans hbasic

theorem ratCast_one_div_den_mul_den_le_abs_sub {r s : ℚ}
    (hrs : (r : ℝ) ≠ (s : ℝ)) :
    (1 : ℝ) / ((r.den : ℝ) * (s.den : ℝ)) ≤
      |(r : ℝ) - (s : ℝ)| := by
  have hrsQ : r ≠ s := by
    intro h
    exact hrs (by simp [h])
  have hQ := rat_one_div_den_mul_den_le_abs_sub hrsQ
  have hR :
      (((1 : ℚ) / ((r.den : ℚ) * (s.den : ℚ))) : ℝ) ≤
        ((|r - s| : ℚ) : ℝ) := by
    exact_mod_cast hQ
  simpa [Rat.cast_div, Rat.cast_mul, Rat.cast_sub] using hR

theorem one_div_rat_den_mul_simpleCFDen_le_abs_sub_simpleCFConvergent {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (r : ℚ) (n : ℕ)
    (hne : (r : ℝ) ≠ (simpleCFConvergent a n : ℝ)) :
    1 / ((r.den : ℝ) * (simpleCFDen a (n + 1) : ℝ)) ≤
      |(r : ℝ) - (simpleCFConvergent a n : ℝ)| := by
  have hrden_pos : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hconv_den_pos : 0 < ((simpleCFConvergent a n).den : ℝ) := by
    exact_mod_cast (simpleCFConvergent a n).den_pos
  have hden_le := simpleCFConvergent_den_le_den_of_positive ha n
  have hprod_le :
      (r.den : ℝ) * ((simpleCFConvergent a n).den : ℝ) ≤
        (r.den : ℝ) * (simpleCFDen a (n + 1) : ℝ) :=
    mul_le_mul_of_nonneg_left hden_le hrden_pos.le
  exact
    (one_div_le_one_div_of_le (mul_pos hrden_pos hconv_den_pos) hprod_le).trans
      (ratCast_one_div_den_mul_den_le_abs_sub hne)

theorem dist_le_abs_sub_of_mem_uIcc {a b x y : ℝ}
    (hx : x ∈ Set.uIcc a b) (hy : y ∈ Set.uIcc a b) :
    dist x y ≤ |b - a| := by
  change x ∈ Set.Icc (a ⊓ b) (a ⊔ b) at hx
  change y ∈ Set.Icc (a ⊓ b) (a ⊔ b) at hy
  rw [Real.dist_eq, abs_sub_le_iff]
  have hspan : a ⊔ b - (a ⊓ b) = |b - a| := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, min_eq_left hab, abs_of_nonneg (sub_nonneg.2 hab)]
    · rw [max_eq_left hba, min_eq_right hba, abs_of_nonpos (sub_nonpos.2 hba)]
      ring
  constructor
  · calc
      x - y ≤ a ⊔ b - (a ⊓ b) := by linarith [hx.2, hy.1]
      _ = |b - a| := hspan
  · calc
      y - x ≤ a ⊔ b - (a ⊓ b) := by linarith [hy.2, hx.1]
      _ = |b - a| := hspan

theorem simpleCFConvergent_dist_le_pseries_bound {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    dist ((simpleCFConvergent a n : ℚ) : ℝ) ((simpleCFConvergent a (n + 1) : ℚ) : ℝ) ≤
      2 / ((n + 1 : ℝ) ^ 2) := by
  have hq₂ : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have hq₁ : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hprod_pos :
      0 < (simpleCFDen a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ) :=
    mul_pos hq₂ hq₁
  have hn_pos : 0 < (n + 1 : ℝ) ^ 2 := sq_pos_of_pos (by positivity)
  have hprod :
      (n + 1 : ℝ) ^ 2 ≤
        2 * ((simpleCFDen a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
    rcases n with _ | n
    · have hq₂_ge : (1 : ℝ) ≤ (simpleCFDen a 2 : ℝ) := by
        exact_mod_cast simpleCFDen_ge_index_of_positive ha 1
      norm_num
      nlinarith [hq₂_ge, hq₁]
    · have hq₂_ge : ((n + 2 : ℕ) : ℝ) ≤ (simpleCFDen a (n + 3) : ℝ) := by
        exact_mod_cast simpleCFDen_ge_index_of_positive ha (n + 2)
      have hq₁_ge : ((n + 1 : ℕ) : ℝ) ≤ (simpleCFDen a (n + 2) : ℝ) := by
        exact_mod_cast simpleCFDen_ge_index_of_positive ha (n + 1)
      have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hn2 : 0 ≤ ((n + 2 : ℕ) : ℝ) := by positivity
      have hmul :
          ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ≤
            (simpleCFDen a (n + 3) : ℝ) * (simpleCFDen a (n + 2) : ℝ) :=
        mul_le_mul hq₂_ge hq₁_ge hn1 (le_trans hn2 hq₂_ge)
      have hsquare :
          (((n + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
            2 * (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
        norm_num
        nlinarith
      nlinarith
  rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm,
    abs_simpleCFConvergent_succ_sub ha n]
  rw [div_le_div_iff₀ hprod_pos hn_pos]
  simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hprod

theorem summable_simpleCFConvergent_dist_bound :
    Summable (fun n : ℕ => 2 / ((n + 1 : ℝ) ^ 2)) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : 1 < 2)
  have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [Nat.cast_add, add_comm] using (summable_nat_add_iff 1).mpr hs
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hshift.mul_left 2

/-- Book proof of convergence in the converse direction: every later convergent
lies in the closed interval with endpoints `c_N, c_{N+1}` (the intervals are
nested), and the interval lengths `1 / (q_{N+1} q_{N+2})` tend to zero. -/
theorem simpleCFConvergent_cauchySeq_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) :
    CauchySeq (fun n : ℕ => ((simpleCFConvergent a n : ℚ) : ℝ)) := by
  refine cauchySeq_of_le_tendsto_0
    (fun N : ℕ =>
      1 / ((simpleCFDen a (N + 2) : ℝ) * (simpleCFDen a (N + 1) : ℝ)))
    (fun n m N hn hm => ?_) ?_
  · have hn' :
        ((simpleCFConvergent a n : ℚ) : ℝ) ∈
          Set.uIcc (simpleCFConvergent a N : ℝ)
            (simpleCFConvergent a (N + 1) : ℝ) := by
      rcases exists_add_of_le hn with ⟨d, rfl⟩
      exact simpleCFConvergent_mem_uIcc_from ha N d
    have hm' :
        ((simpleCFConvergent a m : ℚ) : ℝ) ∈
          Set.uIcc (simpleCFConvergent a N : ℝ)
            (simpleCFConvergent a (N + 1) : ℝ) := by
      rcases exists_add_of_le hm with ⟨d, rfl⟩
      exact simpleCFConvergent_mem_uIcc_from ha N d
    calc
      dist ((simpleCFConvergent a n : ℚ) : ℝ) ((simpleCFConvergent a m : ℚ) : ℝ)
          ≤ |(simpleCFConvergent a (N + 1) : ℝ) - (simpleCFConvergent a N : ℝ)| :=
            dist_le_abs_sub_of_mem_uIcc hn' hm'
      _ = 1 / ((simpleCFDen a (N + 2) : ℝ) * (simpleCFDen a (N + 1) : ℝ)) :=
            abs_simpleCFConvergent_succ_sub ha N
  · have hnonneg :
        ∀ N : ℕ,
          0 ≤ 1 / ((simpleCFDen a (N + 2) : ℝ) * (simpleCFDen a (N + 1) : ℝ)) := by
      intro N
      have hq₁ : 0 < (simpleCFDen a (N + 1) : ℝ) := by
        exact_mod_cast simpleCFDen_pos_of_positive ha N
      have hq₂ : 0 < (simpleCFDen a (N + 2) : ℝ) := by
        exact_mod_cast simpleCFDen_pos_of_positive ha (N + 1)
      positivity
    have hle :
        ∀ N : ℕ,
          1 / ((simpleCFDen a (N + 2) : ℝ) * (simpleCFDen a (N + 1) : ℝ)) ≤
            1 / (simpleCFDen a (N + 1) : ℝ) := by
      intro N
      have hq₁ : 0 < (simpleCFDen a (N + 1) : ℝ) := by
        exact_mod_cast simpleCFDen_pos_of_positive ha N
      have hq₂_ge_one : (1 : ℝ) ≤ (simpleCFDen a (N + 2) : ℝ) := by
        have h0 : 0 < simpleCFDen a (N + 2) := simpleCFDen_pos_of_positive ha (N + 1)
        have h1 : (1 : ℤ) ≤ simpleCFDen a (N + 2) := by omega
        exact_mod_cast h1
      apply one_div_le_one_div_of_le hq₁
      calc
        (simpleCFDen a (N + 1) : ℝ)
            = 1 * (simpleCFDen a (N + 1) : ℝ) := (one_mul _).symm
        _ ≤ (simpleCFDen a (N + 2) : ℝ) * (simpleCFDen a (N + 1) : ℝ) :=
              mul_le_mul_of_nonneg_right hq₂_ge_one hq₁.le
    have hinv_tendsto :
        Filter.Tendsto (fun N : ℕ => 1 / (simpleCFDen a (N + 1) : ℝ)) Filter.atTop
          (𝓝 0) := by
      simpa [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (simpleCFDen_tendsto_atTop_of_positive ha)
    exact squeeze_zero hnonneg hle hinv_tendsto

theorem exists_tendsto_simpleCFConvergent_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) :
    ∃ β : ℝ, Filter.Tendsto
      (fun n : ℕ => ((simpleCFConvergent a n : ℚ) : ℝ)) Filter.atTop (𝓝 β) :=
  cauchySeq_tendsto_of_complete (simpleCFConvergent_cauchySeq_of_positive ha)

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    \emph{Converse.} Fix any $a_0 \in \ZZ$ and any sequence $a_n \in \RestrictedSet{\NN}{\ge 1}$ for $n \ge 1$, and define
    $p_n,q_n$ by the same seeds and recurrence. The Fibonacci-rate growth above depends only on the positivity of the
    partial quotients, so $q_n \to \infty$. Put $c_n:=p_{n+1}/q_{n+1}$. The determinant identity gives
    $$c_{n+1}-c_n
    =\frac{p_{n+2}q_{n+1}-p_{n+1}q_{n+2}}{q_{n+1}q_{n+2}}
    =\frac{(-1)^n}{q_{n+1}q_{n+2}}.$$
    Moreover,
    $$c_{n+2}-c_n
    =\frac{a_{n+2}}{q_{n+1}q_{n+3}}(p_{n+2}q_{n+1}-p_{n+1}q_{n+2})
    =\frac{a_{n+2}(-1)^n}{q_{n+1}q_{n+3}}.$$
    Thus $c_{n+2}$ lies strictly between $c_n$ and $c_{n+1}$. Let $I_n$ be the closed interval with endpoints $c_n$
    and $c_{n+1}$. Then $I_{n+1}\IncludedIn I_n$, and $I_{n+2}\IncludedIn\operatorname{int}I_n$: both $c_{n+2}$ and
    $c_{n+3}$ lie strictly between the endpoints of $I_n$. The lengths $1/(q_{n+1}q_{n+2})$ tend to $0$, so the
    intervals have a unique common point $\beta$, and $c_n\to\beta$. Moreover,
    $\beta\in I_{n+2}\IncludedIn\operatorname{int}I_n$ for every $n$. For $n\ge1$, the $c_n$ are the finite convergents
    $[0;a_1,\ldots,a_n]$. Since $c_0=0$ and $c_1=1/a_1\le1$, it follows that $\beta\in(0,1)$.
-/
theorem SimpleCFInfiniteExpressionConvergesToReal (a₀ : ℤ) (a : ℕ → ℤ)
    (ha : SimpleCFPositivePartials a) :
    ∃ β : ℝ,
      Filter.Tendsto
        (fun n : ℕ => (a₀ : ℝ) + (simpleCFConvergent a n : ℝ))
        Filter.atTop (𝓝 ((a₀ : ℝ) + β)) := by
  rcases exists_tendsto_simpleCFConvergent_of_positive ha with ⟨β, hβ⟩
  exact ⟨β, tendsto_const_nhds.add hβ⟩

def SimpleCFConvergentLimit (a : ℕ → ℤ) (β : ℝ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => ((simpleCFConvergent a n : ℚ) : ℝ)) Filter.atTop (𝓝 β)

def SimpleCFShiftedConvergentLimit (a₀ : ℤ) (a : ℕ → ℤ) (x : ℝ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => (a₀ : ℝ) + (simpleCFConvergent a n : ℝ)) Filter.atTop (𝓝 x)

def SimpleCFLimitInOpenUnitInterval (a : ℕ → ℤ) : Prop :=
  SimpleCFPositivePartials a →
    ∀ β : ℝ, SimpleCFConvergentLimit a β → 0 < β ∧ β < 1

def SimpleCFLimitIrrational (a : ℕ → ℤ) : Prop :=
  SimpleCFPositivePartials a →
    ∀ β : ℝ, SimpleCFConvergentLimit a β → Irrational β

def SimpleCFShiftedLimitIrrational (a₀ : ℤ) (a : ℕ → ℤ) : Prop :=
  SimpleCFPositivePartials a →
    ∀ β : ℝ, SimpleCFConvergentLimit a β → Irrational ((a₀ : ℝ) + β)

theorem simpleCFLimitInOpenUnitInterval_of_positive (a : ℕ → ℤ) :
    SimpleCFLimitInOpenUnitInterval a := by
  intro ha β hβ
  have hlim :
      β ∈ Set.uIcc (simpleCFConvergent a 2 : ℝ) (simpleCFConvergent a 3 : ℝ) :=
    simpleCFConvergent_limit_mem_uIcc ha hβ 2
  have hc₁_mem : (simpleCFConvergent a 1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    simpleCFConvergent_mem_Icc_zero_one_of_positive ha 1
  have hc₀ : (simpleCFConvergent a 0 : ℝ) = 0 := by
    norm_num [simpleCFConvergent]
  have hc₁_ne_zero : (simpleCFConvergent a 1 : ℝ) ≠ 0 := by
    have hne := simpleCFConvergent_succ_ne ha 0
    rwa [hc₀] at hne
  have hc₁_pos : 0 < (simpleCFConvergent a 1 : ℝ) :=
    lt_of_le_of_ne hc₁_mem.1 (Ne.symm hc₁_ne_zero)
  have hc₂_between :
      (simpleCFConvergent a 2 : ℝ) ∈
        Set.uIoo (simpleCFConvergent a 0 : ℝ) (simpleCFConvergent a 1 : ℝ) :=
    simpleCFConvergent_succ_succ_mem_uIoo ha 0
  have hc₂_Ioo :
      (simpleCFConvergent a 2 : ℝ) ∈ Set.Ioo (0 : ℝ) (simpleCFConvergent a 1 : ℝ) := by
    rw [hc₀, Set.uIoo_of_lt hc₁_pos] at hc₂_between
    exact hc₂_between
  have hc₃_between :
      (simpleCFConvergent a 3 : ℝ) ∈
        Set.uIoo (simpleCFConvergent a 1 : ℝ) (simpleCFConvergent a 2 : ℝ) :=
    simpleCFConvergent_succ_succ_mem_uIoo ha 1
  have hc₃_Ioo :
      (simpleCFConvergent a 3 : ℝ) ∈
        Set.Ioo (simpleCFConvergent a 2 : ℝ) (simpleCFConvergent a 1 : ℝ) := by
    simpa [Set.uIoo_of_gt hc₂_Ioo.2] using hc₃_between
  have hlim_Icc :
      β ∈ Set.Icc (simpleCFConvergent a 2 : ℝ) (simpleCFConvergent a 3 : ℝ) := by
    simpa [Set.uIcc_of_lt hc₃_Ioo.1] using hlim
  exact ⟨lt_of_lt_of_le hc₂_Ioo.1 hlim_Icc.1,
    lt_of_le_of_lt hlim_Icc.2 (hc₃_Ioo.2.trans_le hc₁_mem.2)⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    The limit is moreover irrational. If $\beta=p/q$ with $q \ge 1$, then $\beta$ lies strictly between $c_n$ and $c_{n+1}$
    for every $n$, so
    $$\left|\frac{p}{q}-\frac{p_{n+1}}{q_{n+1}}\right|<\left|c_{n+1}-c_n\right|=\frac{1}{q_{n+1}q_{n+2}}.$$
    On the other hand, $p/q\ne p_{n+1}/q_{n+1}$, so
    $$\left|\frac{p}{q}-\frac{p_{n+1}}{q_{n+1}}\right|
    =\frac{|p q_{n+1}-q p_{n+1}|}{q q_{n+1}}
    \ge \frac{1}{q q_{n+1}}.$$
    Hence $q_{n+2}<q$ for every $n$, contradicting $q_n \to \infty$. Thus every infinite expression $[a_0; a_1, a_2,
    \ldots]$ converges to the irrational real $a_0+\beta$.
-/
theorem simpleCFLimitIrrational_of_positive (a : ℕ → ℤ) :
    SimpleCFLimitIrrational a := by
  intro ha β hβ
  rw [Irrational]
  rintro ⟨r, hβr⟩
  let n : ℕ := r.den
  have hstrict :
      β ∈ Set.uIoo (simpleCFConvergent a n : ℝ)
        (simpleCFConvergent a (n + 1) : ℝ) :=
    simpleCFConvergent_limit_mem_uIoo ha hβ n
  have hne : (r : ℝ) ≠ (simpleCFConvergent a n : ℝ) := by
    intro hr_eq
    have hβ_eq : β = (simpleCFConvergent a n : ℝ) := hβr.symm.trans hr_eq
    exact
      (Set.left_notMem_uIoo :
        (simpleCFConvergent a n : ℝ) ∉
          Set.uIoo (simpleCFConvergent a n : ℝ)
            (simpleCFConvergent a (n + 1) : ℝ))
        (by
          rw [hβ_eq] at hstrict
          exact hstrict)
  have hupper :
      |(r : ℝ) - (simpleCFConvergent a n : ℝ)| <
        1 / ((simpleCFDen a (n + 2) : ℝ) *
          (simpleCFDen a (n + 1) : ℝ)) := by
    have hdist := abs_sub_left_lt_of_mem_uIoo hstrict
    simpa [← hβr, abs_simpleCFConvergent_succ_sub ha n] using hdist
  have hlower :
      1 / ((r.den : ℝ) * (simpleCFDen a (n + 1) : ℝ)) ≤
        |(r : ℝ) - (simpleCFConvergent a n : ℝ)| :=
    one_div_rat_den_mul_simpleCFDen_le_abs_sub_simpleCFConvergent ha r n hne
  have hrecip :
      1 / ((r.den : ℝ) * (simpleCFDen a (n + 1) : ℝ)) <
        1 / ((simpleCFDen a (n + 2) : ℝ) *
          (simpleCFDen a (n + 1) : ℝ)) :=
    lt_of_le_of_lt hlower hupper
  have hrden_pos : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hq₁_pos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hq₂_pos : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have hq₂_lt_rden :
      (simpleCFDen a (n + 2) : ℝ) < (r.den : ℝ) := by
    have hprod_lt :
        (simpleCFDen a (n + 2) : ℝ) * (simpleCFDen a (n + 1) : ℝ) <
          (r.den : ℝ) * (simpleCFDen a (n + 1) : ℝ) :=
      lt_of_one_div_lt_one_div (mul_pos hrden_pos hq₁_pos) hrecip
    exact lt_of_mul_lt_mul_right hprod_lt hq₁_pos.le
  have hq₂_ge_succ :
      ((n + 1 : ℕ) : ℝ) ≤ (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_ge_index_of_positive ha (n + 1)
  have hrden_lt_succ : (r.den : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    dsimp [n]
    exact_mod_cast Nat.lt_succ_self r.den
  linarith

theorem simpleCFLimitInOpenUnitInterval_of_limitIrrational (a : ℕ → ℤ)
    (h : SimpleCFLimitIrrational a) :
    SimpleCFLimitInOpenUnitInterval a := by
  intro ha β hβ
  have hmem : β ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hβ
      (Filter.Eventually.of_forall (simpleCFConvergent_mem_Icc_zero_one_of_positive ha))
  have hne1 : β ≠ 1 := by
    simpa using (h ha β hβ).ne_rat (1 : ℚ)
  exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm (h ha β hβ).ne_zero),
    lt_of_le_of_ne hmem.2 hne1⟩

theorem simpleCFShiftedLimitIrrational_of_limitIrrational (a₀ : ℤ) (a : ℕ → ℤ)
    (h : SimpleCFLimitIrrational a) :
    SimpleCFShiftedLimitIrrational a₀ a := by
  intro ha β hβ
  exact (h ha β hβ).intCast_add a₀

theorem simpleCFShiftedLimitIrrational_of_positive (a₀ : ℤ) (a : ℕ → ℤ) :
    SimpleCFShiftedLimitIrrational a₀ a :=
  simpleCFShiftedLimitIrrational_of_limitIrrational a₀ a
    (simpleCFLimitIrrational_of_positive a)

noncomputable def simpleCFIntegerPart (x : ℝ) : ℤ :=
  ⌊x⌋

theorem simpleCFIntegerPart_eq_of_mem_Ioo {x : ℝ} {a₀ : ℤ}
    (hx : x ∈ Set.Ioo (a₀ : ℝ) ((a₀ : ℝ) + 1)) :
    simpleCFIntegerPart x = a₀ := by
  rw [simpleCFIntegerPart, Int.floor_eq_iff]
  exact ⟨le_of_lt hx.1, hx.2⟩

theorem simpleCFIntegerPart_natCast (n : ℕ) :
    simpleCFIntegerPart (n : ℝ) = (n : ℤ) := by
  rw [simpleCFIntegerPart]
  change ⌊((n : ℤ) : ℝ)⌋ = (n : ℤ)
  exact Int.floor_intCast n

theorem simpleCFIntegerPart_mem_Ioo (x : {x : ℝ // Irrational x}) :
    x.1 ∈ Set.Ioo (simpleCFIntegerPart x.1 : ℝ)
      ((simpleCFIntegerPart x.1 : ℝ) + 1) := by
  constructor
  · have hle : (simpleCFIntegerPart x.1 : ℝ) ≤ x.1 := by
      simpa [simpleCFIntegerPart] using Int.floor_le x.1
    exact lt_of_le_of_ne hle (by
      intro hEq
      exact x.2.ne_int (simpleCFIntegerPart x.1) hEq.symm)
  · simp [simpleCFIntegerPart, Int.lt_floor_add_one]

theorem simpleCFIntegerPart_irrational_locallyConstant :
    IsLocallyConstant (fun x : {x : ℝ // Irrational x} => simpleCFIntegerPart x.1) := by
  intro S
  rw [show (fun x : {x : ℝ // Irrational x} => simpleCFIntegerPart x.1) ⁻¹' S =
      ⋃ a₀ : {a₀ : ℤ // a₀ ∈ S},
        ((fun x : {x : ℝ // Irrational x} => x.1) ⁻¹'
          Set.Ioo (a₀.1 : ℝ) ((a₀.1 : ℝ) + 1)) by
    ext x
    constructor
    · intro hxS
      exact Set.mem_iUnion.2
        ⟨⟨simpleCFIntegerPart x.1, hxS⟩, simpleCFIntegerPart_mem_Ioo x⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨a₀, hxIoo⟩
      have hfloor : simpleCFIntegerPart x.1 = a₀.1 :=
        simpleCFIntegerPart_eq_of_mem_Ioo hxIoo
      simp [hfloor, a₀.2]]
  exact isOpen_iUnion fun a₀ => isOpen_Ioo.preimage continuous_subtype_val

theorem simpleCFIntegerPart_irrational_continuous :
    Continuous (fun x : {x : ℝ // Irrational x} => simpleCFIntegerPart x.1) :=
  simpleCFIntegerPart_irrational_locallyConstant.continuous

/-- The `a₀`-th clopen integer cell in the irrational line. -/
def simpleCFIntegerPartCell (a₀ : ℤ) : Set {x : ℝ // Irrational x} :=
  {x | simpleCFIntegerPart x.1 = a₀}

/-- The integer-part cell is exactly the subspace interval
`(a₀, a₀ + 1) \setminus \mathbb{Q}`. -/
theorem simpleCFIntegerPartCell_eq_interval (a₀ : ℤ) :
    simpleCFIntegerPartCell a₀ =
      {x : {x : ℝ // Irrational x} | x.1 ∈ Set.Ioo (a₀ : ℝ) ((a₀ : ℝ) + 1)} := by
  ext x
  constructor
  · intro hx
    have hxIoo := simpleCFIntegerPart_mem_Ioo x
    change simpleCFIntegerPart x.1 = a₀ at hx
    rw [hx] at hxIoo
    exact hxIoo
  · intro hx
    exact simpleCFIntegerPart_eq_of_mem_Ioo hx

theorem isClopen_simpleCFIntegerPartCell (a₀ : ℤ) :
    IsClopen (simpleCFIntegerPartCell a₀) :=
  (isClopen_discrete ({a₀} : Set ℤ)).preimage simpleCFIntegerPart_irrational_continuous

theorem simpleCFIntegerPartCell_value {a₀ : ℤ} {x : {x : ℝ // Irrational x}}
    (hx : x ∈ simpleCFIntegerPartCell a₀) :
    simpleCFIntegerPart x.1 = a₀ :=
  hx

/-- The irrational line is the union of its clopen integer-part cells. -/
theorem iUnion_simpleCFIntegerPartCell :
    (⋃ a₀ : ℤ, simpleCFIntegerPartCell a₀) = (Set.univ : Set {x : ℝ // Irrational x}) := by
  ext x
  constructor
  · intro
    exact Set.mem_univ x
  · intro
    exact Set.mem_iUnion.2 ⟨simpleCFIntegerPart x.1, rfl⟩

/-- Distinct integer-part cells in the irrational line are disjoint. -/
theorem disjoint_simpleCFIntegerPartCell {a₀ b₀ : ℤ} (hab : a₀ ≠ b₀) :
    Disjoint (simpleCFIntegerPartCell a₀) (simpleCFIntegerPartCell b₀) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact hab (hxa.symm.trans hxb)

noncomputable def simpleCFFractionalRemainder (x : ℝ) : ℕ → ℝ
  | 0 => Int.fract x
  | n + 1 => Int.fract ((simpleCFFractionalRemainder x n)⁻¹)

noncomputable def simpleCFAlgorithmPartials (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => ⌊(simpleCFFractionalRemainder x n)⁻¹⌋

def SimpleCFFractionalRemaindersStayIrrationalUnitInterval (x : ℝ) : Prop :=
  Irrational x →
    ∀ n : ℕ,
      Irrational (simpleCFFractionalRemainder x n) ∧
        0 < simpleCFFractionalRemainder x n ∧ simpleCFFractionalRemainder x n < 1

theorem simpleCFFractionalRemainder_irrational_unitInterval (x : ℝ) :
    SimpleCFFractionalRemaindersStayIrrationalUnitInterval x := by
  intro hx n
  induction n with
  | zero =>
      have hirr : Irrational (Int.fract x) := by
        rw [← Int.fract_add_floor x] at hx
        exact hx.of_add_intCast ⌊x⌋
      exact ⟨hirr, lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hirr.ne_zero),
        Int.fract_lt_one x⟩
  | succ n ih =>
      rcases ih with ⟨hirr, -, -⟩
      have hinv_irr : Irrational ((simpleCFFractionalRemainder x n)⁻¹) :=
        hirr.inv
      have hfract_irr :
          Irrational (Int.fract ((simpleCFFractionalRemainder x n)⁻¹)) := by
        rw [← Int.fract_add_floor ((simpleCFFractionalRemainder x n)⁻¹)] at hinv_irr
        exact hinv_irr.of_add_intCast ⌊(simpleCFFractionalRemainder x n)⁻¹⌋
      exact ⟨hfract_irr,
        lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hfract_irr.ne_zero),
        Int.fract_lt_one _⟩

def SimpleCFAlgorithmPartialsPositive (x : ℝ) : Prop :=
  Irrational x → SimpleCFPositivePartials (simpleCFAlgorithmPartials x)

theorem simpleCFAlgorithmPartialsPositive_of_irrational (x : ℝ) :
    SimpleCFAlgorithmPartialsPositive x := by
  intro hx n
  rcases simpleCFFractionalRemainder_irrational_unitInterval x hx n with ⟨-, hpos, hlt⟩
  exact (Int.le_floor).2 (by
    norm_num
    exact ((one_le_inv₀ hpos).2 hlt.le))

theorem simpleCFFractionalRemainder_irrational_continuousAt
    (n : ℕ) (x : {x : ℝ // Irrational x}) :
    ContinuousAt (fun y : {x : ℝ // Irrational x} =>
      simpleCFFractionalRemainder y.1 n) x := by
  induction n with
  | zero =>
      have hxne : x.1 ≠ (⌊x.1⌋ : ℝ) :=
        x.2.ne_int ⌊x.1⌋
      simpa [simpleCFFractionalRemainder, Function.comp_def] using
        (continuousAt_fract (x := x.1) hxne).comp continuous_subtype_val.continuousAt
  | succ n ih =>
      have hrem_irr :
          Irrational (simpleCFFractionalRemainder x.1 n) :=
        (simpleCFFractionalRemainder_irrational_unitInterval x.1 x.2 n).1
      have hrem_ne :
          simpleCFFractionalRemainder x.1 n ≠ 0 :=
        hrem_irr.ne_zero
      have hinv_cont :
          ContinuousAt
            (fun y : {x : ℝ // Irrational x} =>
              (simpleCFFractionalRemainder y.1 n)⁻¹) x :=
        ih.inv₀ hrem_ne
      have hinv_irr :
          Irrational ((simpleCFFractionalRemainder x.1 n)⁻¹) :=
        hrem_irr.inv
      have hinv_ne :
          (simpleCFFractionalRemainder x.1 n)⁻¹ ≠
            (⌊(simpleCFFractionalRemainder x.1 n)⁻¹⌋ : ℝ) :=
        hinv_irr.ne_int ⌊(simpleCFFractionalRemainder x.1 n)⁻¹⌋
      have hfract_cont :
          ContinuousAt Int.fract ((simpleCFFractionalRemainder x.1 n)⁻¹) :=
        continuousAt_fract
          (x := (simpleCFFractionalRemainder x.1 n)⁻¹) hinv_ne
      exact Filter.Tendsto.comp hfract_cont hinv_cont

theorem simpleCFAlgorithmPartials_succ_eventually_eq
    (n : ℕ) (x : {x : ℝ // Irrational x}) :
    ∀ᶠ y in 𝓝 x,
      simpleCFAlgorithmPartials y.1 (n + 1) =
        simpleCFAlgorithmPartials x.1 (n + 1) := by
  let u : ℝ := (simpleCFFractionalRemainder x.1 n)⁻¹
  have hrem_irr :
      Irrational (simpleCFFractionalRemainder x.1 n) :=
    (simpleCFFractionalRemainder_irrational_unitInterval x.1 x.2 n).1
  have hu_irr : Irrational u := by
    simpa [u] using hrem_irr.inv
  have hu_mem : u ∈ Set.Ioo (⌊u⌋ : ℝ) ((⌊u⌋ : ℝ) + 1) := by
    constructor
    · have hle : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
      exact lt_of_le_of_ne hle (by
        intro hEq
        exact hu_irr.ne_int ⌊u⌋ hEq.symm)
    · exact Int.lt_floor_add_one u
  have hinv_cont :
      ContinuousAt
        (fun y : {x : ℝ // Irrational x} =>
          (simpleCFFractionalRemainder y.1 n)⁻¹) x :=
    (simpleCFFractionalRemainder_irrational_continuousAt n x).inv₀
      hrem_irr.ne_zero
  have hevent :
      ∀ᶠ y in 𝓝 x,
        (simpleCFFractionalRemainder y.1 n)⁻¹ ∈
          Set.Ioo (⌊u⌋ : ℝ) ((⌊u⌋ : ℝ) + 1) :=
    hinv_cont.eventually (isOpen_Ioo.mem_nhds hu_mem)
  filter_upwards [hevent] with y hy
  have hfloor :
      ⌊(simpleCFFractionalRemainder y.1 n)⁻¹⌋ = ⌊u⌋ := by
    rw [Int.floor_eq_iff]
    exact ⟨le_of_lt hy.1, hy.2⟩
  simpa [simpleCFAlgorithmPartials, u] using hfloor

theorem simpleCFAlgorithmPartials_succ_continuousAt
    (n : ℕ) (x : {x : ℝ // Irrational x}) :
    ContinuousAt
      (fun y : {x : ℝ // Irrational x} =>
        simpleCFAlgorithmPartials y.1 (n + 1)) x := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [simpleCFAlgorithmPartials_succ_eventually_eq n x] with y hy
  exact hy.symm

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For a nonempty prefix $s = (a_1,\ldots,a_n)$, let
    $$\frac{p_{n+1}}{q_{n+1}} := [0; a_1,\ldots,a_n],
    \qquad
    \frac{p_n}{q_n} := [0; a_1,\ldots,a_{n-1}]$$
-/
noncomputable def simpleCFTailMap (a : ℕ → ℤ) (n : ℕ) (x : ℝ) : ℝ :=
  (x * simpleCFNum a (n + 1) + simpleCFNum a n) /
    (x * simpleCFDen a (n + 1) + simpleCFDen a n)

noncomputable def simpleCFCompleteQuotientValue (a : ℕ → ℤ) (n : ℕ) (x : ℝ) : ℝ :=
  ((simpleCFNum a (n + 1) : ℝ) + x * (simpleCFNum a n : ℝ)) /
    ((simpleCFDen a (n + 1) : ℝ) + x * (simpleCFDen a n : ℝ))

noncomputable def simpleCFEndpoint (a : ℕ → ℤ) (n : ℕ) : ℝ :=
  (simpleCFConvergent a n : ℝ)

noncomputable def simpleCFAdjacentEndpoint (a : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((simpleCFNum a (n + 1) + simpleCFNum a n : ℤ) : ℝ) /
    ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ)

noncomputable def simpleCFFiniteTail (a : ℕ → ℤ) : ℕ → ℝ → ℝ
  | 0, x => 1 / x
  | n + 1, x => simpleCFFiniteTail a n ((a (n + 1) : ℝ) + 1 / x)

theorem simpleCFTailMap_denom_pos_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      0 < x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) := by
  intro n x hx
  exact add_pos_of_pos_of_nonneg
    (mul_pos hx (by exact_mod_cast simpleCFDen_pos_of_positive ha n))
    (by exact_mod_cast simpleCFDen_nonneg_of_positive ha n)

/-- Difference formula for the fractional-linear tail map. This is the
determinant computation behind the book's derivative-sign argument. -/
theorem simpleCFTailMap_sub_tailMap {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    simpleCFTailMap a n y - simpleCFTailMap a n x =
      (y - x) * (-1 : ℝ) ^ (n + 1) /
        ((y * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
          (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))) := by
  have hyden :
      y * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) ≠ 0 :=
    ne_of_gt (simpleCFTailMap_denom_pos_of_positive ha n y hy)
  have hxden :
      x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) ≠ 0 :=
    ne_of_gt (simpleCFTailMap_denom_pos_of_positive ha n x hx)
  have hyden' :
      (simpleCFDen a (n + 1) : ℝ) * y + (simpleCFDen a n : ℝ) ≠ 0 := by
    simpa [mul_comm] using hyden
  have hxden' :
      (simpleCFDen a (n + 1) : ℝ) * x + (simpleCFDen a n : ℝ) ≠ 0 := by
    simpa [mul_comm] using hxden
  have hdetR :
      (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
          (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) =
        (-1 : ℝ) ^ (n + 1) := by
    exact_mod_cast simpleCF_determinant a n
  unfold simpleCFTailMap
  field_simp [hyden, hxden, hyden', hxden']
  linear_combination (y - x) * hdetR

/-- When the prefix length has even parity, the fractional-linear tail map is
strictly decreasing on positive tails. -/
theorem simpleCFTailMap_strictAnti_of_even {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n : ℕ} (hn : Even n) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) :
    simpleCFTailMap a n y < simpleCFTailMap a n x := by
  have hy : 0 < y := hx.trans hxy
  have hsub := simpleCFTailMap_sub_tailMap ha n hx hy
  have hpow : (-1 : ℝ) ^ (n + 1) = -1 := by
    rw [pow_succ, hn.neg_one_pow]
    ring
  have hden_pos :
      0 <
        (y * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
          (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) :=
    mul_pos
      (simpleCFTailMap_denom_pos_of_positive ha n y hy)
      (simpleCFTailMap_denom_pos_of_positive ha n x hx)
  have hnum_neg : (y - x) * (-1 : ℝ) < 0 := by
    nlinarith
  have hdiff_neg : simpleCFTailMap a n y - simpleCFTailMap a n x < 0 := by
    rw [hsub, hpow]
    exact div_neg_of_neg_of_pos hnum_neg hden_pos
  linarith

/-- When the prefix length has odd parity, the fractional-linear tail map is
strictly increasing on positive tails. -/
theorem simpleCFTailMap_strictMono_of_odd {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n : ℕ} (hn : Odd n) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) :
    simpleCFTailMap a n x < simpleCFTailMap a n y := by
  have hy : 0 < y := hx.trans hxy
  have hsub := simpleCFTailMap_sub_tailMap ha n hx hy
  have hpow : (-1 : ℝ) ^ (n + 1) = 1 := by
    rw [pow_succ, hn.neg_one_pow]
    ring
  have hden_pos :
      0 <
        (y * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
          (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) :=
    mul_pos
      (simpleCFTailMap_denom_pos_of_positive ha n y hy)
      (simpleCFTailMap_denom_pos_of_positive ha n x hx)
  have hnum_pos : 0 < (y - x) * (1 : ℝ) := by
    nlinarith
  have hdiff_pos : 0 < simpleCFTailMap a n y - simpleCFTailMap a n x := by
    rw [hsub, hpow]
    exact div_pos hnum_pos hden_pos
  linarith

theorem simpleCFTailMap_sub_endpoint {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    simpleCFTailMap a n x - simpleCFEndpoint a n =
      (-1 : ℝ) ^ n /
        ((simpleCFDen a (n + 1) : ℝ) *
          (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))) := by
  have hQ : (simpleCFDen a (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast simpleCFConvergent_den_ne_zero_of_positive ha n
  have htail :
      x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) ≠ 0 :=
    ne_of_gt (simpleCFTailMap_denom_pos_of_positive ha n x hx)
  have hdetR :
      (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) =
        (-1 : ℝ) ^ n := by
    have hdet := simpleCF_determinant a n
    have hdetR' :
        (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
            (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) =
          ((-1 : ℤ) ^ (n + 1) : ℝ) := by
      exact_mod_cast hdet
    calc
      (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ)
          = -((simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
              (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
            ring
      _ = -(((-1 : ℤ) ^ (n + 1) : ℝ)) := by rw [hdetR']
      _ = (-1 : ℝ) ^ n := by
            norm_num [Int.cast_pow]
            rw [pow_succ]
            ring
  unfold simpleCFTailMap simpleCFEndpoint simpleCFConvergent
  norm_num [Rat.cast_div, simpleCFConvergent_den_ne_zero_of_positive ha n]
  field_simp [hQ, htail]
  ring_nf
  rw [show 1 + n = n + 1 by omega]
  linear_combination hdetR

theorem simpleCFTailMap_sub_adjacentEndpoint {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    simpleCFTailMap a n x - simpleCFAdjacentEndpoint a n =
      (x - 1) * (-1 : ℝ) ^ (n + 1) /
        ((x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
          ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ)) := by
  have htail :
      x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) ≠ 0 :=
    ne_of_gt (simpleCFTailMap_denom_pos_of_positive ha n x hx)
  have hQpos : 0 < simpleCFDen a (n + 1) := simpleCFDen_pos_of_positive ha n
  have hQn_nonneg : 0 ≤ simpleCFDen a n := simpleCFDen_nonneg_of_positive ha n
  have hadj :
      ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos_of_pos_of_nonneg hQpos hQn_nonneg)
  have hdet := simpleCF_determinant a n
  have hdetR :
      (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
          (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) =
        ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    exact_mod_cast hdet
  unfold simpleCFTailMap simpleCFAdjacentEndpoint
  norm_num
  field_simp [htail, hadj]
  ring_nf
  rw [show 1 + n = n + 1 by omega]
  norm_num [Int.cast_pow] at hdetR
  linear_combination (x - 1) * hdetR

theorem simpleCFTailMap_one_eq_adjacentEndpoint {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    simpleCFTailMap a n 1 = simpleCFAdjacentEndpoint a n := by
  have h := simpleCFTailMap_sub_adjacentEndpoint ha n (x := 1) zero_lt_one
  have hzero : simpleCFTailMap a n 1 - simpleCFAdjacentEndpoint a n = 0 := by
    simpa using h
  linarith

theorem simpleCFTailMap_mem_interval_of_gt_one {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ : ℤ) (n : ℕ) {x : ℝ} (hx : 1 < x) :
    (a₀ : ℝ) + simpleCFTailMap a n x ∈
      if Even n then
        Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
          ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
      else
        Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
          ((a₀ : ℝ) + simpleCFEndpoint a n) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hxminus : 0 < x - 1 := sub_pos.2 hx
  have htailpos :
      0 < x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) :=
    simpleCFTailMap_denom_pos_of_positive ha n x hxpos
  have hQpos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hQn_nonneg : 0 ≤ simpleCFDen a n := simpleCFDen_nonneg_of_positive ha n
  have hadjpos :
      0 < ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) := by
    exact_mod_cast add_pos_of_pos_of_nonneg (simpleCFDen_pos_of_positive ha n) hQn_nonneg
  by_cases hn : Even n
  · rw [ite_eq_left hn]
    have hpow : (-1 : ℝ) ^ n = 1 := hn.neg_one_pow
    have hpow_succ : (-1 : ℝ) ^ (n + 1) = -1 := by
      rw [pow_succ, hpow]
      ring
    have hleft : 0 < simpleCFTailMap a n x - simpleCFEndpoint a n := by
      rw [simpleCFTailMap_sub_endpoint ha n hxpos, hpow]
      positivity
    have hright : simpleCFTailMap a n x - simpleCFAdjacentEndpoint a n < 0 := by
      rw [simpleCFTailMap_sub_adjacentEndpoint ha n hxpos, hpow_succ]
      have hden :
          0 <
            (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
              ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) :=
        mul_pos htailpos hadjpos
      have hnum : (x - 1) * (-1 : ℝ) < 0 := by nlinarith
      exact div_neg_of_neg_of_pos hnum hden
    constructor <;> linarith
  · rw [ite_eq_right hn]
    have hnodd : Odd n := Nat.not_even_iff_odd.1 hn
    have hpow : (-1 : ℝ) ^ n = -1 := hnodd.neg_one_pow
    have hpow_succ : (-1 : ℝ) ^ (n + 1) = 1 := by
      rw [pow_succ, hpow]
      ring
    have hright : simpleCFTailMap a n x - simpleCFEndpoint a n < 0 := by
      rw [simpleCFTailMap_sub_endpoint ha n hxpos, hpow]
      have hden :
          0 <
            (simpleCFDen a (n + 1) : ℝ) *
              (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) :=
        mul_pos hQpos htailpos
      exact div_neg_of_neg_of_pos (by norm_num) hden
    have hleft : 0 < simpleCFTailMap a n x - simpleCFAdjacentEndpoint a n := by
      rw [simpleCFTailMap_sub_adjacentEndpoint ha n hxpos, hpow_succ]
      positivity
    constructor <;> linarith

theorem simpleCFTailMap_irrational_of_irrational {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {x : ℝ}
    (hx : 0 < x) (hirr : Irrational x) :
    Irrational (simpleCFTailMap a n x) := by
  have hQne : simpleCFDen a (n + 1) ≠ 0 :=
    ne_of_gt (simpleCFDen_pos_of_positive ha n)
  have hcoeff_ne :
      simpleCFDen a (n + 1) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hQne
  have hmul :
      Irrational
        (x * ((simpleCFDen a (n + 1) ^ 2 : ℤ) : ℝ)) :=
    hirr.mul_intCast hcoeff_ne
  have haff :
      Irrational
        (x * ((simpleCFDen a (n + 1) ^ 2 : ℤ) : ℝ) +
          ((simpleCFDen a (n + 1) * simpleCFDen a n : ℤ) : ℝ)) :=
    hmul.add_intCast (simpleCFDen a (n + 1) * simpleCFDen a n)
  have hdenIrr :
      Irrational
        ((simpleCFDen a (n + 1) : ℝ) *
          (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))) := by
    rw [mul_add]
    simpa only [pow_two, Int.cast_mul, mul_assoc, mul_comm, mul_left_comm, add_comm] using haff
  have hfrac :
      Irrational
        (((-1 : ℝ) ^ n) /
          ((simpleCFDen a (n + 1) : ℝ) *
            (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)))) := by
    rcases neg_one_pow_eq_or ℝ n with hpow | hpow
    · rw [hpow]
      simpa using hdenIrr.ratCast_div (q := (1 : ℚ)) (by norm_num)
    · rw [hpow]
      simpa using hdenIrr.ratCast_div (q := (-1 : ℚ)) (by norm_num)
  have hdiff :
      Irrational (simpleCFTailMap a n x - simpleCFEndpoint a n) := by
    rw [simpleCFTailMap_sub_endpoint ha n hx]
    exact hfrac
  exact Irrational.of_sub_ratCast (q := simpleCFConvergent a n)
    (by simpa [simpleCFEndpoint] using hdiff)

theorem simpleCFTailImageInterval_subset_of_positive
    (a₀ : ℤ) {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (fun x : ℝ => (a₀ : ℝ) + simpleCFTailMap a n x) ''
        {x : ℝ | Irrational x ∧ 1 < x} ⊆
      {y : ℝ | Irrational y ∧
        y ∈
          if Even n then
            Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
              ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
          else
            Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
              ((a₀ : ℝ) + simpleCFEndpoint a n)} := by
  rintro y ⟨x, hx, rfl⟩
  exact
    ⟨(simpleCFTailMap_irrational_of_irrational ha n
        (zero_lt_one.trans hx.2) hx.1).intCast_add a₀,
      simpleCFTailMap_mem_interval_of_gt_one ha a₀ n hx.2⟩

theorem simpleCFEndpoint_eq_div {a : ℕ → ℤ}
    (n : ℕ) :
    simpleCFEndpoint a n =
      (simpleCFNum a (n + 1) : ℝ) / (simpleCFDen a (n + 1) : ℝ) := by
  unfold simpleCFEndpoint simpleCFConvergent
  norm_num [Rat.cast_div]

theorem simpleCFAdjacentEndpoint_den_pos {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    0 < ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) := by
  exact_mod_cast add_pos_of_pos_of_nonneg
    (simpleCFDen_pos_of_positive ha n)
    (simpleCFDen_nonneg_of_positive ha n)

theorem abs_simpleCFAdjacentEndpoint_sub_endpoint {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    |simpleCFAdjacentEndpoint a n - simpleCFEndpoint a n| =
      1 / ((simpleCFDen a (n + 1) : ℝ) *
        ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))) := by
  have hadj := simpleCFTailMap_one_eq_adjacentEndpoint ha n
  have hsub := simpleCFTailMap_sub_endpoint ha n (x := 1) zero_lt_one
  rw [hadj] at hsub
  simp [one_mul] at hsub
  have hQpos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hdenpos :
      0 < (simpleCFDen a (n + 1) : ℝ) *
        ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) :=
    mul_pos hQpos
      (add_pos_of_pos_of_nonneg hQpos (by exact_mod_cast simpleCFDen_nonneg_of_positive ha n))
  calc
    |simpleCFAdjacentEndpoint a n - simpleCFEndpoint a n|
        = |((-1 : ℝ) ^ n /
            ((simpleCFDen a (n + 1) : ℝ) *
              ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))))| := by
          rw [hsub]
    _ = |(-1 : ℝ) ^ n| /
          |(simpleCFDen a (n + 1) : ℝ) *
            ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))| := by
          rw [abs_div]
    _ = 1 / ((simpleCFDen a (n + 1) : ℝ) *
          ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))) := by
          rw [abs_neg_one_pow, abs_of_pos hdenpos]

theorem abs_simpleCFAdjacentEndpoint_sub_endpoint_le_inv_sq {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    |simpleCFAdjacentEndpoint a n - simpleCFEndpoint a n| ≤
      1 / (simpleCFDen a (n + 1) : ℝ) ^ 2 := by
  rw [abs_simpleCFAdjacentEndpoint_sub_endpoint ha n]
  have hQpos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hRnonneg : 0 ≤ (simpleCFDen a n : ℝ) := by
    exact_mod_cast simpleCFDen_nonneg_of_positive ha n
  have hden_ge :
      (simpleCFDen a (n + 1) : ℝ) ^ 2 ≤
        (simpleCFDen a (n + 1) : ℝ) *
          ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) := by
    nlinarith
  exact one_div_le_one_div_of_le (pow_pos hQpos 2) hden_ge

/-- Translating a continued-fraction cylinder endpoint interval into the `a₀`-th
integer cell does not change its length. This is the length calculation used in
the fixed-cell cylinder formula. -/
theorem abs_translated_simpleCFAdjacentEndpoint_sub_endpoint {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ : ℤ) (n : ℕ) :
    |((a₀ : ℝ) + simpleCFAdjacentEndpoint a n) -
        ((a₀ : ℝ) + simpleCFEndpoint a n)| =
      1 / ((simpleCFDen a (n + 1) : ℝ) *
        ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))) := by
  calc
    |((a₀ : ℝ) + simpleCFAdjacentEndpoint a n) -
        ((a₀ : ℝ) + simpleCFEndpoint a n)|
        = |simpleCFAdjacentEndpoint a n - simpleCFEndpoint a n| := by ring_nf
    _ = 1 / ((simpleCFDen a (n + 1) : ℝ) *
        ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))) :=
      abs_simpleCFAdjacentEndpoint_sub_endpoint ha n

/-- The endpoint lengths of the fixed-cell continued-fraction cylinders shrink
to zero. This formalizes the book's use of the determinant identity to get the
neighborhood-base property. -/
theorem tendsto_abs_translated_simpleCFAdjacentEndpoint_sub_endpoint_zero {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ : ℤ) :
    Filter.Tendsto
      (fun n : ℕ =>
        |((a₀ : ℝ) + simpleCFAdjacentEndpoint a n) -
          ((a₀ : ℝ) + simpleCFEndpoint a n)|)
      Filter.atTop (𝓝 0) := by
  have hden_tendsto :
      Filter.Tendsto (fun n : ℕ => (simpleCFDen a (n + 1) : ℝ)) Filter.atTop
        Filter.atTop :=
    simpleCFDen_tendsto_atTop_of_positive ha
  have hinv_tendsto :
      Filter.Tendsto (fun n : ℕ => 1 / (simpleCFDen a (n + 1) : ℝ)) Filter.atTop
        (𝓝 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden_tendsto
  refine squeeze_zero (fun n => abs_nonneg _) ?_ hinv_tendsto
  intro n
  rw [abs_translated_simpleCFAdjacentEndpoint_sub_endpoint ha a₀ n]
  have hQpos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hQge : 1 ≤ (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hRnonneg : 0 ≤ (simpleCFDen a n : ℝ) := by
    exact_mod_cast simpleCFDen_nonneg_of_positive ha n
  have hden_ge :
      (simpleCFDen a (n + 1) : ℝ) ≤
        (simpleCFDen a (n + 1) : ℝ) *
          ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) := by
    nlinarith
  exact one_div_le_one_div_of_le hQpos hden_ge

/-- Algebraic inverse to the fractional-linear tail map. -/
noncomputable def simpleCFTailMapInverse (a : ℕ → ℤ) (n : ℕ) (t : ℝ) : ℝ :=
  ((simpleCFNum a n : ℝ) - t * (simpleCFDen a n : ℝ)) /
    (t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ))

theorem simpleCFTailMapInverse_denom_eq {a : ℕ → ℤ} (n : ℕ) {t : ℝ}
    (hden : t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) ≠ 0) :
    simpleCFTailMapInverse a n t * (simpleCFDen a (n + 1) : ℝ) +
        (simpleCFDen a n : ℝ) =
      (-1 : ℝ) ^ n /
        (t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ)) := by
  have hdetR :
      (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) =
        (-1 : ℝ) ^ n := by
    have hdet := simpleCF_determinant a n
    have hdetR' :
        (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
            (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) =
          ((-1 : ℤ) ^ (n + 1) : ℝ) := by
      exact_mod_cast hdet
    calc
      (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ)
          = -((simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
              (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
            ring
      _ = -(((-1 : ℤ) ^ (n + 1) : ℝ)) := by rw [hdetR']
      _ = (-1 : ℝ) ^ n := by
            norm_num [Int.cast_pow]
            rw [pow_succ]
            ring
  unfold simpleCFTailMapInverse
  field_simp [hden]
  ring_nf
  rw [show 1 + n = n + 1 by omega]
  linear_combination hdetR

theorem simpleCFTailMapInverse_num_eq {a : ℕ → ℤ} (n : ℕ) {t : ℝ}
    (hden : t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) ≠ 0) :
    simpleCFTailMapInverse a n t * (simpleCFNum a (n + 1) : ℝ) +
        (simpleCFNum a n : ℝ) =
      t * (-1 : ℝ) ^ n /
        (t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ)) := by
  have hdetR :
      (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) =
        (-1 : ℝ) ^ n := by
    have hdet := simpleCF_determinant a n
    have hdetR' :
        (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
            (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) =
          ((-1 : ℤ) ^ (n + 1) : ℝ) := by
      exact_mod_cast hdet
    calc
      (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ)
          = -((simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
              (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
            ring
      _ = -(((-1 : ℤ) ^ (n + 1) : ℝ)) := by rw [hdetR']
      _ = (-1 : ℝ) ^ n := by
            norm_num [Int.cast_pow]
            rw [pow_succ]
            ring
  unfold simpleCFTailMapInverse
  field_simp [hden]
  ring_nf
  rw [show 1 + n = n + 1 by omega]
  linear_combination t * hdetR

theorem simpleCFTailMap_simpleCFTailMapInverse {a : ℕ → ℤ} (n : ℕ) {t : ℝ}
    (hden : t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) ≠ 0) :
    simpleCFTailMap a n (simpleCFTailMapInverse a n t) = t := by
  rw [simpleCFTailMap]
  rw [simpleCFTailMapInverse_num_eq n hden, simpleCFTailMapInverse_denom_eq n hden]
  field_simp [hden, pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)]

theorem simpleCFTailMap_ratCast_rational (a : ℕ → ℤ) (n : ℕ) (q : ℚ) :
    ∃ r : ℚ, simpleCFTailMap a n (q : ℝ) = (r : ℝ) := by
  refine
    ⟨(q * (simpleCFNum a (n + 1) : ℚ) + (simpleCFNum a n : ℚ)) /
      (q * (simpleCFDen a (n + 1) : ℚ) + (simpleCFDen a n : ℚ)), ?_⟩
  unfold simpleCFTailMap
  norm_num

theorem simpleCFTailMapInverse_irrational_of_irrational {a : ℕ → ℤ} (n : ℕ) {t : ℝ}
    (hden : t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) ≠ 0)
    (htirr : Irrational t) :
    Irrational (simpleCFTailMapInverse a n t) := by
  intro hrat
  rcases hrat with ⟨q, hq⟩
  rcases simpleCFTailMap_ratCast_rational a n q with ⟨r, hr⟩
  refine htirr ⟨r, ?_⟩
  calc
    (r : ℝ) = simpleCFTailMap a n (q : ℝ) := hr.symm
    _ = simpleCFTailMap a n (simpleCFTailMapInverse a n t) := by rw [hq]
    _ = t := simpleCFTailMap_simpleCFTailMapInverse n hden

theorem simpleCFTailMapInverse_gt_one_of_mem_interval {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {t : ℝ}
    (ht : t ∈
      if Even n then
        Set.Ioo (simpleCFEndpoint a n) (simpleCFAdjacentEndpoint a n)
      else
        Set.Ioo (simpleCFAdjacentEndpoint a n) (simpleCFEndpoint a n)) :
    1 < simpleCFTailMapInverse a n t := by
  have hQpos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hAdjDenPos : 0 < ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) :=
    simpleCFAdjacentEndpoint_den_pos ha n
  by_cases hn : Even n
  · have htI :
        t ∈ Set.Ioo (simpleCFEndpoint a n) (simpleCFAdjacentEndpoint a n) := by
      simpa [hn] using ht
    have hdenpos :
        0 < t * (simpleCFDen a (n + 1) : ℝ) -
          (simpleCFNum a (n + 1) : ℝ) := by
      have htleft :
          (simpleCFNum a (n + 1) : ℝ) / (simpleCFDen a (n + 1) : ℝ) < t := by
        simpa [simpleCFEndpoint_eq_div (a := a) n] using htI.1
      have hmul := (div_lt_iff₀ hQpos).1 htleft
      nlinarith
    have hnum_gt_den :
        t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) <
          (simpleCFNum a n : ℝ) - t * (simpleCFDen a n : ℝ) := by
      have htright :
          t <
            ((simpleCFNum a (n + 1) + simpleCFNum a n : ℤ) : ℝ) /
              ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) := by
        simpa [simpleCFAdjacentEndpoint] using htI.2
      have hmul := (lt_div_iff₀ hAdjDenPos).1 htright
      norm_num [Int.cast_add] at hmul
      nlinarith
    unfold simpleCFTailMapInverse
    exact (one_lt_div hdenpos).2 hnum_gt_den
  · have htI :
        t ∈ Set.Ioo (simpleCFAdjacentEndpoint a n) (simpleCFEndpoint a n) := by
      simpa [hn] using ht
    have hdenneg :
        t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) < 0 := by
      have htright :
          t < (simpleCFNum a (n + 1) : ℝ) / (simpleCFDen a (n + 1) : ℝ) := by
        simpa [simpleCFEndpoint_eq_div (a := a) n] using htI.2
      have hmul := (lt_div_iff₀ hQpos).1 htright
      nlinarith
    have hnum_lt_den :
        (simpleCFNum a n : ℝ) - t * (simpleCFDen a n : ℝ) <
          t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) := by
      have htleft :
          ((simpleCFNum a (n + 1) + simpleCFNum a n : ℤ) : ℝ) /
              ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) < t := by
        simpa [simpleCFAdjacentEndpoint] using htI.1
      have hmul := (div_lt_iff₀ hAdjDenPos).1 htleft
      norm_num [Int.cast_add] at hmul
      nlinarith
    unfold simpleCFTailMapInverse
    exact (one_lt_div_of_neg hdenneg).2 hnum_lt_den

theorem simpleCFTailMapInverse_den_ne_zero_of_mem_interval {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {t : ℝ}
    (ht : t ∈
      if Even n then
        Set.Ioo (simpleCFEndpoint a n) (simpleCFAdjacentEndpoint a n)
      else
        Set.Ioo (simpleCFAdjacentEndpoint a n) (simpleCFEndpoint a n)) :
    t * (simpleCFDen a (n + 1) : ℝ) - (simpleCFNum a (n + 1) : ℝ) ≠ 0 := by
  have hQpos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  by_cases hn : Even n
  · have htI :
        t ∈ Set.Ioo (simpleCFEndpoint a n) (simpleCFAdjacentEndpoint a n) := by
      simpa [hn] using ht
    have htleft :
        (simpleCFNum a (n + 1) : ℝ) / (simpleCFDen a (n + 1) : ℝ) < t := by
      simpa [simpleCFEndpoint_eq_div (a := a) n] using htI.1
    have hmul := (div_lt_iff₀ hQpos).1 htleft
    exact ne_of_gt (by nlinarith)
  · have htI :
        t ∈ Set.Ioo (simpleCFAdjacentEndpoint a n) (simpleCFEndpoint a n) := by
      simpa [hn] using ht
    have htright :
        t < (simpleCFNum a (n + 1) : ℝ) / (simpleCFDen a (n + 1) : ℝ) := by
      simpa [simpleCFEndpoint_eq_div (a := a) n] using htI.2
    have hmul := (lt_div_iff₀ hQpos).1 htright
    exact ne_of_lt (by nlinarith)

theorem simpleCFTailImageInterval_superset_of_positive
    (a₀ : ℤ) {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) (n : ℕ) :
    {y : ℝ | Irrational y ∧
        y ∈
          if Even n then
            Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
              ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
          else
            Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
              ((a₀ : ℝ) + simpleCFEndpoint a n)} ⊆
      (fun x : ℝ => (a₀ : ℝ) + simpleCFTailMap a n x) ''
        {x : ℝ | Irrational x ∧ 1 < x} := by
  rintro y ⟨hyirr, hyint⟩
  let t : ℝ := y - (a₀ : ℝ)
  have htint :
      t ∈
        if Even n then
          Set.Ioo (simpleCFEndpoint a n) (simpleCFAdjacentEndpoint a n)
        else
          Set.Ioo (simpleCFAdjacentEndpoint a n) (simpleCFEndpoint a n) := by
    by_cases hn : Even n
    · rw [ite_eq_left hn] at hyint ⊢
      dsimp [t]
      constructor
      · linarith [hyint.1]
      · linarith [hyint.2]
    · rw [ite_eq_right hn] at hyint ⊢
      dsimp [t]
      constructor
      · linarith [hyint.1]
      · linarith [hyint.2]
  have hden := simpleCFTailMapInverse_den_ne_zero_of_mem_interval ha n htint
  have hxgt := simpleCFTailMapInverse_gt_one_of_mem_interval ha n htint
  have htirr : Irrational t := by
    simpa [t] using hyirr.sub_intCast a₀
  have hxirr := simpleCFTailMapInverse_irrational_of_irrational n hden htirr
  refine ⟨simpleCFTailMapInverse a n t, ⟨hxirr, hxgt⟩, ?_⟩
  dsimp [t]
  rw [simpleCFTailMap_simpleCFTailMapInverse n hden]
  ring

theorem simpleCFTailImageInterval_eq_of_positive
    (a₀ : ℤ) {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (fun x : ℝ => (a₀ : ℝ) + simpleCFTailMap a n x) ''
        {x : ℝ | Irrational x ∧ 1 < x} =
      {y : ℝ | Irrational y ∧
        y ∈
          if Even n then
            Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
              ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
          else
            Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
              ((a₀ : ℝ) + simpleCFEndpoint a n)} := by
  exact subset_antisymm
    (simpleCFTailImageInterval_subset_of_positive a₀ ha n)
    (simpleCFTailImageInterval_superset_of_positive a₀ ha n)

theorem simpleCFTailMap_succ_eq {a : ℕ → ℤ} {n : ℕ} {x : ℝ} (hx : x ≠ 0) :
    simpleCFTailMap a n ((a (n + 1) : ℝ) + 1 / x) =
      simpleCFTailMap a (n + 1) x := by
  rw [simpleCFTailMap, simpleCFTailMap, simpleCFNum_succ_succ, simpleCFDen_succ_succ]
  field_simp [hx]
  norm_num
  ring_nf

theorem SimpleCFFiniteTailFormulaClaim {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      simpleCFFiniteTail a n x = simpleCFTailMap a n x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp [simpleCFFiniteTail, simpleCFTailMap]
  | succ n ih =>
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt hx
      have htail_pos : 0 < (a (n + 1) : ℝ) + 1 / x := by
        exact add_pos_of_nonneg_of_pos
          (by exact_mod_cast le_trans zero_le_one (ha n))
          (one_div_pos.mpr hx)
      rw [simpleCFFiniteTail, ih ((a (n + 1) : ℝ) + 1 / x) htail_pos,
        simpleCFTailMap_succ_eq hxne]

def SimpleCFCompleteQuotientRelation (a : ℕ → ℤ) (α : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, α n = 1 / ((a (n + 1) : ℝ) + α (n + 1))

def SimpleCFAlgorithmCompleteQuotientRelation (x : ℝ) : Prop :=
  Irrational x →
    SimpleCFCompleteQuotientRelation
      (simpleCFAlgorithmPartials x) (simpleCFFractionalRemainder x)

theorem simpleCFAlgorithmCompleteQuotientRelation_of_irrational (x : ℝ) :
    SimpleCFAlgorithmCompleteQuotientRelation x := by
  intro hx n
  have hsum :
      Int.fract ((simpleCFFractionalRemainder x n)⁻¹) +
          (⌊(simpleCFFractionalRemainder x n)⁻¹⌋ : ℝ) =
        (simpleCFFractionalRemainder x n)⁻¹ :=
    Int.fract_add_floor _
  have hsum' :
      (simpleCFAlgorithmPartials x (n + 1) : ℝ) +
          simpleCFFractionalRemainder x (n + 1) =
        (simpleCFFractionalRemainder x n)⁻¹ := by
    simp [simpleCFAlgorithmPartials, simpleCFFractionalRemainder, add_comm, hsum]
  rw [hsum']
  rw [one_div, inv_inv]

theorem simpleCFCompleteQuotientValue_succ_eq {a : ℕ → ℤ} {n : ℕ} {x : ℝ}
    (hx : (a (n + 1) : ℝ) + x ≠ 0) :
    simpleCFCompleteQuotientValue a n (1 / ((a (n + 1) : ℝ) + x)) =
      simpleCFCompleteQuotientValue a (n + 1) x := by
  rw [simpleCFCompleteQuotientValue, simpleCFCompleteQuotientValue,
    simpleCFNum_succ_succ, simpleCFDen_succ_succ]
  field_simp [hx]
  norm_num
  ring_nf

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    The \termdefine{tail formula}
    $$\alpha_0 \;=\; \frac{p_{n+1} + \alpha_n p_n}{q_{n+1} + \alpha_n q_n}$$
    holds for $n \ge 0$. At $n = 0$ it reduces to the tautology $\alpha_0 = (p_1 + \alpha_0 p_0)/(q_1 + \alpha_0 q_0) =
    \alpha_0$. \emph{Inductive step at $n \ge 1$:} substitute $\alpha_{n-1} = 1/(a_n + \alpha_n)$ into the formula at level
    $n - 1$ and clear:
-/
theorem SimpleCFTailFormulaClaim {a : ℕ → ℤ} {α : ℕ → ℝ}
    (hα : SimpleCFCompleteQuotientRelation a α)
    (hpos : ∀ n : ℕ, 0 < (a (n + 1) : ℝ) + α (n + 1)) :
    ∀ n : ℕ, α 0 = simpleCFCompleteQuotientValue a n (α n) := by
  intro n
  induction n with
  | zero =>
      simp [simpleCFCompleteQuotientValue]
  | succ n ih =>
      rw [ih, hα n, simpleCFCompleteQuotientValue_succ_eq (ne_of_gt (hpos n))]

theorem simpleCF_cross_determinant_rev (a : ℕ → ℤ) (n : ℕ) :
    (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
        (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) =
      (-1 : ℝ) ^ n := by
  have hdet := simpleCF_determinant a n
  have hdetR :
      (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
          (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) =
        ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    exact_mod_cast hdet
  calc
    (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) -
        (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ)
        = -((simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
          (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ)) := by
            ring
    _ = -(((-1 : ℤ) ^ (n + 1) : ℝ)) := by rw [hdetR]
    _ = (-1 : ℝ) ^ n := by
          norm_num [Int.cast_pow]
          rw [pow_succ]
          ring

theorem simpleCFCompleteQuotientValue_succ_sub_convergent {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    simpleCFCompleteQuotientValue a (n + 1) x - (simpleCFConvergent a n : ℝ) =
      (-1 : ℝ) ^ n /
        ((simpleCFDen a (n + 1) : ℝ) *
          ((simpleCFDen a (n + 2) : ℝ) + x * (simpleCFDen a (n + 1) : ℝ))) := by
  have hQ : (simpleCFDen a (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast simpleCFConvergent_den_ne_zero_of_positive ha n
  have hQ1pos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hQ2pos : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have htailpos :
      0 < (simpleCFDen a (n + 2) : ℝ) + x * (simpleCFDen a (n + 1) : ℝ) :=
    add_pos_of_pos_of_nonneg hQ2pos (mul_nonneg hx hQ1pos.le)
  have htail :
      (simpleCFDen a (n + 2) : ℝ) + x * (simpleCFDen a (n + 1) : ℝ) ≠ 0 :=
    ne_of_gt htailpos
  have hdetR := simpleCF_cross_determinant_rev a (n + 1)
  unfold simpleCFCompleteQuotientValue simpleCFConvergent
  norm_num [Rat.cast_div, simpleCFConvergent_den_ne_zero_of_positive ha n]
  field_simp [hQ, htail]
  ring_nf
  rw [show 2 + n = n + 2 by omega, show 1 + n = n + 1 by omega]
  linear_combination -hdetR

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    Combining the tail formula at level $n + 1$ with (ii):
    $$\begin{aligned}
    \left| \alpha_0 - \frac{p_{n+1}}{q_{n+1}} \right|
    &\;\overset{\text{tail}}{=}\; \left|
    \frac{p_{n+2} + \alpha_{n+1} p_{n+1}}{q_{n+2} + \alpha_{n+1} q_{n+1}}
    - \frac{p_{n+1}}{q_{n+1}}
    \right| \\
    &\;=\; \frac{|p_{n+2} q_{n+1} - p_{n+1} q_{n+2}|}{q_{n+1}(q_{n+2} + \alpha_{n+1} q_{n+1})} \\
    &\;\overset{\text{(ii)}}{=}\; \frac{1}{q_{n+1}(q_{n+2} + \alpha_{n+1} q_{n+1})} \\
    &\;<\; \frac{1}{q_{n+1} q_{n+2}}.
    \end{aligned}$$
-/
/-- The book's strict convergent error bound: the tail formula at level `n + 1`
and the determinant identity bound the distance from `α₀` to the `n`-th
convergent strictly by `1 / (q_{n+1} q_{n+2})`. -/
theorem abs_simpleCFCompleteQuotientValue_succ_sub_convergent_lt {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |simpleCFCompleteQuotientValue a (n + 1) x - (simpleCFConvergent a n : ℝ)| <
      1 / ((simpleCFDen a (n + 1) : ℝ) * (simpleCFDen a (n + 2) : ℝ)) := by
  have hQ1pos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha n
  have hQ2pos : 0 < (simpleCFDen a (n + 2) : ℝ) := by
    exact_mod_cast simpleCFDen_pos_of_positive ha (n + 1)
  have htailpos :
      0 < (simpleCFDen a (n + 2) : ℝ) + x * (simpleCFDen a (n + 1) : ℝ) :=
    add_pos_of_pos_of_nonneg hQ2pos (mul_nonneg hx.le hQ1pos.le)
  rw [simpleCFCompleteQuotientValue_succ_sub_convergent ha n hx.le, abs_div,
    abs_neg_one_pow, abs_of_pos (mul_pos hQ1pos htailpos)]
  apply one_div_lt_one_div_of_lt (mul_pos hQ1pos hQ2pos)
  nlinarith [mul_pos hx (mul_pos hQ1pos hQ1pos)]

theorem simpleCFAlgorithmConvergent_tendsto_fractionalRemainder (x : ℝ)
    (hx : Irrational x) :
    SimpleCFConvergentLimit (simpleCFAlgorithmPartials x)
      (simpleCFFractionalRemainder x 0) := by
  let a := simpleCFAlgorithmPartials x
  let α := simpleCFFractionalRemainder x
  have ha : SimpleCFPositivePartials a := simpleCFAlgorithmPartialsPositive_of_irrational x hx
  have hα : SimpleCFCompleteQuotientRelation a α :=
    simpleCFAlgorithmCompleteQuotientRelation_of_irrational x hx
  have hunit : ∀ n : ℕ, Irrational (α n) ∧ 0 < α n ∧ α n < 1 := by
    intro n
    exact simpleCFFractionalRemainder_irrational_unitInterval x hx n
  have hpos : ∀ n : ℕ, 0 < (a (n + 1) : ℝ) + α (n + 1) := by
    intro n
    exact add_pos_of_nonneg_of_pos
      (by exact_mod_cast le_trans zero_le_one (ha n))
      (hunit (n + 1)).2.1
  have htail := SimpleCFTailFormulaClaim hα hpos
  have hbound :
      ∀ n : ℕ,
        dist ((simpleCFConvergent a n : ℚ) : ℝ) (α 0) ≤
          1 / (simpleCFDen a (n + 1) : ℝ) := by
    intro n
    have hstrict :=
      abs_simpleCFCompleteQuotientValue_succ_sub_convergent_lt ha n
        (hunit (n + 1)).2.1
    have hQ1pos : 0 < (simpleCFDen a (n + 1) : ℝ) := by
      exact_mod_cast simpleCFDen_pos_of_positive ha n
    have hQ2_ge_one : (1 : ℝ) ≤ (simpleCFDen a (n + 2) : ℝ) := by
      have h0 : 0 < simpleCFDen a (n + 2) := simpleCFDen_pos_of_positive ha (n + 1)
      have h1 : (1 : ℤ) ≤ simpleCFDen a (n + 2) := by omega
      exact_mod_cast h1
    refine le_of_lt ?_
    calc
      dist ((simpleCFConvergent a n : ℚ) : ℝ) (α 0)
          = |((simpleCFConvergent a n : ℚ) : ℝ) -
              simpleCFCompleteQuotientValue a (n + 1) (α (n + 1))| := by
                rw [htail (n + 1), dist_eq_norm, Real.norm_eq_abs]
      _ = |simpleCFCompleteQuotientValue a (n + 1) (α (n + 1)) -
            ((simpleCFConvergent a n : ℚ) : ℝ)| := by
              rw [abs_sub_comm]
      _ < 1 / ((simpleCFDen a (n + 1) : ℝ) * (simpleCFDen a (n + 2) : ℝ)) := hstrict
      _ ≤ 1 / (simpleCFDen a (n + 1) : ℝ) := by
            apply one_div_le_one_div_of_le hQ1pos
            exact le_mul_of_one_le_right hQ1pos.le hQ2_ge_one
  have hden_tendsto :
      Filter.Tendsto (fun n : ℕ => (simpleCFDen a (n + 1) : ℝ)) Filter.atTop
        Filter.atTop :=
    simpleCFDen_tendsto_atTop_of_positive ha
  have hinv_tendsto :
      Filter.Tendsto (fun n : ℕ => 1 / (simpleCFDen a (n + 1) : ℝ)) Filter.atTop
        (𝓝 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden_tendsto
  exact tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun n => dist_nonneg) hbound hinv_tendsto)

/-- Book-level continued-fraction convergence statement for an arbitrary positive sequence of
partial quotients. `SimpleCFInfiniteExpressionConvergesToReal` proves the convergence part in
Lean; this stronger specification also includes the book's irrationality and interval
conclusions. -/
def SimpleCFInfiniteExpressionConvergesToIrrational (a₀ : ℤ) (a : ℕ → ℤ) : Prop :=
  SimpleCFPositivePartials a →
    ∃ β : ℝ,
      0 < β ∧ β < 1 ∧ Irrational ((a₀ : ℝ) + β) ∧
        Filter.Tendsto
          (fun n : ℕ => (a₀ : ℝ) + (simpleCFConvergent a n : ℝ))
          Filter.atTop (𝓝 ((a₀ : ℝ) + β))

theorem simpleCFInfiniteExpressionConvergesToIrrational_of_limit_properties
    (a₀ : ℤ) (a : ℕ → ℤ)
    (hunit : SimpleCFLimitInOpenUnitInterval a)
    (hirr : SimpleCFShiftedLimitIrrational a₀ a) :
    SimpleCFInfiniteExpressionConvergesToIrrational a₀ a := by
  intro ha
  rcases exists_tendsto_simpleCFConvergent_of_positive ha with ⟨β, hβ⟩
  exact ⟨β, (hunit ha β hβ).1, (hunit ha β hβ).2, hirr ha β hβ,
    tendsto_const_nhds.add hβ⟩

theorem simpleCFInfiniteExpressionConvergesToIrrational_of_shiftedLimitIrrational
    (a₀ : ℤ) (a : ℕ → ℤ) (h : SimpleCFShiftedLimitIrrational a₀ a) :
    SimpleCFInfiniteExpressionConvergesToIrrational a₀ a :=
  simpleCFInfiniteExpressionConvergesToIrrational_of_limit_properties a₀ a
    (simpleCFLimitInOpenUnitInterval_of_positive a) h

theorem simpleCFInfiniteExpressionConvergesToIrrational_of_limitIrrational
    (a₀ : ℤ) (a : ℕ → ℤ) (h : SimpleCFLimitIrrational a) :
    SimpleCFInfiniteExpressionConvergesToIrrational a₀ a :=
  simpleCFInfiniteExpressionConvergesToIrrational_of_shiftedLimitIrrational a₀ a
    (simpleCFShiftedLimitIrrational_of_limitIrrational a₀ a h)

theorem simpleCFInfiniteExpressionConvergesToIrrational_of_positive
    (a₀ : ℤ) (a : ℕ → ℤ) :
    SimpleCFInfiniteExpressionConvergesToIrrational a₀ a :=
  simpleCFInfiniteExpressionConvergesToIrrational_of_limitIrrational a₀ a
    (simpleCFLimitIrrational_of_positive a)

def SimpleCFExpansionData (x : ℝ) (a₀ : ℤ) (a : ℕ → ℤ) : Prop :=
  a 0 = 0 ∧
    SimpleCFPositivePartials a ∧
      SimpleCFShiftedConvergentLimit a₀ a x

theorem simpleCFExpansionData_fractionalLimit {x : ℝ} {a₀ : ℤ} {a : ℕ → ℤ}
    (hdata : SimpleCFExpansionData x a₀ a) :
    SimpleCFConvergentLimit a (x - (a₀ : ℝ)) := by
  have hconst :
      Filter.Tendsto (fun _ : ℕ => (a₀ : ℝ)) Filter.atTop (𝓝 (a₀ : ℝ)) :=
    tendsto_const_nhds
  have h := hdata.2.2.sub hconst
  simpa [SimpleCFShiftedConvergentLimit, SimpleCFConvergentLimit] using h

theorem simpleCFExpansionData_fractionalPart_mem_Ioo {x : ℝ} {a₀ : ℤ}
    {a : ℕ → ℤ} (hdata : SimpleCFExpansionData x a₀ a) :
    x - (a₀ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
  simpleCFLimitInOpenUnitInterval_of_positive a hdata.2.1 (x - (a₀ : ℝ))
    (simpleCFExpansionData_fractionalLimit hdata)

theorem simpleCFExpansionData_integerPart_eq {x : ℝ} {a₀ : ℤ} {a : ℕ → ℤ}
    (hdata : SimpleCFExpansionData x a₀ a) :
    a₀ = simpleCFIntegerPart x := by
  have hunit := simpleCFExpansionData_fractionalPart_mem_Ioo hdata
  have hfloor : ⌊x⌋ = a₀ := by
    rw [Int.floor_eq_iff]
    constructor
    · linarith [hunit.1]
    · linarith [hunit.2]
  simpa [simpleCFIntegerPart] using hfloor.symm

theorem simpleCFExpansionData_integerPart_unique {x : ℝ} {a₀ b₀ : ℤ}
    {a b : ℕ → ℤ}
    (ha : SimpleCFExpansionData x a₀ a) (hb : SimpleCFExpansionData x b₀ b) :
    a₀ = b₀ := by
  rw [simpleCFExpansionData_integerPart_eq ha,
    simpleCFExpansionData_integerPart_eq hb]

theorem simpleCFConvergent_one_eq (a : ℕ → ℤ) :
    (simpleCFConvergent a 1 : ℝ) = 1 / (a 1 : ℝ) := by
  norm_num [simpleCFConvergent, simpleCFNum_succ_succ, simpleCFDen_succ_succ,
    Rat.cast_div]

theorem simpleCFConvergent_two_eq (a : ℕ → ℤ) :
    (simpleCFConvergent a 2 : ℝ) =
      (a 2 : ℝ) / ((a 1 : ℝ) * (a 2 : ℝ) + 1) := by
  norm_num [simpleCFConvergent, simpleCFNum_succ_succ, simpleCFDen_succ_succ,
    Rat.cast_div, Int.cast_add, Int.cast_mul]
  ring

/-- Drop the first positive partial quotient. The zero coordinate is a dummy coordinate used to
make `ℕ → ℤ` sequences canonical in `SimpleCFExpansionData`. -/
def simpleCFShiftPartials (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => a (n + 2)

@[simp]
theorem simpleCFShiftPartials_zero (a : ℕ → ℤ) :
    simpleCFShiftPartials a 0 = 0 :=
  rfl

@[simp]
theorem simpleCFShiftPartials_succ (a : ℕ → ℤ) (n : ℕ) :
    simpleCFShiftPartials a (n + 1) = a (n + 2) :=
  rfl

theorem simpleCFShiftPartials_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) :
    SimpleCFPositivePartials (simpleCFShiftPartials a) := by
  intro n
  simpa [simpleCFShiftPartials] using ha (n + 1)

theorem simpleCFNum_succ_eq_shiftDen (a : ℕ → ℤ) :
    ∀ n : ℕ,
      simpleCFNum a (n + 1) = simpleCFDen (simpleCFShiftPartials a) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simp
      · simp [simpleCFNum_succ_succ]
      · rw [show n + 2 + 1 = n + 3 by omega,
          show n + 3 = (n + 1) + 2 by omega, simpleCFNum_succ_succ]
        rw [show n + 2 = n + 2 by rfl, simpleCFDen_succ_succ]
        simp [simpleCFShiftPartials, ih (n + 1) (by omega), ih n (by omega)]

theorem simpleCFDen_succ_eq_shift (a : ℕ → ℤ) :
    ∀ n : ℕ,
      simpleCFDen a (n + 1) =
        a 1 * simpleCFDen (simpleCFShiftPartials a) n +
          simpleCFNum (simpleCFShiftPartials a) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simp
      · simp [simpleCFDen_succ_succ]
      · rw [show n + 2 + 1 = n + 3 by omega,
          show n + 3 = (n + 1) + 2 by omega, simpleCFDen_succ_succ]
        rw [ih (n + 1) (by omega), ih n (by omega)]
        rw [show n + 2 = n + 2 by rfl, simpleCFDen_succ_succ,
          simpleCFNum_succ_succ]
        simp [simpleCFShiftPartials]
        ring

theorem simpleCFConvergent_succ_eq_one_div_add_shift {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (simpleCFConvergent a (n + 1) : ℝ) =
      1 / ((a 1 : ℝ) +
        (simpleCFConvergent (simpleCFShiftPartials a) n : ℝ)) := by
  let b := simpleCFShiftPartials a
  have hb : SimpleCFPositivePartials b := simpleCFShiftPartials_positive ha
  have hdenb : (simpleCFDen b (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast simpleCFConvergent_den_ne_zero_of_positive hb n
  have hdenb' : (simpleCFDen (simpleCFShiftPartials a) (n + 1) : ℝ) ≠ 0 := by
    simpa [b] using hdenb
  have hdena : (simpleCFDen a (n + 2) : ℝ) ≠ 0 := by
    exact_mod_cast simpleCFConvergent_den_ne_zero_of_positive ha (n + 1)
  have hnum := simpleCFNum_succ_eq_shiftDen a (n + 1)
  have hden := simpleCFDen_succ_eq_shift a (n + 1)
  have hsum_ne :
      (a 1 : ℝ) + (simpleCFConvergent b n : ℝ) ≠ 0 := by
    have hb_nonneg :
        0 ≤ (simpleCFConvergent b n : ℝ) :=
      (simpleCFConvergent_mem_Icc_zero_one_of_positive hb n).1
    have ha₁_pos : 0 < (a 1 : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one (ha 0)
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha₁_pos hb_nonneg)
  have hsum_ne' :
      (a 1 : ℝ) +
          (simpleCFNum (simpleCFShiftPartials a) (n + 1) : ℝ) *
            (simpleCFDen (simpleCFShiftPartials a) (n + 1) : ℝ)⁻¹ ≠ 0 := by
    simpa [b, simpleCFConvergent, Rat.cast_div, div_eq_mul_inv, hdenb] using hsum_ne
  have hden_sum_ne :
      ((a 1 * simpleCFDen (simpleCFShiftPartials a) (n + 1) +
          simpleCFNum (simpleCFShiftPartials a) (n + 1) : ℤ) : ℝ) ≠ 0 := by
    rw [← hden]
    exact hdena
  have hden_sum_neR :
      (a 1 : ℝ) * (simpleCFDen (simpleCFShiftPartials a) (n + 1) : ℝ) +
          (simpleCFNum (simpleCFShiftPartials a) (n + 1) : ℝ) ≠ 0 := by
    simpa [Int.cast_add, Int.cast_mul] using hden_sum_ne
  have hsum_ne_div :
      (a 1 : ℝ) +
          (simpleCFNum (simpleCFShiftPartials a) (n + 1) : ℝ) /
            (simpleCFDen (simpleCFShiftPartials a) (n + 1) : ℝ) ≠ 0 := by
    simpa [div_eq_mul_inv] using hsum_ne'
  unfold simpleCFConvergent
  norm_num [Rat.cast_div, hdena, hdenb]
  rw [hnum, hden]
  field_simp [hdenb, hsum_ne_div, hden_sum_ne]
  norm_num [Int.cast_add, Int.cast_mul]
  rw [mul_comm (simpleCFDen (simpleCFShiftPartials a) (n + 1) : ℝ) (a 1 : ℝ)]
  rw [div_self hden_sum_neR]

theorem simpleCFShiftConvergent_eq_inv_sub {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) :
    (simpleCFConvergent (simpleCFShiftPartials a) n : ℝ) =
      (simpleCFConvergent a (n + 1) : ℝ)⁻¹ - (a 1 : ℝ) := by
  let b := simpleCFShiftPartials a
  have hb : SimpleCFPositivePartials b := simpleCFShiftPartials_positive ha
  have hb_nonneg :
      0 ≤ (simpleCFConvergent b n : ℝ) :=
    (simpleCFConvergent_mem_Icc_zero_one_of_positive hb n).1
  have ha₁_pos : 0 < (a 1 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (ha 0)
  have hsum_pos :
      0 < (a 1 : ℝ) + (simpleCFConvergent b n : ℝ) :=
    add_pos_of_pos_of_nonneg ha₁_pos hb_nonneg
  rw [simpleCFConvergent_succ_eq_one_div_add_shift ha n]
  field_simp [ne_of_gt hsum_pos]
  ring

theorem simpleCFShiftPartials_iterate_apply (a : ℕ → ℤ) (k m : ℕ) :
    Nat.iterate simpleCFShiftPartials k a (m + 1) = a (k + m + 1) := by
  induction k generalizing m with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp [simpleCFShiftPartials, ih (m + 1)]
      congr 1
      omega

theorem simpleCFExpansionData_firstPartial_eq_floor_inv_fractional {x : ℝ}
    {a₀ : ℤ} {a : ℕ → ℤ} (hdata : SimpleCFExpansionData x a₀ a) :
    a 1 = ⌊(x - (a₀ : ℝ))⁻¹⌋ := by
  let β : ℝ := x - (a₀ : ℝ)
  have hlim : SimpleCFConvergentLimit a β :=
    simpleCFExpansionData_fractionalLimit hdata
  have hbetween :
      β ∈ Set.uIoo (simpleCFConvergent a 1 : ℝ) (simpleCFConvergent a 2 : ℝ) :=
    simpleCFConvergent_limit_mem_uIoo hdata.2.1 hlim 1
  have ha₁_pos : 0 < (a 1 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (hdata.2.1 0)
  have ha₁_one_pos : 0 < (a 1 : ℝ) + 1 := by
    linarith
  have ha₂_ge_one : 1 ≤ (a 2 : ℝ) := by
    exact_mod_cast hdata.2.1 1
  have ha₂_pos : 0 < (a 2 : ℝ) := lt_of_lt_of_le zero_lt_one ha₂_ge_one
  have hden₂_pos : 0 < (a 1 : ℝ) * (a 2 : ℝ) + 1 := by
    nlinarith [mul_pos ha₁_pos ha₂_pos]
  have hc₂_lt_c₁ :
      (simpleCFConvergent a 2 : ℝ) < (simpleCFConvergent a 1 : ℝ) := by
    rw [simpleCFConvergent_one_eq, simpleCFConvergent_two_eq]
    rw [div_lt_div_iff₀ hden₂_pos ha₁_pos]
    nlinarith
  have hI :
      β ∈ Set.Ioo (simpleCFConvergent a 2 : ℝ) (simpleCFConvergent a 1 : ℝ) := by
    simpa [Set.uIoo_of_gt hc₂_lt_c₁] using hbetween
  have hβ_pos : 0 < β := by
    exact (simpleCFExpansionData_fractionalPart_mem_Ioo hdata).1
  have hβ_upper : β < 1 / (a 1 : ℝ) := by
    simpa [simpleCFConvergent_one_eq] using hI.2
  have hc₂_lower :
      1 / ((a 1 : ℝ) + 1) ≤ (simpleCFConvergent a 2 : ℝ) := by
    rw [simpleCFConvergent_two_eq]
    rw [div_le_div_iff₀ ha₁_one_pos hden₂_pos]
    nlinarith
  have hβ_lower : 1 / ((a 1 : ℝ) + 1) < β :=
    lt_of_le_of_lt hc₂_lower hI.1
  have hfloor : ⌊β⁻¹⌋ = a 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [inv_eq_one_div]
      exact (le_one_div ha₁_pos hβ_pos).2 hβ_upper.le
    · rw [inv_eq_one_div]
      exact (one_div_lt hβ_pos ha₁_one_pos).2 hβ_lower
  exact hfloor.symm

theorem simpleCFExpansionData_tail {x : ℝ} {a₀ : ℤ} {a : ℕ → ℤ}
    (hdata : SimpleCFExpansionData x a₀ a) :
    SimpleCFExpansionData ((x - (a₀ : ℝ))⁻¹) (a 1) (simpleCFShiftPartials a) := by
  let β : ℝ := x - (a₀ : ℝ)
  have hβ_unit : β ∈ Set.Ioo (0 : ℝ) 1 :=
    simpleCFExpansionData_fractionalPart_mem_Ioo hdata
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_unit.1
  have hlim : SimpleCFConvergentLimit a β :=
    simpleCFExpansionData_fractionalLimit hdata
  have hlim_succ :
      Filter.Tendsto
        (fun n : ℕ => (simpleCFConvergent a (n + 1) : ℝ))
        Filter.atTop (𝓝 β) :=
    hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hinv :
      Filter.Tendsto
        (fun n : ℕ => (simpleCFConvergent a (n + 1) : ℝ)⁻¹)
        Filter.atTop (𝓝 β⁻¹) :=
    hlim_succ.inv₀ hβ_ne
  have hraw :
      Filter.Tendsto
        (fun n : ℕ =>
          (simpleCFConvergent a (n + 1) : ℝ)⁻¹ - (a 1 : ℝ))
        Filter.atTop (𝓝 (β⁻¹ - (a 1 : ℝ))) :=
    hinv.sub tendsto_const_nhds
  have htail :
      SimpleCFConvergentLimit (simpleCFShiftPartials a) (β⁻¹ - (a 1 : ℝ)) := by
    refine Filter.Tendsto.congr' ?_ hraw
    exact Filter.Eventually.of_forall fun n =>
      (simpleCFShiftConvergent_eq_inv_sub hdata.2.1 n).symm
  refine ⟨rfl, simpleCFShiftPartials_positive hdata.2.1, ?_⟩
  have hshifted :
      Filter.Tendsto
        (fun n : ℕ =>
          (a 1 : ℝ) + (simpleCFConvergent (simpleCFShiftPartials a) n : ℝ))
        Filter.atTop (𝓝 ((a 1 : ℝ) + (β⁻¹ - (a 1 : ℝ)))) :=
    tendsto_const_nhds.add htail
  have htarget : (a 1 : ℝ) + (β⁻¹ - (a 1 : ℝ)) = (x - (a₀ : ℝ))⁻¹ := by
    simp [β]
  rw [htarget] at hshifted
  simpa [SimpleCFShiftedConvergentLimit, SimpleCFConvergentLimit] using hshifted

theorem simpleCFExpansionData_firstPartial_unique {x : ℝ} {a₀ b₀ : ℤ}
    {a b : ℕ → ℤ}
    (ha : SimpleCFExpansionData x a₀ a) (hb : SimpleCFExpansionData x b₀ b) :
    a 1 = b 1 := by
  have h₀ : a₀ = b₀ := simpleCFExpansionData_integerPart_unique ha hb
  rw [simpleCFExpansionData_firstPartial_eq_floor_inv_fractional ha,
    simpleCFExpansionData_firstPartial_eq_floor_inv_fractional hb, h₀]

theorem simpleCFExpansionData_iterate_shift_pair {x : ℝ} {a₀ b₀ : ℤ}
    {a b : ℕ → ℤ}
    (ha : SimpleCFExpansionData x a₀ a) (hb : SimpleCFExpansionData x b₀ b) :
    ∀ n : ℕ,
      ∃ y : ℝ, ∃ c₀ d₀ : ℤ, ∃ ca cb : ℕ → ℤ,
        ca = Nat.iterate simpleCFShiftPartials n a ∧
          cb = Nat.iterate simpleCFShiftPartials n b ∧
            SimpleCFExpansionData y c₀ ca ∧
              SimpleCFExpansionData y d₀ cb := by
  intro n
  induction n with
  | zero =>
      exact ⟨x, a₀, b₀, a, b, rfl, rfl, ha, hb⟩
  | succ n ih =>
      rcases ih with ⟨y, c₀, d₀, ca, cb, hca, hcb, hcaData, hcbData⟩
      have hc₀d₀ : c₀ = d₀ :=
        simpleCFExpansionData_integerPart_unique hcaData hcbData
      have hnextA := simpleCFExpansionData_tail hcaData
      have hnextB₀ := simpleCFExpansionData_tail hcbData
      have hnextB :
          SimpleCFExpansionData ((y - (c₀ : ℝ))⁻¹) (cb 1)
            (simpleCFShiftPartials cb) := by
        rwa [hc₀d₀]
      refine ⟨(y - (c₀ : ℝ))⁻¹, ca 1, cb 1,
        simpleCFShiftPartials ca, simpleCFShiftPartials cb, ?_, ?_,
        hnextA, hnextB⟩
      · rw [hca, Function.iterate_succ_apply']
      · rw [hcb, Function.iterate_succ_apply']

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    \emph{Uniqueness.} Suppose $\alpha = [a_0; a_1, a_2, \ldots] = [b_0; b_1, b_2, \ldots]$ with $a_0, b_0 \in \ZZ$ and
    $a_n, b_n \in \RestrictedSet{\NN}{\ge 1}$ for $n \ge 1$. By the converse, $\alpha - a_0 = [0; a_1, a_2, \ldots] \in (0,
    1)$ and $\alpha - b_0 = [0; b_1, b_2, \ldots] \in (0, 1)$, forcing $a_0 = b_0 = \lfloor \alpha \rfloor$ and equating the
    tails. For finite truncations,
    $$[0;a_1,\ldots,a_n]^{-1}=[a_1;\ldots,a_n],$$
    and continuity of reciprocation at the positive limit lets this identity pass to the limit. Hence
    $$\frac{1}{\alpha - a_0} = [a_1; a_2, \ldots] = [b_1; b_2, \ldots],$$
    and the same argument applied to this value yields $a_1 = b_1$. Inductively $a_n = b_n$ for all $n$.
-/
theorem simpleCFExpansionData_positivePartials_unique {x : ℝ} {a₀ b₀ : ℤ}
    {a b : ℕ → ℤ}
    (ha : SimpleCFExpansionData x a₀ a) (hb : SimpleCFExpansionData x b₀ b) :
    ∀ n : ℕ, a (n + 1) = b (n + 1) := by
  intro n
  rcases simpleCFExpansionData_iterate_shift_pair ha hb n with
    ⟨y, c₀, d₀, ca, cb, hca, hcb, hcaData, hcbData⟩
  have hfirst : ca 1 = cb 1 :=
    simpleCFExpansionData_firstPartial_unique hcaData hcbData
  have hca1 : ca 1 = a (n + 1) := by
    rw [hca]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      simpleCFShiftPartials_iterate_apply a n 0
  have hcb1 : cb 1 = b (n + 1) := by
    rw [hcb]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      simpleCFShiftPartials_iterate_apply b n 0
  exact hca1.symm.trans (hfirst.trans hcb1)

def SimpleCFAlgorithmProducesExpansion (x : ℝ) : Prop :=
  Irrational x →
    SimpleCFExpansionData x (simpleCFIntegerPart x) (simpleCFAlgorithmPartials x)

theorem simpleCFAlgorithmProducesExpansion_of_irrational (x : ℝ) :
    SimpleCFAlgorithmProducesExpansion x := by
  intro hx
  refine ⟨rfl, simpleCFAlgorithmPartialsPositive_of_irrational x hx, ?_⟩
  have hfrac :=
    simpleCFAlgorithmConvergent_tendsto_fractionalRemainder x hx
  have hconst :
      Filter.Tendsto (fun _ : ℕ => (simpleCFIntegerPart x : ℝ)) Filter.atTop
        (𝓝 (simpleCFIntegerPart x : ℝ)) :=
    tendsto_const_nhds
  have hshift :=
    hconst.add hfrac
  simpa [SimpleCFShiftedConvergentLimit, SimpleCFConvergentLimit, simpleCFIntegerPart,
    simpleCFFractionalRemainder, add_comm, Int.fract_add_floor] using hshift

def SimpleCFExpansionExistenceForIrrationals : Prop :=
  ∀ x : ℝ, Irrational x →
    ∃ data : ℤ × (ℕ → ℤ), SimpleCFExpansionData x data.1 data.2

def SimpleCFExpansionUniquenessForIrrationals : Prop :=
  ∀ x : ℝ, Irrational x →
    ∀ a₀ b₀ : ℤ, ∀ a b : ℕ → ℤ,
      SimpleCFExpansionData x a₀ a →
        SimpleCFExpansionData x b₀ b →
          a₀ = b₀ ∧ a = b

theorem simpleCFExpansionUniquenessForIrrationals_of_expansionData :
    SimpleCFExpansionUniquenessForIrrationals := by
  intro x _hx a₀ b₀ a b ha hb
  have h₀ : a₀ = b₀ := simpleCFExpansionData_integerPart_unique ha hb
  have hpos : ∀ n : ℕ, a (n + 1) = b (n + 1) :=
    simpleCFExpansionData_positivePartials_unique ha hb
  refine ⟨h₀, ?_⟩
  funext n
  cases n with
  | zero =>
      exact ha.1.trans hb.1.symm
  | succ n =>
      exact hpos n

def SimpleCFExpansionExistsUniquelyForIrrationals : Prop :=
  ∀ x : ℝ, Irrational x →
    ∃! data : ℤ × (ℕ → ℤ), SimpleCFExpansionData x data.1 data.2

theorem simpleCFExpansionExistenceForIrrationals_of_algorithm
    (h : ∀ x : ℝ, SimpleCFAlgorithmProducesExpansion x) :
    SimpleCFExpansionExistenceForIrrationals := by
  intro x hx
  exact ⟨⟨simpleCFIntegerPart x, simpleCFAlgorithmPartials x⟩, h x hx⟩

theorem simpleCFExpansionExistenceForIrrationals_of_algorithmExpansion :
    SimpleCFExpansionExistenceForIrrationals :=
  simpleCFExpansionExistenceForIrrationals_of_algorithm
    simpleCFAlgorithmProducesExpansion_of_irrational

theorem simpleCFExpansionExistsUniquelyForIrrationals_of_existence_uniqueness
    (hex : SimpleCFExpansionExistenceForIrrationals)
    (huniq : SimpleCFExpansionUniquenessForIrrationals) :
    SimpleCFExpansionExistsUniquelyForIrrationals := by
  intro x hx
  rcases hex x hx with ⟨data, hdata⟩
  refine ⟨data, hdata, ?_⟩
  intro other hother
  rcases huniq x hx data.1 other.1 data.2 other.2 hdata hother with ⟨h₀, htail⟩
  cases data
  cases other
  simp_all

theorem simpleCFExpansionExistsUniquelyForIrrationals_of_algorithmExpansion :
    SimpleCFExpansionExistsUniquelyForIrrationals :=
  simpleCFExpansionExistsUniquelyForIrrationals_of_existence_uniqueness
    simpleCFExpansionExistenceForIrrationals_of_algorithmExpansion
    simpleCFExpansionUniquenessForIrrationals_of_expansionData

def SimpleCFConverseForPositivePartials : Prop :=
  ∀ a₀ : ℤ, ∀ a : ℕ → ℤ, SimpleCFInfiniteExpressionConvergesToIrrational a₀ a

theorem simpleCFConverseForPositivePartials_of_positive :
    SimpleCFConverseForPositivePartials := by
  intro a₀ a
  exact simpleCFInfiniteExpressionConvergesToIrrational_of_positive a₀ a

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: statement
  kind: theorem
  title: Simple continued fraction expansion theorem
-/
/-- Book-level existence and uniqueness theorem for simple continued-fraction expansions of
irrationals. Mathlib's algorithmic continued-fraction API proves convergence and nontermination
for `GenContFract.of`; connecting that API to the custom textbook coordinates is a separate
global development. -/
def SimpleCFExistenceUniquenessForIrrationals : Prop :=
  SimpleCFExpansionExistsUniquelyForIrrationals ∧
    SimpleCFConverseForPositivePartials

theorem simpleCFExistenceUniquenessForIrrationals_of_parts
    (hexuniq : SimpleCFExpansionExistsUniquelyForIrrationals)
    (hconv : SimpleCFConverseForPositivePartials) :
    SimpleCFExistenceUniquenessForIrrationals :=
  ⟨hexuniq, hconv⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: statement
  kind: theorem
  title: Simple continued fraction expansion theorem
-/
theorem simpleCFExistenceUniquenessForIrrationals_of_algorithmExpansion :
    SimpleCFExistenceUniquenessForIrrationals :=
  simpleCFExistenceUniquenessForIrrationals_of_parts
    simpleCFExpansionExistsUniquelyForIrrationals_of_algorithmExpansion
    simpleCFConverseForPositivePartials_of_positive

/-- Image formula for a continued-fraction cylinder under the fractional-linear tail map.
The target is the irrational part of the interval, matching the book's
`\SetDifference{...}{\QQ}`. -/
theorem simpleCFTailImageIntervalFact (a₀ : ℤ) (a : ℕ → ℤ) (n : ℕ) :
    SimpleCFPositivePartials a →
    (fun x : ℝ => (a₀ : ℝ) + simpleCFTailMap a n x) ''
        {x : ℝ | Irrational x ∧ 1 < x} =
      {y : ℝ | Irrational y ∧
        y ∈
          if Even n then
            Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
              ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
          else
            Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
              ((a₀ : ℝ) + simpleCFEndpoint a n)} := by
  intro ha
  exact simpleCFTailImageInterval_eq_of_positive a₀ ha n

theorem simpleCFTailImageIntervalFact_of_positive
    (a₀ : ℤ) (a : ℕ → ℤ) (n : ℕ) :
    SimpleCFPositivePartials a →
      (fun x : ℝ => (a₀ : ℝ) + simpleCFTailMap a n x) ''
          {x : ℝ | Irrational x ∧ 1 < x} =
        {y : ℝ | Irrational y ∧
          y ∈
            if Even n then
              Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
                ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
            else
              Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
                ((a₀ : ℝ) + simpleCFEndpoint a n)} :=
  simpleCFTailImageIntervalFact a₀ a n

abbrev positiveNat : Type :=
  {n : ℕ // 1 ≤ n}

instance : Inhabited positiveNat where
  default := ⟨1, by omega⟩

/-- The tail entries of a simple continued fraction are positive naturals, which are coded by
subtracting one. -/
def positiveNatEquivNat : positiveNat ≃ ℕ where
  toFun n := n.1 - 1
  invFun n := ⟨n + 1, by omega⟩
  left_inv n := by
    apply Subtype.ext
    exact Nat.sub_add_cancel n.2
  right_inv n := by
    exact Nat.add_sub_cancel n 1

noncomputable def positiveNatSeqHomeomorphBaire :
    (ℕ → positiveNat) ≃ₜ baire_space where
  toEquiv :=
    { toFun := fun s n => positiveNatEquivNat (s n)
      invFun := fun g n => positiveNatEquivNat.symm (g n)
      left_inv := by
        intro s
        funext n
        simp
      right_inv := by
        intro g
        funext n
        simp }
  continuous_toFun := by
    refine continuous_pi fun n => ?_
    exact (continuous_of_discreteTopology (f := positiveNatEquivNat)).comp
      (continuous_apply n)
  continuous_invFun := by
    refine continuous_pi fun n => ?_
    exact (continuous_of_discreteTopology (f := positiveNatEquivNat.symm)).comp
      (continuous_apply n)

def shiftPositiveNat (s : ℕ → positiveNat) : ℕ → positiveNat :=
  fun n => s (n + 1)

@[simp]
theorem shiftPositiveNat_apply (s : ℕ → positiveNat) (n : ℕ) :
    shiftPositiveNat s n = s (n + 1) :=
  rfl

/-- Recode a direction bit together with positive run lengths as one natural initial
coordinate followed by positive tail coordinates. The `false` branch encodes a zero
initial coordinate, while the `true` branch records the first positive entry and shifts
the remaining sequence. -/
noncomputable def boolPositiveNatSeqEquivNatPositiveNatSeq :
    Bool × (ℕ → positiveNat) ≃ ℕ × (ℕ → positiveNat) where
  toFun p :=
    if p.1 then
      ((p.2 0).1, fun n => p.2 (n + 1))
    else
      (0, p.2)
  invFun c :=
    if h : c.1 = 0 then
      (false, c.2)
    else
      (true, fun
        | 0 => ⟨c.1, Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h)⟩
        | n + 1 => c.2 n)
  left_inv p := by
    cases p with
    | mk ε s =>
        cases ε
        · simp
        · have hpos : 0 < (s 0).1 := Nat.succ_le_iff.mp (s 0).2
          have hne : (s 0).1 ≠ 0 := by omega
          simp [hne]
          funext n
          cases n <;> simp
  right_inv c := by
    cases c with
    | mk a s =>
        by_cases ha : a = 0
        · simp [ha]
        · apply Prod.ext
          · simp [ha]
          · funext n
            cases n <;> simp [ha]

theorem boolPositiveNatSeqEquivNatPositiveNatSeq_false (s : ℕ → positiveNat) :
    boolPositiveNatSeqEquivNatPositiveNatSeq (false, s) = (0, s) := by
  simp [boolPositiveNatSeqEquivNatPositiveNatSeq]

theorem boolPositiveNatSeqEquivNatPositiveNatSeq_true (s : ℕ → positiveNat) :
    boolPositiveNatSeqEquivNatPositiveNatSeq (true, s) =
      ((s 0).1, shiftPositiveNat s) := by
  apply Prod.ext
  · simp [boolPositiveNatSeqEquivNatPositiveNatSeq]
  · funext n
    simp [boolPositiveNatSeqEquivNatPositiveNatSeq, shiftPositiveNat]

/-- The topological form of `boolPositiveNatSeqEquivNatPositiveNatSeq`. -/
noncomputable def boolPositiveNatSeqHomeomorphNatPositiveNatSeq :
    Bool × (ℕ → positiveNat) ≃ₜ ℕ × (ℕ → positiveNat) where
  toEquiv := boolPositiveNatSeqEquivNatPositiveNatSeq
  continuous_toFun := by
    have hfst :
        Continuous (fun p : Bool × (ℕ → positiveNat) =>
          if p.1 then (p.2 0).1 else 0) := by
      have hpair : Continuous (fun p : Bool × (ℕ → positiveNat) => (p.1, p.2 0)) :=
        continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)
      exact (continuous_of_discreteTopology
        (f := fun p : Bool × positiveNat => if p.1 then p.2.1 else 0)).comp hpair
    have hsnd :
        Continuous (fun p : Bool × (ℕ → positiveNat) =>
          if p.1 then (fun n => p.2 (n + 1)) else p.2) := by
      refine continuous_pi fun n => ?_
      have htriple :
          Continuous (fun p : Bool × (ℕ → positiveNat) =>
            ((p.1, p.2 (n + 1)), p.2 n)) :=
        (continuous_fst.prodMk ((continuous_apply (n + 1)).comp continuous_snd)).prodMk
          ((continuous_apply n).comp continuous_snd)
      have hcoord : Continuous (fun p : Bool × (ℕ → positiveNat) =>
          if p.1 then p.2 (n + 1) else p.2 n) :=
        (continuous_of_discreteTopology
        (f := fun p : (Bool × positiveNat) × positiveNat =>
          if p.1.1 then p.1.2 else p.2)).comp htriple
      convert hcoord using 1
      funext p
      cases p.1 <;> rfl
    convert hfst.prodMk hsnd using 1
    funext p
    rcases p with ⟨ε, s⟩
    cases ε <;> simp [boolPositiveNatSeqEquivNatPositiveNatSeq]
  continuous_invFun := by
    have hfst :
        Continuous (fun c : ℕ × (ℕ → positiveNat) =>
          if c.1 = 0 then false else true) := by
      exact (continuous_of_discreteTopology
        (f := fun a : ℕ => if a = 0 then false else true)).comp continuous_fst
    have hsnd :
        Continuous (fun c : ℕ × (ℕ → positiveNat) =>
          if h : c.1 = 0 then
            c.2
          else
            fun
              | 0 => ⟨c.1, Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h)⟩
              | n + 1 => c.2 n) := by
      refine continuous_pi fun n => ?_
      cases n with
      | zero =>
          have hpair : Continuous (fun c : ℕ × (ℕ → positiveNat) => (c.1, c.2 0)) :=
            continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)
          have hcoord : Continuous (fun c : ℕ × (ℕ → positiveNat) =>
              if h : c.1 = 0 then c.2 0
              else ⟨c.1, Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h)⟩) :=
            (continuous_of_discreteTopology
            (f := fun p : ℕ × positiveNat =>
              if h : p.1 = 0 then p.2
              else ⟨p.1, Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h)⟩)).comp hpair
          convert hcoord using 1
          funext c
          by_cases h : c.1 = 0 <;> simp [h]
      | succ n =>
          have htriple :
              Continuous (fun c : ℕ × (ℕ → positiveNat) =>
                ((c.1, c.2 (n + 1)), c.2 n)) :=
            (continuous_fst.prodMk ((continuous_apply (n + 1)).comp continuous_snd)).prodMk
              ((continuous_apply n).comp continuous_snd)
          have hcoord : Continuous (fun c : ℕ × (ℕ → positiveNat) =>
              if c.1 = 0 then c.2 (n + 1) else c.2 n) :=
            (continuous_of_discreteTopology
            (f := fun p : (ℕ × positiveNat) × positiveNat =>
              if p.1.1 = 0 then p.1.2 else p.2)).comp htriple
          convert hcoord using 1
          funext c
          by_cases h : c.1 = 0 <;> simp [h]
    convert hfst.prodMk hsnd using 1
    funext c
    by_cases h : c.1 = 0 <;> simp [boolPositiveNatSeqEquivNatPositiveNatSeq, h]

/-- Code positive continued-fraction coordinates `(a₀, a₁, a₂, ...)` as a point of
Baire space: the natural integer part goes in coordinate `0`, and the positive tail
entries occupy the remaining coordinates. -/
def natPositiveNatSeqEquivBaire :
    (ℕ × (ℕ → positiveNat)) ≃ baire_space where
  toFun x := fun
    | 0 => x.1
    | n + 1 => positiveNatEquivNat (x.2 n)
  invFun x :=
    (x 0, fun n => positiveNatEquivNat.symm (x (n + 1)))
  left_inv x := by
    cases x with
    | mk a tail =>
        simp
  right_inv x := by
    funext n
    cases n with
    | zero => simp
    | succ n => simp

/-- The coordinate coding above is a homeomorphism. This is the formal version of
the positive continued-fraction row `a₀ ∈ ℕ` in the comparison table. -/
noncomputable def natPositiveNatSeqHomeomorphBaire :
    (ℕ × (ℕ → positiveNat)) ≃ₜ baire_space where
  toEquiv := natPositiveNatSeqEquivBaire
  continuous_toFun := by
    refine continuous_pi ?_
    intro n
    cases n with
    | zero =>
        exact continuous_fst
    | succ n =>
        exact (continuous_of_discreteTopology (f := positiveNatEquivNat)).comp
          ((continuous_apply n).comp continuous_snd)
  continuous_invFun := by
    refine (continuous_apply 0).prodMk ?_
    exact continuous_pi fun n =>
      (continuous_of_discreteTopology (f := positiveNatEquivNat.symm)).comp
        (continuous_apply (n + 1))

/-- Code the continued-fraction coordinates `(a₀, a₁, a₂, ...)` as a point of Baire space:
the integer part goes in coordinate `0`, and the positive tail entries occupy the remaining
coordinates. -/
noncomputable def intPositiveNatSeqEquivBaire :
    (ℤ × (ℕ → positiveNat)) ≃ baire_space where
  toFun x := fun
    | 0 => (Denumerable.eqv ℤ) x.1
    | n + 1 => positiveNatEquivNat (x.2 n)
  invFun x :=
    ((Denumerable.eqv ℤ).symm (x 0), fun n => positiveNatEquivNat.symm (x (n + 1)))
  left_inv x := by
    cases x with
    | mk z tail =>
        simp
  right_inv x := by
    funext n
    cases n with
    | zero => simp
    | succ n => simp

/-- The coordinate coding above is a homeomorphism. This is the formal version of the book's
final identification
`ℤ × {1,2,...}^ω` with Baire space in the continued-fraction model. -/
noncomputable def intPositiveNatSeqHomeomorphBaire :
    (ℤ × (ℕ → positiveNat)) ≃ₜ baire_space where
  toEquiv := intPositiveNatSeqEquivBaire
  continuous_toFun := by
    refine continuous_pi ?_
    intro n
    cases n with
    | zero =>
        exact (continuous_of_discreteTopology (f := Denumerable.eqv ℤ)).comp continuous_fst
    | succ n =>
        exact (continuous_of_discreteTopology (f := positiveNatEquivNat)).comp
          ((continuous_apply n).comp continuous_snd)
  continuous_invFun := by
    refine
      ((continuous_of_discreteTopology (f := (Denumerable.eqv ℤ).symm)).comp
          (continuous_apply 0)).prodMk ?_
    exact continuous_pi fun n =>
      (continuous_of_discreteTopology (f := positiveNatEquivNat.symm)).comp
        (continuous_apply (n + 1))

/-- Convert a sequence of positive natural partial quotients into the integer-valued partial
quotient sequence used by the custom continued-fraction recurrence. Coordinate `0` is the
canonical dummy value. -/
def positiveNatSeqPartials (s : ℕ → positiveNat) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (s n : ℕ)

@[simp]
theorem positiveNatSeqPartials_zero (s : ℕ → positiveNat) :
    positiveNatSeqPartials s 0 = 0 :=
  rfl

@[simp]
theorem positiveNatSeqPartials_succ (s : ℕ → positiveNat) (n : ℕ) :
    positiveNatSeqPartials s (n + 1) = (s n : ℕ) :=
  rfl

theorem positiveNatSeqPartials_positive (s : ℕ → positiveNat) :
    SimpleCFPositivePartials (positiveNatSeqPartials s) := by
  intro n
  simpa [positiveNatSeqPartials] using (show (1 : ℤ) ≤ ((s n : ℕ) : ℤ) by
    exact_mod_cast (s n).2)

/-- The algorithmic positive tail of an irrational, viewed as positive natural numbers. -/
noncomputable def simpleCFIrrationalTail (x : {x : ℝ // Irrational x}) :
    ℕ → positiveNat :=
  fun n =>
    ⟨Int.toNat (simpleCFAlgorithmPartials x.1 (n + 1)), by
      have hposZ : (1 : ℤ) ≤ simpleCFAlgorithmPartials x.1 (n + 1) :=
        simpleCFAlgorithmPartialsPositive_of_irrational x.1 x.2 n
      have hnonneg : 0 ≤ simpleCFAlgorithmPartials x.1 (n + 1) :=
        le_trans (by norm_num) hposZ
      have hcast :
          (((Int.toNat (simpleCFAlgorithmPartials x.1 (n + 1))) : ℕ) : ℤ) =
            simpleCFAlgorithmPartials x.1 (n + 1) :=
        Int.toNat_of_nonneg hnonneg
      have hposNatZ :
          (1 : ℤ) ≤
            (((Int.toNat (simpleCFAlgorithmPartials x.1 (n + 1))) : ℕ) : ℤ) := by
        simpa [hcast] using hposZ
      exact_mod_cast hposNatZ⟩

theorem simpleCFIrrationalTail_coordinate_eventually_eq
    (n : ℕ) (x : {x : ℝ // Irrational x}) :
    ∀ᶠ y in 𝓝 x, simpleCFIrrationalTail y n = simpleCFIrrationalTail x n := by
  filter_upwards [simpleCFAlgorithmPartials_succ_eventually_eq n x] with y hy
  apply Subtype.ext
  simp [simpleCFIrrationalTail, hy]

theorem simpleCFIrrationalTail_coordinate_continuousAt
    (n : ℕ) (x : {x : ℝ // Irrational x}) :
    ContinuousAt (fun y : {x : ℝ // Irrational x} => simpleCFIrrationalTail y n) x := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [simpleCFIrrationalTail_coordinate_eventually_eq n x] with y hy
  exact hy.symm

theorem simpleCFIrrationalTail_continuous :
    Continuous simpleCFIrrationalTail := by
  refine continuous_pi fun n => ?_
  rw [continuous_iff_continuousAt]
  intro x
  exact simpleCFIrrationalTail_coordinate_continuousAt n x

theorem positiveNatSeqPartials_simpleCFIrrationalTail
    (x : {x : ℝ // Irrational x}) :
    positiveNatSeqPartials (simpleCFIrrationalTail x) =
      simpleCFAlgorithmPartials x.1 := by
  funext n
  cases n with
  | zero =>
      rfl
  | succ n =>
      have hposZ : (1 : ℤ) ≤ simpleCFAlgorithmPartials x.1 (n + 1) :=
        simpleCFAlgorithmPartialsPositive_of_irrational x.1 x.2 n
      have hnonneg : 0 ≤ simpleCFAlgorithmPartials x.1 (n + 1) :=
        le_trans (by norm_num) hposZ
      have hcast :
          (((Int.toNat (simpleCFAlgorithmPartials x.1 (n + 1))) : ℕ) : ℤ) =
            simpleCFAlgorithmPartials x.1 (n + 1) :=
        Int.toNat_of_nonneg hnonneg
      simp [positiveNatSeqPartials, simpleCFIrrationalTail, hcast]

/-- Continued-fraction coordinates of an irrational: integer part plus positive tail. -/
noncomputable def simpleCFCoordinate
    (x : {x : ℝ // Irrational x}) : ℤ × (ℕ → positiveNat) :=
  (simpleCFIntegerPart x.1, simpleCFIrrationalTail x)

theorem simpleCFCoordinate_fst_continuous :
    Continuous (fun x : {x : ℝ // Irrational x} => (simpleCFCoordinate x).1) := by
  simpa [simpleCFCoordinate] using simpleCFIntegerPart_irrational_continuous

theorem simpleCFCoordinate_continuous :
    Continuous simpleCFCoordinate := by
  change Continuous fun x : {x : ℝ // Irrational x} =>
    (simpleCFIntegerPart x.1, simpleCFIrrationalTail x)
  exact simpleCFIntegerPart_irrational_continuous.prodMk simpleCFIrrationalTail_continuous

/-- The fractional limit selected by a positive continued-fraction tail. -/
noncomputable def simpleCFCoordinateBeta (a₀ : ℤ) (s : ℕ → positiveNat) : ℝ :=
  Classical.choose
    (simpleCFInfiniteExpressionConvergesToIrrational_of_positive a₀
      (positiveNatSeqPartials s) (positiveNatSeqPartials_positive s))

theorem simpleCFCoordinateBeta_spec (a₀ : ℤ) (s : ℕ → positiveNat) :
    0 < simpleCFCoordinateBeta a₀ s ∧
      simpleCFCoordinateBeta a₀ s < 1 ∧
        Irrational ((a₀ : ℝ) + simpleCFCoordinateBeta a₀ s) ∧
          Filter.Tendsto
            (fun n : ℕ =>
              (a₀ : ℝ) + (simpleCFConvergent (positiveNatSeqPartials s) n : ℝ))
            Filter.atTop (𝓝 ((a₀ : ℝ) + simpleCFCoordinateBeta a₀ s)) :=
  Classical.choose_spec
    (simpleCFInfiniteExpressionConvergesToIrrational_of_positive a₀
      (positiveNatSeqPartials s) (positiveNatSeqPartials_positive s))

theorem simpleCFNum_eq_of_eq_on_le {a b : ℕ → ℤ} {N k : ℕ}
    (h : ∀ i : ℕ, i ≤ N → a i = b i) (hk : k ≤ N + 1) :
    simpleCFNum a k = simpleCFNum b k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | _ | k
      · rfl
      · rfl
      · rw [simpleCFNum_succ_succ, simpleCFNum_succ_succ]
        rw [h (k + 1) (by omega), ih (k + 1) (by omega) (by omega),
          ih k (by omega) (by omega)]

theorem simpleCFDen_eq_of_eq_on_le {a b : ℕ → ℤ} {N k : ℕ}
    (h : ∀ i : ℕ, i ≤ N → a i = b i) (hk : k ≤ N + 1) :
    simpleCFDen a k = simpleCFDen b k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | _ | k
      · rfl
      · rfl
      · rw [simpleCFDen_succ_succ, simpleCFDen_succ_succ]
        rw [h (k + 1) (by omega), ih (k + 1) (by omega) (by omega),
          ih k (by omega) (by omega)]

theorem simpleCFConvergent_eq_of_eq_on_le {a b : ℕ → ℤ} {N n : ℕ}
    (h : ∀ i : ℕ, i ≤ N → a i = b i) (hn : n ≤ N) :
    simpleCFConvergent a n = simpleCFConvergent b n := by
  unfold simpleCFConvergent
  rw [simpleCFNum_eq_of_eq_on_le h (by omega : n + 1 ≤ N + 1),
    simpleCFDen_eq_of_eq_on_le h (by omega : n + 1 ≤ N + 1)]

theorem positiveNatSeqPartials_eq_on_le_of_mem_cyl {s t : ℕ → positiveNat} {N : ℕ}
    (ht : t ∈ cyl (seqPrefix s N)) :
    ∀ i : ℕ, i ≤ N → positiveNatSeqPartials t i = positiveNatSeqPartials s i := by
  intro i hi
  cases i with
  | zero =>
      simp
  | succ m =>
      have hm : m < N := by omega
      have hcoord : t m = s m := by
        calc
          t m = (seqPrefix s N).get ⟨m, by simpa using hm⟩ := ht m (by simpa using hm)
          _ = s m := seqPrefix_get s (by simpa using hm)
      simp [positiveNatSeqPartials, hcoord]

/-- Two positive continued-fraction tails in the same finite cylinder have the
same custom partial-quotient sequence up to the corresponding closed prefix
level. This is the finite-cylinder form used by Stern--Brocot node labels. -/
theorem positiveNatSeqPartials_eq_on_le_of_mem_same_cyl
    {pref : finseq positiveNat} {s t : ℕ → positiveNat}
    (hs : s ∈ cyl pref) (ht : t ∈ cyl pref) :
    ∀ i : ℕ, i ≤ pref.length →
      positiveNatSeqPartials s i = positiveNatSeqPartials t i := by
  intro i hi
  cases i with
  | zero =>
      simp
  | succ m =>
      have hm : m < pref.length := by omega
      have hscoord : s m = pref.get ⟨m, hm⟩ := hs m hm
      have htcoord : t m = pref.get ⟨m, hm⟩ := ht m hm
      simp [positiveNatSeqPartials, hscoord, htcoord]

theorem simpleCFCoordinateBeta_convergentLimit (a₀ : ℤ) (s : ℕ → positiveNat) :
    SimpleCFConvergentLimit (positiveNatSeqPartials s)
      (simpleCFCoordinateBeta a₀ s) := by
  have hlim := (simpleCFCoordinateBeta_spec a₀ s).2.2.2
  have hconst :
      Filter.Tendsto (fun _ : ℕ => (a₀ : ℝ)) Filter.atTop (𝓝 (a₀ : ℝ)) :=
    tendsto_const_nhds
  have hsub := hlim.sub hconst
  simpa [SimpleCFConvergentLimit] using hsub

theorem simpleCFCoordinateBeta_mem_uIcc (a₀ : ℤ) (s : ℕ → positiveNat) (n : ℕ) :
    simpleCFCoordinateBeta a₀ s ∈
      Set.uIcc (simpleCFConvergent (positiveNatSeqPartials s) n : ℝ)
        (simpleCFConvergent (positiveNatSeqPartials s) (n + 1) : ℝ) :=
  simpleCFConvergent_limit_mem_uIcc (positiveNatSeqPartials_positive s)
    (simpleCFCoordinateBeta_convergentLimit a₀ s) n

theorem simpleCFCoordinateBeta_dist_le_of_mem_cyl
    (a₀ : ℤ) (s t : ℕ → positiveNat) (n : ℕ)
    (ht : t ∈ cyl (seqPrefix s (n + 1))) :
    dist (simpleCFCoordinateBeta a₀ t) (simpleCFCoordinateBeta a₀ s) ≤
      |(simpleCFConvergent (positiveNatSeqPartials s) (n + 1) : ℝ) -
        (simpleCFConvergent (positiveNatSeqPartials s) n : ℝ)| := by
  let a := positiveNatSeqPartials s
  let b := positiveNatSeqPartials t
  have hprefix :
      ∀ i : ℕ, i ≤ n + 1 → b i = a i :=
    positiveNatSeqPartials_eq_on_le_of_mem_cyl ht
  have hconv_n : simpleCFConvergent b n = simpleCFConvergent a n :=
    simpleCFConvergent_eq_of_eq_on_le hprefix (by omega)
  have hconv_succ :
      simpleCFConvergent b (n + 1) = simpleCFConvergent a (n + 1) :=
    simpleCFConvergent_eq_of_eq_on_le hprefix (by omega)
  have hs :=
    simpleCFCoordinateBeta_mem_uIcc a₀ s n
  have htmem :
      simpleCFCoordinateBeta a₀ t ∈
        Set.uIcc (simpleCFConvergent a n : ℝ)
          (simpleCFConvergent a (n + 1) : ℝ) := by
    have ht' := simpleCFCoordinateBeta_mem_uIcc a₀ t n
    simpa [a, b, hconv_n, hconv_succ] using ht'
  have hs' :
      simpleCFCoordinateBeta a₀ s ∈
        Set.uIcc (simpleCFConvergent a n : ℝ)
          (simpleCFConvergent a (n + 1) : ℝ) := by
    simpa [a] using hs
  simpa [abs_sub_comm] using dist_le_abs_sub_of_mem_uIcc htmem hs'

theorem simpleCFCoordinateBeta_continuous (a₀ : ℤ) :
    Continuous (fun s : ℕ → positiveNat => simpleCFCoordinateBeta a₀ s) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hbound_tendsto :
      Filter.Tendsto (fun n : ℕ => 2 / ((n + 1 : ℝ) ^ 2)) Filter.atTop (𝓝 0) :=
    summable_simpleCFConvergent_dist_bound.tendsto_atTop_zero
  have hlt_event :
      ∀ᶠ n : ℕ in Filter.atTop, 2 / ((n + 1 : ℝ) ^ 2) < ε :=
    hbound_tendsto.eventually (gt_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hlt_event with ⟨n, hn⟩
  have hcyl_mem :
      cyl (seqPrefix s (n + 1)) ∈ 𝓝 s :=
    (isOpen_cyl (seqPrefix s (n + 1))).mem_nhds (mem_cyl_seqPrefix s (n + 1))
  filter_upwards [hcyl_mem] with t ht
  have hdist_le :=
    simpleCFCoordinateBeta_dist_le_of_mem_cyl a₀ s t n ht
  have hstep_le :
      |(simpleCFConvergent (positiveNatSeqPartials s) (n + 1) : ℝ) -
        (simpleCFConvergent (positiveNatSeqPartials s) n : ℝ)| ≤
          2 / ((n + 1 : ℝ) ^ 2) := by
    have h :=
      simpleCFConvergent_dist_le_pseries_bound (positiveNatSeqPartials_positive s) n
    simpa [Real.dist_eq, abs_sub_comm] using h
  exact lt_of_le_of_lt (hdist_le.trans hstep_le) (hn n le_rfl)

theorem simpleCFCoordinateBeta_prod_continuous :
    Continuous (fun c : ℤ × (ℕ → positiveNat) => simpleCFCoordinateBeta c.1 c.2) := by
  rw [continuous_iff_continuousAt]
  intro c
  have htail :
      Filter.Tendsto
        (fun d : ℤ × (ℕ → positiveNat) => simpleCFCoordinateBeta c.1 d.2)
        (𝓝 c) (𝓝 (simpleCFCoordinateBeta c.1 c.2)) :=
    (simpleCFCoordinateBeta_continuous c.1).continuousAt.comp continuous_snd.continuousAt
  have hfst : ∀ᶠ d : ℤ × (ℕ → positiveNat) in 𝓝 c, d.1 = c.1 := by
    have hopen : IsOpen {d : ℤ × (ℕ → positiveNat) | d.1 = c.1} := by
      have hdisc : IsOpen ({c.1} : Set ℤ) := isOpen_discrete _
      simpa [Set.preimage] using hdisc.preimage continuous_fst
    exact hopen.mem_nhds rfl
  refine Filter.Tendsto.congr' ?_ htail
  filter_upwards [hfst] with d hd
  simp [hd]

/-- Reconstruct the irrational represented by continued-fraction coordinates. -/
noncomputable def simpleCFRealOfCoordinate
    (c : ℤ × (ℕ → positiveNat)) : {x : ℝ // Irrational x} :=
  ⟨(c.1 : ℝ) + simpleCFCoordinateBeta c.1 c.2,
    (simpleCFCoordinateBeta_spec c.1 c.2).2.2.1⟩

theorem simpleCFRealOfCoordinate_val_continuous :
    Continuous (fun c : ℤ × (ℕ → positiveNat) => (simpleCFRealOfCoordinate c).1) := by
  have hint :
      Continuous (fun c : ℤ × (ℕ → positiveNat) => (c.1 : ℝ)) :=
    (Int.cast_continuous (R := ℝ)).comp continuous_fst
  simp only [simpleCFRealOfCoordinate]
  exact hint.add simpleCFCoordinateBeta_prod_continuous

theorem simpleCFRealOfCoordinate_continuous :
    Continuous simpleCFRealOfCoordinate :=
  simpleCFRealOfCoordinate_val_continuous.subtype_mk _

theorem simpleCFRealOfCoordinate_expansionData
    (c : ℤ × (ℕ → positiveNat)) :
    SimpleCFExpansionData (simpleCFRealOfCoordinate c).1 c.1
      (positiveNatSeqPartials c.2) := by
  exact ⟨rfl, positiveNatSeqPartials_positive c.2,
    (simpleCFCoordinateBeta_spec c.1 c.2).2.2.2⟩

theorem simpleCFCoordinate_simpleCFRealOfCoordinate
    (c : ℤ × (ℕ → positiveNat)) :
    simpleCFCoordinate (simpleCFRealOfCoordinate c) = c := by
  rcases c with ⟨a₀, s⟩
  apply Prod.ext
  · have halgo :
        SimpleCFExpansionData (simpleCFRealOfCoordinate (a₀, s)).1
          (simpleCFIntegerPart (simpleCFRealOfCoordinate (a₀, s)).1)
          (simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1) :=
        simpleCFAlgorithmProducesExpansion_of_irrational
          (simpleCFRealOfCoordinate (a₀, s)).1 (simpleCFRealOfCoordinate (a₀, s)).2
    have htarget :
        SimpleCFExpansionData (simpleCFRealOfCoordinate (a₀, s)).1 a₀
          (positiveNatSeqPartials s) :=
      simpleCFRealOfCoordinate_expansionData (a₀, s)
    exact simpleCFExpansionData_integerPart_unique halgo htarget
  · funext n
    apply Subtype.ext
    have halgo :
        SimpleCFExpansionData (simpleCFRealOfCoordinate (a₀, s)).1
          (simpleCFIntegerPart (simpleCFRealOfCoordinate (a₀, s)).1)
          (simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1) :=
        simpleCFAlgorithmProducesExpansion_of_irrational
          (simpleCFRealOfCoordinate (a₀, s)).1 (simpleCFRealOfCoordinate (a₀, s)).2
    have htarget :
        SimpleCFExpansionData (simpleCFRealOfCoordinate (a₀, s)).1 a₀
          (positiveNatSeqPartials s) :=
      simpleCFRealOfCoordinate_expansionData (a₀, s)
    have hpartial :
        simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1 (n + 1) =
          positiveNatSeqPartials s (n + 1) :=
      simpleCFExpansionData_positivePartials_unique halgo htarget n
    have hposZ :
        (1 : ℤ) ≤
          simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1 (n + 1) :=
      simpleCFAlgorithmPartialsPositive_of_irrational
        (simpleCFRealOfCoordinate (a₀, s)).1 (simpleCFRealOfCoordinate (a₀, s)).2 n
    have hnonneg :
        0 ≤ simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1 (n + 1) :=
      le_trans (by norm_num) hposZ
    have hcast :
        (((Int.toNat
          (simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1
            (n + 1))) : ℕ) : ℤ) =
          simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1 (n + 1) :=
      Int.toNat_of_nonneg hnonneg
    have hnatCast :
        (((Int.toNat
          (simpleCFAlgorithmPartials (simpleCFRealOfCoordinate (a₀, s)).1
            (n + 1))) : ℕ) : ℤ) = ((s n : ℕ) : ℤ) := by
      simpa [positiveNatSeqPartials] using hcast.trans hpartial
    exact_mod_cast hnatCast

theorem simpleCFRealOfCoordinate_simpleCFCoordinate
    (x : {x : ℝ // Irrational x}) :
    simpleCFRealOfCoordinate (simpleCFCoordinate x) = x := by
  apply Subtype.ext
  have htail :
      positiveNatSeqPartials (simpleCFIrrationalTail x) =
        simpleCFAlgorithmPartials x.1 :=
    positiveNatSeqPartials_simpleCFIrrationalTail x
  have hchosen :
      Filter.Tendsto
        (fun n : ℕ =>
          (simpleCFIntegerPart x.1 : ℝ) +
            (simpleCFConvergent (positiveNatSeqPartials (simpleCFIrrationalTail x)) n : ℝ))
        Filter.atTop
        (𝓝 ((simpleCFRealOfCoordinate (simpleCFCoordinate x)).1)) := by
    simpa [simpleCFRealOfCoordinate, simpleCFCoordinate, simpleCFCoordinateBeta]
      using (simpleCFCoordinateBeta_spec (simpleCFIntegerPart x.1)
        (simpleCFIrrationalTail x)).2.2.2
  have halgo :
      Filter.Tendsto
        (fun n : ℕ =>
          (simpleCFIntegerPart x.1 : ℝ) +
            (simpleCFConvergent (positiveNatSeqPartials (simpleCFIrrationalTail x)) n : ℝ))
        Filter.atTop (𝓝 x.1) := by
    have hdata := simpleCFAlgorithmProducesExpansion_of_irrational x.1 x.2
    simpa [SimpleCFShiftedConvergentLimit, htail] using hdata.2.2
  exact tendsto_nhds_unique hchosen halgo

/-- The set-level continued-fraction coordinate equivalence supplied by the expansion theorem.
The later topological facts state the continuity/homeomorphism upgrade. -/
noncomputable def simpleCFCoordinateEquiv :
    {x : ℝ // Irrational x} ≃ ℤ × (ℕ → positiveNat) where
  toFun := simpleCFCoordinate
  invFun := simpleCFRealOfCoordinate
  left_inv := simpleCFRealOfCoordinate_simpleCFCoordinate
  right_inv := simpleCFCoordinate_simpleCFRealOfCoordinate

theorem simpleCFCoordinateEquiv_symm_continuous :
    Continuous simpleCFCoordinateEquiv.symm := by
  simpa [simpleCFCoordinateEquiv] using simpleCFRealOfCoordinate_continuous

noncomputable def simpleCFCoordinateHomeomorph :
    {x : ℝ // Irrational x} ≃ₜ ℤ × (ℕ → positiveNat) where
  toEquiv := simpleCFCoordinateEquiv
  continuous_toFun := simpleCFCoordinate_continuous
  continuous_invFun := simpleCFCoordinateEquiv_symm_continuous

/-- A finite partial-quotient cylinder in the irrational line: fix the integer
part `a₀` and a finite prefix of positive tail partial quotients. -/
def simpleCFPartialQuotientCylinder (a₀ : ℤ) (s : finseq positiveNat) :
    Set {x : ℝ // Irrational x} :=
  {x | (simpleCFCoordinate x).1 = a₀} ∩
    {x | (simpleCFCoordinate x).2 ∈ cyl s}

theorem mem_simpleCFPartialQuotientCylinder_iff
    (a₀ : ℤ) (s : finseq positiveNat) (x : {x : ℝ // Irrational x}) :
    x ∈ simpleCFPartialQuotientCylinder a₀ s ↔
      simpleCFIntegerPart x.1 = a₀ ∧
        ∀ i (hi : i < s.length), simpleCFIrrationalTail x i = s.get ⟨i, hi⟩ := by
  rfl

/-- Finite partial-quotient cylinders are clopen in the irrational line. -/
theorem isClopen_simpleCFPartialQuotientCylinder (a₀ : ℤ) (s : finseq positiveNat) :
    IsClopen (simpleCFPartialQuotientCylinder a₀ s) := by
  have hfst : IsClopen {x : {x : ℝ // Irrational x} | (simpleCFCoordinate x).1 = a₀} :=
    (isClopen_discrete ({a₀} : Set ℤ)).preimage simpleCFCoordinate_fst_continuous
  have hsnd : IsClopen
      {x : {x : ℝ // Irrational x} | (simpleCFCoordinate x).2 ∈ cyl s} :=
    (isClopen_cyl s).preimage simpleCFCoordinate_continuous.snd
  exact hfst.inter hsnd

/-- Finite partial-quotient cylinders form a topological basis for the irrational line. -/
theorem isTopologicalBasis_simpleCFPartialQuotientCylinder :
    IsTopologicalBasis {U : Set {x : ℝ // Irrational x} |
      ∃ a₀ : ℤ, ∃ s : finseq positiveNat, U = simpleCFPartialQuotientCylinder a₀ s} := by
  let H := simpleCFCoordinateHomeomorph
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨a₀, s, rfl⟩
    exact (isClopen_simpleCFPartialQuotientCylinder a₀ s).isOpen
  · intro x U hxU hU
    have hW : IsOpen (H '' U) := H.isOpenMap U hU
    let a₀ : ℤ := (H x).1
    let V : Set (ℕ → positiveNat) := {t | (a₀, t) ∈ H '' U}
    have hVopen : IsOpen V := hW.preimage (Continuous.prodMk_right a₀)
    have hxV : (H x).2 ∈ V := by
      exact ⟨x, hxU, by simp [a₀]⟩
    obtain ⟨s, hxs, hsV⟩ := exists_cyl_subset_of_mem_open (A := positiveNat) hxV hVopen
    refine ⟨simpleCFPartialQuotientCylinder a₀ s, ⟨a₀, s, rfl⟩, ?_, ?_⟩
    · change (simpleCFCoordinate x).1 = a₀ ∧ (simpleCFCoordinate x).2 ∈ cyl s
      exact ⟨by simp [a₀, H, simpleCFCoordinateHomeomorph, simpleCFCoordinateEquiv],
        by simpa [H, simpleCFCoordinateHomeomorph, simpleCFCoordinateEquiv] using hxs⟩
    · intro y hy
      have hycoord :
          (H y).1 = a₀ ∧ (H y).2 ∈ cyl s := by
        simpa [H, simpleCFCoordinateHomeomorph, simpleCFCoordinateEquiv, simpleCFPartialQuotientCylinder] using hy
      have htailV : (H y).2 ∈ V := hsV hycoord.2
      rcases htailV with ⟨z, hzU, hzEq⟩
      have hpair : (a₀, (H y).2) = H y := by
        ext <;> simp [hycoord.1]
      have hzy : H z = H y := hzEq.trans hpair
      have hyz : y = z := (H.injective hzy).symm
      simpa [hyz] using hzU

/-- Continued-fraction coordinates on the positive irrational half-line. The integer part is
nonnegative, so it is coded as a natural number. -/
noncomputable def simpleCFPositiveCoordinateEquiv :
    {x : ℝ // Irrational x ∧ 0 < x} ≃ ℕ × (ℕ → positiveNat) where
  toFun x :=
    (Int.toNat (simpleCFIntegerPart x.1), simpleCFIrrationalTail ⟨x.1, x.2.1⟩)
  invFun c :=
    ⟨(simpleCFRealOfCoordinate ((c.1 : ℤ), c.2)).1,
      ⟨(simpleCFRealOfCoordinate ((c.1 : ℤ), c.2)).2,
        by
          have hβ := simpleCFCoordinateBeta_spec (c.1 : ℤ) c.2
          have hnonneg : (0 : ℝ) ≤ (c.1 : ℤ) := by exact_mod_cast Nat.zero_le c.1
          simp [simpleCFRealOfCoordinate]
          exact add_pos_of_nonneg_of_pos hnonneg hβ.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    let y : {x : ℝ // Irrational x} := ⟨x.1, x.2.1⟩
    have hnonneg : 0 ≤ simpleCFIntegerPart x.1 := by
      simpa [simpleCFIntegerPart] using (Int.floor_nonneg.2 x.2.2.le)
    let a₀ : ℤ := ((Int.toNat (simpleCFIntegerPart x.1) : ℕ) : ℤ)
    have hcast :
        a₀ = simpleCFIntegerPart x.1 :=
      Int.toNat_of_nonneg hnonneg
    have hcoord :
        (a₀, simpleCFIrrationalTail y) = simpleCFCoordinate y := by
      apply Prod.ext
      · exact hcast
      · rfl
    have hreal :
        simpleCFRealOfCoordinate (a₀, simpleCFIrrationalTail y) = y := by
      rw [hcoord]
      exact simpleCFRealOfCoordinate_simpleCFCoordinate y
    exact congrArg (fun z : {x : ℝ // Irrational x} => z.1) hreal
  right_inv c := by
    cases c with
    | mk a s =>
        have hcoord := simpleCFCoordinate_simpleCFRealOfCoordinate ((a : ℤ), s)
        apply Prod.ext
        · have hfst := congrArg Prod.fst hcoord
          have hfst' :
              simpleCFIntegerPart (simpleCFRealOfCoordinate ((a : ℤ), s)).1 =
                (a : ℤ) := by
            simpa [simpleCFCoordinate] using hfst
          have hcast : Int.toNat (a : ℤ) = a :=
            Int.toNat_natCast a
          calc
            Int.toNat (simpleCFIntegerPart (simpleCFRealOfCoordinate ((a : ℤ), s)).1)
                = Int.toNat (a : ℤ) := by rw [hfst']
            _ = a := hcast
        · have hsnd := congrArg Prod.snd hcoord
          simpa [simpleCFCoordinate] using hsnd

theorem simpleCFPositiveCoordinateEquiv_continuous :
    Continuous (fun x : {x : ℝ // Irrational x ∧ 0 < x} =>
      simpleCFPositiveCoordinateEquiv x) := by
  let i : {x : ℝ // Irrational x ∧ 0 < x} → {x : ℝ // Irrational x} :=
    fun x => ⟨x.1, x.2.1⟩
  have hi : Continuous i :=
    continuous_subtype_val.subtype_mk _
  have hfst :
      Continuous (fun x : {x : ℝ // Irrational x ∧ 0 < x} =>
        Int.toNat (simpleCFIntegerPart x.1)) :=
    (continuous_of_discreteTopology (f := Int.toNat)).comp
      (simpleCFIntegerPart_irrational_continuous.comp hi)
  have hsnd :
      Continuous (fun x : {x : ℝ // Irrational x ∧ 0 < x} =>
        simpleCFIrrationalTail ⟨x.1, x.2.1⟩) :=
    simpleCFIrrationalTail_continuous.comp hi
  simpa [simpleCFPositiveCoordinateEquiv, i] using hfst.prodMk hsnd

theorem simpleCFPositiveCoordinateEquiv_symm_continuous :
    Continuous (fun c : ℕ × (ℕ → positiveNat) =>
      simpleCFPositiveCoordinateEquiv.symm c) := by
  let j : ℕ × (ℕ → positiveNat) → ℤ × (ℕ → positiveNat) :=
    fun c => ((c.1 : ℤ), c.2)
  have hj : Continuous j :=
    ((continuous_of_discreteTopology (f := fun n : ℕ => (n : ℤ))).comp continuous_fst).prodMk
      continuous_snd
  let f : ℕ × (ℕ → positiveNat) → {x : ℝ // Irrational x ∧ 0 < x} :=
    fun c =>
      ⟨(simpleCFRealOfCoordinate (j c)).1,
        ⟨(simpleCFRealOfCoordinate (j c)).2,
          by
            have hβ := simpleCFCoordinateBeta_spec (c.1 : ℤ) c.2
            have hnonneg : (0 : ℝ) ≤ (c.1 : ℤ) := by exact_mod_cast Nat.zero_le c.1
            simp [simpleCFRealOfCoordinate, j]
            exact add_pos_of_nonneg_of_pos hnonneg hβ.1⟩⟩
  have hf : Continuous f :=
    (simpleCFRealOfCoordinate_val_continuous.comp hj).subtype_mk _
  simpa [simpleCFPositiveCoordinateEquiv, f, j] using hf

noncomputable def simpleCFPositiveCoordinateHomeomorph :
    {x : ℝ // Irrational x ∧ 0 < x} ≃ₜ ℕ × (ℕ → positiveNat) where
  toEquiv := simpleCFPositiveCoordinateEquiv
  continuous_toFun := simpleCFPositiveCoordinateEquiv_continuous
  continuous_invFun := simpleCFPositiveCoordinateEquiv_symm_continuous

theorem positiveIrrationalContinuedFractionHomeomorphismFact :
    Nonempty ({x : ℝ // Irrational x ∧ 0 < x} ≃ₜ ℕ × (ℕ → positiveNat)) :=
  ⟨simpleCFPositiveCoordinateHomeomorph⟩

/-- In positive continued-fraction coordinates, first coordinate `0` is exactly
the unit interval `(0,1)`. This is the continued-fraction half of the
comparison-table row `(0,1) \setminus ℚ`. -/
theorem simpleCFPositiveCoordinateHomeomorph_fst_eq_zero_iff_lt_one
    (x : {x : ℝ // Irrational x ∧ 0 < x}) :
    (simpleCFPositiveCoordinateHomeomorph x).1 = 0 ↔ x.1 < 1 := by
  constructor
  · intro hzero
    have hnat : Int.toNat (simpleCFIntegerPart x.1) = 0 := by
      simpa [simpleCFPositiveCoordinateHomeomorph, simpleCFPositiveCoordinateEquiv]
        using hzero
    have hnonneg : 0 ≤ simpleCFIntegerPart x.1 := by
      simpa [simpleCFIntegerPart] using Int.floor_nonneg.mpr x.2.2.le
    have hfloor : simpleCFIntegerPart x.1 = 0 := by
      have hcast : (Int.toNat (simpleCFIntegerPart x.1) : ℤ) = (0 : ℤ) := by
        simpa using congrArg (fun n : ℕ => (n : ℤ)) hnat
      simpa [Int.toNat_of_nonneg hnonneg] using hcast
    have hxIoo := simpleCFIntegerPart_mem_Ioo ⟨x.1, x.2.1⟩
    rw [hfloor] at hxIoo
    simpa using hxIoo.2
  · intro hxlt
    have hfloor : simpleCFIntegerPart x.1 = 0 :=
      simpleCFIntegerPart_eq_of_mem_Ioo (a₀ := 0)
        ⟨by simpa using x.2.2, by simpa using hxlt⟩
    simp [simpleCFPositiveCoordinateHomeomorph, simpleCFPositiveCoordinateEquiv, hfloor]

/-- The positive irrational half-line is a Baire-space model: continued fractions give
the coordinate `a₀ ∈ ℕ` followed by positive tail partial quotients, and this countable
discrete product is coded as `ω^ω`. -/
noncomputable def positiveIrrationalBaireHomeomorph :
    {x : ℝ // Irrational x ∧ 0 < x} ≃ₜ baire_space :=
  simpleCFPositiveCoordinateHomeomorph.trans natPositiveNatSeqHomeomorphBaire

theorem positiveIrrationalBaireHomeomorphismFact :
    Nonempty ({x : ℝ // Irrational x ∧ 0 < x} ≃ₜ baire_space) :=
  ⟨positiveIrrationalBaireHomeomorph⟩

/-- The sign bit used in the comparison table for the whole irrational line. The
positive half is coded by `true`; the negative half is coded by `false`. -/
noncomputable def irrationalSign (x : {x : ℝ // Irrational x}) : Bool :=
  if 0 < x.1 then true else false

/-- The absolute value of an irrational real, viewed as a positive irrational. -/
def irrationalAbsPositive (x : {x : ℝ // Irrational x}) :
    {x : ℝ // Irrational x ∧ 0 < x} :=
  ⟨|x.1|,
    ⟨by
      by_cases hx : x.1 < 0
      · rw [abs_of_neg hx]
        exact x.2.neg
      · rw [abs_of_nonneg (le_of_not_gt hx)]
        exact x.2,
      abs_pos.mpr x.2.ne_zero⟩⟩

theorem irrationalAbsPositive_apply (x : {x : ℝ // Irrational x}) :
    (irrationalAbsPositive x).1 = |x.1| := rfl

theorem irrationalSign_eq_true_of_pos {x : {x : ℝ // Irrational x}} (hx : 0 < x.1) :
    irrationalSign x = true := by
  simp [irrationalSign, hx]

theorem irrationalSign_eq_false_of_neg {x : {x : ℝ // Irrational x}} (hx : x.1 < 0) :
    irrationalSign x = false := by
  have hnot : ¬ 0 < x.1 := not_lt_of_gt hx
  simp [irrationalSign, hnot]

theorem irrationalSign_continuous :
    Continuous irrationalSign := by
  rw [continuous_def]
  intro U hU
  by_cases ht : true ∈ U
  · by_cases hf : false ∈ U
    · have hUuniv : U = Set.univ := by
        ext b
        cases b <;> simp [ht, hf]
      rw [hUuniv]
      exact isOpen_univ
    · have hpre :
          irrationalSign ⁻¹' U = {x : {x : ℝ // Irrational x} | 0 < x.1} := by
        ext x
        by_cases hx : 0 < x.1
        · simp [irrationalSign, hx, ht]
        · simp [irrationalSign, hx, hf]
      rw [hpre]
      exact isOpen_Ioi.preimage continuous_subtype_val
  · by_cases hf : false ∈ U
    · have hpre :
          irrationalSign ⁻¹' U = {x : {x : ℝ // Irrational x} | x.1 < 0} := by
        ext x
        by_cases hxpos : 0 < x.1
        · have hxnotneg : ¬ x.1 < 0 := not_lt_of_gt hxpos
          simp [irrationalSign, hxpos, ht, hxnotneg]
        · have hxneg : x.1 < 0 :=
            lt_of_le_of_ne (le_of_not_gt hxpos) x.2.ne_zero
          simp [irrationalSign, hxpos, hf, hxneg]
      rw [hpre]
      exact isOpen_Iio.preimage continuous_subtype_val
    · have hUempty : U = ∅ := by
        ext b
        cases b <;> simp [ht, hf]
      rw [hUempty]
      exact isOpen_empty

theorem irrationalAbsPositive_continuous :
    Continuous irrationalAbsPositive := by
  exact ((continuous_abs.comp continuous_subtype_val).subtype_mk _)

/-- Rebuild an irrational real from a sign bit and a positive irrational absolute
value. -/
def signedIrrationalOfSignAbs
    (p : Bool × {x : ℝ // Irrational x ∧ 0 < x}) :
    {x : ℝ // Irrational x} :=
  ⟨(if p.1 then (1 : ℝ) else -1) * p.2.1,
    by
      by_cases hp : p.1
      · simpa [hp] using p.2.2.1
      · simpa [hp] using p.2.2.1.neg⟩

theorem signedIrrationalOfSignAbs_continuous :
    Continuous signedIrrationalOfSignAbs := by
  have hsign :
      Continuous (fun p : Bool × {x : ℝ // Irrational x ∧ 0 < x} =>
        if p.1 then (1 : ℝ) else -1) :=
    (continuous_of_discreteTopology
      (f := fun b : Bool => if b then (1 : ℝ) else -1)).comp continuous_fst
  have hval :
      Continuous (fun p : Bool × {x : ℝ // Irrational x ∧ 0 < x} => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact (hsign.mul hval).subtype_mk _

/-- The whole irrational line splits into a sign bit and the positive irrational
half-line by sending `x` to `(sign x, |x|)`. -/
noncomputable def irrationalSignAbsEquiv :
    {x : ℝ // Irrational x} ≃ Bool × {x : ℝ // Irrational x ∧ 0 < x} where
  toFun x := (irrationalSign x, irrationalAbsPositive x)
  invFun := signedIrrationalOfSignAbs
  left_inv x := by
    apply Subtype.ext
    by_cases hx : 0 < x.1
    · simp [signedIrrationalOfSignAbs, irrationalSign, irrationalAbsPositive, hx,
        abs_of_pos hx]
    · have hxlt : x.1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hx) x.2.ne_zero
      simp [signedIrrationalOfSignAbs, irrationalSign, irrationalAbsPositive, hx,
        abs_of_neg hxlt]
  right_inv p := by
    rcases p with ⟨b, y⟩
    apply Prod.ext
    · cases b
      · have hnot : ¬ 0 < -y.1 := by linarith [y.2.2]
        simp [signedIrrationalOfSignAbs, irrationalSign, hnot]
      · simp [signedIrrationalOfSignAbs, irrationalSign, y.2.2]
    · cases b
      · apply Subtype.ext
        have hyneg : -y.1 < 0 := by linarith [y.2.2]
        simp [signedIrrationalOfSignAbs, irrationalAbsPositive, abs_of_neg hyneg]
      · apply Subtype.ext
        simp [signedIrrationalOfSignAbs, irrationalAbsPositive, abs_of_pos y.2.2]

theorem irrationalSignAbsEquiv_apply (x : {x : ℝ // Irrational x}) :
    irrationalSignAbsEquiv x = (irrationalSign x, irrationalAbsPositive x) := rfl

theorem irrationalSignAbsEquiv_symm_apply
    (p : Bool × {x : ℝ // Irrational x ∧ 0 < x}) :
    irrationalSignAbsEquiv.symm p = signedIrrationalOfSignAbs p := rfl

theorem irrationalSignAbsEquiv_continuous :
    Continuous (fun x : {x : ℝ // Irrational x} => irrationalSignAbsEquiv x) := by
  exact irrationalSign_continuous.prodMk irrationalAbsPositive_continuous

theorem irrationalSignAbsEquiv_symm_continuous :
    Continuous (fun p : Bool × {x : ℝ // Irrational x ∧ 0 < x} =>
      irrationalSignAbsEquiv.symm p) := by
  exact signedIrrationalOfSignAbs_continuous

/-- Homeomorphism form of the comparison-table row
`\mathbb R \setminus \mathbb Q =` sign times the positive irrational model. -/
noncomputable def irrationalSignAbsHomeomorph :
    {x : ℝ // Irrational x} ≃ₜ Bool × {x : ℝ // Irrational x ∧ 0 < x} where
  toEquiv := irrationalSignAbsEquiv
  continuous_toFun := irrationalSignAbsEquiv_continuous
  continuous_invFun := irrationalSignAbsEquiv_symm_continuous

theorem irrationalSignAbsHomeomorph_apply (x : {x : ℝ // Irrational x}) :
    irrationalSignAbsHomeomorph x = (irrationalSign x, irrationalAbsPositive x) :=
  rfl

/-- On the `a₀`-th irrational interval, continued-fraction coordinates reduce to the
positive tail. This is the set-level core of the book's fractional-part branch. -/
noncomputable def simpleCFFractionalCoordinateEquiv (a₀ : ℤ) :
    {x : ℝ // Irrational x ∧ (a₀ : ℝ) < x ∧ x < (a₀ : ℝ) + 1} ≃
      (ℕ → positiveNat) where
  toFun x := (simpleCFCoordinate ⟨x.1, x.2.1⟩).2
  invFun s :=
    ⟨(simpleCFRealOfCoordinate (a₀, s)).1,
      ⟨(simpleCFRealOfCoordinate (a₀, s)).2,
        by
          have hβ := simpleCFCoordinateBeta_spec a₀ s
          constructor <;> simp [simpleCFRealOfCoordinate] <;> linarith⟩⟩
  left_inv x := by
    apply Subtype.ext
    let y : {x : ℝ // Irrational x} := ⟨x.1, x.2.1⟩
    have hfloor : simpleCFIntegerPart x.1 = a₀ := by
      rw [simpleCFIntegerPart, Int.floor_eq_iff]
      constructor <;> linarith [x.2.2.1, x.2.2.2]
    have hcoord :
        simpleCFCoordinate y = (a₀, (simpleCFCoordinate y).2) := by
      apply Prod.ext
      · exact hfloor
      · rfl
    have hreal :
        simpleCFRealOfCoordinate (a₀, (simpleCFCoordinate y).2) = y := by
      rw [← hcoord]
      exact simpleCFRealOfCoordinate_simpleCFCoordinate y
    exact congrArg (fun z : {x : ℝ // Irrational x} => z.1) hreal
  right_inv s := by
    have h :=
      congrArg Prod.snd (simpleCFCoordinate_simpleCFRealOfCoordinate (a₀, s))
    simpa [simpleCFCoordinate] using h

theorem simpleCFRealOfCoordinate_fixedInt_continuous (a₀ : ℤ) :
    Continuous (fun s : ℕ → positiveNat => (simpleCFRealOfCoordinate (a₀, s)).1) := by
  simp only [simpleCFRealOfCoordinate]
  exact continuous_const.add (simpleCFCoordinateBeta_continuous a₀)

theorem simpleCFFractionalCoordinateEquiv_symm_continuous (a₀ : ℤ) :
    Continuous (fun s : ℕ → positiveNat =>
      (simpleCFFractionalCoordinateEquiv a₀).symm s) := by
  let f :
      (ℕ → positiveNat) →
        {x : ℝ // Irrational x ∧ (a₀ : ℝ) < x ∧ x < (a₀ : ℝ) + 1} :=
    fun s =>
      ⟨(simpleCFRealOfCoordinate (a₀, s)).1,
        ⟨(simpleCFRealOfCoordinate (a₀, s)).2,
          by
            have hβ := simpleCFCoordinateBeta_spec a₀ s
            constructor <;> simp [simpleCFRealOfCoordinate] <;> linarith⟩⟩
  have hf : Continuous f :=
    (simpleCFRealOfCoordinate_fixedInt_continuous a₀).subtype_mk _
  simpa [simpleCFFractionalCoordinateEquiv, f] using hf

theorem simpleCFFractionalCoordinateEquiv_continuous (a₀ : ℤ) :
    Continuous (fun x :
      {x : ℝ // Irrational x ∧ (a₀ : ℝ) < x ∧ x < (a₀ : ℝ) + 1} =>
        simpleCFFractionalCoordinateEquiv a₀ x) := by
  let i :
      {x : ℝ // Irrational x ∧ (a₀ : ℝ) < x ∧ x < (a₀ : ℝ) + 1} →
        {x : ℝ // Irrational x} :=
    fun x => ⟨x.1, x.2.1⟩
  have hi : Continuous i :=
    continuous_subtype_val.subtype_mk _
  have hcoord : Continuous (fun x => (simpleCFCoordinate (i x)).2) :=
    (simpleCFCoordinate_continuous.comp hi).snd
  simpa [simpleCFFractionalCoordinateEquiv, i] using hcoord

noncomputable def simpleCFFractionalCoordinateHomeomorph (a₀ : ℤ) :
    {x : ℝ // Irrational x ∧ (a₀ : ℝ) < x ∧ x < (a₀ : ℝ) + 1} ≃ₜ
      (ℕ → positiveNat) where
  toEquiv := simpleCFFractionalCoordinateEquiv a₀
  continuous_toFun := simpleCFFractionalCoordinateEquiv_continuous a₀
  continuous_invFun := simpleCFFractionalCoordinateEquiv_symm_continuous a₀

/-- The fractional branch over `(0,1)`, stated with the exact domain used by the Gauss map. -/
noncomputable def simpleCFUnitIntervalCoordinateEquiv :
    {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ (ℕ → positiveNat) where
  toFun x := simpleCFIrrationalTail ⟨x.1, x.2.1⟩
  invFun s :=
    ⟨(simpleCFRealOfCoordinate (0, s)).1,
      ⟨(simpleCFRealOfCoordinate (0, s)).2,
        by
          have hβ := simpleCFCoordinateBeta_spec 0 s
          constructor <;> simp [simpleCFRealOfCoordinate] <;> linarith⟩⟩
  left_inv x := by
    apply Subtype.ext
    let y : {x : ℝ // Irrational x} := ⟨x.1, x.2.1⟩
    have hfloor : simpleCFIntegerPart x.1 = 0 := by
      rw [simpleCFIntegerPart, Int.floor_eq_iff]
      exact ⟨by simpa using le_of_lt x.2.2.1, by simpa using x.2.2.2⟩
    have hcoord :
        simpleCFCoordinate y = (0, simpleCFIrrationalTail y) := by
      apply Prod.ext
      · exact hfloor
      · rfl
    have hreal :
        simpleCFRealOfCoordinate (0, simpleCFIrrationalTail y) = y := by
      rw [← hcoord]
      exact simpleCFRealOfCoordinate_simpleCFCoordinate y
    exact congrArg (fun z : {x : ℝ // Irrational x} => z.1) hreal
  right_inv s := by
    have h :=
      congrArg Prod.snd (simpleCFCoordinate_simpleCFRealOfCoordinate (0, s))
    simpa [simpleCFCoordinate] using h

theorem simpleCFUnitIntervalCoordinateEquiv_continuous :
    Continuous (fun x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} =>
      simpleCFUnitIntervalCoordinateEquiv x) := by
  let i : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} → {x : ℝ // Irrational x} :=
    fun x => ⟨x.1, x.2.1⟩
  have hi : Continuous i :=
    continuous_subtype_val.subtype_mk _
  simpa [simpleCFUnitIntervalCoordinateEquiv, i, Function.comp_def] using
    simpleCFIrrationalTail_continuous.comp hi

theorem simpleCFUnitIntervalCoordinateEquiv_symm_continuous :
    Continuous (fun s : ℕ → positiveNat => simpleCFUnitIntervalCoordinateEquiv.symm s) := by
  let f :
      (ℕ → positiveNat) →
        {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} :=
    fun s =>
      ⟨(simpleCFRealOfCoordinate (0, s)).1,
        ⟨(simpleCFRealOfCoordinate (0, s)).2,
          by
            have hβ := simpleCFCoordinateBeta_spec 0 s
            constructor <;> simp [simpleCFRealOfCoordinate] <;> linarith⟩⟩
  have hf : Continuous f :=
    (simpleCFRealOfCoordinate_fixedInt_continuous 0).subtype_mk _
  simpa [simpleCFUnitIntervalCoordinateEquiv, f] using hf

noncomputable def simpleCFUnitIntervalCoordinateHomeomorph :
    {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ₜ (ℕ → positiveNat) where
  toEquiv := simpleCFUnitIntervalCoordinateEquiv
  continuous_toFun := simpleCFUnitIntervalCoordinateEquiv_continuous
  continuous_invFun := simpleCFUnitIntervalCoordinateEquiv_symm_continuous

/-- The left shift on Baire space. -/
def baireShift (g : baire_space) : baire_space :=
  fun n => g (n + 1)

theorem positiveNatSeqHomeomorphBaire_shift (s : ℕ → positiveNat) :
    positiveNatSeqHomeomorphBaire (shiftPositiveNat s) =
      baireShift (positiveNatSeqHomeomorphBaire s) := by
  rfl

/-- The `(0,1) \setminus \mathbb{Q}` row in the continued-fraction comparison table:
the `a₀ = 0` continued-fraction coordinates identify the unit-interval irrationals
with Baire space. -/
noncomputable def simpleCFUnitIntervalBaireHomeomorph :
    {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ₜ baire_space :=
  simpleCFUnitIntervalCoordinateHomeomorph.trans positiveNatSeqHomeomorphBaire

theorem unitIntervalIrrationalsBaireHomeomorphismFact :
    Nonempty ({x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ₜ baire_space) :=
  ⟨simpleCFUnitIntervalBaireHomeomorph⟩

/-- Reassociate the positive-irrational subtype cut out by `< 1` with the
book-facing subtype of irrational points in `(0,1)`. -/
noncomputable def positiveIrrationalLtOneHomeomorphUnitInterval :
    {x : {x : ℝ // Irrational x ∧ 0 < x} // x.1 < 1} ≃ₜ
      {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} where
  toFun x := ⟨x.1.1, ⟨x.1.2.1, x.1.2.2, by simpa using x.2⟩⟩
  invFun x := ⟨⟨x.1, ⟨x.2.1, x.2.2.1⟩⟩, by simpa using x.2.2.2⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl
  continuous_toFun := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hbase :
        Continuous (fun x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} =>
          (⟨x.1, ⟨x.2.1, x.2.2.1⟩⟩ : {x : ℝ // Irrational x ∧ 0 < x})) :=
      continuous_subtype_val.subtype_mk _
    exact hbase.subtype_mk _

/-- The continued-fraction coordinate homeomorphism from the book. -/
theorem continuedFractionCoordinateHomeomorphismFact :
    Nonempty ({x : ℝ // Irrational x} ≃ₜ (ℤ × (ℕ → positiveNat))) :=
  ⟨simpleCFCoordinateHomeomorph⟩

/-- The induced homeomorphism between the irrationals and Baire space. -/
theorem continuedFractionBaireHomeomorphismFact :
    Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) := by
  rcases continuedFractionCoordinateHomeomorphismFact with ⟨θ⟩
  exact ⟨θ.trans intPositiveNatSeqHomeomorphBaire⟩

/-- The continued-fraction coordinates give the direct Polish-space proof for the irrational
line mentioned in the book. -/
theorem irrationals_polish_via_continuedFractions :
    PolishSpace {x : ℝ // Irrational x} := by
  have : PolishSpace baire_space := baire_space_polish
  rcases continuedFractionBaireHomeomorphismFact with ⟨θ⟩
  exact θ.isClosedEmbedding.polishSpace

/-- The coordinate homeomorphism implies the Baire-space homeomorphism by the explicit coding
used in the book. -/
theorem continuedFractionBaireHomeomorphismFact_of_coordinate
    (h : Nonempty ({x : ℝ // Irrational x} ≃ₜ (ℤ × (ℕ → positiveNat)))) :
    Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) := by
  rcases h with ⟨θ⟩
  exact ⟨θ.trans intPositiveNatSeqHomeomorphBaire⟩

/-- The fixed integer cell of irrational reals used for the book's
`\theta_{a₀}` coordinate branch. -/
abbrev simpleCFFractionalInterval (a₀ : ℤ) : Type :=
  {x : ℝ // Irrational x ∧ (a₀ : ℝ) < x ∧ x < (a₀ : ℝ) + 1}

/-- The fixed-integer-cell fractional-part branch of the continued-fraction coordinate
homeomorphism. -/
theorem fractionalPartContinuedFractionHomeomorphismFact (a₀ : ℤ) :
    Nonempty ({x : ℝ // Irrational x ∧ (a₀ : ℝ) < x ∧ x < (a₀ : ℝ) + 1} ≃ₜ
      (ℕ → positiveNat)) :=
  ⟨simpleCFFractionalCoordinateHomeomorph a₀⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: statement
  kind: fact
  title: Continued-fraction coordinate homeomorphism
-/
/-- Book-facing package for the global continued-fraction coordinate map, its
Baire-space coding, and the fixed-integer-cell fractional coordinate maps. -/
theorem continuedFractionCoordinateModelsFact :
    Nonempty ({x : ℝ // Irrational x} ≃ₜ (ℤ × (ℕ → positiveNat))) ∧
      Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) ∧
      ∀ a₀ : ℤ, Nonempty (simpleCFFractionalInterval a₀ ≃ₜ (ℕ → positiveNat)) :=
  ⟨continuedFractionCoordinateHomeomorphismFact,
    continuedFractionBaireHomeomorphismFact,
    fractionalPartContinuedFractionHomeomorphismFact⟩

/-- The continued-fraction cylinder inside the fixed integer cell `I_{a₀}`. This is
`\theta_{a₀}^{-1}(\cyl{s})` in the book. -/
def simpleCFFractionalCylinder (a₀ : ℤ) (s : finseq positiveNat) :
    Set (simpleCFFractionalInterval a₀) :=
  (simpleCFFractionalCoordinateHomeomorph a₀) ⁻¹' cyl s

theorem mem_simpleCFFractionalCylinder_iff
    (a₀ : ℤ) (s : finseq positiveNat) (x : simpleCFFractionalInterval a₀) :
    x ∈ simpleCFFractionalCylinder a₀ s ↔
      ∀ i (hi : i < s.length),
        simpleCFIrrationalTail ⟨x.1, x.2.1⟩ i = s.get ⟨i, hi⟩ := by
  rfl

theorem isClopen_simpleCFFractionalCylinder (a₀ : ℤ) (s : finseq positiveNat) :
    IsClopen (simpleCFFractionalCylinder a₀ s) := by
  exact (isClopen_cyl s).preimage (simpleCFFractionalCoordinateHomeomorph a₀).continuous

/-- Fixed-cell continued-fraction cylinders split into their immediate
positive-partial-quotient child cylinders. -/
theorem simpleCFFractionalCylinder_eq_iUnion_immediate_subcylinders
    (a₀ : ℤ) (s : finseq positiveNat) :
    simpleCFFractionalCylinder a₀ s =
      ⋃ k : positiveNat, simpleCFFractionalCylinder a₀ (concat s [k]) := by
  ext x
  simp only [simpleCFFractionalCylinder, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · intro hx
    refine ⟨(simpleCFFractionalCoordinateHomeomorph a₀ x) s.length, ?_⟩
    exact (mem_cyl_concat_iff
      (s := s) (t := [(simpleCFFractionalCoordinateHomeomorph a₀ x) s.length])).2
        ⟨hx, by simp⟩
  · rintro ⟨k, hxk⟩
    exact cyl_concat_subset s [k] hxk

/-- Distinct immediate positive-partial-quotient child cylinders in a fixed
continued-fraction cell are disjoint. -/
theorem disjoint_simpleCFFractional_immediate_subcylinders
    (a₀ : ℤ) (s : finseq positiveNat) {m n : positiveNat} (hmn : m ≠ n) :
    Disjoint (simpleCFFractionalCylinder a₀ (concat s [m]))
      (simpleCFFractionalCylinder a₀ (concat s [n])) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  change (simpleCFFractionalCoordinateHomeomorph a₀ x) ∈ cyl (concat s [m]) at hxm
  change (simpleCFFractionalCoordinateHomeomorph a₀ x) ∈ cyl (concat s [n]) at hxn
  have htail_m := (mem_cyl_concat_iff
    (s := s) (t := [m]) (x := simpleCFFractionalCoordinateHomeomorph a₀ x)).1 hxm
  have htail_n := (mem_cyl_concat_iff
    (s := s) (t := [n]) (x := simpleCFFractionalCoordinateHomeomorph a₀ x)).1 hxn
  have hm : simpleCFFractionalCoordinateHomeomorph a₀ x s.length = m := by
    simpa using (prefixOfSeq_singleton.1 htail_m.2)
  have hn : simpleCFFractionalCoordinateHomeomorph a₀ x s.length = n := by
    simpa using (prefixOfSeq_singleton.1 htail_n.2)
  exact hmn (hm.symm.trans hn)

/-- Book notation `\Phi_{a₀}(A)`: a prefix up-set codes the union of the corresponding
continued-fraction cylinders in `I_{a₀}`. -/
def simpleCFFractionalCylinderCode (a₀ : ℤ) (A : Set (finseq positiveNat)) :
    Set (simpleCFFractionalInterval a₀) :=
  ⋃ s : {s : finseq positiveNat // s ∈ A}, simpleCFFractionalCylinder a₀ s.1

/-- Book notation `\Psi_{a₀}(V)`: finite continued-fraction prefixes whose cylinders
are contained in `V`. -/
def simpleCFFractionalOpenCylinderCode (a₀ : ℤ)
    (V : Set (simpleCFFractionalInterval a₀)) : Set (finseq positiveNat) :=
  {s | simpleCFFractionalCylinder a₀ s ⊆ V}

theorem mem_simpleCFFractionalCylinderCode {a₀ : ℤ} {A : Set (finseq positiveNat)}
    {x : simpleCFFractionalInterval a₀} :
    x ∈ simpleCFFractionalCylinderCode a₀ A ↔
      ∃ s : finseq positiveNat, s ∈ A ∧ x ∈ simpleCFFractionalCylinder a₀ s := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hxs⟩
    exact ⟨s.1, s.2, hxs⟩
  · rintro ⟨s, hsA, hxs⟩
    exact Set.mem_iUnion.2 ⟨⟨s, hsA⟩, hxs⟩

/-- Fixed-cell version of the cylinder-code Galois connection from the previous chapter,
transported through continued-fraction coordinates. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: statement
  kind: remark
  title: Cylinder codes
-/
theorem simpleCFFractionalCylinderCode_subset_iff_subset_openCylinderCode
    {a₀ : ℤ} {A : Set (finseq positiveNat)}
    {V : Set (simpleCFFractionalInterval a₀)} :
    simpleCFFractionalCylinderCode a₀ A ⊆ V ↔
      A ⊆ simpleCFFractionalOpenCylinderCode a₀ V := by
  constructor
  · intro h s hsA x hxs
    exact h (mem_simpleCFFractionalCylinderCode.2 ⟨s, hsA, hxs⟩)
  · intro h x hx
    rcases mem_simpleCFFractionalCylinderCode.1 hx with ⟨s, hsA, hxs⟩
    exact h hsA hxs

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The \termuse{Gauss map} $T$ on $\SetDifference{(0, 1)}{\QQ}$ is the left shift in continued-fraction coordinates,
    $$[0; a_1, a_2, a_3, \ldots] \longmapsto [0; a_2, a_3, \ldots],$$
-/
noncomputable def gaussMap (x : ℝ) : ℝ :=
  Int.fract x⁻¹

/-- On the open unit interval, the first continued-fraction remainder is the Gauss map. -/
theorem simpleCFFractionalRemainder_gaussMap
    (x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) (n : ℕ) :
    simpleCFFractionalRemainder (gaussMap x.1) n =
      simpleCFFractionalRemainder x.1 (n + 1) := by
  induction n with
  | zero =>
      simp [gaussMap, simpleCFFractionalRemainder,
        Int.fract_eq_self.2 ⟨x.2.2.1.le, x.2.2.2⟩]
  | succ n ih =>
      simp [simpleCFFractionalRemainder, ih]

theorem gaussMap_irrational_unitInterval
    (x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) :
    Irrational (gaussMap x.1) ∧ 0 < gaussMap x.1 ∧ gaussMap x.1 < 1 := by
  have h := simpleCFFractionalRemainder_irrational_unitInterval x.1 x.2.1 1
  simpa [gaussMap, simpleCFFractionalRemainder,
    Int.fract_eq_self.2 ⟨x.2.2.1.le, x.2.2.2⟩] using h

theorem simpleCFAlgorithmPartials_gaussMap
    (x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) (n : ℕ) :
    simpleCFAlgorithmPartials (gaussMap x.1) (n + 1) =
      simpleCFAlgorithmPartials x.1 (n + 2) := by
  simp [simpleCFAlgorithmPartials, simpleCFFractionalRemainder_gaussMap x n]

theorem simpleCFIrrationalTail_gaussMap
    (x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) :
    simpleCFIrrationalTail ⟨gaussMap x.1, (gaussMap_irrational_unitInterval x).1⟩ =
      shiftPositiveNat (simpleCFIrrationalTail ⟨x.1, x.2.1⟩) := by
  funext n
  apply Subtype.ext
  exact congrArg Int.toNat (simpleCFAlgorithmPartials_gaussMap x n)

/-- Set-level Gauss-map shift correspondence for the explicit fractional coordinate
equivalence. -/
theorem simpleCFUnitIntervalCoordinateEquiv_gaussMap_shift
    (x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) :
    ∃ hx : Irrational (gaussMap x.1) ∧ 0 < gaussMap x.1 ∧ gaussMap x.1 < 1,
      simpleCFUnitIntervalCoordinateEquiv ⟨gaussMap x.1, hx⟩ =
        shiftPositiveNat (simpleCFUnitIntervalCoordinateEquiv x) := by
  refine ⟨gaussMap_irrational_unitInterval x, ?_⟩
  exact simpleCFIrrationalTail_gaussMap x

/-- Homeomorphism-coordinate form of the Gauss-map left-shift rule. -/
theorem simpleCFUnitIntervalCoordinateHomeomorph_gaussMap_shift
    (x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) :
    ∃ hx : Irrational (gaussMap x.1) ∧ 0 < gaussMap x.1 ∧ gaussMap x.1 < 1,
      simpleCFUnitIntervalCoordinateHomeomorph ⟨gaussMap x.1, hx⟩ =
        shiftPositiveNat (simpleCFUnitIntervalCoordinateHomeomorph x) := by
  rcases simpleCFUnitIntervalCoordinateEquiv_gaussMap_shift x with ⟨hx, hshift⟩
  exact ⟨hx, by simpa [simpleCFUnitIntervalCoordinateHomeomorph] using hshift⟩

/-- Baire-coordinate form of the Gauss-map left-shift rule on
`(0,1) \setminus \mathbb{Q}`. -/
theorem simpleCFUnitIntervalBaireHomeomorph_gaussMap_shift
    (x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) :
    ∃ hx : Irrational (gaussMap x.1) ∧ 0 < gaussMap x.1 ∧ gaussMap x.1 < 1,
      simpleCFUnitIntervalBaireHomeomorph ⟨gaussMap x.1, hx⟩ =
        baireShift (simpleCFUnitIntervalBaireHomeomorph x) := by
  rcases simpleCFUnitIntervalCoordinateHomeomorph_gaussMap_shift x with ⟨hx, hshift⟩
  refine ⟨hx, ?_⟩
  calc
    simpleCFUnitIntervalBaireHomeomorph ⟨gaussMap x.1, hx⟩
        = positiveNatSeqHomeomorphBaire
            (simpleCFUnitIntervalCoordinateHomeomorph ⟨gaussMap x.1, hx⟩) := rfl
    _ = positiveNatSeqHomeomorphBaire
            (shiftPositiveNat (simpleCFUnitIntervalCoordinateHomeomorph x)) := by
          rw [hshift]
    _ = baireShift
            (positiveNatSeqHomeomorphBaire (simpleCFUnitIntervalCoordinateHomeomorph x)) :=
          positiveNatSeqHomeomorphBaire_shift (simpleCFUnitIntervalCoordinateHomeomorph x)
    _ = baireShift (simpleCFUnitIntervalBaireHomeomorph x) := rfl

/-- Shift correspondence for the Gauss map under continued-fraction coordinates. -/
theorem gaussMapShiftCorrespondenceFact :
  ∃ θ : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ₜ (ℕ → positiveNat),
    ∀ x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1},
      ∃ hx : Irrational (gaussMap x.1) ∧ 0 < gaussMap x.1 ∧ gaussMap x.1 < 1,
        θ ⟨gaussMap x.1, hx⟩ = shiftPositiveNat (θ x) := by
  refine ⟨simpleCFUnitIntervalCoordinateHomeomorph, ?_⟩
  intro x
  rcases simpleCFUnitIntervalCoordinateEquiv_gaussMap_shift x with ⟨hx, hshift⟩
  exact ⟨hx, by
    simpa [simpleCFUnitIntervalCoordinateHomeomorph] using hshift⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \emph{Existence.} Set $a_0 := \lfloor \alpha \rfloor$ and $\alpha_0 := \{\alpha\}$, and for $n \ge 0$ define $a_{n+1}
    := \lfloor 1/\alpha_n \rfloor$ and $\alpha_{n+1} := \{1/\alpha_n\}$. The fractional part of any irrational is itself
    irrational and lies in $(0, 1)$, so $\alpha_0 \in \SetDifference{(0, 1)}{\QQ}$; inductively, if $\alpha_n \in
    \SetDifference{(0, 1)}{\QQ}$ then $1/\alpha_n$ is irrational and greater than $1$, giving $a_{n+1} \in
    \RestrictedSet{\NN}{\ge 1}$ and
    $\alpha_{n+1} \in \SetDifference{(0, 1)}{\QQ}$. Define $p_n, q_n$ by the seed values $(p_0, q_0) := (1, 0)$ and $(p_1,
    q_1) := (0, 1)$ and the recurrence
    \begin{equation*}
    \begin{aligned}
    p_{n+1} &\;:=\; a_n p_n + p_{n-1}, \\
    q_{n+1} &\;:=\; a_n q_n + q_{n-1}
    \end{aligned}
    \quad (n \ge 1). \tag{$*$}
    \end{equation*}
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For any positive real $x$ and $n \ge 0$,
    \begin{equation*}
    \relax[0; a_1, \ldots, a_n, x] \;=\; \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}. \tag{i}
    \end{equation*}
    \emph{Base $n = 0$:} $[0; x] = 1/x = (x \cdot p_1 + p_0)/(x \cdot q_1 + q_0)$, from the seed values.
    \emph{Inductive step at $n \ge 1$:}
    $$\begin{aligned}
    \relax[0; a_1, \ldots, a_n, x]
    &\;=\; [0; a_1, \ldots, a_{n-1}, a_n + 1/x] \\
    &\;\overset{\text{(i)}}{=}\; \frac{(a_n + 1/x) p_n + p_{n-1}}{(a_n + 1/x) q_n + q_{n-1}} \\
    &\;=\; \frac{x(a_n p_n + p_{n-1}) + p_n}{x(a_n q_n + q_{n-1}) + q_n} \\
    &\;\overset{(*)}{=}\; \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}.
    \end{aligned}$$
    Setting $x = a_n$ in (i) at level $n - 1$ and applying $(*)$, for $n \ge 1$:
    $$[0; a_1, \ldots, a_n] \;\overset{\text{(i)}}{=}\; \frac{a_n p_n + p_{n-1}}{a_n q_n + q_{n-1}}
    \;\overset{(*)}{=}\; \frac{p_{n+1}}{q_{n+1}}.$$
    We will also need:
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    $$\begin{aligned}
    \alpha_0
    &\;=\; \frac{p_n + \alpha_{n-1} p_{n-1}}{q_n + \alpha_{n-1} q_{n-1}} \\
    &\;=\; \frac{(a_n + \alpha_n) p_n + p_{n-1}}{(a_n + \alpha_n) q_n + q_{n-1}} \\
    &\;\overset{(*)}{=}\; \frac{p_{n+1} + \alpha_n p_n}{q_{n+1} + \alpha_n q_n}.
    \end{aligned}$$
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Since each $a_n \ge 1$ for $n \ge 1$, $(*)$ gives $q_{n+1} \ge q_n + q_{n-1}$ for $n \ge 1$, with $q_1 = 1$ and $q_2 \ge
    1$, so $q_n$ grows at least at the Fibonacci rate; in particular $q_{n+1} \to \infty$ and
    $p_{n+1}/q_{n+1} \to \alpha_0$. Hence $\alpha = a_0 + \alpha_0 = [a_0; a_1, a_2, \ldots]$.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    The expansion theorem makes $\theta$ and every $\theta_{a_0}$ bijective.
    The integer-part component $\alpha \mapsto a_0$ is locally constant on the clopen partition
    $$
    \SetDifference{\R}{\QQ}
    =
    \InternalDisjointUnion_{n \in \ZZ} (\SetDifference{(n, n+1)}{\QQ}).
    $$
    It has value $n$ on the $n$-th piece, hence is continuous to $\ZZ$ with the
    discrete topology.
    To compute a basic cylinder, fix $a_1, \ldots, a_n$ and let the remaining tail vary. Formula (i) gives, for the next
    complete quotient $x \in \SetDifference{(1,\infty)}{\QQ}$,
    $$\alpha
    \;=\;
    a_0 + \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}.$$
    The derivative of this fractional-linear function has the sign of
    $$p_{n+1} q_n - p_n q_{n+1} = (-1)^{n+1},$$
    by (ii), so it is decreasing when $n$ is even and increasing when $n$ is odd. As $x$ ranges over
    $\SetDifference{(1,\infty)}{\QQ}$, the two endpoint limits are obtained at $x \to \infty$ and $x \to 1^+$, giving
    $p_{n+1}/q_{n+1}$ and
    $(p_{n+1}+p_n)/(q_{n+1}+q_n)$. Hence
    $$
    \theta_{a_0}^{-1}\!\left(\cyl{(a_1, \ldots, a_n)}\right)
    \;=\;
    \begin{cases}
    \SetDifference{\left(a_0 + \dfrac{p_{n+1}}{q_{n+1}},\; a_0 + \dfrac{p_{n+1} + p_n}{q_{n+1} + q_n}\right)}{\QQ}, & n
    \text{ even},
    \\[1.2em]
    \SetDifference{\left(a_0 + \dfrac{p_{n+1} + p_n}{q_{n+1} + q_n},\; a_0 + \dfrac{p_{n+1}}{q_{n+1}}\right)}{\QQ},
    & n \text{ odd},
    \end{cases}
    $$
    an open subinterval of $\SetDifference{(a_0,a_0+1)}{\QQ}$, so $\theta_{a_0}$ is continuous. For the inverse, the
    determinant identity shows that these subintervals have length
    $1/(q_{n+1}(q_{n+1}+q_n))\le 1/q_{n+1}^2\to0$, so they form a neighborhood base for the subspace
    topology. Hence $\theta_{a_0}^{-1}$ is continuous. The clopen partition into intervals between consecutive integers then shows that $\theta$ is a
    homeomorphism.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The final identification with $\BaireSpace$ uses that $\ZZ$, $\RestrictedSet{\NN}{\ge 1}$, and $\omega$ are countable
    discrete spaces: code $a_0$ into coordinate $0$ via a bijection $\ZZ \cong \omega$, code the tail coordinates via a
    bijection $\RestrictedSet{\NN}{\ge 1} \cong \omega$, and then prepend the first coordinate to the recoded tail.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Under the homeomorphism $\theta_0$, the shift on
    $\funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}}$ corresponds to the \termdefine{Gauss map}
    $T(x):=\{1/x\}$ on $\SetDifference{(0,1)}{\QQ}$. This is the iteration
    $\alpha_n\mapsto\alpha_{n+1}$ of fractional remainders used above. The corresponding complete quotient is
    $1/\alpha_n=[a_{n+1};a_{n+2},\ldots]$. Thus shifting the partial quotients describes the Gauss map.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The coordinates also prove directly that the irrationals are Polish. Alternatively, they are a $\Gdelta$
    subset of $\R$, so Alexandrov's theorem in §{sec:alexandrov-theorem} shows that they are Polish.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The two rational boundary points of the fractional cylinder $\theta_0^{-1}(\cyl{s})$ are:
    $$\begin{aligned}
    F_s(\infty)
    &= \frac{p_{n+1}}{q_{n+1}}, \\
    F_s(1)
    &= \frac{p_{n+1} + p_n}{q_{n+1} + q_n}
     = \frac{p_{n+1}}{q_{n+1}} \oplus \frac{p_n}{q_n}.
    \end{aligned}$$
    Thus, in the integer cell $(a_0,a_0+1)$, the continued-fraction interval formula above becomes
    $$
    \theta_{a_0}^{-1}(\cyl{s})
    \;=\;
    \begin{cases}
    \SetDifference{\left(a_0 + F_s(\infty), a_0 + F_s(1)\right)}{\QQ}, & n \text{ even}, \\[0.8em]
    \SetDifference{\left(a_0 + F_s(1), a_0 + F_s(\infty)\right)}{\QQ}, & n \text{ odd}.
    \end{cases}
    $$
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Subdividing the cylinder by the next partial quotient gives
    $$\theta_{a_0}^{-1}(\cyl{s}) \;=\; \InternalDisjointUnion_{k \ge 1}
    \theta_{a_0}^{-1}(\cyl{s \concat (k)}).$$
-/

/-- Book-facing package for the simple continued-fraction subsection: irrational
reals have unique simple continued-fraction expansions and positive infinite
partial quotients converge to irrationals; the coordinate map is a homeomorphism,
the denominator growth, consecutive-convergent estimates, and nested-interval
step hold for positive partial quotients; its fixed-integer cells are clopen and
have fractional-coordinate branches; and the transported cylinder-code Galois
connection, parity-dependent cylinder interval formula, shrinking endpoint-length
estimate, and Gauss-map shift rule hold in continued-fraction coordinates. -/
theorem concreteSimpleContinuedFractionFacts :
    (∀ a : ℕ → ℤ, ∀ n : ℕ,
      simpleCFNum a (n + 1) * simpleCFDen a n -
          simpleCFNum a n * simpleCFDen a (n + 1) =
        (-1 : ℤ) ^ (n + 1)) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ, ∀ d : ℤ,
        d ∣ simpleCFNum a (n + 1) →
          d ∣ simpleCFDen a (n + 1) →
            d ∣ (1 : ℤ)) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a →
        ∀ n : ℕ, 0 < simpleCFDen a (n + 1)) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a →
        ∀ n : ℕ, (n : ℤ) ≤ simpleCFDen a (n + 1)) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a →
        Filter.Tendsto (fun n : ℕ => (simpleCFDen a (n + 1) : ℝ))
          Filter.atTop Filter.atTop) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ, ∀ d : ℤ,
        d ∣ simpleCFNum a (n + 2) →
          d ∣ simpleCFDen a (n + 2) →
            d ∣ (1 : ℤ)) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a →
        ∀ n : ℕ, ∀ x : ℝ, 0 < x →
          simpleCFFiniteTail a n x = simpleCFTailMap a n x) ∧
      (∀ x : ℝ, Irrational x →
        SimpleCFCompleteQuotientRelation
          (simpleCFAlgorithmPartials x) (simpleCFFractionalRemainder x)) ∧
      (∀ a : ℕ → ℤ, ∀ α : ℕ → ℝ,
        SimpleCFCompleteQuotientRelation a α →
          (∀ n : ℕ, 0 < (a (n + 1) : ℝ) + α (n + 1)) →
            ∀ n : ℕ, α 0 = simpleCFCompleteQuotientValue a n (α n)) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a → ∀ n : ℕ,
        ((simpleCFConvergent a (n + 1) : ℝ) -
            (simpleCFConvergent a n : ℝ)) =
          ((-1 : ℝ) ^ (n + 2)) /
            ((simpleCFDen a (n + 2) : ℝ) *
              (simpleCFDen a (n + 1) : ℝ))) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a → ∀ n : ℕ,
        ((simpleCFConvergent a (n + 2) : ℝ) -
            (simpleCFConvergent a n : ℝ)) =
          ((a (n + 2) : ℝ) * ((-1 : ℝ) ^ (n + 2))) /
            ((simpleCFDen a (n + 3) : ℝ) *
              (simpleCFDen a (n + 1) : ℝ))) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a → ∀ n : ℕ,
        |(simpleCFConvergent a (n + 2) : ℝ) -
            (simpleCFConvergent a n : ℝ)| <
          |(simpleCFConvergent a (n + 1) : ℝ) -
            (simpleCFConvergent a n : ℝ)|) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a → ∀ n : ℕ,
        (simpleCFConvergent a (n + 2) : ℝ) ∈
          Set.uIoo (simpleCFConvergent a n : ℝ)
            (simpleCFConvergent a (n + 1) : ℝ)) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a →
        CauchySeq (fun n : ℕ => ((simpleCFConvergent a n : ℚ) : ℝ))) ∧
      (∀ a : ℕ → ℤ, SimpleCFPositivePartials a →
        ∃ β : ℝ, SimpleCFConvergentLimit a β) ∧
      (∀ a : ℕ → ℤ, SimpleCFLimitInOpenUnitInterval a) ∧
      (∀ a : ℕ → ℤ, SimpleCFLimitIrrational a) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, SimpleCFShiftedLimitIrrational a₀ a) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ,
        SimpleCFInfiniteExpressionConvergesToIrrational a₀ a) ∧
      SimpleCFExistenceUniquenessForIrrationals ∧
      SimpleCFExpansionExistsUniquelyForIrrationals ∧
      SimpleCFConverseForPositivePartials ∧
      Nonempty ({x : ℝ // Irrational x} ≃ₜ (ℤ × (ℕ → positiveNat))) ∧
      Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) ∧
      PolishSpace {x : ℝ // Irrational x} ∧
      IsLocallyConstant (fun x : {x : ℝ // Irrational x} => simpleCFIntegerPart x.1) ∧
      Continuous (fun x : {x : ℝ // Irrational x} => simpleCFIntegerPart x.1) ∧
      (∀ a₀ : ℤ,
        simpleCFIntegerPartCell a₀ =
          {x : {x : ℝ // Irrational x} |
            x.1 ∈ Set.Ioo (a₀ : ℝ) ((a₀ : ℝ) + 1)}) ∧
      (∀ a₀ : ℤ, ∀ x : {x : ℝ // Irrational x},
        x ∈ simpleCFIntegerPartCell a₀ → simpleCFIntegerPart x.1 = a₀) ∧
      (∀ a₀ : ℤ, IsClopen (simpleCFIntegerPartCell a₀)) ∧
      (⋃ a₀ : ℤ, simpleCFIntegerPartCell a₀) = (Set.univ : Set {x : ℝ // Irrational x}) ∧
      (∀ a₀ b₀ : ℤ, a₀ ≠ b₀ →
        Disjoint (simpleCFIntegerPartCell a₀) (simpleCFIntegerPartCell b₀)) ∧
      (∀ a₀ : ℤ,
        Nonempty (simpleCFFractionalInterval a₀ ≃ₜ (ℕ → positiveNat))) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat,
        IsClopen (simpleCFFractionalCylinder a₀ s)) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat,
        simpleCFFractionalCylinder a₀ s =
          ⋃ k : positiveNat, simpleCFFractionalCylinder a₀ (concat s [k])) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat, ∀ m n : positiveNat, m ≠ n →
        Disjoint (simpleCFFractionalCylinder a₀ (concat s [m]))
          (simpleCFFractionalCylinder a₀ (concat s [n]))) ∧
      (∀ a₀ : ℤ, ∀ A : Set (finseq positiveNat),
        ∀ x : simpleCFFractionalInterval a₀,
          x ∈ simpleCFFractionalCylinderCode a₀ A ↔
            ∃ s : finseq positiveNat, s ∈ A ∧ x ∈ simpleCFFractionalCylinder a₀ s) ∧
      (∀ a₀ : ℤ, ∀ A : Set (finseq positiveNat),
        ∀ V : Set (simpleCFFractionalInterval a₀),
          simpleCFFractionalCylinderCode a₀ A ⊆ V ↔
            A ⊆ simpleCFFractionalOpenCylinderCode a₀ V) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a → Even n →
          ∀ x y : ℝ, 0 < x → x < y →
            simpleCFTailMap a n y < simpleCFTailMap a n x) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a → Odd n →
          ∀ x y : ℝ, 0 < x → x < y →
            simpleCFTailMap a n x < simpleCFTailMap a n y) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          (fun x : ℝ => (a₀ : ℝ) + simpleCFTailMap a n x) ''
              {x : ℝ | Irrational x ∧ 1 < x} =
            {y : ℝ | Irrational y ∧
              y ∈
                if Even n then
                  Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
                    ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
                else
                  Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
                    ((a₀ : ℝ) + simpleCFEndpoint a n)}) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          |((a₀ : ℝ) + simpleCFAdjacentEndpoint a n) -
              ((a₀ : ℝ) + simpleCFEndpoint a n)| =
            1 / ((simpleCFDen a (n + 1) : ℝ) *
              ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)))) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ,
        SimpleCFPositivePartials a →
          Filter.Tendsto
            (fun n : ℕ =>
              |((a₀ : ℝ) + simpleCFAdjacentEndpoint a n) -
                ((a₀ : ℝ) + simpleCFEndpoint a n)|)
            Filter.atTop (𝓝 0)) ∧
      (∃ θ : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ₜ (ℕ → positiveNat),
        ∀ x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1},
          ∃ hx : Irrational (gaussMap x.1) ∧ 0 < gaussMap x.1 ∧ gaussMap x.1 < 1,
            θ ⟨gaussMap x.1, hx⟩ = shiftPositiveNat (θ x)) := by
  refine ⟨simpleCF_determinant, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_,
    simpleCFExistenceUniquenessForIrrationals_of_algorithmExpansion,
    simpleCFExpansionExistsUniquelyForIrrationals_of_algorithmExpansion,
    simpleCFConverseForPositivePartials_of_positive,
    continuedFractionCoordinateHomeomorphismFact, continuedFractionBaireHomeomorphismFact,
    irrationals_polish_via_continuedFractions, simpleCFIntegerPart_irrational_locallyConstant,
    simpleCFIntegerPart_irrational_continuous, ?_, ?_, ?_, iUnion_simpleCFIntegerPartCell,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, gaussMapShiftCorrespondenceFact⟩
  · intro a n d hp hq
    exact simpleCF_common_divisor_dvd_one a n hp hq
  · intro a ha n
    exact simpleCFDen_pos_of_positive ha n
  · intro a ha n
    exact simpleCFDen_ge_index_of_positive ha n
  · intro a ha
    exact simpleCFDen_tendsto_atTop_of_positive ha
  · intro a n d hp hq
    exact simpleCFConvergent_num_den_lowestTerms n hp hq
  · intro a ha n x hx
    exact SimpleCFFiniteTailFormulaClaim ha n x hx
  · intro x hx
    exact simpleCFAlgorithmCompleteQuotientRelation_of_irrational x hx
  · intro a α hα hpos n
    exact SimpleCFTailFormulaClaim hα hpos n
  · intro a ha n
    exact simpleCFConvergent_succ_sub ha n
  · intro a ha n
    exact simpleCFConvergent_succ_succ_sub ha n
  · intro a ha n
    exact abs_simpleCFConvergent_succ_succ_sub_lt_succ_sub ha n
  · intro a ha n
    exact simpleCFConvergent_succ_succ_mem_uIoo ha n
  · intro a ha
    exact simpleCFConvergent_cauchySeq_of_positive ha
  · intro a ha
    simpa [SimpleCFConvergentLimit] using exists_tendsto_simpleCFConvergent_of_positive ha
  · intro a
    exact simpleCFLimitInOpenUnitInterval_of_positive a
  · intro a
    exact simpleCFLimitIrrational_of_positive a
  · intro a₀ a
    exact simpleCFShiftedLimitIrrational_of_positive a₀ a
  · intro a₀ a
    exact simpleCFInfiniteExpressionConvergesToIrrational_of_positive a₀ a
  · intro a₀
    exact simpleCFIntegerPartCell_eq_interval a₀
  · intro a₀ x hx
    exact simpleCFIntegerPartCell_value hx
  · intro a₀
    exact isClopen_simpleCFIntegerPartCell a₀
  · intro a₀ b₀ hne
    exact disjoint_simpleCFIntegerPartCell hne
  · intro a₀
    exact fractionalPartContinuedFractionHomeomorphismFact a₀
  · intro a₀ s
    exact isClopen_simpleCFFractionalCylinder a₀ s
  · intro a₀ s
    exact simpleCFFractionalCylinder_eq_iUnion_immediate_subcylinders a₀ s
  · intro a₀ s m n hmn
    exact disjoint_simpleCFFractional_immediate_subcylinders a₀ s hmn
  · intro a₀ A x
    exact mem_simpleCFFractionalCylinderCode (a₀ := a₀) (A := A) (x := x)
  · intro a₀ A V
    exact simpleCFFractionalCylinderCode_subset_iff_subset_openCylinderCode
      (a₀ := a₀) (A := A) (V := V)
  · intro a n ha hn x y hx hxy
    exact simpleCFTailMap_strictAnti_of_even ha hn hx hxy
  · intro a n ha hn x y hx hxy
    exact simpleCFTailMap_strictMono_of_odd ha hn hx hxy
  · intro a₀ a n ha
    exact simpleCFTailImageInterval_eq_of_positive a₀ ha n
  · intro a₀ a n ha
    exact abs_translated_simpleCFAdjacentEndpoint_sub_endpoint ha a₀ n
  · intro a₀ a ha
    exact tendsto_abs_translated_simpleCFAdjacentEndpoint_sub_endpoint_zero ha a₀

theorem real_continuedFraction_convergents_tendsto (x : ℝ) :
    Filter.Tendsto (GenContFract.of x).convs Filter.atTop (𝓝 x) :=
  GenContFract.of_convergence x

theorem real_continuedFraction_terminates_iff_exists_rat (x : ℝ) :
    (GenContFract.of x).Terminates ↔ ∃ q : ℚ, x = (q : ℝ) :=
  GenContFract.terminates_iff_rat x

theorem real_continuedFraction_terminates_iff_not_irrational (x : ℝ) :
    (GenContFract.of x).Terminates ↔ ¬ Irrational x := by
  simpa [Irrational, Set.mem_range, eq_comm] using
    (real_continuedFraction_terminates_iff_exists_rat x)

theorem irrational_continuedFraction_not_terminates {x : ℝ} (hx : Irrational x) :
    ¬ (GenContFract.of x).Terminates := by
  intro hterm
  exact (real_continuedFraction_terminates_iff_not_irrational x).mp hterm hx

theorem irrational_continuedFraction_converges_and_not_terminates {x : ℝ} (hx : Irrational x) :
    Filter.Tendsto (GenContFract.of x).convs Filter.atTop (𝓝 x) ∧
      ¬ (GenContFract.of x).Terminates :=
  ⟨real_continuedFraction_convergents_tendsto x, irrational_continuedFraction_not_terminates hx⟩

/-!
## Stern-Brocot arithmetic

This records the determinant computations used by the book's Stern-Brocot discussion:
semiconvergents are Farey-adjacent to the fixed endpoint, and adjacent semiconvergents
are Farey neighbors.
-/

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The \termdefine{mediant} of two fractions is
    $$\frac{a}{b} \oplus \frac{c}{d} \;:=\; \frac{a+c}{b+d}.$$
-/
/-- The mediant of two fractions given by numerator-denominator pairs. -/
def rationalMediant (p q r s : ℤ) : ℚ :=
  ((p + r : ℤ) : ℚ) / ((q + s : ℤ) : ℚ)

/-- Farey adjacency for two numerator-denominator pairs. -/
def fareyNeighbor (p q r s : ℤ) : Prop :=
  |p * s - q * r| = (1 : ℤ)

/-- Ordered Farey neighbors have gap `1 / (bd)` in real coordinates. This is the
formula used in the Stern--Brocot interval estimate. -/
theorem orderedFareyNeighbor_real_sub_eq_one_div {a b c d : ℤ}
    (hb : b ≠ 0) (hd : d ≠ 0) (hdet : b * c - a * d = 1) :
    (c : ℝ) / (d : ℝ) - (a : ℝ) / (b : ℝ) =
      1 / ((b : ℝ) * (d : ℝ)) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hprod : (b : ℝ) * (d : ℝ) ≠ 0 := mul_ne_zero hbR hdR
  have hdetR : (b : ℝ) * (c : ℝ) - (a : ℝ) * (d : ℝ) = 1 := by
    exact_mod_cast hdet
  field_simp [hbR, hdR, hprod]
  linear_combination hdetR

theorem fareyNeighbor_left_common_divisor_dvd_one {p q r s d : ℤ}
    (h : fareyNeighbor p q r s) (hp : d ∣ p) (hq : d ∣ q) :
    d ∣ (1 : ℤ) := by
  have hdiff : d ∣ p * s - q * r :=
    dvd_sub (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_left hq _)
  have habs : d ∣ |p * s - q * r| := (dvd_abs d (p * s - q * r)).2 hdiff
  rwa [h] at habs

theorem fareyNeighbor_right_common_divisor_dvd_one {p q r s d : ℤ}
    (h : fareyNeighbor p q r s) (hr : d ∣ r) (hs : d ∣ s) :
    d ∣ (1 : ℤ) := by
  have hdiff : d ∣ p * s - q * r :=
    dvd_sub (dvd_mul_of_dvd_right hs _) (dvd_mul_of_dvd_right hr _)
  have habs : d ∣ |p * s - q * r| := (dvd_abs d (p * s - q * r)).2 hdiff
  rwa [h] at habs

/-- Numerator of the `k`-th semiconvergent between consecutive continued-fraction
convergents. -/
def simpleCFSemiconvergentNum (a : ℕ → ℤ) (n k : ℕ) : ℤ :=
  (k : ℤ) * simpleCFNum a (n + 1) + simpleCFNum a n

/-- Denominator of the `k`-th semiconvergent between consecutive continued-fraction
convergents. -/
def simpleCFSemiconvergentDen (a : ℕ → ℤ) (n k : ℕ) : ℤ :=
  (k : ℤ) * simpleCFDen a (n + 1) + simpleCFDen a n

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The cut points are the \termdefineas{semiconvergent}{semiconvergents}
    $$F_s(k) \;=\; \frac{k p_{n+1} + p_n}{k q_{n+1} + q_n} \qquad (k \ge 1),$$
    and each child is the interval between two adjacent translated cut points:
-/
/-- The rational value of a semiconvergent. -/
def simpleCFSemiconvergent (a : ℕ → ℤ) (n k : ℕ) : ℚ :=
  (simpleCFSemiconvergentNum a n k : ℚ) /
    (simpleCFSemiconvergentDen a n k : ℚ)

/-- Numerator of the integer-cell translate `a₀ + F_s(k)` of a semiconvergent. -/
def simpleCFShiftedSemiconvergentNum (a₀ : ℤ) (a : ℕ → ℤ) (n k : ℕ) : ℤ :=
  a₀ * simpleCFSemiconvergentDen a n k + simpleCFSemiconvergentNum a n k

/-- The rational label obtained by translating a semiconvergent into the integer cell
indexed by `a₀`. -/
def simpleCFShiftedSemiconvergent (a₀ : ℤ) (a : ℕ → ℤ) (n k : ℕ) : ℚ :=
  (simpleCFShiftedSemiconvergentNum a₀ a n k : ℚ) /
    (simpleCFSemiconvergentDen a n k : ℚ)

theorem simpleCFSemiconvergentNum_eq_of_eq_on_le {a b : ℕ → ℤ} {N n k : ℕ}
    (h : ∀ i : ℕ, i ≤ N → a i = b i) (hn : n ≤ N) :
    simpleCFSemiconvergentNum a n k = simpleCFSemiconvergentNum b n k := by
  unfold simpleCFSemiconvergentNum
  rw [simpleCFNum_eq_of_eq_on_le h (by omega : n + 1 ≤ N + 1),
    simpleCFNum_eq_of_eq_on_le h (by omega : n ≤ N + 1)]

theorem simpleCFSemiconvergentDen_eq_of_eq_on_le {a b : ℕ → ℤ} {N n k : ℕ}
    (h : ∀ i : ℕ, i ≤ N → a i = b i) (hn : n ≤ N) :
    simpleCFSemiconvergentDen a n k = simpleCFSemiconvergentDen b n k := by
  unfold simpleCFSemiconvergentDen
  rw [simpleCFDen_eq_of_eq_on_le h (by omega : n + 1 ≤ N + 1),
    simpleCFDen_eq_of_eq_on_le h (by omega : n ≤ N + 1)]

theorem simpleCFShiftedSemiconvergentNum_eq_of_eq_on_le {a b : ℕ → ℤ}
    {N n k : ℕ} (a₀ : ℤ)
    (h : ∀ i : ℕ, i ≤ N → a i = b i) (hn : n ≤ N) :
    simpleCFShiftedSemiconvergentNum a₀ a n k =
      simpleCFShiftedSemiconvergentNum a₀ b n k := by
  unfold simpleCFShiftedSemiconvergentNum
  rw [simpleCFSemiconvergentDen_eq_of_eq_on_le h hn,
    simpleCFSemiconvergentNum_eq_of_eq_on_le h hn]

theorem simpleCFShiftedSemiconvergent_eq_of_eq_on_le {a b : ℕ → ℤ}
    {N n k : ℕ} (a₀ : ℤ)
    (h : ∀ i : ℕ, i ≤ N → a i = b i) (hn : n ≤ N) :
    simpleCFShiftedSemiconvergent a₀ a n k =
      simpleCFShiftedSemiconvergent a₀ b n k := by
  unfold simpleCFShiftedSemiconvergent
  rw [simpleCFShiftedSemiconvergentNum_eq_of_eq_on_le a₀ h hn,
    simpleCFSemiconvergentDen_eq_of_eq_on_le h hn]

/-- A shifted semiconvergent label at the prefix length is well-defined on a
finite continued-fraction cylinder: changing the infinite tail after that
prefix does not change the rational label. -/
theorem simpleCFShiftedSemiconvergent_eq_of_mem_same_cyl
    (a₀ : ℤ) (pref : finseq positiveNat) {s t : ℕ → positiveNat} (k : ℕ)
    (hs : s ∈ cyl pref) (ht : t ∈ cyl pref) :
    simpleCFShiftedSemiconvergent a₀ (positiveNatSeqPartials s) pref.length k =
      simpleCFShiftedSemiconvergent a₀ (positiveNatSeqPartials t) pref.length k := by
  exact simpleCFShiftedSemiconvergent_eq_of_eq_on_le a₀
    (positiveNatSeqPartials_eq_on_le_of_mem_same_cyl hs ht) le_rfl

theorem simpleCFTailMap_natCast_eq_semiconvergent (a : ℕ → ℤ) (n k : ℕ) :
    simpleCFTailMap a n (k : ℝ) = (simpleCFSemiconvergent a n k : ℝ) := by
  unfold simpleCFTailMap simpleCFSemiconvergent
    simpleCFSemiconvergentNum simpleCFSemiconvergentDen
  norm_num [Rat.cast_div]

theorem simpleCFSemiconvergentDen_pos_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    0 < simpleCFSemiconvergentDen a n k := by
  unfold simpleCFSemiconvergentDen
  have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
  exact add_pos_of_pos_of_nonneg
    (mul_pos hkZ (simpleCFDen_pos_of_positive ha n))
    (simpleCFDen_nonneg_of_positive ha n)

theorem simpleCFSemiconvergentNum_pos_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    0 < simpleCFSemiconvergentNum a n k := by
  rcases n with _ | n
  · simp [simpleCFSemiconvergentNum]
  · unfold simpleCFSemiconvergentNum
    have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
    exact add_pos_of_pos_of_nonneg
      (mul_pos hkZ (simpleCFNum_pos_of_positive ha n))
      (simpleCFNum_nonneg_of_positive ha (n + 1))

theorem simpleCFNum_lt_den_of_positive_from_three {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) :
    ∀ n : ℕ, simpleCFNum a (n + 3) < simpleCFDen a (n + 3) := by
  intro n
  induction n with
  | zero =>
      rw [show 0 + 3 = 1 + 2 by norm_num, simpleCFNum_succ_succ,
        simpleCFDen_succ_succ]
      norm_num [simpleCFNum_succ_succ, simpleCFDen_succ_succ]
      have ha₁ : 1 ≤ a 1 := ha 0
      have ha₂_nonneg : 0 ≤ a 2 := le_trans zero_le_one (ha 1)
      have hmul : a 2 * 1 ≤ a 2 * a 1 :=
        mul_le_mul_of_nonneg_left ha₁ ha₂_nonneg
      nlinarith
  | succ n ih =>
      rw [show n + 1 + 3 = n + 4 by omega,
        show n + 4 = (n + 2) + 2 by omega, simpleCFNum_succ_succ,
        simpleCFDen_succ_succ]
      have ha_pos : 0 < a (n + 3) := lt_of_lt_of_le zero_lt_one (ha (n + 2))
      have hle :
          simpleCFNum a (n + 2) ≤ simpleCFDen a (n + 2) := by
        simpa [show n + 2 = (n + 1) + 1 by omega] using
          simpleCFNum_le_den_of_positive ha (n + 1)
      exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left ih ha_pos) hle

theorem simpleCFSemiconvergentNum_lt_den_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    simpleCFSemiconvergentNum a n k < simpleCFSemiconvergentDen a n k := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · simp [simpleCFSemiconvergentNum, simpleCFSemiconvergentDen,
      simpleCFNum_succ_succ, simpleCFDen_succ_succ]
    have ha₁ : 1 ≤ a 1 := ha 0
    have hk_nonneg : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hmul : (k : ℤ) * 1 ≤ (k : ℤ) * a 1 :=
      mul_le_mul_of_nonneg_left ha₁ hk_nonneg
    nlinarith
  · unfold simpleCFSemiconvergentNum simpleCFSemiconvergentDen
    have hk_pos : 0 < (k : ℤ) := by exact_mod_cast hk
    have hlt :
        simpleCFNum a (n + 3) < simpleCFDen a (n + 3) :=
      simpleCFNum_lt_den_of_positive_from_three ha n
    have hle :
        simpleCFNum a (n + 2) ≤ simpleCFDen a (n + 2) := by
      simpa [show n + 2 = (n + 1) + 1 by omega] using
        simpleCFNum_le_den_of_positive ha (n + 1)
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hlt hk_pos) hle

theorem simpleCFSemiconvergent_pos_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    0 < simpleCFSemiconvergent a n k := by
  unfold simpleCFSemiconvergent
  exact div_pos
    (by exact_mod_cast simpleCFSemiconvergentNum_pos_of_positive ha n hk)
    (by exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk)

theorem simpleCFSemiconvergent_mem_Ioo_zero_one_of_positive {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((simpleCFSemiconvergent a n k : ℚ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hposQ : (0 : ℚ) < simpleCFSemiconvergent a n k :=
    simpleCFSemiconvergent_pos_of_positive ha n hk
  have hdenQ : (0 : ℚ) < (simpleCFSemiconvergentDen a n k : ℚ) := by
    exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk
  have hnum_lt_denQ :
      (simpleCFSemiconvergentNum a n k : ℚ) <
        (simpleCFSemiconvergentDen a n k : ℚ) := by
    exact_mod_cast simpleCFSemiconvergentNum_lt_den_of_positive ha hn hk
  have hltQ : simpleCFSemiconvergent a n k < (1 : ℚ) := by
    unfold simpleCFSemiconvergent
    exact (div_lt_one hdenQ).2 hnum_lt_denQ
  exact ⟨by exact_mod_cast hposQ, by exact_mod_cast hltQ⟩

theorem simpleCFShiftedSemiconvergentNum_pos_of_nonneg {a₀ : ℤ} {a : ℕ → ℤ}
    (ha₀ : 0 ≤ a₀) (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ}
    (hk : 0 < k) :
    0 < simpleCFShiftedSemiconvergentNum a₀ a n k := by
  unfold simpleCFShiftedSemiconvergentNum
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg ha₀ (le_of_lt (simpleCFSemiconvergentDen_pos_of_positive ha n hk)))
    (simpleCFSemiconvergentNum_pos_of_positive ha n hk)

theorem simpleCFSemiconvergent_one_eq_mediant (a : ℕ → ℤ) (n : ℕ) :
    simpleCFSemiconvergent a n 1 =
      rationalMediant (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
        (simpleCFNum a n) (simpleCFDen a n) := by
  simp [simpleCFSemiconvergent, simpleCFSemiconvergentNum,
    simpleCFSemiconvergentDen, rationalMediant, add_comm]

theorem simpleCFShiftedSemiconvergent_eq_intCast_add {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ : ℤ) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    simpleCFShiftedSemiconvergent a₀ a n k =
      (a₀ : ℚ) + simpleCFSemiconvergent a n k := by
  have hden_int : simpleCFSemiconvergentDen a n k ≠ 0 :=
    ne_of_gt (simpleCFSemiconvergentDen_pos_of_positive ha n hk)
  have hden : (simpleCFSemiconvergentDen a n k : ℚ) ≠ 0 := by
    exact_mod_cast hden_int
  unfold simpleCFShiftedSemiconvergent simpleCFSemiconvergent
    simpleCFShiftedSemiconvergentNum
  rw [show ((a₀ * simpleCFSemiconvergentDen a n k +
        simpleCFSemiconvergentNum a n k : ℤ) : ℚ) =
      (a₀ : ℚ) * (simpleCFSemiconvergentDen a n k : ℚ) +
        (simpleCFSemiconvergentNum a n k : ℚ) by norm_num]
  field_simp [hden]

/-- The `k = 1` label in the integer cell is the translate of the mediant endpoint. -/
theorem simpleCFShiftedSemiconvergent_one_eq_intCast_add_mediant {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ : ℤ) (n : ℕ) :
    simpleCFShiftedSemiconvergent a₀ a n 1 =
      (a₀ : ℚ) +
        rationalMediant (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
          (simpleCFNum a n) (simpleCFDen a n) := by
  rw [simpleCFShiftedSemiconvergent_eq_intCast_add ha a₀ n (by norm_num : 0 < (1 : ℕ))]
  rw [simpleCFSemiconvergent_one_eq_mediant]

/-- The empty-prefix Stern--Brocot label is `[a₀;1] = a₀ + 1`. -/
theorem simpleCFShiftedSemiconvergent_emptyPrefix_label (a₀ : ℤ) (a : ℕ → ℤ) :
    simpleCFShiftedSemiconvergent a₀ a 0 1 = (a₀ : ℚ) + 1 := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen]

/-- Positive integers use the terminating convention `m = [m - 1; 1]`. -/
theorem simpleCFShiftedSemiconvergent_positiveInteger_label {m : ℕ} (hm : 0 < m)
    (a : ℕ → ℤ) :
    simpleCFShiftedSemiconvergent ((m - 1 : ℕ) : ℤ) a 0 1 = (m : ℚ) := by
  rw [simpleCFShiftedSemiconvergent_emptyPrefix_label]
  have hNat : m - 1 + 1 = m := Nat.sub_add_cancel hm
  exact_mod_cast hNat

/-- The Stern--Brocot rational label of the continued-fraction cylinder with integer
cell `a₀` and finite tail prefix ending at level `n`: `[a₀; a₁, ..., aₙ, 1]`. -/
def sternBrocotNodeLabel (a₀ : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℚ :=
  simpleCFShiftedSemiconvergent (a₀ : ℤ) a n 1

/-- The node label is the translated mediant endpoint of the corresponding
continued-fraction cylinder. -/
theorem sternBrocotNodeLabel_eq_intCast_add_mediant {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ : ℕ) (n : ℕ) :
    sternBrocotNodeLabel a₀ a n =
      (a₀ : ℚ) +
        rationalMediant (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
          (simpleCFNum a n) (simpleCFDen a n) := by
  simpa [sternBrocotNodeLabel] using
    simpleCFShiftedSemiconvergent_one_eq_intCast_add_mediant ha (a₀ : ℤ) n

/-- The empty-prefix node label gives the terminating convention `m = [m - 1; 1]`
for positive integers. -/
theorem sternBrocotNodeLabel_positiveInteger {m : ℕ} (hm : 0 < m)
    (a : ℕ → ℤ) :
    sternBrocotNodeLabel (m - 1) a 0 = (m : ℚ) := by
  exact simpleCFShiftedSemiconvergent_positiveInteger_label hm a

/-- The Stern--Brocot node label assigned to a finite continued-fraction cylinder
is independent of the infinite tail used to extend that cylinder. This is the
well-definedness part of the book's label
`θ_{a₀}^{-1}(cyl(s)) ↦ [a₀; a₁, ..., aₙ, 1]`. -/
theorem sternBrocotNodeLabel_eq_of_mem_same_cylinder
    (a₀ : ℕ) (pref : finseq positiveNat) {s t : ℕ → positiveNat}
    (hs : s ∈ cyl pref) (ht : t ∈ cyl pref) :
    sternBrocotNodeLabel a₀ (positiveNatSeqPartials s) pref.length =
      sternBrocotNodeLabel a₀ (positiveNatSeqPartials t) pref.length := by
  exact simpleCFShiftedSemiconvergent_eq_of_mem_same_cyl (a₀ : ℤ) pref 1 hs ht

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The mediant endpoint gives each continued-fraction cylinder its rational label. The node $\theta_{a_0}^{-1}(\cyl{s})$ has label
    $$[a_0; a_1,\ldots,a_n,1],
    \qquad \text{where } s=(a_1,\ldots,a_n),\;\; a_0 \in \NN.$$
-/
/-- The rational label of the finite continued-fraction cylinder
`θ_{a₀}^{-1}(cyl(pref))`. The auxiliary infinite tail is the canonical extension
of the finite prefix; the next theorem shows that the value is independent of
this choice. -/
noncomputable def sternBrocotFiniteCylinderLabel (a₀ : ℕ)
    (pref : finseq positiveNat) : ℚ :=
  sternBrocotNodeLabel a₀ (positiveNatSeqPartials (extendFinseq pref)) pref.length

/-- Finite fractional tail notation, read from the front:
`[0; pref, x]`. The terminating convention uses `x = 1`. -/
noncomputable def simpleCFTerminatingTailValue : finseq positiveNat → ℝ → ℝ
  | [], x => 1 / x
  | a :: pref, x => 1 / ((a.1 : ℝ) + simpleCFTerminatingTailValue pref x)

/-- Appending one partial quotient to the right agrees with the end-recursive
finite-tail update used by `simpleCFFiniteTail`. -/
theorem simpleCFTerminatingTailValue_append_singleton
    (pref : finseq positiveNat) (a : positiveNat) (x : ℝ) :
    simpleCFTerminatingTailValue (pref ++ [a]) x =
      simpleCFTerminatingTailValue pref ((a.1 : ℝ) + 1 / x) := by
  induction pref with
  | nil =>
      simp [simpleCFTerminatingTailValue]
  | cons b pref ih =>
      simp [simpleCFTerminatingTailValue, ih]

/-- The front-recursive finite-tail notation agrees with the existing
end-recursive continued-fraction tail map whenever the infinite tail extends the
finite prefix. -/
theorem simpleCFTerminatingTailValue_eq_simpleCFFiniteTail_of_mem_cyl
    (pref : finseq positiveNat) {s : ℕ → positiveNat} (hs : s ∈ cyl pref)
    (x : ℝ) :
    simpleCFTerminatingTailValue pref x =
      simpleCFFiniteTail (positiveNatSeqPartials s) pref.length x := by
  induction pref using List.reverseRecOn generalizing x with
  | nil =>
      simp [simpleCFTerminatingTailValue, simpleCFFiniteTail]
  | append_singleton pref a ih =>
      have hs_pref : s ∈ cyl pref := cyl_concat_subset pref [a] (by simpa [concat] using hs)
      have hlast : positiveNatSeqPartials s (pref.length + 1) = (a.1 : ℤ) := by
        have hcoord : s pref.length = a := by
          have h := hs pref.length (by simp)
          simpa [concat] using h
        simp [positiveNatSeqPartials, hcoord]
      rw [simpleCFTerminatingTailValue_append_singleton]
      rw [ih hs_pref ((a.1 : ℝ) + 1 / x)]
      rw [show (pref ++ [a]).length = pref.length + 1 by simp]
      rw [simpleCFFiniteTail, hlast]
      norm_num

/-- Finite terminating tails are positive for positive terminal input. -/
theorem simpleCFTerminatingTailValue_pos_of_pos
    (pref : finseq positiveNat) {x : ℝ} (hx : 0 < x) :
    0 < simpleCFTerminatingTailValue pref x := by
  induction pref with
  | nil =>
      simpa [simpleCFTerminatingTailValue] using one_div_pos.mpr hx
  | cons a pref ih =>
      have ha_pos : 0 < (a.1 : ℝ) := by
        have ha_one : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast a.2
        linarith
      have htail_pos : 0 < simpleCFTerminatingTailValue pref x := ih
      have hden_pos : 0 < (a.1 : ℝ) + simpleCFTerminatingTailValue pref x := by
        positivity
      simpa [simpleCFTerminatingTailValue] using one_div_pos.mpr hden_pos

/-- A nonempty finite terminating tail lies strictly below `1`. -/
theorem simpleCFTerminatingTailValue_cons_lt_one
    (a : positiveNat) (pref : finseq positiveNat) {x : ℝ} (hx : 0 < x) :
    simpleCFTerminatingTailValue (a :: pref) x < 1 := by
  have htail_pos : 0 < simpleCFTerminatingTailValue pref x :=
    simpleCFTerminatingTailValue_pos_of_pos pref hx
  have hden_gt_one : 1 < (a.1 : ℝ) + simpleCFTerminatingTailValue pref x := by
    have ha_one : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast a.2
    linarith
  have hden_pos : 0 < (a.1 : ℝ) + simpleCFTerminatingTailValue pref x :=
    zero_lt_one.trans hden_gt_one
  rw [simpleCFTerminatingTailValue]
  rw [div_lt_iff₀ hden_pos]
  linarith

/-- Real value of the chosen terminating continued-fraction expression
`[a₀; pref, 1]`. This is the finite-expression convention used for the
Stern--Brocot rational labels. -/
noncomputable def simpleCFTerminatingExpressionValue (a₀ : ℕ)
    (pref : finseq positiveNat) : ℝ :=
  (a₀ : ℝ) + simpleCFTerminatingTailValue pref 1

/-- The rational finite-cylinder label has real value equal to the chosen
terminating continued-fraction expression `[a₀; pref, 1]`. -/
theorem sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue
    (a₀ : ℕ) (pref : finseq positiveNat) :
    ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) =
      simpleCFTerminatingExpressionValue a₀ pref := by
  rw [sternBrocotFiniteCylinderLabel, sternBrocotNodeLabel]
  rw [simpleCFShiftedSemiconvergent_eq_intCast_add
    (positiveNatSeqPartials_positive (extendFinseq pref)) (a₀ : ℤ) pref.length
    (by norm_num : 0 < (1 : ℕ))]
  rw [Rat.cast_add]
  norm_num
  rw [← simpleCFTailMap_natCast_eq_semiconvergent
    (positiveNatSeqPartials (extendFinseq pref)) pref.length 1]
  rw [← SimpleCFFiniteTailFormulaClaim
    (positiveNatSeqPartials_positive (extendFinseq pref)) pref.length ((1 : ℕ) : ℝ)
    (by norm_num)]
  rw [simpleCFTerminatingExpressionValue]
  rw [simpleCFTerminatingTailValue_eq_simpleCFFiniteTail_of_mem_cyl pref
    (extendFinseq_mem_cyl pref) 1]
  norm_num

/-- The empty terminating expression is `[a₀;1] = a₀ + 1`. -/
theorem simpleCFTerminatingExpressionValue_empty (a₀ : ℕ) :
    simpleCFTerminatingExpressionValue a₀ [] = (a₀ : ℝ) + 1 := by
  norm_num [simpleCFTerminatingExpressionValue, simpleCFTerminatingTailValue]

/-- The empty-prefix terminating convention writes a positive integer as
`m = [m - 1;1]`. -/
theorem simpleCFTerminatingExpressionValue_empty_positiveInteger
    {m : ℕ} (hm : 0 < m) :
    simpleCFTerminatingExpressionValue (m - 1) [] = (m : ℝ) := by
  rw [simpleCFTerminatingExpressionValue_empty]
  have hNat : m - 1 + 1 = m := Nat.sub_add_cancel hm
  exact_mod_cast hNat

/-- The empty terminating expression `[a₀;1]` has integer part `a₀ + 1`. -/
theorem simpleCFTerminatingExpressionValue_empty_integerPart (a₀ : ℕ) :
    simpleCFIntegerPart (simpleCFTerminatingExpressionValue a₀ []) =
      ((a₀ + 1 : ℕ) : ℤ) := by
  have hvalue :
      simpleCFTerminatingExpressionValue a₀ [] = ((a₀ + 1 : ℕ) : ℝ) := by
    rw [simpleCFTerminatingExpressionValue_empty]
    norm_num
  rw [hvalue]
  exact simpleCFIntegerPart_natCast (a₀ + 1)

/-- Empty chosen terminating expressions are injective in the displayed integer
part. -/
theorem simpleCFTerminatingExpressionValue_empty_injective :
    Function.Injective (fun a₀ : ℕ => simpleCFTerminatingExpressionValue a₀ []) := by
  intro a₀ b₀ h
  change simpleCFTerminatingExpressionValue a₀ [] =
    simpleCFTerminatingExpressionValue b₀ [] at h
  have hint : ((a₀ + 1 : ℕ) : ℤ) = ((b₀ + 1 : ℕ) : ℤ) := by
    rw [← simpleCFTerminatingExpressionValue_empty_integerPart a₀, h,
      simpleCFTerminatingExpressionValue_empty_integerPart b₀]
  have hnat : a₀ + 1 = b₀ + 1 := by
    exact_mod_cast hint
  omega

/-- Recursive form of the chosen terminating expression:
`[a₀; a, pref, 1] = a₀ + 1 / [a; pref, 1]`. -/
theorem simpleCFTerminatingExpressionValue_cons
    (a₀ : ℕ) (a : positiveNat) (pref : finseq positiveNat) :
    simpleCFTerminatingExpressionValue a₀ (a :: pref) =
      (a₀ : ℝ) + 1 / simpleCFTerminatingExpressionValue a.1 pref := by
  simp [simpleCFTerminatingExpressionValue, simpleCFTerminatingTailValue]

/-- A terminating expression always lies strictly above its integer part. -/
theorem simpleCFTerminatingExpressionValue_gt_integerPart
    (a₀ : ℕ) (pref : finseq positiveNat) :
    (a₀ : ℝ) < simpleCFTerminatingExpressionValue a₀ pref := by
  have htail : 0 < simpleCFTerminatingTailValue pref (1 : ℝ) :=
    simpleCFTerminatingTailValue_pos_of_pos pref zero_lt_one
  simp [simpleCFTerminatingExpressionValue]
  linarith

/-- Chosen terminating continued-fraction expressions are positive. -/
theorem simpleCFTerminatingExpressionValue_pos
    (a₀ : ℕ) (pref : finseq positiveNat) :
    0 < simpleCFTerminatingExpressionValue a₀ pref := by
  exact lt_of_le_of_lt (by exact_mod_cast Nat.zero_le a₀)
    (simpleCFTerminatingExpressionValue_gt_integerPart a₀ pref)

/-- A nonempty terminating expression lies strictly inside the integer cell
`(a₀,a₀+1)`. This is the finite rational analogue of the irrational
continued-fraction coordinate cell. -/
theorem simpleCFTerminatingExpressionValue_nonempty_mem_Ioo_integerCell
    (a₀ : ℕ) {pref : finseq positiveNat} (hpref : pref ≠ []) :
    simpleCFTerminatingExpressionValue a₀ pref ∈ Set.Ioo (a₀ : ℝ) ((a₀ : ℝ) + 1) := by
  constructor
  · exact simpleCFTerminatingExpressionValue_gt_integerPart a₀ pref
  · cases pref with
    | nil =>
        exact False.elim (hpref rfl)
    | cons a pref =>
        have htail_lt :
            simpleCFTerminatingTailValue (a :: pref) (1 : ℝ) < 1 :=
          simpleCFTerminatingTailValue_cons_lt_one a pref zero_lt_one
        simp [simpleCFTerminatingExpressionValue]
        linarith

/-- A nonempty chosen terminating expression recovers its integer part by
flooring. This is the first uniqueness step for the final-`1` terminating
continued-fraction convention. -/
theorem simpleCFTerminatingExpressionValue_nonempty_integerPart
    (a₀ : ℕ) {pref : finseq positiveNat} (hpref : pref ≠ []) :
    simpleCFIntegerPart (simpleCFTerminatingExpressionValue a₀ pref) = (a₀ : ℤ) := by
  refine simpleCFIntegerPart_eq_of_mem_Ioo (a₀ := (a₀ : ℤ)) ?_
  simpa using simpleCFTerminatingExpressionValue_nonempty_mem_Ioo_integerCell a₀ hpref

/-- Empty and nonempty chosen terminating expressions are disjoint. -/
theorem simpleCFTerminatingExpressionValue_empty_ne_nonempty
    (a₀ b₀ : ℕ) {pref : finseq positiveNat} (hpref : pref ≠ []) :
    simpleCFTerminatingExpressionValue a₀ [] ≠
      simpleCFTerminatingExpressionValue b₀ pref := by
  intro h
  have hint : ((a₀ + 1 : ℕ) : ℤ) = (b₀ : ℤ) := by
    rw [← simpleCFTerminatingExpressionValue_empty_integerPart a₀, h,
      simpleCFTerminatingExpressionValue_nonempty_integerPart b₀ hpref]
  have hnat : a₀ + 1 = b₀ := by
    exact_mod_cast hint
  have hvalue : simpleCFTerminatingExpressionValue a₀ [] = (b₀ : ℝ) := by
    have hreal : ((a₀ + 1 : ℕ) : ℝ) = (b₀ : ℝ) := by
      exact_mod_cast hnat
    simpa [simpleCFTerminatingExpressionValue_empty] using hreal
  have hgt := simpleCFTerminatingExpressionValue_gt_integerPart b₀ pref
  rw [← h, hvalue] at hgt
  exact (lt_irrefl (b₀ : ℝ)) hgt

/-- Nonempty and empty chosen terminating expressions are disjoint. -/
theorem simpleCFTerminatingExpressionValue_nonempty_ne_empty
    (a₀ b₀ : ℕ) {pref : finseq positiveNat} (hpref : pref ≠ []) :
    simpleCFTerminatingExpressionValue a₀ pref ≠
      simpleCFTerminatingExpressionValue b₀ [] := by
  intro h
  exact simpleCFTerminatingExpressionValue_empty_ne_nonempty b₀ a₀ hpref h.symm

/-- Equal nonempty chosen terminating expressions have the same integer part. -/
theorem simpleCFTerminatingExpressionValue_integerPart_eq_of_eq_nonempty
    {a₀ b₀ : ℕ} {pref qref : finseq positiveNat}
    (hpref : pref ≠ []) (hqref : qref ≠ [])
    (h :
      simpleCFTerminatingExpressionValue a₀ pref =
        simpleCFTerminatingExpressionValue b₀ qref) :
    a₀ = b₀ := by
  have ha :
      simpleCFIntegerPart (simpleCFTerminatingExpressionValue a₀ pref) = (a₀ : ℤ) :=
    simpleCFTerminatingExpressionValue_nonempty_integerPart a₀ hpref
  have hb :
      simpleCFIntegerPart (simpleCFTerminatingExpressionValue b₀ qref) = (b₀ : ℤ) :=
    simpleCFTerminatingExpressionValue_nonempty_integerPart b₀ hqref
  have hint : (a₀ : ℤ) = (b₀ : ℤ) := by
    rw [← ha, h, hb]
  exact_mod_cast hint

/-- The chosen final-`1` terminating continued-fraction expression is
injective in its integer part and finite positive tail. This is the recursive
core behind the book's uniqueness claim for the terminating convention. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For uniqueness, an empty positive prefix has value $a_0+1$, while a nonempty one has value strictly between
    $a_0$ and $a_0+1$. Hence an integer has only the displayed empty-prefix expansion. For a noninteger, the floor
    recovers $a_0$; subtracting it and taking the reciprocal recovers the remaining terminating expression.
    Repeating this step determines all the positive entries, including the final $1$ convention.
-/
theorem simpleCFTerminatingExpressionValue_injective :
    ∀ {a₀ b₀ : ℕ} {pref qref : finseq positiveNat},
      simpleCFTerminatingExpressionValue a₀ pref =
        simpleCFTerminatingExpressionValue b₀ qref →
          a₀ = b₀ ∧ pref = qref := by
  intro a₀ b₀ pref
  induction pref generalizing a₀ b₀ with
  | nil =>
      intro qref h
      cases qref with
      | nil =>
          exact ⟨simpleCFTerminatingExpressionValue_empty_injective h, rfl⟩
      | cons b qref =>
          exact False.elim
            (simpleCFTerminatingExpressionValue_empty_ne_nonempty a₀ b₀ (by simp) h)
  | cons a pref ih =>
      intro qref h
      cases qref with
      | nil =>
          exact False.elim
            (simpleCFTerminatingExpressionValue_nonempty_ne_empty a₀ b₀ (by simp) h)
      | cons b qref =>
          have hhead₀ : a₀ = b₀ :=
            simpleCFTerminatingExpressionValue_integerPart_eq_of_eq_nonempty
              (by simp) (by simp) h
          subst b₀
          have hrec :
              simpleCFTerminatingExpressionValue a.1 pref =
                simpleCFTerminatingExpressionValue b.1 qref := by
            have h' := h
            rw [simpleCFTerminatingExpressionValue_cons,
              simpleCFTerminatingExpressionValue_cons] at h'
            have hfrac :
                1 / simpleCFTerminatingExpressionValue a.1 pref =
                  1 / simpleCFTerminatingExpressionValue b.1 qref := by
              linarith
            have hfracInv :
                (simpleCFTerminatingExpressionValue a.1 pref)⁻¹ =
                  (simpleCFTerminatingExpressionValue b.1 qref)⁻¹ := by
              simpa [one_div] using hfrac
            exact inv_inj.mp hfracInv
          rcases ih hrec with ⟨habNat, hpref⟩
          have hab : a = b := by
            exact Subtype.ext habNat
          subst b
          subst qref
          exact ⟨rfl, rfl⟩

/-- The chosen terminating-expression labels are closed under the left
Stern--Brocot move `q ↦ q/(q+1)`. -/
theorem simpleCFTerminatingExpressionValue_leftMove_exists
    (a₀ : ℕ) (pref : finseq positiveNat) :
    ∃ pref' : finseq positiveNat,
      simpleCFTerminatingExpressionValue 0 pref' =
        simpleCFTerminatingExpressionValue a₀ pref /
          (simpleCFTerminatingExpressionValue a₀ pref + 1) := by
  cases a₀ with
  | zero =>
      cases pref with
      | nil =>
          refine ⟨[⟨1, by omega⟩], ?_⟩
          norm_num [simpleCFTerminatingExpressionValue, simpleCFTerminatingTailValue]
      | cons a pref =>
          let b : positiveNat := ⟨a.1 + 1, by omega⟩
          refine ⟨b :: pref, ?_⟩
          have hx : simpleCFTerminatingExpressionValue a.1 pref ≠ 0 :=
            ne_of_gt (simpleCFTerminatingExpressionValue_pos a.1 pref)
          have hb :
              simpleCFTerminatingExpressionValue b.1 pref =
                simpleCFTerminatingExpressionValue a.1 pref + 1 := by
            simp [b, simpleCFTerminatingExpressionValue]
            ring
          rw [simpleCFTerminatingExpressionValue_cons,
            simpleCFTerminatingExpressionValue_cons, hb]
          field_simp [hx]
          ring
  | succ n =>
      let one : positiveNat := ⟨1, by omega⟩
      let a : positiveNat := ⟨n + 1, by omega⟩
      refine ⟨one :: a :: pref, ?_⟩
      have hx : simpleCFTerminatingExpressionValue (n + 1) pref ≠ 0 :=
        ne_of_gt (simpleCFTerminatingExpressionValue_pos (n + 1) pref)
      rw [simpleCFTerminatingExpressionValue_cons,
        simpleCFTerminatingExpressionValue_cons]
      simp [one, a]
      field_simp [hx]

/-- Equal nonempty finite-cylinder Stern--Brocot labels have the same integer
part. This lifts the terminating-expression uniqueness step back to rational
labels. -/
theorem sternBrocotFiniteCylinderLabel_integerPart_eq_of_eq_nonempty
    {a₀ b₀ : ℕ} {pref qref : finseq positiveNat}
    (hpref : pref ≠ []) (hqref : qref ≠ [])
    (h :
      sternBrocotFiniteCylinderLabel a₀ pref =
        sternBrocotFiniteCylinderLabel b₀ qref) :
    a₀ = b₀ := by
  apply simpleCFTerminatingExpressionValue_integerPart_eq_of_eq_nonempty hpref hqref
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) h
  change ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) =
    ((sternBrocotFiniteCylinderLabel b₀ qref : ℚ) : ℝ) at hreal
  rw [sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue a₀ pref,
    sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue b₀ qref] at hreal
  exact hreal

/-- The finite-cylinder Stern--Brocot label function is injective in the
integer part and finite positive tail under the chosen final-`1` convention. -/
theorem sternBrocotFiniteCylinderLabel_injective :
    ∀ {a₀ b₀ : ℕ} {pref qref : finseq positiveNat},
      sternBrocotFiniteCylinderLabel a₀ pref =
        sternBrocotFiniteCylinderLabel b₀ qref →
          a₀ = b₀ ∧ pref = qref := by
  intro a₀ b₀ pref qref h
  apply simpleCFTerminatingExpressionValue_injective
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) h
  change ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) =
    ((sternBrocotFiniteCylinderLabel b₀ qref : ℚ) : ℝ) at hreal
  rw [sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue a₀ pref,
    sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue b₀ qref] at hreal
  exact hreal

/-- Finite-cylinder Stern--Brocot labels are closed under the left move
`q ↦ q/(q+1)`. -/
theorem sternBrocotFiniteCylinderLabel_leftMove_exists
    (a₀ : ℕ) (pref : finseq positiveNat) :
    ∃ pref' : finseq positiveNat,
      sternBrocotFiniteCylinderLabel 0 pref' =
        sternBrocotFiniteCylinderLabel a₀ pref /
          (sternBrocotFiniteCylinderLabel a₀ pref + 1) := by
  rcases simpleCFTerminatingExpressionValue_leftMove_exists a₀ pref with ⟨pref', hpref'⟩
  refine ⟨pref', ?_⟩
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_div, Rat.cast_add, Rat.cast_one,
    sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue 0 pref',
    sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue a₀ pref]
  exact hpref'

/-- Empty finite-cylinder Stern--Brocot labels are injective in the displayed
integer part. -/
theorem sternBrocotFiniteCylinderLabel_empty_injective :
    Function.Injective (fun a₀ : ℕ => sternBrocotFiniteCylinderLabel a₀ []) := by
  intro a₀ b₀ h
  apply simpleCFTerminatingExpressionValue_empty_injective
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) h
  change ((sternBrocotFiniteCylinderLabel a₀ [] : ℚ) : ℝ) =
    ((sternBrocotFiniteCylinderLabel b₀ [] : ℚ) : ℝ) at hreal
  rw [sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue a₀ [],
    sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue b₀ []] at hreal
  exact hreal

/-- Empty and nonempty finite-cylinder Stern--Brocot labels are disjoint. -/
theorem sternBrocotFiniteCylinderLabel_empty_ne_nonempty
    (a₀ b₀ : ℕ) {pref : finseq positiveNat} (hpref : pref ≠ []) :
    sternBrocotFiniteCylinderLabel a₀ [] ≠
      sternBrocotFiniteCylinderLabel b₀ pref := by
  intro h
  apply simpleCFTerminatingExpressionValue_empty_ne_nonempty a₀ b₀ hpref
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) h
  change ((sternBrocotFiniteCylinderLabel a₀ [] : ℚ) : ℝ) =
    ((sternBrocotFiniteCylinderLabel b₀ pref : ℚ) : ℝ) at hreal
  rw [sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue a₀ [],
    sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue b₀ pref] at hreal
  exact hreal

/-- Nonempty and empty finite-cylinder Stern--Brocot labels are disjoint. -/
theorem sternBrocotFiniteCylinderLabel_nonempty_ne_empty
    (a₀ b₀ : ℕ) {pref : finseq positiveNat} (hpref : pref ≠ []) :
    sternBrocotFiniteCylinderLabel a₀ pref ≠
      sternBrocotFiniteCylinderLabel b₀ [] := by
  intro h
  exact sternBrocotFiniteCylinderLabel_empty_ne_nonempty b₀ a₀ hpref h.symm

/-- Any infinite positive-partial-quotient tail extending a finite prefix computes
the same finite-cylinder Stern--Brocot label. -/
theorem sternBrocotFiniteCylinderLabel_eq_nodeLabel_of_mem_cyl
    (a₀ : ℕ) (pref : finseq positiveNat) {s : ℕ → positiveNat}
    (hs : s ∈ cyl pref) :
    sternBrocotFiniteCylinderLabel a₀ pref =
      sternBrocotNodeLabel a₀ (positiveNatSeqPartials s) pref.length := by
  exact sternBrocotNodeLabel_eq_of_mem_same_cylinder a₀ pref
    (extendFinseq_mem_cyl pref) hs

/-- The finite-cylinder label is realized by an actual infinite positive
continued-fraction tail extending the prefix. -/
theorem sternBrocotFiniteCylinderLabel_realized
    (a₀ : ℕ) (pref : finseq positiveNat) :
    ∃ s : ℕ → positiveNat,
      s ∈ cyl pref ∧
        sternBrocotFiniteCylinderLabel a₀ pref =
          sternBrocotNodeLabel a₀ (positiveNatSeqPartials s) pref.length := by
  exact ⟨extendFinseq pref, extendFinseq_mem_cyl pref, rfl⟩

/-- The empty-prefix finite-cylinder label gives the terminating convention
`m = [m - 1; 1]` for positive integers. -/
theorem sternBrocotFiniteCylinderLabel_empty_positiveInteger
    {m : ℕ} (hm : 0 < m) :
    sternBrocotFiniteCylinderLabel (m - 1) [] = (m : ℚ) := by
  exact sternBrocotNodeLabel_positiveInteger hm
    (positiveNatSeqPartials (extendFinseq ([] : finseq positiveNat)))

/-- The empty-prefix finite-cylinder label is `[a₀; 1] = a₀ + 1`. -/
theorem sternBrocotFiniteCylinderLabel_empty (a₀ : ℕ) :
    sternBrocotFiniteCylinderLabel a₀ [] = ((a₀ + 1 : ℕ) : ℚ) := by
  have h := sternBrocotFiniteCylinderLabel_empty_positiveInteger
    (m := a₀ + 1) (by omega)
  simpa using h

theorem simpleCFShiftedSemiconvergent_pos_of_nonneg {a₀ : ℤ} {a : ℕ → ℤ}
    (ha₀ : 0 ≤ a₀) (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ}
    (hk : 0 < k) :
    0 < simpleCFShiftedSemiconvergent a₀ a n k := by
  unfold simpleCFShiftedSemiconvergent
  exact div_pos
    (by exact_mod_cast simpleCFShiftedSemiconvergentNum_pos_of_nonneg ha₀ ha n hk)
    (by exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk)

/-- Stern--Brocot node labels lie in the positive rationals. -/
theorem sternBrocotNodeLabel_pos {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ : ℕ) (n : ℕ) :
    0 < sternBrocotNodeLabel a₀ a n := by
  exact simpleCFShiftedSemiconvergent_pos_of_nonneg
    (by exact_mod_cast Nat.zero_le a₀) ha n (by norm_num : 0 < (1 : ℕ))

/-- Finite continued-fraction cylinder labels are positive rationals. -/
theorem sternBrocotFiniteCylinderLabel_pos
    (a₀ : ℕ) (pref : finseq positiveNat) :
    0 < sternBrocotFiniteCylinderLabel a₀ pref := by
  exact sternBrocotNodeLabel_pos
    (positiveNatSeqPartials_positive (extendFinseq pref)) a₀ pref.length

/-- Increasing the integer part of a finite continued-fraction label by one
performs the Stern--Brocot right Möbius move `q ↦ q + 1` on that node label. -/
theorem sternBrocotNodeLabel_succ_integerPart {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ n : ℕ) :
    sternBrocotNodeLabel (a₀ + 1) a n = sternBrocotNodeLabel a₀ a n + 1 := by
  rw [sternBrocotNodeLabel, sternBrocotNodeLabel,
    simpleCFShiftedSemiconvergent_eq_intCast_add ha ((a₀ + 1 : ℕ) : ℤ) n
      (by norm_num : 0 < (1 : ℕ)),
    simpleCFShiftedSemiconvergent_eq_intCast_add ha (a₀ : ℤ) n
      (by norm_num : 0 < (1 : ℕ))]
  norm_num
  ring

/-- Increasing the integer part of a finite-cylinder label performs the right
Stern--Brocot move `q ↦ q+1`. -/
theorem sternBrocotFiniteCylinderLabel_succ_integerPart
    (a₀ : ℕ) (pref : finseq positiveNat) :
    sternBrocotFiniteCylinderLabel (a₀ + 1) pref =
      sternBrocotFiniteCylinderLabel a₀ pref + 1 := by
  exact sternBrocotNodeLabel_succ_integerPart
    (positiveNatSeqPartials_positive (extendFinseq pref)) a₀ pref.length

/-- Non-root labels in the `L`-subtree, equivalently the `a₀ = 0` integer cell
with a nonempty finite tail prefix, lie in `(0,1)`. -/
theorem sternBrocotNodeLabel_zero_mem_Ioo_zero_one {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n : ℕ} (hn : 0 < n) :
    ((sternBrocotNodeLabel 0 a n : ℚ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  change ((simpleCFShiftedSemiconvergent (0 : ℤ) a n 1 : ℚ) : ℝ) ∈
    Set.Ioo (0 : ℝ) 1
  rw [simpleCFShiftedSemiconvergent_eq_intCast_add
    ha (0 : ℤ) n (by norm_num : 0 < (1 : ℕ))]
  norm_num
  rcases simpleCFSemiconvergent_mem_Ioo_zero_one_of_positive ha hn
      (by norm_num : 0 < (1 : ℕ)) with
    ⟨hpos, hlt⟩
  exact ⟨by exact_mod_cast hpos, hlt⟩

theorem simpleCFSemiconvergent_endpoint_determinant
    (a : ℕ → ℤ) (n k : ℕ) :
    simpleCFNum a (n + 1) * simpleCFSemiconvergentDen a n k -
        simpleCFDen a (n + 1) * simpleCFSemiconvergentNum a n k =
      (-1 : ℤ) ^ (n + 1) := by
  have hdet := simpleCF_determinant a n
  calc
    simpleCFNum a (n + 1) * simpleCFSemiconvergentDen a n k -
        simpleCFDen a (n + 1) * simpleCFSemiconvergentNum a n k
        = simpleCFNum a (n + 1) * simpleCFDen a n -
            simpleCFNum a n * simpleCFDen a (n + 1) := by
          simp [simpleCFSemiconvergentNum, simpleCFSemiconvergentDen]
          ring
    _ = (-1 : ℤ) ^ (n + 1) := hdet

theorem abs_simpleCFSemiconvergent_endpoint_determinant
    (a : ℕ → ℤ) (n k : ℕ) :
    |simpleCFNum a (n + 1) * simpleCFSemiconvergentDen a n k -
        simpleCFDen a (n + 1) * simpleCFSemiconvergentNum a n k| =
      (1 : ℤ) := by
  rw [simpleCFSemiconvergent_endpoint_determinant]
  exact abs_neg_one_pow (n + 1)

theorem simpleCFSemiconvergent_endpoint_fareyNeighbor
    (a : ℕ → ℤ) (n k : ℕ) :
    fareyNeighbor (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
      (simpleCFSemiconvergentNum a n k) (simpleCFSemiconvergentDen a n k) := by
  rw [fareyNeighbor, simpleCFSemiconvergent_endpoint_determinant]
  exact abs_neg_one_pow (n + 1)

theorem abs_simpleCFSemiconvergent_sub_endpoint {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    |(simpleCFSemiconvergent a n k : ℝ) - simpleCFEndpoint a n| =
      1 / ((simpleCFDen a (n + 1) : ℝ) *
        (simpleCFSemiconvergentDen a n k : ℝ)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsub := simpleCFTailMap_sub_endpoint ha n (x := (k : ℝ)) hkR
  rw [simpleCFTailMap_natCast_eq_semiconvergent] at hsub
  have hden_eq :
      (k : ℝ) * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) =
        (simpleCFSemiconvergentDen a n k : ℝ) := by
    simp [simpleCFSemiconvergentDen]
  rw [hden_eq] at hsub
  have hprod_pos :
      0 < (simpleCFDen a (n + 1) : ℝ) *
        (simpleCFSemiconvergentDen a n k : ℝ) := by
    exact mul_pos
      (by exact_mod_cast simpleCFDen_pos_of_positive ha n)
      (by exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk)
  calc
    |(simpleCFSemiconvergent a n k : ℝ) - simpleCFEndpoint a n|
        = |((-1 : ℝ) ^ n /
            ((simpleCFDen a (n + 1) : ℝ) *
              (simpleCFSemiconvergentDen a n k : ℝ)))| := by
          rw [hsub]
    _ = |(-1 : ℝ) ^ n| /
          |(simpleCFDen a (n + 1) : ℝ) *
            (simpleCFSemiconvergentDen a n k : ℝ)| := by
          rw [abs_div]
    _ = 1 / ((simpleCFDen a (n + 1) : ℝ) *
          (simpleCFSemiconvergentDen a n k : ℝ)) := by
          rw [abs_neg_one_pow, abs_of_pos hprod_pos]

theorem simpleCFTailMap_sub_semiconvergent {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx : 0 < x) :
    simpleCFTailMap a n x - (simpleCFSemiconvergent a n k : ℝ) =
      (x - (k : ℝ)) * (-1 : ℝ) ^ (n + 1) /
        ((x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
          (simpleCFSemiconvergentDen a n k : ℝ)) := by
  have htail :
      x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) ≠ 0 :=
    ne_of_gt (simpleCFTailMap_denom_pos_of_positive ha n x hx)
  have hsemi_int : simpleCFSemiconvergentDen a n k ≠ 0 :=
    ne_of_gt (simpleCFSemiconvergentDen_pos_of_positive ha n hk)
  have hsemi : (simpleCFSemiconvergentDen a n k : ℝ) ≠ 0 := by
    exact_mod_cast hsemi_int
  have hsemi_exp :
      (simpleCFDen a (n + 1) : ℝ) * (k : ℝ) + (simpleCFDen a n : ℝ) ≠ 0 := by
    simpa [simpleCFSemiconvergentDen, mul_comm, mul_left_comm, mul_assoc] using hsemi
  have hdetR :
      (simpleCFNum a (n + 1) : ℝ) * (simpleCFDen a n : ℝ) -
        (simpleCFNum a n : ℝ) * (simpleCFDen a (n + 1) : ℝ) =
        (-1 : ℝ) ^ (n + 1) := by
    exact_mod_cast simpleCF_determinant a n
  unfold simpleCFTailMap simpleCFSemiconvergent
    simpleCFSemiconvergentNum simpleCFSemiconvergentDen
  norm_num [Rat.cast_div]
  field_simp [htail, hsemi_exp]
  linear_combination (x - (k : ℝ)) * hdetR

theorem simpleCFSemiconvergent_common_divisor_dvd_one
    (a : ℕ → ℤ) (n k : ℕ) {d : ℤ}
    (hnum : d ∣ simpleCFSemiconvergentNum a n k)
    (hden : d ∣ simpleCFSemiconvergentDen a n k) :
    d ∣ (1 : ℤ) := by
  have hdiff :
      d ∣ simpleCFNum a (n + 1) * simpleCFSemiconvergentDen a n k -
          simpleCFDen a (n + 1) * simpleCFSemiconvergentNum a n k :=
    dvd_sub (dvd_mul_of_dvd_right hden _) (dvd_mul_of_dvd_right hnum _)
  rw [simpleCFSemiconvergent_endpoint_determinant] at hdiff
  have hunit : IsUnit ((-1 : ℤ) ^ (n + 1)) := by
    rw [Int.isUnit_iff]
    exact neg_one_pow_eq_or ℤ (n + 1)
  exact dvd_trans hdiff (isUnit_iff_dvd_one.mp hunit)

theorem simpleCFSemiconvergent_lowestTerms
    (a : ℕ → ℤ) (n k : ℕ) {d : ℤ}
    (hnum : d ∣ simpleCFSemiconvergentNum a n k)
    (hden : d ∣ simpleCFSemiconvergentDen a n k) :
    d ∣ (1 : ℤ) :=
  simpleCFSemiconvergent_common_divisor_dvd_one a n k hnum hden

theorem simpleCFShiftedSemiconvergent_common_divisor_dvd_one
    (a₀ : ℤ) (a : ℕ → ℤ) (n k : ℕ) {d : ℤ}
    (hnum : d ∣ simpleCFShiftedSemiconvergentNum a₀ a n k)
    (hden : d ∣ simpleCFSemiconvergentDen a n k) :
    d ∣ (1 : ℤ) := by
  have hnum₀ :
      d ∣ simpleCFShiftedSemiconvergentNum a₀ a n k -
        a₀ * simpleCFSemiconvergentDen a n k :=
    dvd_sub hnum (dvd_mul_of_dvd_right hden a₀)
  have hsemi_num : d ∣ simpleCFSemiconvergentNum a n k := by
    simpa [simpleCFShiftedSemiconvergentNum] using hnum₀
  exact simpleCFSemiconvergent_common_divisor_dvd_one a n k hsemi_num hden

theorem simpleCFShiftedSemiconvergent_lowestTerms
    (a₀ : ℤ) (a : ℕ → ℤ) (n k : ℕ) {d : ℤ}
    (hnum : d ∣ simpleCFShiftedSemiconvergentNum a₀ a n k)
    (hden : d ∣ simpleCFSemiconvergentDen a n k) :
    d ∣ (1 : ℤ) :=
  simpleCFShiftedSemiconvergent_common_divisor_dvd_one a₀ a n k hnum hden

/-- The Stern--Brocot node label is in lowest terms, in the divisor form used by the
continued-fraction determinant calculation. -/
theorem sternBrocotNodeLabel_lowestTerms
    (a₀ : ℕ) (a : ℕ → ℤ) (n : ℕ) {d : ℤ}
    (hnum : d ∣ simpleCFShiftedSemiconvergentNum (a₀ : ℤ) a n 1)
    (hden : d ∣ simpleCFSemiconvergentDen a n 1) :
    d ∣ (1 : ℤ) :=
  simpleCFShiftedSemiconvergent_lowestTerms (a₀ : ℤ) a n 1 hnum hden

/-- A non-root finite cylinder in the `L`-subtree has a well-defined Stern--Brocot
label, and that label is a rational in `(0,1)` written in lowest terms. This is
the Lean form of the book's statement that the Farey-tree nodes are the rationals
in `(0,1)` in lowest terms, on the finite-node side. -/
theorem sternBrocotLSubtreeFiniteCylinderLabel_wellDefined_mem_Ioo_lowestTerms
    {pref : finseq positiveNat} (hpref : pref ≠ [])
    {s t : ℕ → positiveNat} (hs : s ∈ cyl pref) (ht : t ∈ cyl pref) :
    sternBrocotNodeLabel 0 (positiveNatSeqPartials s) pref.length =
        sternBrocotNodeLabel 0 (positiveNatSeqPartials t) pref.length ∧
      ((sternBrocotNodeLabel 0 (positiveNatSeqPartials s) pref.length : ℚ) : ℝ) ∈
        Set.Ioo (0 : ℝ) 1 ∧
      ∀ d : ℤ,
        d ∣ simpleCFShiftedSemiconvergentNum (0 : ℤ)
            (positiveNatSeqPartials s) pref.length 1 →
          d ∣ simpleCFSemiconvergentDen (positiveNatSeqPartials s) pref.length 1 →
            d ∣ (1 : ℤ) := by
  have hlen : 0 < pref.length := List.length_pos_of_ne_nil hpref
  refine ⟨sternBrocotNodeLabel_eq_of_mem_same_cylinder 0 pref hs ht, ?_, ?_⟩
  · exact sternBrocotNodeLabel_zero_mem_Ioo_zero_one
      (positiveNatSeqPartials_positive s) (n := pref.length) hlen
  · intro d hnum hden
    exact sternBrocotNodeLabel_lowestTerms 0 (positiveNatSeqPartials s) pref.length hnum hden

theorem simpleCFSemiconvergent_adjacent_determinant
    (a : ℕ → ℤ) (n k : ℕ) :
    simpleCFSemiconvergentNum a n k * simpleCFSemiconvergentDen a n (k + 1) -
        simpleCFSemiconvergentDen a n k * simpleCFSemiconvergentNum a n (k + 1) =
      (-1 : ℤ) ^ n := by
  have hdet := simpleCF_determinant a n
  calc
    simpleCFSemiconvergentNum a n k * simpleCFSemiconvergentDen a n (k + 1) -
        simpleCFSemiconvergentDen a n k * simpleCFSemiconvergentNum a n (k + 1)
        = simpleCFNum a n * simpleCFDen a (n + 1) -
            simpleCFNum a (n + 1) * simpleCFDen a n := by
          simp [simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, Nat.cast_add]
          ring
    _ = (-1 : ℤ) ^ n := by
      calc
        simpleCFNum a n * simpleCFDen a (n + 1) -
            simpleCFNum a (n + 1) * simpleCFDen a n
            = -(simpleCFNum a (n + 1) * simpleCFDen a n -
                simpleCFNum a n * simpleCFDen a (n + 1)) := by
              ring
        _ = -((-1 : ℤ) ^ (n + 1)) := by rw [hdet]
        _ = (-1 : ℤ) ^ n := by
          rw [pow_succ]
          ring

theorem abs_simpleCFSemiconvergent_adjacent_determinant
    (a : ℕ → ℤ) (n k : ℕ) :
    |simpleCFSemiconvergentNum a n k * simpleCFSemiconvergentDen a n (k + 1) -
        simpleCFSemiconvergentDen a n k * simpleCFSemiconvergentNum a n (k + 1)| =
      (1 : ℤ) := by
  rw [simpleCFSemiconvergent_adjacent_determinant]
  exact abs_neg_one_pow n

theorem simpleCFSemiconvergent_adjacent_fareyNeighbor
    (a : ℕ → ℤ) (n k : ℕ) :
    fareyNeighbor (simpleCFSemiconvergentNum a n k)
      (simpleCFSemiconvergentDen a n k)
      (simpleCFSemiconvergentNum a n (k + 1))
      (simpleCFSemiconvergentDen a n (k + 1)) := by
  rw [fareyNeighbor, simpleCFSemiconvergent_adjacent_determinant]
  exact abs_neg_one_pow n

/-- Translating adjacent semiconvergent cut points by an integer cell preserves
the adjacent determinant. -/
theorem simpleCFShiftedSemiconvergent_adjacent_determinant
    (a₀ : ℤ) (a : ℕ → ℤ) (n k : ℕ) :
    simpleCFShiftedSemiconvergentNum a₀ a n k * simpleCFSemiconvergentDen a n (k + 1) -
        simpleCFSemiconvergentDen a n k *
          simpleCFShiftedSemiconvergentNum a₀ a n (k + 1) =
      (-1 : ℤ) ^ n := by
  calc
    simpleCFShiftedSemiconvergentNum a₀ a n k * simpleCFSemiconvergentDen a n (k + 1) -
        simpleCFSemiconvergentDen a n k *
          simpleCFShiftedSemiconvergentNum a₀ a n (k + 1)
        = simpleCFSemiconvergentNum a n k * simpleCFSemiconvergentDen a n (k + 1) -
            simpleCFSemiconvergentDen a n k *
              simpleCFSemiconvergentNum a n (k + 1) := by
          simp [simpleCFShiftedSemiconvergentNum]
          ring
    _ = (-1 : ℤ) ^ n :=
      simpleCFSemiconvergent_adjacent_determinant a n k

/-- Adjacent translated Stern--Brocot cut points are Farey neighbors in the
integer cell. -/
theorem simpleCFShiftedSemiconvergent_adjacent_fareyNeighbor
    (a₀ : ℤ) (a : ℕ → ℤ) (n k : ℕ) :
    fareyNeighbor (simpleCFShiftedSemiconvergentNum a₀ a n k)
      (simpleCFSemiconvergentDen a n k)
      (simpleCFShiftedSemiconvergentNum a₀ a n (k + 1))
      (simpleCFSemiconvergentDen a n (k + 1)) := by
  rw [fareyNeighbor, simpleCFShiftedSemiconvergent_adjacent_determinant]
  exact abs_neg_one_pow n

theorem simpleCFSemiconvergent_adjacent_sub {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    (simpleCFSemiconvergent a n (k + 1) : ℝ) -
        (simpleCFSemiconvergent a n k : ℝ) =
      -((-1 : ℝ) ^ n) /
        ((simpleCFSemiconvergentDen a n k : ℝ) *
          (simpleCFSemiconvergentDen a n (k + 1) : ℝ)) := by
  have hden₀_int : simpleCFSemiconvergentDen a n k ≠ 0 :=
    ne_of_gt (simpleCFSemiconvergentDen_pos_of_positive ha n hk)
  have hden₁_int : simpleCFSemiconvergentDen a n (k + 1) ≠ 0 :=
    ne_of_gt (simpleCFSemiconvergentDen_pos_of_positive ha n (Nat.succ_pos k))
  have hden₀ : (simpleCFSemiconvergentDen a n k : ℝ) ≠ 0 := by
    exact_mod_cast hden₀_int
  have hden₁ : (simpleCFSemiconvergentDen a n (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast hden₁_int
  have hdetR :
      (simpleCFSemiconvergentNum a n k : ℝ) *
          (simpleCFSemiconvergentDen a n (k + 1) : ℝ) -
        (simpleCFSemiconvergentDen a n k : ℝ) *
          (simpleCFSemiconvergentNum a n (k + 1) : ℝ) =
        (-1 : ℝ) ^ n := by
    exact_mod_cast simpleCFSemiconvergent_adjacent_determinant a n k
  unfold simpleCFSemiconvergent
  norm_num [Rat.cast_div]
  field_simp [hden₀, hden₁]
  linear_combination -hdetR

theorem abs_simpleCFSemiconvergent_adjacent_sub {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    |(simpleCFSemiconvergent a n (k + 1) : ℝ) -
        (simpleCFSemiconvergent a n k : ℝ)| =
      1 / ((simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ)) := by
  have hprod_pos :
      0 < (simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ) := by
    exact mul_pos
      (by exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk)
      (by
        exact_mod_cast
          simpleCFSemiconvergentDen_pos_of_positive ha n (Nat.succ_pos k))
  have hsub := simpleCFSemiconvergent_adjacent_sub ha n hk
  calc
    |(simpleCFSemiconvergent a n (k + 1) : ℝ) -
        (simpleCFSemiconvergent a n k : ℝ)|
        = |(-((-1 : ℝ) ^ n) /
            ((simpleCFSemiconvergentDen a n k : ℝ) *
              (simpleCFSemiconvergentDen a n (k + 1) : ℝ)))| := by
          rw [hsub]
    _ = |(-((-1 : ℝ) ^ n))| /
          |(simpleCFSemiconvergentDen a n k : ℝ) *
            (simpleCFSemiconvergentDen a n (k + 1) : ℝ)| := by
          rw [abs_div]
    _ = 1 / ((simpleCFSemiconvergentDen a n k : ℝ) *
          (simpleCFSemiconvergentDen a n (k + 1) : ℝ)) := by
          rw [abs_neg, abs_neg_one_pow, abs_of_pos hprod_pos]

/-- Translating adjacent Stern--Brocot cut points does not change their real
gap length. -/
theorem abs_simpleCFShiftedSemiconvergent_adjacent_sub {a₀ : ℤ} {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    |(simpleCFShiftedSemiconvergent a₀ a n (k + 1) : ℝ) -
        (simpleCFShiftedSemiconvergent a₀ a n k : ℝ)| =
      1 / ((simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ)) := by
  have hsucc :
      simpleCFShiftedSemiconvergent a₀ a n (k + 1) =
        (a₀ : ℚ) + simpleCFSemiconvergent a n (k + 1) :=
    simpleCFShiftedSemiconvergent_eq_intCast_add ha a₀ n (Nat.succ_pos k)
  have hk_eq :
      simpleCFShiftedSemiconvergent a₀ a n k =
        (a₀ : ℚ) + simpleCFSemiconvergent a n k :=
    simpleCFShiftedSemiconvergent_eq_intCast_add ha a₀ n hk
  calc
    |(simpleCFShiftedSemiconvergent a₀ a n (k + 1) : ℝ) -
        (simpleCFShiftedSemiconvergent a₀ a n k : ℝ)|
        = |(simpleCFSemiconvergent a n (k + 1) : ℝ) -
            (simpleCFSemiconvergent a n k : ℝ)| := by
          rw [hsucc, hk_eq]
          norm_num
    _ = 1 / ((simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ)) :=
      abs_simpleCFSemiconvergent_adjacent_sub ha n hk

theorem simpleCFSemiconvergent_adjacent_lt_of_even {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n k : ℕ} (hn : Even n) (hk : 0 < k) :
    (simpleCFSemiconvergent a n (k + 1) : ℝ) <
      (simpleCFSemiconvergent a n k : ℝ) := by
  have hsub := simpleCFSemiconvergent_adjacent_sub ha n hk
  have hprod_pos :
      0 < (simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ) := by
    exact mul_pos
      (by exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk)
      (by
        exact_mod_cast
          simpleCFSemiconvergentDen_pos_of_positive ha n (Nat.succ_pos k))
  rw [hn.neg_one_pow] at hsub
  have hneg :
      -1 / ((simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ)) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hprod_pos
  linarith

theorem simpleCFSemiconvergent_lt_adjacent_of_odd {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n k : ℕ} (hn : Odd n) (hk : 0 < k) :
    (simpleCFSemiconvergent a n k : ℝ) <
      (simpleCFSemiconvergent a n (k + 1) : ℝ) := by
  have hsub := simpleCFSemiconvergent_adjacent_sub ha n hk
  have hprod_pos :
      0 < (simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ) := by
    exact mul_pos
      (by exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk)
      (by
        exact_mod_cast
          simpleCFSemiconvergentDen_pos_of_positive ha n (Nat.succ_pos k))
  rw [hn.neg_one_pow] at hsub
  have hpos :
      0 < 1 / ((simpleCFSemiconvergentDen a n k : ℝ) *
        (simpleCFSemiconvergentDen a n (k + 1) : ℝ)) :=
    one_div_pos.mpr hprod_pos
  linarith

/-- In an integer cell, translated adjacent semiconvergents are ordered as the
book's child-cylinder formula states when the prefix length is even. -/
theorem simpleCFShiftedSemiconvergent_adjacent_lt_of_even {a₀ : ℤ} {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n k : ℕ} (hn : Even n) (hk : 0 < k) :
    (simpleCFShiftedSemiconvergent a₀ a n (k + 1) : ℝ) <
      (simpleCFShiftedSemiconvergent a₀ a n k : ℝ) := by
  have hsucc :
      simpleCFShiftedSemiconvergent a₀ a n (k + 1) =
        (a₀ : ℚ) + simpleCFSemiconvergent a n (k + 1) :=
    simpleCFShiftedSemiconvergent_eq_intCast_add ha a₀ n (Nat.succ_pos k)
  have hkq :
      simpleCFShiftedSemiconvergent a₀ a n k =
        (a₀ : ℚ) + simpleCFSemiconvergent a n k :=
    simpleCFShiftedSemiconvergent_eq_intCast_add ha a₀ n hk
  rw [hsucc, hkq]
  norm_num [Rat.cast_add]
  exact_mod_cast simpleCFSemiconvergent_adjacent_lt_of_even ha hn hk

/-- In an integer cell, translated adjacent semiconvergents are ordered as the
book's child-cylinder formula states when the prefix length is odd. -/
theorem simpleCFShiftedSemiconvergent_lt_adjacent_of_odd {a₀ : ℤ} {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n k : ℕ} (hn : Odd n) (hk : 0 < k) :
    (simpleCFShiftedSemiconvergent a₀ a n k : ℝ) <
      (simpleCFShiftedSemiconvergent a₀ a n (k + 1) : ℝ) := by
  have hkq :
      simpleCFShiftedSemiconvergent a₀ a n k =
        (a₀ : ℚ) + simpleCFSemiconvergent a n k :=
    simpleCFShiftedSemiconvergent_eq_intCast_add ha a₀ n hk
  have hsucc :
      simpleCFShiftedSemiconvergent a₀ a n (k + 1) =
        (a₀ : ℚ) + simpleCFSemiconvergent a n (k + 1) :=
    simpleCFShiftedSemiconvergent_eq_intCast_add ha a₀ n (Nat.succ_pos k)
  rw [hkq, hsucc]
  norm_num [Rat.cast_add]
  exact_mod_cast simpleCFSemiconvergent_lt_adjacent_of_odd ha hn hk

theorem simpleCFTailMap_mem_semiconvergent_interval_of_mem_Ioo {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx : x ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ)) :
    simpleCFTailMap a n x ∈
      if Even n then
        Set.Ioo (simpleCFSemiconvergent a n (k + 1) : ℝ)
          (simpleCFSemiconvergent a n k : ℝ)
      else
        Set.Ioo (simpleCFSemiconvergent a n k : ℝ)
          (simpleCFSemiconvergent a n (k + 1) : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hxpos : 0 < x := hkR.trans hx.1
  have htailpos :
      0 < x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ) :=
    simpleCFTailMap_denom_pos_of_positive ha n x hxpos
  have hden_k_pos :
      0 <
        (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
          (simpleCFSemiconvergentDen a n k : ℝ) := by
    exact mul_pos htailpos
      (by exact_mod_cast simpleCFSemiconvergentDen_pos_of_positive ha n hk)
  have hden_succ_pos :
      0 <
        (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)) *
          (simpleCFSemiconvergentDen a n (k + 1) : ℝ) := by
    exact mul_pos htailpos
      (by
        exact_mod_cast
          simpleCFSemiconvergentDen_pos_of_positive ha n (Nat.succ_pos k))
  by_cases hn : Even n
  · rw [ite_eq_left hn]
    have hpow : (-1 : ℝ) ^ (n + 1) = -1 := by
      rw [pow_succ, hn.neg_one_pow]
      ring
    have hleft :
        0 < simpleCFTailMap a n x -
          (simpleCFSemiconvergent a n (k + 1) : ℝ) := by
      rw [simpleCFTailMap_sub_semiconvergent ha n (Nat.succ_pos k) hxpos, hpow]
      have hnum : (x - ((k + 1 : ℕ) : ℝ)) * (-1 : ℝ) > 0 := by
        nlinarith [hx.2]
      exact div_pos hnum hden_succ_pos
    have hright :
        simpleCFTailMap a n x - (simpleCFSemiconvergent a n k : ℝ) < 0 := by
      rw [simpleCFTailMap_sub_semiconvergent ha n hk hxpos, hpow]
      have hnum : (x - (k : ℝ)) * (-1 : ℝ) < 0 := by
        nlinarith [hx.1]
      exact div_neg_of_neg_of_pos hnum hden_k_pos
    constructor <;> linarith
  · rw [ite_eq_right hn]
    have hnodd : Odd n := Nat.not_even_iff_odd.1 hn
    have hpow : (-1 : ℝ) ^ (n + 1) = 1 := by
      rw [pow_succ, hnodd.neg_one_pow]
      ring
    have hleft :
        0 < simpleCFTailMap a n x - (simpleCFSemiconvergent a n k : ℝ) := by
      rw [simpleCFTailMap_sub_semiconvergent ha n hk hxpos, hpow]
      have hnum : 0 < (x - (k : ℝ)) * (1 : ℝ) := by
        nlinarith [hx.1]
      exact div_pos hnum hden_k_pos
    have hright :
        simpleCFTailMap a n x -
          (simpleCFSemiconvergent a n (k + 1) : ℝ) < 0 := by
      rw [simpleCFTailMap_sub_semiconvergent ha n (Nat.succ_pos k) hxpos, hpow]
      have hnum : (x - ((k + 1 : ℕ) : ℝ)) * (1 : ℝ) < 0 := by
        nlinarith [hx.2]
      exact div_neg_of_neg_of_pos hnum hden_succ_pos
    constructor <;> linarith

theorem simpleCFTailMap_natCast_add_inv_mem_semiconvergent_interval_of_gt_one
    {a : ℕ → ℤ} (ha : SimpleCFPositivePartials a) (n : ℕ) {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx : 1 < x) :
    simpleCFTailMap a n ((k : ℝ) + 1 / x) ∈
      if Even n then
        Set.Ioo (simpleCFSemiconvergent a n (k + 1) : ℝ)
          (simpleCFSemiconvergent a n k : ℝ)
      else
        Set.Ioo (simpleCFSemiconvergent a n k : ℝ)
          (simpleCFSemiconvergent a n (k + 1) : ℝ) := by
  apply simpleCFTailMap_mem_semiconvergent_interval_of_mem_Ioo ha n hk
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hinv_pos : 0 < 1 / x := one_div_pos.mpr hxpos
  have hinv_lt_one : 1 / x < 1 := by
    rw [div_lt_iff₀ hxpos]
    simpa using hx
  constructor
  · linarith
  · have hsucc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
    rw [hsucc]
    linarith

/-- Book-facing statement for the Stern--Brocot cylinder geometry: semiconvergents
are the rational cut points, the mediant endpoint is the `k = 1` cut point,
endpoint and adjacent cut points are Farey neighbors, the ordered
Farey-neighbor gap formula is available, the translated labels are in lowest
terms, their gaps and parity-dependent order are as in the book, and child
complete quotients lie between the adjacent cut points. -/
def ConcreteSternBrocotCylinderGeometryStatement : Prop :=
    (∀ a : ℕ → ℤ, ∀ n k : ℕ,
      simpleCFTailMap a n (k : ℝ) = (simpleCFSemiconvergent a n k : ℝ)) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ,
        simpleCFSemiconvergent a n 1 =
          rationalMediant (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
            (simpleCFNum a n) (simpleCFDen a n)) ∧
      (∀ a : ℕ → ℤ, ∀ n k : ℕ,
        fareyNeighbor (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
          (simpleCFSemiconvergentNum a n k) (simpleCFSemiconvergentDen a n k)) ∧
      (∀ a : ℕ → ℤ, ∀ n k : ℕ, ∀ d : ℤ,
        d ∣ simpleCFSemiconvergentNum a n k →
          d ∣ simpleCFSemiconvergentDen a n k →
            d ∣ (1 : ℤ)) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n k : ℕ, ∀ d : ℤ,
        d ∣ simpleCFShiftedSemiconvergentNum a₀ a n k →
          d ∣ simpleCFSemiconvergentDen a n k →
            d ∣ (1 : ℤ)) ∧
      (∀ a : ℕ → ℤ, ∀ n k : ℕ,
        fareyNeighbor (simpleCFSemiconvergentNum a n k)
          (simpleCFSemiconvergentDen a n k)
          (simpleCFSemiconvergentNum a n (k + 1))
          (simpleCFSemiconvergentDen a n (k + 1))) ∧
      (∀ p q r s : ℤ, q ≠ 0 → s ≠ 0 → q * r - p * s = 1 →
        (r : ℝ) / (s : ℝ) - (p : ℝ) / (q : ℝ) =
          1 / ((q : ℝ) * (s : ℝ))) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n k : ℕ,
        fareyNeighbor (simpleCFShiftedSemiconvergentNum a₀ a n k)
          (simpleCFSemiconvergentDen a n k)
          (simpleCFShiftedSemiconvergentNum a₀ a n (k + 1))
          (simpleCFSemiconvergentDen a n (k + 1))) ∧
      (∀ a : ℕ → ℤ, ∀ n k : ℕ,
        SimpleCFPositivePartials a → 0 < k →
          |(simpleCFSemiconvergent a n k : ℝ) - simpleCFEndpoint a n| =
            1 / ((simpleCFDen a (n + 1) : ℝ) *
              (simpleCFSemiconvergentDen a n k : ℝ))) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n k : ℕ,
        SimpleCFPositivePartials a → 0 < k →
          |(simpleCFShiftedSemiconvergent a₀ a n (k + 1) : ℝ) -
            (simpleCFShiftedSemiconvergent a₀ a n k : ℝ)| =
            1 / ((simpleCFSemiconvergentDen a n k : ℝ) *
              (simpleCFSemiconvergentDen a n (k + 1) : ℝ))) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n k : ℕ,
        SimpleCFPositivePartials a → Even n → 0 < k →
          (simpleCFShiftedSemiconvergent a₀ a n (k + 1) : ℝ) <
            (simpleCFShiftedSemiconvergent a₀ a n k : ℝ)) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n k : ℕ,
        SimpleCFPositivePartials a → Odd n → 0 < k →
          (simpleCFShiftedSemiconvergent a₀ a n k : ℝ) <
            (simpleCFShiftedSemiconvergent a₀ a n (k + 1) : ℝ)) ∧
      (∀ a : ℕ → ℤ, ∀ n k : ℕ,
        SimpleCFPositivePartials a → 0 < k →
          ∀ x : ℝ, 1 < x →
            simpleCFTailMap a n ((k : ℝ) + 1 / x) ∈
              if Even n then
                Set.Ioo (simpleCFSemiconvergent a n (k + 1) : ℝ)
                  (simpleCFSemiconvergent a n k : ℝ)
              else
                Set.Ioo (simpleCFSemiconvergent a n k : ℝ)
                  (simpleCFSemiconvergent a n (k + 1) : ℝ))

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Adjacent semiconvergents $F_s(k)$ and $F_s(k+1)$ are Farey neighbors for the same determinant reason.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Adjacent semiconvergents $F_s(k)$ and $F_s(k+1)$ are Farey neighbors for the same determinant reason.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Pairs $\tfrac{a}{b}, \tfrac{c}{d}$ with $|bc - ad| = 1$ are \termdefineas{Farey neighbor}{Farey neighbors}. The
    determinant identity $|p_{n+1} q_n - p_n q_{n+1}| = 1$ implies
    $$\left|p_{n+1}(k q_{n+1} + q_n) - q_{n+1}(k p_{n+1} + p_n)\right| = 1,$$
    so every semiconvergent $F_s(k)$ is Farey-adjacent to $\tfrac{p_{n+1}}{q_{n+1}}$ and is therefore in lowest terms.
-/
/-- Book-facing package proving the Stern--Brocot cylinder geometry statement. -/
theorem concreteSternBrocotCylinderGeometryFacts :
    ConcreteSternBrocotCylinderGeometryStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a n k
    exact simpleCFTailMap_natCast_eq_semiconvergent a n k
  · intro a n
    exact simpleCFSemiconvergent_one_eq_mediant a n
  · intro a n k
    exact simpleCFSemiconvergent_endpoint_fareyNeighbor a n k
  · intro a n k d hnum hden
    exact simpleCFSemiconvergent_lowestTerms a n k hnum hden
  · intro a₀ a n k d hnum hden
    exact simpleCFShiftedSemiconvergent_lowestTerms a₀ a n k hnum hden
  · intro a n k
    exact simpleCFSemiconvergent_adjacent_fareyNeighbor a n k
  · intro p q r s hq hs hdet
    exact orderedFareyNeighbor_real_sub_eq_one_div hq hs hdet
  · intro a₀ a n k
    exact simpleCFShiftedSemiconvergent_adjacent_fareyNeighbor a₀ a n k
  · intro a n k ha hk
    exact abs_simpleCFSemiconvergent_sub_endpoint ha n hk
  · intro a₀ a n k ha hk
    exact abs_simpleCFShiftedSemiconvergent_adjacent_sub ha n hk
  · intro a₀ a n k ha hn hk
    exact simpleCFShiftedSemiconvergent_adjacent_lt_of_even ha hn hk
  · intro a₀ a n k ha hn hk
    exact simpleCFShiftedSemiconvergent_lt_adjacent_of_odd ha hn hk
  · intro a n k ha hk x hx
    exact simpleCFTailMap_natCast_add_inv_mem_semiconvergent_interval_of_gt_one ha n hk hx

/-!
## Stern-Brocot finite run-length words

This records the finite L/R word coding used for rational labels in the Stern-Brocot
tree. The final `1` block in the terminating continued fraction is omitted, as in the
book.
-/

inductive sternBrocotDirection where
  | left
  | right
deriving DecidableEq, Repr

abbrev sternBrocotWord : Type :=
  List sternBrocotDirection

/-- Positive rational labels generated from `1` by the two elementary
Stern--Brocot Möbius moves `q ↦ q + 1` and `q ↦ q/(q+1)`. This is the
Euclidean-generation core behind the finite rational labels. -/
inductive sternBrocotTreeLabel : ℚ → Prop
  | root : sternBrocotTreeLabel 1
  | right {q : ℚ} : sternBrocotTreeLabel q → sternBrocotTreeLabel (q + 1)
  | left {q : ℚ} : sternBrocotTreeLabel q → sternBrocotTreeLabel (q / (q + 1))

theorem sternBrocotTreeLabel_pos {q : ℚ} (h : sternBrocotTreeLabel q) :
    0 < q := by
  induction h with
  | root =>
      norm_num
  | right h ih =>
      linarith
  | left h ih =>
      exact div_pos ih (by linarith)

theorem sternBrocotTreeLabel_nat_div (p d : ℕ) (hp : 0 < p) (hd : 0 < d) :
    sternBrocotTreeLabel ((p : ℚ) / (d : ℚ)) := by
  let N := p + d
  suffices hmain :
      ∀ N : ℕ, ∀ p d : ℕ, p + d = N → 0 < p → 0 < d →
        sternBrocotTreeLabel ((p : ℚ) / (d : ℚ)) by
    exact hmain N p d rfl hp hd
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro p d hsum hp hd
      by_cases hpd : p = d
      · subst d
        rw [div_self]
        · exact sternBrocotTreeLabel.root
        · exact_mod_cast ne_of_gt hp
      · by_cases hgt : d < p
        · have hpmd : 0 < p - d := Nat.sub_pos_of_lt hgt
          have hsum_lt : p - d + d < N := by omega
          have hprev :
              sternBrocotTreeLabel (((p - d : ℕ) : ℚ) / (d : ℚ)) :=
            ih (p - d + d) hsum_lt (p - d) d rfl hpmd hd
          have hden : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
          have hsub_cast : ((p - d : ℕ) : ℚ) = (p : ℚ) - (d : ℚ) := by
            norm_num [Nat.cast_sub (le_of_lt hgt)]
          have hq :
              ((p : ℚ) / (d : ℚ)) =
                (((p - d : ℕ) : ℚ) / (d : ℚ)) + 1 := by
            rw [hsub_cast]
            field_simp [hden]
            ring_nf
          simpa [hq] using sternBrocotTreeLabel.right hprev
        · have hlt : p < d := by omega
          have hdmP : 0 < d - p := Nat.sub_pos_of_lt hlt
          have hsum_lt : p + (d - p) < N := by omega
          have hprev :
              sternBrocotTreeLabel ((p : ℚ) / ((d - p : ℕ) : ℚ)) :=
            ih (p + (d - p)) hsum_lt p (d - p) rfl hp hdmP
          have hdiff : ((d - p : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast ne_of_gt hdmP
          have hsub_cast : ((d - p : ℕ) : ℚ) = (d : ℚ) - (p : ℚ) := by
            norm_num [Nat.cast_sub (le_of_lt hlt)]
          have hq :
              ((p : ℚ) / (d : ℚ)) =
                ((p : ℚ) / ((d - p : ℕ) : ℚ)) /
                  ((p : ℚ) / ((d - p : ℕ) : ℚ) + 1) := by
            have hd_eq : (d : ℚ) = ((d - p : ℕ) : ℚ) + (p : ℚ) := by
              rw [hsub_cast]
              ring
            rw [hd_eq]
            field_simp [hdiff]
            ring
          simpa [hq] using sternBrocotTreeLabel.left hprev

/-- Every positive rational occurs as a finite Stern--Brocot tree label. This is the
Euclidean-induction core of the book's surjectivity statement for positive rational
labels. -/
theorem sternBrocotTreeLabel_surjective_positiveRat (q : ℚ) (hq : 0 < q) :
    sternBrocotTreeLabel q := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hnat_pos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum_pos)
  have hden_pos : 0 < q.den := q.den_pos
  have hlabel :=
    sternBrocotTreeLabel_nat_div q.num.natAbs q.den hnat_pos hden_pos
  have hnum_cast : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
    have hq_nonneg : 0 ≤ q := le_of_lt hq
    norm_num [Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq_nonneg)]
    exact hq_nonneg
  simpa [hnum_cast, Rat.num_div_den] using hlabel

/-- Labels obtained by one final left Möbius move from a generated finite
Stern--Brocot label. Set-theoretically these are exactly the positive rational
labels in the displayed `L`-subtree. -/
def sternBrocotLSubtreeLabel (q : ℚ) : Prop :=
  ∃ r : ℚ, sternBrocotTreeLabel r ∧ q = r / (r + 1)

theorem sternBrocotLSubtreeLabel_treeLabel {q : ℚ}
    (h : sternBrocotLSubtreeLabel q) :
    sternBrocotTreeLabel q := by
  rcases h with ⟨r, hr, rfl⟩
  exact sternBrocotTreeLabel.left hr

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The L-subtree, rooted at $\tfrac{1}{2}$, is the \termdefine{Farey tree}; its nodes are the rationals in $(0,1)$ in
    lowest terms.
-/
/-- The `L`-subtree of the Stern--Brocot tree consists exactly of the rational
labels in the open unit interval. -/
theorem sternBrocotLSubtreeLabel_iff_pos_lt_one (q : ℚ) :
    sternBrocotLSubtreeLabel q ↔ 0 < q ∧ q < 1 := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hrpos : 0 < r := sternBrocotTreeLabel_pos hr
    constructor
    · exact div_pos hrpos (by linarith)
    · exact (div_lt_one (by linarith : 0 < r + 1)).2 (by linarith)
  · intro hq
    let r : ℚ := q / (1 - q)
    have hdenpos : 0 < 1 - q := by linarith
    have hrpos : 0 < r := div_pos hq.1 hdenpos
    refine ⟨r, sternBrocotTreeLabel_surjective_positiveRat r hrpos, ?_⟩
    have hdenne : (1 - q : ℚ) ≠ 0 := ne_of_gt hdenpos
    unfold r
    field_simp [hdenne]
    ring

/-- Labels obtained by one final right Möbius move from a generated finite
Stern--Brocot label. -/
def sternBrocotRightMoveLabel (q : ℚ) : Prop :=
  ∃ r : ℚ, sternBrocotTreeLabel r ∧ q = r + 1

theorem sternBrocotRightMoveLabel_treeLabel {q : ℚ}
    (h : sternBrocotRightMoveLabel q) :
    sternBrocotTreeLabel q := by
  rcases h with ⟨r, hr, rfl⟩
  exact sternBrocotTreeLabel.right hr

theorem sternBrocotRightMoveLabel_iff_one_lt (q : ℚ) :
    sternBrocotRightMoveLabel q ↔ 1 < q := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hrpos : 0 < r := sternBrocotTreeLabel_pos hr
    linarith
  · intro hq
    let r : ℚ := q - 1
    have hrpos : 0 < r := by
      unfold r
      linarith
    refine ⟨r, sternBrocotTreeLabel_surjective_positiveRat r hrpos, ?_⟩
    unfold r
    ring

/-- Every positive rational label is either the root label, lies in the
`L`-subtree, or lies in the image of one final right Möbius move. This is the
case split used by Euclidean descent. -/
theorem sternBrocotPositiveRat_root_or_left_or_right (q : ℚ) (hq : 0 < q) :
    q = 1 ∨ sternBrocotLSubtreeLabel q ∨ sternBrocotRightMoveLabel q := by
  by_cases hlt : q < 1
  · exact Or.inr (Or.inl ((sternBrocotLSubtreeLabel_iff_pos_lt_one q).2 ⟨hq, hlt⟩))
  · by_cases hone : q = 1
    · exact Or.inl hone
    · have hgt : 1 < q := by
        exact lt_of_le_of_ne (le_of_not_gt hlt) (fun h => hone h.symm)
      exact Or.inr (Or.inr ((sternBrocotRightMoveLabel_iff_one_lt q).2 hgt))

theorem sternBrocotNodeLabel_treeLabel {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ n : ℕ) :
    sternBrocotTreeLabel (sternBrocotNodeLabel a₀ a n) :=
  sternBrocotTreeLabel_surjective_positiveRat
    (sternBrocotNodeLabel a₀ a n) (sternBrocotNodeLabel_pos ha a₀ n)

/-- Finite continued-fraction cylinder labels are generated finite
Stern--Brocot tree labels. -/
theorem sternBrocotFiniteCylinderLabel_treeLabel
    (a₀ : ℕ) (pref : finseq positiveNat) :
    sternBrocotTreeLabel (sternBrocotFiniteCylinderLabel a₀ pref) :=
  sternBrocotNodeLabel_treeLabel
    (positiveNatSeqPartials_positive (extendFinseq pref)) a₀ pref.length

/-- Every generated finite Stern--Brocot tree label is realized by an actual
finite continued-fraction cylinder label. -/
theorem sternBrocotTreeLabel_exists_finiteCylinderLabel {q : ℚ}
    (h : sternBrocotTreeLabel q) :
    ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
      sternBrocotFiniteCylinderLabel a₀ pref = q := by
  induction h with
  | root =>
      refine ⟨0, [], ?_⟩
      simpa using
        (sternBrocotFiniteCylinderLabel_empty_positiveInteger (m := 1) (by norm_num))
  | right h ih =>
      rcases ih with ⟨a₀, pref, hlabel⟩
      refine ⟨a₀ + 1, pref, ?_⟩
      rw [sternBrocotFiniteCylinderLabel_succ_integerPart, hlabel]
  | left h ih =>
      rcases ih with ⟨a₀, pref, hlabel⟩
      rcases sternBrocotFiniteCylinderLabel_leftMove_exists a₀ pref with ⟨pref', hleft⟩
      refine ⟨0, pref', ?_⟩
      rw [hlabel] at hleft
      exact hleft

/-- Every positive rational is realized as a finite continued-fraction cylinder
label under the chosen final-`1` convention. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Here is an elementary justification of that convention. For existence, use the subtractive Euclidean algorithm
    on $r=p/q>0$ with positive integers $p,q$. If $p=q$, then $r=1=[0;1]$. If $p>q$, reduce to
    $(p-q)/q$ and recover $r$ by adding $1$. If $p<q$, reduce to $t=p/(q-p)$ and recover
    $r=t/(t+1)$. The sum of numerator and denominator decreases at each reduction. Both recovery operations
    preserve finite expansions ending in $1$: adding $1$ increases the integer part, while
    $t/(t+1)=1/(1+1/t)$ inserts an initial reciprocal and combines the adjacent integer terms when needed.
    Thus induction gives the required expansion for every positive rational.
-/
theorem sternBrocotFiniteCylinderLabel_surjective_positiveRat
    (q : ℚ) (hq : 0 < q) :
    ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
      sternBrocotFiniteCylinderLabel a₀ pref = q :=
  sternBrocotTreeLabel_exists_finiteCylinderLabel
    (sternBrocotTreeLabel_surjective_positiveRat q hq)

/-- The chosen finite continued-fraction cylinder labels are a bijection from
integer part plus finite positive tail to positive rational labels. -/
theorem sternBrocotFiniteCylinderLabel_bijective_positiveRat :
    Function.Bijective
      (fun p : Sigma fun _ : ℕ => finseq positiveNat =>
        (⟨sternBrocotFiniteCylinderLabel p.1 p.2,
          sternBrocotFiniteCylinderLabel_pos p.1 p.2⟩ :
          {q : ℚ // 0 < q})) := by
  constructor
  · rintro ⟨a₀, pref⟩ ⟨b₀, qref⟩ h
    have hlabel :
        sternBrocotFiniteCylinderLabel a₀ pref =
          sternBrocotFiniteCylinderLabel b₀ qref :=
      congrArg Subtype.val h
    rcases sternBrocotFiniteCylinderLabel_injective hlabel with ⟨rfl, rfl⟩
    rfl
  · intro q
    rcases sternBrocotFiniteCylinderLabel_surjective_positiveRat q.1 q.2 with
      ⟨a₀, pref, hlabel⟩
    refine ⟨⟨a₀, pref⟩, ?_⟩
    exact Subtype.ext hlabel

/-- A finite continued-fraction node label with one larger integer part is a
right-move label generated from the previous node label. -/
theorem sternBrocotNodeLabel_succ_integerPart_rightMoveLabel {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) (a₀ n : ℕ) :
    sternBrocotRightMoveLabel (sternBrocotNodeLabel (a₀ + 1) a n) := by
  refine ⟨sternBrocotNodeLabel a₀ a n, sternBrocotNodeLabel_treeLabel ha a₀ n, ?_⟩
  exact sternBrocotNodeLabel_succ_integerPart ha a₀ n

/-- Nonempty finite continued-fraction node labels in the zero integer cell are
exactly `L`-subtree labels in the Euclidean Stern--Brocot generation. -/
theorem sternBrocotNodeLabel_zero_lSubtreeLabel {a : ℕ → ℤ}
    (ha : SimpleCFPositivePartials a) {n : ℕ} (hn : 0 < n) :
    sternBrocotLSubtreeLabel (sternBrocotNodeLabel 0 a n) := by
  have hIoo := sternBrocotNodeLabel_zero_mem_Ioo_zero_one ha hn
  exact (sternBrocotLSubtreeLabel_iff_pos_lt_one _).2
    ⟨by exact_mod_cast hIoo.1, by exact_mod_cast hIoo.2⟩

def sternBrocotPartialDirection (n : ℕ) : sternBrocotDirection :=
  if Even n then sternBrocotDirection.right else sternBrocotDirection.left

theorem sternBrocotPartialDirection_even {n : ℕ} (hn : Even n) :
    sternBrocotPartialDirection n = sternBrocotDirection.right := by
  simp [sternBrocotPartialDirection, hn]

theorem sternBrocotPartialDirection_odd {n : ℕ} (hn : Odd n) :
    sternBrocotPartialDirection n = sternBrocotDirection.left := by
  have hne : ¬ Even n := Nat.not_even_iff_odd.2 hn
  simp [sternBrocotPartialDirection, hne]

theorem sternBrocotPartialDirection_succ_ne (n : ℕ) :
    sternBrocotPartialDirection (n + 1) ≠ sternBrocotPartialDirection n := by
  by_cases hn : Even n
  · have hn_succ : Odd (n + 1) := by
      rcases hn with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    rw [sternBrocotPartialDirection_even hn,
      sternBrocotPartialDirection_odd hn_succ]
    decide
  · have hn_odd : Odd n := Nat.not_even_iff_odd.1 hn
    have hn_succ : Even (n + 1) := by
      rcases hn_odd with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      omega
    rw [sternBrocotPartialDirection_even hn_succ,
      sternBrocotPartialDirection_odd hn_odd]
    decide

def sternBrocotTailRunWordFrom (n : ℕ) : List positiveNat → sternBrocotWord
  | [] => []
  | a :: tail =>
      List.replicate a.1 (sternBrocotPartialDirection n) ++
        sternBrocotTailRunWordFrom (n + 1) tail

theorem sternBrocotTailRunWordFrom_cons_even {n : ℕ} (hn : Even n)
    (a : positiveNat) (tail : List positiveNat) :
    sternBrocotTailRunWordFrom n (a :: tail) =
      List.replicate a.1 sternBrocotDirection.right ++
        sternBrocotTailRunWordFrom (n + 1) tail := by
  simp [sternBrocotTailRunWordFrom, sternBrocotPartialDirection_even hn]

theorem sternBrocotTailRunWordFrom_cons_odd {n : ℕ} (hn : Odd n)
    (a : positiveNat) (tail : List positiveNat) :
    sternBrocotTailRunWordFrom n (a :: tail) =
      List.replicate a.1 sternBrocotDirection.left ++
        sternBrocotTailRunWordFrom (n + 1) tail := by
  simp [sternBrocotTailRunWordFrom, sternBrocotPartialDirection_odd hn]

theorem sternBrocotTailRunWordFrom_takeWhile_length (n : ℕ)
    (a : positiveNat) (tail : List positiveNat) :
    (List.takeWhile
      (fun d : sternBrocotDirection => decide (d = sternBrocotPartialDirection n))
      (sternBrocotTailRunWordFrom n (a :: tail))).length = a.1 := by
  cases tail with
  | nil =>
      simp [sternBrocotTailRunWordFrom]
  | cons b tail =>
      have hne :
          sternBrocotPartialDirection (n + 1) ≠ sternBrocotPartialDirection n :=
        sternBrocotPartialDirection_succ_ne n
      simp [sternBrocotTailRunWordFrom]
      intro _hl
      have hbpos : 0 < b.1 := by omega
      simpa [hbpos] using hne

/-- Run-length coding for the label `[a₀; a₁, ..., aₙ, 1]`, with the final `1`
block omitted. -/
def sternBrocotRunLengthWord (a₀ : ℕ) (tail : List positiveNat) : sternBrocotWord :=
  List.replicate a₀ sternBrocotDirection.right ++ sternBrocotTailRunWordFrom 1 tail

theorem sternBrocotRunLengthWord_empty (a₀ : ℕ) :
    sternBrocotRunLengthWord a₀ [] =
      List.replicate a₀ sternBrocotDirection.right := by
  simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom]

theorem sternBrocotRunLengthWord_cons (a₀ : ℕ) (a : positiveNat)
    (tail : List positiveNat) :
    sternBrocotRunLengthWord a₀ (a :: tail) =
      List.replicate a₀ sternBrocotDirection.right ++
        List.replicate a.1 sternBrocotDirection.left ++
          sternBrocotTailRunWordFrom 2 tail := by
  rw [sternBrocotRunLengthWord]
  rw [sternBrocotTailRunWordFrom_cons_odd (show Odd 1 by norm_num)]
  simp [List.append_assoc]

theorem sternBrocotRunLengthWord_takeWhile_right_length (a₀ : ℕ)
    (pref : List positiveNat) :
    (List.takeWhile
      (fun d : sternBrocotDirection => decide (d = sternBrocotDirection.right))
      (sternBrocotRunLengthWord a₀ pref)).length = a₀ := by
  cases pref with
  | nil =>
      simp [sternBrocotRunLengthWord_empty]
  | cons a tail =>
      rw [sternBrocotRunLengthWord_cons]
      simp
      intro _hl
      have hapos : 0 < a.1 := by omega
      simp [hapos]

/-- In the `a₀ = 0` cell, any nonempty finite partial-quotient prefix gives a
Stern--Brocot word extending the root `L`. This is the finite-word side of the
book's statement that the `L`-subtree is rooted at `1/2`. -/
theorem sternBrocotRunLengthWord_zero_cons_left_prefix (a : positiveNat)
    (tail : List positiveNat) :
    prefixOf [sternBrocotDirection.left]
      (sternBrocotRunLengthWord 0 (a :: tail)) := by
  rw [sternBrocotRunLengthWord_cons]
  refine ⟨List.replicate (a.1 - 1) sternBrocotDirection.left ++
      sternBrocotTailRunWordFrom 2 tail, ?_⟩
  have hrep :
      List.replicate a.1 sternBrocotDirection.left =
        [sternBrocotDirection.left] ++
          List.replicate (a.1 - 1) sternBrocotDirection.left := by
    have hlen : a.1 = 1 + (a.1 - 1) := by omega
    rw [hlen, List.replicate_add]
    simp
  simp [hrep]

/-- A nonempty finite continued-fraction prefix in the unit interval has an L/R
word in the `L`-subtree. -/
theorem sternBrocotRunLengthWord_zero_nonempty_left_prefix
    {pref : List positiveNat} (hpref : pref ≠ []) :
    prefixOf [sternBrocotDirection.left] (sternBrocotRunLengthWord 0 pref) := by
  cases pref with
  | nil =>
      exact (hpref rfl).elim
  | cons a tail =>
      exact sternBrocotRunLengthWord_zero_cons_left_prefix a tail

theorem sternBrocotTailRunWordFrom_append_singleton (m : ℕ) :
    ∀ (pref : List positiveNat) (a : positiveNat),
      sternBrocotTailRunWordFrom m (pref ++ [a]) =
        sternBrocotTailRunWordFrom m pref ++
          List.replicate a.1 (sternBrocotPartialDirection (m + pref.length)) := by
  intro pref
  induction pref generalizing m with
  | nil =>
      intro a
      simp [sternBrocotTailRunWordFrom]
  | cons head tail ih =>
      intro a
      simp [sternBrocotTailRunWordFrom, ih (m + 1), List.append_assoc,
        Nat.add_assoc, Nat.add_comm]

/-- Appending one more finite partial quotient appends the corresponding final
Stern--Brocot run. The index of the appended run is `prefix.length + 1`, matching
the book's `D_n`. -/
theorem sternBrocotRunLengthWord_append_singleton (a₀ : ℕ)
    (pref : List positiveNat) (a : positiveNat) :
    sternBrocotRunLengthWord a₀ (pref ++ [a]) =
      sternBrocotRunLengthWord a₀ pref ++
        List.replicate a.1 (sternBrocotPartialDirection (pref.length + 1)) := by
  rw [sternBrocotRunLengthWord, sternBrocotRunLengthWord,
    sternBrocotTailRunWordFrom_append_singleton]
  simp [List.append_assoc, Nat.add_comm]

/-- Adding one more finite partial quotient extends the assigned Stern--Brocot
word. This is the one-step extension relation behind the finite binary tree. -/
theorem sternBrocotRunLengthWord_prefix_append_singleton (a₀ : ℕ)
    (pref : List positiveNat) (a : positiveNat) :
    prefixOf (sternBrocotRunLengthWord a₀ pref)
      (sternBrocotRunLengthWord a₀ (pref ++ [a])) := by
  rw [sternBrocotRunLengthWord_append_singleton]
  exact (sternBrocotRunLengthWord a₀ pref).prefix_append _

/-- The finite run-length coding is monotone for prefix extension: extending a
continued-fraction prefix extends the assigned Stern--Brocot L/R word. This is
the Lean form of ordering the rational labels by extension of their assigned
words. -/
theorem sternBrocotRunLengthWord_prefix_of_prefix (a₀ : ℕ)
    {pref tail : List positiveNat} (h : prefixOf pref tail) :
    prefixOf (sternBrocotRunLengthWord a₀ pref)
      (sternBrocotRunLengthWord a₀ tail) := by
  rcases h with ⟨extra, rfl⟩
  suffices hgo : ∀ pref extra : List positiveNat,
      prefixOf (sternBrocotRunLengthWord a₀ pref)
        (sternBrocotRunLengthWord a₀ (pref ++ extra)) by
    exact hgo pref extra
  intro pref extra
  induction extra generalizing pref with
  | nil =>
      simp
  | cons a rest ih =>
      have hstep :
          prefixOf (sternBrocotRunLengthWord a₀ pref)
            (sternBrocotRunLengthWord a₀ (pref ++ [a])) :=
        sternBrocotRunLengthWord_prefix_append_singleton a₀ pref a
      have htail :
          prefixOf (sternBrocotRunLengthWord a₀ (pref ++ [a]))
            (sternBrocotRunLengthWord a₀ ((pref ++ [a]) ++ rest)) :=
        ih (pref ++ [a])
      exact hstep.trans (by simpa [List.append_assoc] using htail)

/-- If the last partial quotient has even index, the final run is an `R`-run. -/
theorem sternBrocotRunLengthWord_append_singleton_even (a₀ : ℕ)
    (pref : List positiveNat) (a : positiveNat)
    (hn : Even (pref.length + 1)) :
    sternBrocotRunLengthWord a₀ (pref ++ [a]) =
      sternBrocotRunLengthWord a₀ pref ++
        List.replicate a.1 sternBrocotDirection.right := by
  rw [sternBrocotRunLengthWord_append_singleton,
    sternBrocotPartialDirection_even hn]

/-- If the last partial quotient has odd index, the final run is an `L`-run. -/
theorem sternBrocotRunLengthWord_append_singleton_odd (a₀ : ℕ)
    (pref : List positiveNat) (a : positiveNat)
    (hn : Odd (pref.length + 1)) :
    sternBrocotRunLengthWord a₀ (pref ++ [a]) =
      sternBrocotRunLengthWord a₀ pref ++
        List.replicate a.1 sternBrocotDirection.left := by
  rw [sternBrocotRunLengthWord_append_singleton,
    sternBrocotPartialDirection_odd hn]

theorem sternBrocotPartialDirection_add_two (n : ℕ) :
    sternBrocotPartialDirection (n + 2) = sternBrocotPartialDirection n := by
  by_cases hn : Even n
  · have hn2 : Even (n + 2) := by
      rcases hn with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      omega
    simp [sternBrocotPartialDirection, hn, hn2]
  · have hnodd : Odd n := Nat.not_even_iff_odd.1 hn
    have hn2odd : Odd (n + 2) := by
      rcases hnodd with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      omega
    have hn2 : ¬ Even (n + 2) := Nat.not_even_iff_odd.2 hn2odd
    simp [sternBrocotPartialDirection, hn, hn2]

theorem sternBrocotTailRunWordFrom_add_two (n : ℕ)
    (tail : List positiveNat) :
    sternBrocotTailRunWordFrom (n + 2) tail =
      sternBrocotTailRunWordFrom n tail := by
  induction tail generalizing n with
  | nil =>
      simp [sternBrocotTailRunWordFrom]
  | cons a tail ih =>
      simp [sternBrocotTailRunWordFrom, sternBrocotPartialDirection_add_two n,
        ih (n + 1), Nat.add_assoc]

theorem sternBrocotTailRunWordFrom_eq_nil_iff (n : ℕ)
    (tail : List positiveNat) :
    sternBrocotTailRunWordFrom n tail = [] ↔ tail = [] := by
  constructor
  · intro h
    cases tail with
    | nil =>
        rfl
    | cons a tail =>
        have hnonempty :
            List.replicate a.1 (sternBrocotPartialDirection n) ++
              sternBrocotTailRunWordFrom (n + 1) tail ≠ [] := by
          have hrep :
              List.replicate a.1 (sternBrocotPartialDirection n) ≠ [] := by
            simp [List.replicate_eq_nil_iff]
            omega
          intro hnil
          exact hrep (List.append_eq_nil_iff.mp hnil).1
        exact False.elim (hnonempty (by simpa [sternBrocotTailRunWordFrom] using h))
  · intro h
    rw [h]
    simp [sternBrocotTailRunWordFrom]

theorem sternBrocotTailRunWordFrom_injective (n : ℕ) :
    Function.Injective (sternBrocotTailRunWordFrom n) := by
  intro pref
  induction pref generalizing n with
  | nil =>
      intro qref h
      exact ((sternBrocotTailRunWordFrom_eq_nil_iff n qref).1 h.symm).symm
  | cons a tail ih =>
      intro qref h
      cases qref with
      | nil =>
          have hnil : sternBrocotTailRunWordFrom n (a :: tail) = [] := h
          have hbad : a :: tail = [] :=
            (sternBrocotTailRunWordFrom_eq_nil_iff n (a :: tail)).1 hnil
          cases hbad
      | cons b qtail =>
          have hlen :
              a.1 = b.1 := by
            have htake := congrArg
              (fun w : sternBrocotWord =>
                (List.takeWhile
                  (fun d : sternBrocotDirection =>
                    decide (d = sternBrocotPartialDirection n)) w).length) h
            simpa [sternBrocotTailRunWordFrom_takeWhile_length n a tail,
              sternBrocotTailRunWordFrom_takeWhile_length n b qtail] using htake
          have hab : a = b := Subtype.ext hlen
          subst b
          have htail :
              sternBrocotTailRunWordFrom (n + 1) tail =
                sternBrocotTailRunWordFrom (n + 1) qtail := by
            have hdrop := congrArg (List.drop a.1) h
            simpa [sternBrocotTailRunWordFrom] using hdrop
          have htail_eq : tail = qtail := ih (n + 1) htail
          rw [htail_eq]

theorem sternBrocotRunLengthWord_eq_nil_iff (a₀ : ℕ)
    (pref : List positiveNat) :
    sternBrocotRunLengthWord a₀ pref = [] ↔ a₀ = 0 ∧ pref = [] := by
  constructor
  · intro h
    have hsplit :
        a₀ = 0 ∧ sternBrocotTailRunWordFrom 1 pref = [] := by
      simpa [sternBrocotRunLengthWord, List.replicate_eq_nil_iff] using h
    have ha₀ : a₀ = 0 := hsplit.1
    have hpref : pref = [] := by
      exact (sternBrocotTailRunWordFrom_eq_nil_iff 1 pref).1 hsplit.2
    exact ⟨ha₀, hpref⟩
  · rintro ⟨rfl, rfl⟩
    simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom]

theorem sternBrocotRunLengthWord_prepend_right (a₀ : ℕ)
    (pref : List positiveNat) :
    sternBrocotRunLengthWord (a₀ + 1) pref =
      sternBrocotDirection.right :: sternBrocotRunLengthWord a₀ pref := by
  simp [sternBrocotRunLengthWord, List.replicate_succ]

theorem sternBrocotRunLengthWord_succ_head? (a₀ : ℕ)
    (pref : List positiveNat) :
    (sternBrocotRunLengthWord (a₀ + 1) pref).head? =
      some sternBrocotDirection.right := by
  rw [sternBrocotRunLengthWord_prepend_right]
  rfl

theorem sternBrocotRunLengthWord_zero_cons_head? (a : positiveNat)
    (tail : List positiveNat) :
    (sternBrocotRunLengthWord 0 (a :: tail)).head? =
      some sternBrocotDirection.left := by
  have hrep :
      List.replicate a.1 sternBrocotDirection.left =
        sternBrocotDirection.left ::
          List.replicate (a.1 - 1) sternBrocotDirection.left := by
    have hlen : a.1 = 1 + (a.1 - 1) := by omega
    rw [hlen, List.replicate_add]
    simp
  rw [sternBrocotRunLengthWord_cons, hrep]
  simp

theorem sternBrocotRunLengthWord_zero_cons_ne_succ
    (a : positiveNat) (tail : List positiveNat) (b₀ : ℕ)
    (qref : List positiveNat) :
    sternBrocotRunLengthWord 0 (a :: tail) ≠
      sternBrocotRunLengthWord (b₀ + 1) qref := by
  intro h
  have hhead := congrArg List.head? h
  rw [sternBrocotRunLengthWord_zero_cons_head?,
    sternBrocotRunLengthWord_succ_head?] at hhead
  simp at hhead

theorem sternBrocotRunLengthWord_injective :
    ∀ {a₀ b₀ : ℕ} {pref qref : List positiveNat},
      sternBrocotRunLengthWord a₀ pref =
        sternBrocotRunLengthWord b₀ qref →
          a₀ = b₀ ∧ pref = qref := by
  intro a₀ b₀ pref qref h
  have ha₀ : a₀ = b₀ := by
    have htake := congrArg
      (fun w : sternBrocotWord =>
        (List.takeWhile
          (fun d : sternBrocotDirection =>
            decide (d = sternBrocotDirection.right)) w).length) h
    simpa [sternBrocotRunLengthWord_takeWhile_right_length a₀ pref,
      sternBrocotRunLengthWord_takeWhile_right_length b₀ qref] using htake
  subst b₀
  have htail :
      sternBrocotTailRunWordFrom 1 pref =
        sternBrocotTailRunWordFrom 1 qref := by
    have hdrop := congrArg (List.drop a₀) h
    simpa [sternBrocotRunLengthWord] using hdrop
  have hpref : pref = qref :=
    sternBrocotTailRunWordFrom_injective 1 htail
  exact ⟨rfl, hpref⟩

theorem sternBrocotFiniteCylinderLabel_eq_of_runLengthWord_eq
    {a₀ b₀ : ℕ} {pref qref : List positiveNat}
    (h :
      sternBrocotRunLengthWord a₀ pref =
        sternBrocotRunLengthWord b₀ qref) :
    sternBrocotFiniteCylinderLabel a₀ pref =
      sternBrocotFiniteCylinderLabel b₀ qref := by
  rcases sternBrocotRunLengthWord_injective h with ⟨rfl, rfl⟩
  rfl

theorem sternBrocotRunLengthWord_prepend_left_exists (a₀ : ℕ)
    (pref : List positiveNat) :
    ∃ b₀ : ℕ, ∃ qref : List positiveNat,
      sternBrocotRunLengthWord b₀ qref =
        sternBrocotDirection.left :: sternBrocotRunLengthWord a₀ pref := by
  cases a₀ with
  | zero =>
      cases pref with
      | nil =>
          let one : positiveNat := ⟨1, by omega⟩
          refine ⟨0, [one], ?_⟩
          simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom, one,
            sternBrocotPartialDirection_odd (show Odd 1 by norm_num)]
      | cons a tail =>
          let a' : positiveNat := ⟨a.1 + 1, by omega⟩
          refine ⟨0, a' :: tail, ?_⟩
          rw [sternBrocotRunLengthWord_cons, sternBrocotRunLengthWord_cons]
          simp [a', List.replicate_succ]
  | succ m =>
      let one : positiveNat := ⟨1, by omega⟩
      let a : positiveNat := ⟨m + 1, by omega⟩
      refine ⟨0, one :: a :: pref, ?_⟩
      simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom, one, a,
        sternBrocotTailRunWordFrom_add_two,
        sternBrocotPartialDirection_odd (show Odd 1 by norm_num),
        sternBrocotPartialDirection_even (show Even 2 by norm_num)]

/-- Every finite Stern--Brocot L/R word is the run-length word of some finite
continued-fraction node. This is the finite-word bridge hidden in the book's
phrase "the rational at finite node `b`". -/
theorem sternBrocotRunLengthWord_surjective (w : sternBrocotWord) :
    ∃ a₀ : ℕ, ∃ pref : List positiveNat,
      sternBrocotRunLengthWord a₀ pref = w := by
  induction w with
  | nil =>
      exact ⟨0, [], by simp [sternBrocotRunLengthWord_empty]⟩
  | cons d w ih =>
      rcases ih with ⟨a₀, pref, hword⟩
      cases d with
      | left =>
          rcases sternBrocotRunLengthWord_prepend_left_exists a₀ pref with
            ⟨b₀, qref, hprepend⟩
          exact ⟨b₀, qref, by rw [hprepend, hword]⟩
      | right =>
          exact ⟨a₀ + 1, pref, by rw [sternBrocotRunLengthWord_prepend_right, hword]⟩

/-- The finite-cylinder data `(a₀, pref)` assigned to a Stern--Brocot rational
node, sent to its run-length L/R word. -/
def sternBrocotFiniteCylinderRunLengthWord
    (node : ℕ × finseq positiveNat) : sternBrocotWord :=
  sternBrocotRunLengthWord node.1 node.2

/-- Assigning run-length L/R words identifies the finite continued-fraction
cylinder nodes with the finite binary tree. -/
theorem sternBrocotFiniteCylinderRunLengthWord_bijective :
    Function.Bijective sternBrocotFiniteCylinderRunLengthWord := by
  constructor
  · rintro ⟨a₀, pref⟩ ⟨b₀, qref⟩ h
    change sternBrocotRunLengthWord a₀ pref =
      sternBrocotRunLengthWord b₀ qref at h
    rcases sternBrocotRunLengthWord_injective h with ⟨rfl, rfl⟩
    rfl
  · intro w
    rcases sternBrocotRunLengthWord_surjective w with ⟨a₀, pref, hword⟩
    exact ⟨(a₀, pref), by simpa [sternBrocotFiniteCylinderRunLengthWord] using hword⟩

theorem sternBrocotRunLengthWord_one :
    sternBrocotRunLengthWord 0 [] = [] := by
  simp [sternBrocotRunLengthWord_empty]

theorem sternBrocotRunLengthWord_one_half :
    sternBrocotRunLengthWord 0 [⟨1, by omega⟩] =
      [sternBrocotDirection.left] := by
  simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom,
    sternBrocotPartialDirection]

theorem sternBrocotRunLengthWord_two :
    sternBrocotRunLengthWord 1 [] =
      [sternBrocotDirection.right] := by
  simp [sternBrocotRunLengthWord_empty]

theorem sternBrocotRunLengthWord_one_third :
    sternBrocotRunLengthWord 0 [⟨2, by omega⟩] =
      [sternBrocotDirection.left, sternBrocotDirection.left] := by
  simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom,
    sternBrocotPartialDirection]

theorem sternBrocotRunLengthWord_two_thirds :
    sternBrocotRunLengthWord 0 [⟨1, by omega⟩, ⟨1, by omega⟩] =
      [sternBrocotDirection.left, sternBrocotDirection.right] := by
  simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom,
    sternBrocotPartialDirection]

theorem sternBrocotRunLengthWord_three_halves :
    sternBrocotRunLengthWord 1 [⟨1, by omega⟩] =
      [sternBrocotDirection.right, sternBrocotDirection.left] := by
  simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom,
    sternBrocotPartialDirection]

theorem sternBrocotRunLengthWord_three :
    sternBrocotRunLengthWord 2 [] =
      [sternBrocotDirection.right, sternBrocotDirection.right] := by
  simp [sternBrocotRunLengthWord_empty]

theorem sternBrocotRunLengthWord_five_halves :
    sternBrocotRunLengthWord 2 [⟨1, by omega⟩] =
      [sternBrocotDirection.right, sternBrocotDirection.right, sternBrocotDirection.left] := by
  simp [sternBrocotRunLengthWord, sternBrocotTailRunWordFrom,
    sternBrocotPartialDirection]

def sternBrocotExamplePartials : ℕ → ℤ :=
  fun _ => 1

def sternBrocotOneThirdPartials : ℕ → ℤ :=
  fun n => if n = 1 then 2 else 1

theorem sternBrocotLabel_one :
    simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 0 1 = (1 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotExamplePartials]

theorem sternBrocotLabel_one_half :
    simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 1 1 = (1 / 2 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotExamplePartials]

theorem sternBrocotLabel_two :
    simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 0 1 = (2 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotExamplePartials]

theorem sternBrocotLabel_one_third :
    simpleCFShiftedSemiconvergent 0 sternBrocotOneThirdPartials 1 1 = (1 / 3 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotOneThirdPartials]

theorem sternBrocotLabel_two_thirds :
    simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 2 1 = (2 / 3 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotExamplePartials]

theorem sternBrocotLabel_three_halves :
    simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 1 1 = (3 / 2 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotExamplePartials]

theorem sternBrocotLabel_three :
    simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 0 1 = (3 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotExamplePartials]

theorem sternBrocotLabel_five_halves :
    simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 1 1 = (5 / 2 : ℚ) := by
  norm_num [simpleCFShiftedSemiconvergent, simpleCFShiftedSemiconvergentNum,
    simpleCFSemiconvergentNum, simpleCFSemiconvergentDen, simpleCFNum, simpleCFDen,
    sternBrocotExamplePartials]

/-- The prose example `[2; 1, 1] = 5 / 2` has run-length word `RRL`. -/
theorem sternBrocotFiveHalves_label_and_word :
    (sternBrocotRunLengthWord 2 [⟨1, by omega⟩],
      simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 1 1) =
        ([sternBrocotDirection.right, sternBrocotDirection.right, sternBrocotDirection.left],
          (5 / 2 : ℚ)) := by
  exact Prod.ext sternBrocotRunLengthWord_five_halves sternBrocotLabel_five_halves

/-- The displayed initial Stern--Brocot tree and the adjacent `5 / 2` prose
example have exactly the book's L/R words and rational labels. -/
theorem sternBrocotInitialTreeDiagram_labels_and_words :
    (sternBrocotRunLengthWord 0 [],
        simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 0 1) =
          (([] : sternBrocotWord), (1 : ℚ)) ∧
      (sternBrocotRunLengthWord 0 [⟨1, by omega⟩],
        simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 1 1) =
          ([sternBrocotDirection.left], (1 / 2 : ℚ)) ∧
      (sternBrocotRunLengthWord 0 [⟨2, by omega⟩],
        simpleCFShiftedSemiconvergent 0 sternBrocotOneThirdPartials 1 1) =
          ([sternBrocotDirection.left, sternBrocotDirection.left], (1 / 3 : ℚ)) ∧
      (sternBrocotRunLengthWord 0 [⟨1, by omega⟩, ⟨1, by omega⟩],
        simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 2 1) =
          ([sternBrocotDirection.left, sternBrocotDirection.right], (2 / 3 : ℚ)) ∧
      (sternBrocotRunLengthWord 1 [],
        simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 0 1) =
          ([sternBrocotDirection.right], (2 : ℚ)) ∧
      (sternBrocotRunLengthWord 1 [⟨1, by omega⟩],
        simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 1 1) =
          ([sternBrocotDirection.right, sternBrocotDirection.left], (3 / 2 : ℚ)) ∧
      (sternBrocotRunLengthWord 2 [],
        simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 0 1) =
          ([sternBrocotDirection.right, sternBrocotDirection.right], (3 : ℚ)) ∧
      (sternBrocotRunLengthWord 2 [⟨1, by omega⟩],
        simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 1 1) =
          ([sternBrocotDirection.right, sternBrocotDirection.right, sternBrocotDirection.left],
            (5 / 2 : ℚ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Prod.ext sternBrocotRunLengthWord_one sternBrocotLabel_one
  · exact Prod.ext sternBrocotRunLengthWord_one_half sternBrocotLabel_one_half
  · exact Prod.ext sternBrocotRunLengthWord_one_third sternBrocotLabel_one_third
  · exact Prod.ext sternBrocotRunLengthWord_two_thirds sternBrocotLabel_two_thirds
  · exact Prod.ext sternBrocotRunLengthWord_two sternBrocotLabel_two
  · exact Prod.ext sternBrocotRunLengthWord_three_halves sternBrocotLabel_three_halves
  · exact Prod.ext sternBrocotRunLengthWord_three sternBrocotLabel_three
  · exact sternBrocotFiveHalves_label_and_word

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    By the determinant calculation above, each label is in lowest terms.

    This labeling is a bijection from positive continued-fraction cylinders to $\RestrictedSet{\QQ}{>0}$. Surjectivity is
    exactly the terminating expansion convention: if
    $$r = [a_0; a_1,\ldots,a_{n-1},1],$$
    then $r$ is the label of $\theta_{a_0}^{-1}(\cyl{(a_1,\ldots,a_{n-1})})$, with the empty prefix covering the integer
    case $m=[m-1;1]$. Injectivity follows from uniqueness of the chosen terminating expansion.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Assign to the same cylinder $\theta_{a_0}^{-1}(\cyl{(a_1,\ldots,a_n)})$ a finite L/R word by run-length coding the label
    $[a_0; a_1,\ldots,a_n,1]$ and omitting the final $1$-block. For $n \ge 1$, this word is
    $$
    \wordRepeat{R}{a_0}\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\cdots\wordRepeat{D_n}{a_n},
    \qquad
    D_n =
    \begin{cases}
    R, & n \text{ even}, \\
    L, & n \text{ odd}.
    \end{cases}
    $$
    For $s=\emptyset$ this gives $\wordRepeat{R}{a_0}$; in particular $1=[0;1]$ gets the empty word. Thus $\tfrac{1}{2} =
    [0;1,1]$ has word $L$, and $\tfrac{5}{2} = [2;1,1]$ has word $RRL$.

    Every finite L/R word has a unique decomposition into alternating runs, allowing the initial R-run to have length
    zero. Thus the rational labels correspond bijectively to finite L/R words. Order them by extension of these words,
    not by inclusion of the original continued-fraction cylinders. The resulting binary tree is the
    \termdefine{Stern--Brocot tree}:
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \begin{center}
    \begin{tikzpicture}[
      level distance=1.0cm,
      sibling distance=3.4cm,
      every node/.style={align=center, inner sep=1pt},
      level 2/.style={sibling distance=1.7cm}
    ]
    \node {$\emptyset:\ \tfrac{1}{1}$}
      child { node {$L:\ \tfrac{1}{2}$}
        child { node {$LL:\ \tfrac{1}{3}$} }
        child { node {$LR:\ \tfrac{2}{3}$} }
      }
      child { node {$R:\ \tfrac{2}{1}$}
        child { node {$RL:\ \tfrac{3}{2}$} }
        child { node {$RR:\ \tfrac{3}{1}$} }
      };
    \end{tikzpicture}
    \end{center}
-/
/-- Book-facing package for the finite Stern--Brocot rational-label paragraphs:
the transported cylinder-code Galois connection holds in each integer cell, node
labels are translated mediant endpoints, labels are well-defined on finite
continued-fraction cylinders, the finite-cylinder label function is realized
by and independent of any extending tail, its real value is the chosen
terminating expression `[a₀; pref, 1]`, the front-recursive finite expression
agrees with the existing tail map, nonempty terminating expressions lie in their
integer cell, positive integer labels use the empty-prefix convention, positive
and lowest-term facts hold for the labels,
continued-fraction node and cylinder labels are generated finite
Stern--Brocot tree labels, finite-cylinder labels are closed under the left and
right Stern--Brocot moves and realize all generated and positive rational
labels,
increasing the integer part realizes the right Möbius move on node labels,
the finite Stern--Brocot tree generates exactly positive rational labels,
its `L`-subtree labels are exactly the rational labels in `(0,1)`,
nonempty zero-cell node labels are generated `L`-subtree labels,
right-move labels are exactly the rational labels above `1`, and every
positive rational has the corresponding root/left/right Euclidean split, the
chosen terminating-expression and finite-label conventions are injective, empty
terminating expressions and finite labels are injective and disjoint from
nonempty ones, nonempty terminating expressions and finite labels recover their
integer part,
non-root `L`-subtree labels lie in `(0,1)`, finite run-length words have the
stated parity and extension behavior, and the displayed first two levels have
the advertised labels. -/
theorem concreteSternBrocotFiniteLabelFacts :
    (∀ a₀ : ℤ, ∀ A : Set (finseq positiveNat),
      ∀ V : Set (simpleCFFractionalInterval a₀),
        simpleCFFractionalCylinderCode a₀ A ⊆ V ↔
          A ⊆ simpleCFFractionalOpenCylinderCode a₀ V) ∧
      (∀ a₀ : ℕ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          sternBrocotNodeLabel a₀ a n =
            (a₀ : ℚ) +
              rationalMediant (simpleCFNum a (n + 1)) (simpleCFDen a (n + 1))
                (simpleCFNum a n) (simpleCFDen a n)) ∧
      (∀ m : ℕ, 0 < m → ∀ a : ℕ → ℤ,
        sternBrocotNodeLabel (m - 1) a 0 = (m : ℚ)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat, ∀ s t : ℕ → positiveNat,
        s ∈ cyl pref → t ∈ cyl pref →
          sternBrocotNodeLabel a₀ (positiveNatSeqPartials s) pref.length =
            sternBrocotNodeLabel a₀ (positiveNatSeqPartials t) pref.length) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        ∃ s : ℕ → positiveNat,
          s ∈ cyl pref ∧
            sternBrocotFiniteCylinderLabel a₀ pref =
              sternBrocotNodeLabel a₀ (positiveNatSeqPartials s) pref.length) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat, ∀ s : ℕ → positiveNat,
        s ∈ cyl pref →
          sternBrocotFiniteCylinderLabel a₀ pref =
            sternBrocotNodeLabel a₀ (positiveNatSeqPartials s) pref.length) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) =
          simpleCFTerminatingExpressionValue a₀ pref) ∧
      (∀ pref : finseq positiveNat, ∀ s : ℕ → positiveNat, ∀ x : ℝ,
        s ∈ cyl pref →
          simpleCFTerminatingTailValue pref x =
            simpleCFFiniteTail (positiveNatSeqPartials s) pref.length x) ∧
      (∀ a₀ : ℕ,
        simpleCFTerminatingExpressionValue a₀ [] = (a₀ : ℝ) + 1) ∧
      (∀ m : ℕ, 0 < m →
        simpleCFTerminatingExpressionValue (m - 1) [] = (m : ℝ)) ∧
      (∀ a₀ : ℕ,
        simpleCFIntegerPart (simpleCFTerminatingExpressionValue a₀ []) =
          ((a₀ + 1 : ℕ) : ℤ)) ∧
      (∀ a₀ b₀ : ℕ,
        simpleCFTerminatingExpressionValue a₀ [] =
          simpleCFTerminatingExpressionValue b₀ [] →
            a₀ = b₀) ∧
      (∀ a₀ : ℕ, ∀ a : positiveNat, ∀ pref : finseq positiveNat,
        simpleCFTerminatingExpressionValue a₀ (a :: pref) =
          (a₀ : ℝ) + 1 / simpleCFTerminatingExpressionValue a.1 pref) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        (a₀ : ℝ) < simpleCFTerminatingExpressionValue a₀ pref) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat, pref ≠ [] →
        simpleCFTerminatingExpressionValue a₀ pref ∈ Set.Ioo (a₀ : ℝ) ((a₀ : ℝ) + 1)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat, pref ≠ [] →
        simpleCFIntegerPart (simpleCFTerminatingExpressionValue a₀ pref) = (a₀ : ℤ)) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        pref ≠ [] → qref ≠ [] →
          simpleCFTerminatingExpressionValue a₀ pref =
            simpleCFTerminatingExpressionValue b₀ qref →
              a₀ = b₀) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        pref ≠ [] → qref ≠ [] →
          sternBrocotFiniteCylinderLabel a₀ pref =
            sternBrocotFiniteCylinderLabel b₀ qref →
              a₀ = b₀) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        simpleCFTerminatingExpressionValue a₀ pref =
          simpleCFTerminatingExpressionValue b₀ qref →
            a₀ = b₀ ∧ pref = qref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        sternBrocotFiniteCylinderLabel a₀ pref =
          sternBrocotFiniteCylinderLabel b₀ qref →
            a₀ = b₀ ∧ pref = qref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref : finseq positiveNat, pref ≠ [] →
        simpleCFTerminatingExpressionValue a₀ [] ≠
          simpleCFTerminatingExpressionValue b₀ pref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref : finseq positiveNat, pref ≠ [] →
        simpleCFTerminatingExpressionValue a₀ pref ≠
          simpleCFTerminatingExpressionValue b₀ []) ∧
      (∀ a₀ b₀ : ℕ,
        sternBrocotFiniteCylinderLabel a₀ [] =
          sternBrocotFiniteCylinderLabel b₀ [] →
            a₀ = b₀) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref : finseq positiveNat, pref ≠ [] →
        sternBrocotFiniteCylinderLabel a₀ [] ≠
          sternBrocotFiniteCylinderLabel b₀ pref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref : finseq positiveNat, pref ≠ [] →
        sternBrocotFiniteCylinderLabel a₀ pref ≠
          sternBrocotFiniteCylinderLabel b₀ []) ∧
      (∀ m : ℕ, 0 < m →
        sternBrocotFiniteCylinderLabel (m - 1) [] = (m : ℚ)) ∧
      (∀ a₀ : ℕ,
        sternBrocotFiniteCylinderLabel a₀ [] = ((a₀ + 1 : ℕ) : ℚ)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        0 < sternBrocotFiniteCylinderLabel a₀ pref) ∧
      (∀ a₀ : ℕ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a → 0 < sternBrocotNodeLabel a₀ a n) ∧
      (∀ a₀ : ℕ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          sternBrocotTreeLabel (sternBrocotNodeLabel a₀ a n)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotTreeLabel (sternBrocotFiniteCylinderLabel a₀ pref)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        ∃ pref' : finseq positiveNat,
          sternBrocotFiniteCylinderLabel 0 pref' =
            sternBrocotFiniteCylinderLabel a₀ pref /
              (sternBrocotFiniteCylinderLabel a₀ pref + 1)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotFiniteCylinderLabel (a₀ + 1) pref =
          sternBrocotFiniteCylinderLabel a₀ pref + 1) ∧
      (∀ q : ℚ, sternBrocotTreeLabel q →
        ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
          sternBrocotFiniteCylinderLabel a₀ pref = q) ∧
      (∀ q : ℚ, 0 < q →
        ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
          sternBrocotFiniteCylinderLabel a₀ pref = q) ∧
      Function.Bijective
        (fun p : Sigma fun _ : ℕ => finseq positiveNat =>
          (⟨sternBrocotFiniteCylinderLabel p.1 p.2,
            sternBrocotFiniteCylinderLabel_pos p.1 p.2⟩ :
            {q : ℚ // 0 < q})) ∧
      (∀ a₀ : ℕ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          sternBrocotNodeLabel (a₀ + 1) a n =
            sternBrocotNodeLabel a₀ a n + 1) ∧
      (∀ a₀ : ℕ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          sternBrocotRightMoveLabel (sternBrocotNodeLabel (a₀ + 1) a n)) ∧
      (∀ q : ℚ, sternBrocotTreeLabel q → 0 < q) ∧
      (∀ q : ℚ, 0 < q → sternBrocotTreeLabel q) ∧
      (∀ q : ℚ, sternBrocotLSubtreeLabel q ↔ 0 < q ∧ q < 1) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a → 0 < n →
          sternBrocotLSubtreeLabel (sternBrocotNodeLabel 0 a n)) ∧
      (∀ q : ℚ, sternBrocotRightMoveLabel q ↔ 1 < q) ∧
      (∀ q : ℚ, 0 < q →
        q = 1 ∨ sternBrocotLSubtreeLabel q ∨ sternBrocotRightMoveLabel q) ∧
      (∀ a₀ : ℕ, ∀ a : ℕ → ℤ, ∀ n : ℕ, ∀ d : ℤ,
        d ∣ simpleCFShiftedSemiconvergentNum (a₀ : ℤ) a n 1 →
          d ∣ simpleCFSemiconvergentDen a n 1 →
            d ∣ (1 : ℤ)) ∧
      (∀ pref : finseq positiveNat, pref ≠ [] → ∀ s t : ℕ → positiveNat,
        s ∈ cyl pref → t ∈ cyl pref →
          sternBrocotNodeLabel 0 (positiveNatSeqPartials s) pref.length =
              sternBrocotNodeLabel 0 (positiveNatSeqPartials t) pref.length ∧
            ((sternBrocotNodeLabel 0 (positiveNatSeqPartials s) pref.length : ℚ) : ℝ) ∈
              Set.Ioo (0 : ℝ) 1 ∧
            ∀ d : ℤ,
              d ∣ simpleCFShiftedSemiconvergentNum (0 : ℤ)
                  (positiveNatSeqPartials s) pref.length 1 →
                d ∣ simpleCFSemiconvergentDen (positiveNatSeqPartials s) pref.length 1 →
                  d ∣ (1 : ℤ)) ∧
      (∀ a₀ : ℕ,
        sternBrocotRunLengthWord a₀ [] =
          List.replicate a₀ sternBrocotDirection.right) ∧
      (∀ a₀ : ℕ, ∀ a : positiveNat, ∀ tail : List positiveNat,
        sternBrocotRunLengthWord a₀ (a :: tail) =
          List.replicate a₀ sternBrocotDirection.right ++
            List.replicate a.1 sternBrocotDirection.left ++
              sternBrocotTailRunWordFrom 2 tail) ∧
      (∀ a₀ : ℕ, ∀ pref : List positiveNat, ∀ a : positiveNat,
        prefixOf (sternBrocotRunLengthWord a₀ pref)
          (sternBrocotRunLengthWord a₀ (pref ++ [a]))) ∧
      (∀ a₀ : ℕ, ∀ pref tail : List positiveNat,
        prefixOf pref tail →
          prefixOf (sternBrocotRunLengthWord a₀ pref)
            (sternBrocotRunLengthWord a₀ tail)) ∧
      (∀ pref : List positiveNat, pref ≠ [] →
        prefixOf [sternBrocotDirection.left] (sternBrocotRunLengthWord 0 pref)) ∧
      (∀ a₀ : ℕ, ∀ pref : List positiveNat, ∀ a : positiveNat,
        Even (pref.length + 1) →
          sternBrocotRunLengthWord a₀ (pref ++ [a]) =
            sternBrocotRunLengthWord a₀ pref ++
              List.replicate a.1 sternBrocotDirection.right) ∧
      (∀ a₀ : ℕ, ∀ pref : List positiveNat, ∀ a : positiveNat,
        Odd (pref.length + 1) →
          sternBrocotRunLengthWord a₀ (pref ++ [a]) =
            sternBrocotRunLengthWord a₀ pref ++
              List.replicate a.1 sternBrocotDirection.left) ∧
      (sternBrocotRunLengthWord 0 [],
          simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 0 1) =
            (([] : sternBrocotWord), (1 : ℚ)) ∧
        (sternBrocotRunLengthWord 0 [⟨1, by omega⟩],
          simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 1 1) =
            ([sternBrocotDirection.left], (1 / 2 : ℚ)) ∧
          (sternBrocotRunLengthWord 0 [⟨2, by omega⟩],
            simpleCFShiftedSemiconvergent 0 sternBrocotOneThirdPartials 1 1) =
              ([sternBrocotDirection.left, sternBrocotDirection.left], (1 / 3 : ℚ)) ∧
            (sternBrocotRunLengthWord 0 [⟨1, by omega⟩, ⟨1, by omega⟩],
              simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 2 1) =
                ([sternBrocotDirection.left, sternBrocotDirection.right], (2 / 3 : ℚ)) ∧
              (sternBrocotRunLengthWord 1 [],
                simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 0 1) =
                  ([sternBrocotDirection.right], (2 : ℚ)) ∧
                (sternBrocotRunLengthWord 1 [⟨1, by omega⟩],
                  simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 1 1) =
                    ([sternBrocotDirection.right, sternBrocotDirection.left], (3 / 2 : ℚ)) ∧
                  (sternBrocotRunLengthWord 2 [],
                    simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 0 1) =
                      ([sternBrocotDirection.right, sternBrocotDirection.right], (3 : ℚ)) ∧
                    (sternBrocotRunLengthWord 2 [⟨1, by omega⟩],
                      simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 1 1) =
                        ([sternBrocotDirection.right, sternBrocotDirection.right,
                          sternBrocotDirection.left], (5 / 2 : ℚ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ A V
    exact simpleCFFractionalCylinderCode_subset_iff_subset_openCylinderCode
  · intro a₀ a n ha
    exact sternBrocotNodeLabel_eq_intCast_add_mediant ha a₀ n
  · intro m hm a
    exact sternBrocotNodeLabel_positiveInteger hm a
  · intro a₀ pref s t hs ht
    exact sternBrocotNodeLabel_eq_of_mem_same_cylinder a₀ pref hs ht
  · intro a₀ pref
    exact sternBrocotFiniteCylinderLabel_realized a₀ pref
  · intro a₀ pref s hs
    exact sternBrocotFiniteCylinderLabel_eq_nodeLabel_of_mem_cyl a₀ pref hs
  · intro a₀ pref
    exact sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue a₀ pref
  · intro pref s x hs
    exact simpleCFTerminatingTailValue_eq_simpleCFFiniteTail_of_mem_cyl pref hs x
  · intro a₀
    exact simpleCFTerminatingExpressionValue_empty a₀
  · intro m hm
    exact simpleCFTerminatingExpressionValue_empty_positiveInteger hm
  · intro a₀
    exact simpleCFTerminatingExpressionValue_empty_integerPart a₀
  · intro a₀ b₀ h
    exact simpleCFTerminatingExpressionValue_empty_injective h
  · intro a₀ a pref
    exact simpleCFTerminatingExpressionValue_cons a₀ a pref
  · intro a₀ pref
    exact simpleCFTerminatingExpressionValue_gt_integerPart a₀ pref
  · intro a₀ pref hpref
    exact simpleCFTerminatingExpressionValue_nonempty_mem_Ioo_integerCell a₀ hpref
  · intro a₀ pref hpref
    exact simpleCFTerminatingExpressionValue_nonempty_integerPart a₀ hpref
  · intro a₀ b₀ pref qref hpref hqref h
    exact simpleCFTerminatingExpressionValue_integerPart_eq_of_eq_nonempty hpref hqref h
  · intro a₀ b₀ pref qref hpref hqref h
    exact sternBrocotFiniteCylinderLabel_integerPart_eq_of_eq_nonempty hpref hqref h
  · intro a₀ b₀ pref qref h
    exact simpleCFTerminatingExpressionValue_injective h
  · intro a₀ b₀ pref qref h
    exact sternBrocotFiniteCylinderLabel_injective h
  · intro a₀ b₀ pref hpref
    exact simpleCFTerminatingExpressionValue_empty_ne_nonempty a₀ b₀ hpref
  · intro a₀ b₀ pref hpref
    exact simpleCFTerminatingExpressionValue_nonempty_ne_empty a₀ b₀ hpref
  · intro a₀ b₀ h
    exact sternBrocotFiniteCylinderLabel_empty_injective h
  · intro a₀ b₀ pref hpref
    exact sternBrocotFiniteCylinderLabel_empty_ne_nonempty a₀ b₀ hpref
  · intro a₀ b₀ pref hpref
    exact sternBrocotFiniteCylinderLabel_nonempty_ne_empty a₀ b₀ hpref
  · intro m hm
    exact sternBrocotFiniteCylinderLabel_empty_positiveInteger hm
  · intro a₀
    exact sternBrocotFiniteCylinderLabel_empty a₀
  · intro a₀ pref
    exact sternBrocotFiniteCylinderLabel_pos a₀ pref
  · intro a₀ a n ha
    exact sternBrocotNodeLabel_pos ha a₀ n
  · intro a₀ a n ha
    exact sternBrocotNodeLabel_treeLabel ha a₀ n
  · intro a₀ pref
    exact sternBrocotFiniteCylinderLabel_treeLabel a₀ pref
  · intro a₀ pref
    exact sternBrocotFiniteCylinderLabel_leftMove_exists a₀ pref
  · intro a₀ pref
    exact sternBrocotFiniteCylinderLabel_succ_integerPart a₀ pref
  · intro q hq
    exact sternBrocotTreeLabel_exists_finiteCylinderLabel hq
  · intro q hq
    exact sternBrocotFiniteCylinderLabel_surjective_positiveRat q hq
  · exact sternBrocotFiniteCylinderLabel_bijective_positiveRat
  · intro a₀ a n ha
    exact sternBrocotNodeLabel_succ_integerPart ha a₀ n
  · intro a₀ a n ha
    exact sternBrocotNodeLabel_succ_integerPart_rightMoveLabel ha a₀ n
  · intro q hq
    exact sternBrocotTreeLabel_pos hq
  · intro q hq
    exact sternBrocotTreeLabel_surjective_positiveRat q hq
  · intro q
    exact sternBrocotLSubtreeLabel_iff_pos_lt_one q
  · intro a n ha hn
    exact sternBrocotNodeLabel_zero_lSubtreeLabel ha hn
  · intro q
    exact sternBrocotRightMoveLabel_iff_one_lt q
  · intro q hq
    exact sternBrocotPositiveRat_root_or_left_or_right q hq
  · intro a₀ a n d hnum hden
    exact sternBrocotNodeLabel_lowestTerms a₀ a n hnum hden
  · intro pref hpref s t hs ht
    exact sternBrocotLSubtreeFiniteCylinderLabel_wellDefined_mem_Ioo_lowestTerms
      hpref hs ht
  · intro a₀
    exact sternBrocotRunLengthWord_empty a₀
  · intro a₀ a tail
    exact sternBrocotRunLengthWord_cons a₀ a tail
  · intro a₀ pref a
    exact sternBrocotRunLengthWord_prefix_append_singleton a₀ pref a
  · intro a₀ pref tail h
    exact sternBrocotRunLengthWord_prefix_of_prefix a₀ h
  · intro pref hpref
    exact sternBrocotRunLengthWord_zero_nonempty_left_prefix hpref
  · intro a₀ pref a hn
    exact sternBrocotRunLengthWord_append_singleton_even a₀ pref a hn
  · intro a₀ pref a hn
    exact sternBrocotRunLengthWord_append_singleton_odd a₀ pref a hn
  · exact sternBrocotInitialTreeDiagram_labels_and_words

/-!
## Infinite subsets of omega

This records the concrete Baire-space model by infinite subsets of `ω`.
-/

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \item \emph{Infinite subsets.} The \termdefineas{infinite subset of omega}{space of infinite subsets of $\omega$}
    is the subspace
    $$
    \infiniteSubsets{\omega}:=\{A\IncludedIn\omega:A\text{ is infinite}\}
    $$
    of $\PowerSet{\omega}\cong\CantorSpace$.
-/
/-- Book notation `\infiniteSubsets{\omega}` as a subset of `\PowerSet{\omega}`. -/
def infiniteSubsetsOmegaSet : Set powersetOmega :=
  {A | Set.Infinite (A : Set ℕ)}

/-- The subspace of infinite subsets of `ω`. -/
abbrev infiniteSubsetsOmega : Type :=
  infiniteSubsetsOmegaSet

/-- The open tail condition used in the `Gδ` presentation of infinite subsets. -/
def infiniteSubsetsOmegaTailSet (n : ℕ) : Set powersetOmega :=
  {A | ∃ m : ℕ, n ≤ m ∧ m ∈ (A : Set ℕ)}

/-- The `n`-th tail condition is the union of one-coordinate membership
decisions for witnesses `m ≥ n`. This is the formal version of the book's
"once some `m ≥ n` is known to lie in `A`" observation. -/
theorem infiniteSubsetsOmegaTailSet_eq_iUnion_membershipDecisionSet (n : ℕ) :
    infiniteSubsetsOmegaTailSet n =
      ⋃ m : {m : ℕ // n ≤ m}, membershipDecisionSet {m.1} ∅ := by
  ext A
  constructor
  · rintro ⟨m, hnm, hmA⟩
    exact Set.mem_iUnion.2 ⟨⟨m, hnm⟩, by simp [membershipDecisionSet, hmA]⟩
  · rintro hA
    rcases Set.mem_iUnion.1 hA with ⟨m, hmA⟩
    exact ⟨m.1, m.2, by simpa [membershipDecisionSet] using hmA⟩

/-- The tail condition is open: one known member above `n` is a finite membership decision. -/
theorem infiniteSubsetsOmegaTailSet_isOpen (n : ℕ) :
    IsOpen (infiniteSubsetsOmegaTailSet n) := by
  rw [infiniteSubsetsOmegaTailSet_eq_iUnion_membershipDecisionSet]
  exact isOpen_iUnion fun m => (membershipDecisionSet_isClopen {m.1} ∅).isOpen

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The space $\infiniteSubsets{\omega}$ is a $\Gdelta$ subset of $\CantorSpace$:
    $$
    \infiniteSubsets{\omega}
    \;=\;
    \bigcap_{n \in \omega} \{A \IncludedIn \omega : \exists m \ge n,\; m \in A\}.
    $$
-/
/-- Book-level `Gδ` presentation of `\infiniteSubsets{\omega}`. -/
theorem infiniteSubsetsOmegaGdeltaPresentationFact :
    infiniteSubsetsOmegaSet = ⋂ n : ℕ, infiniteSubsetsOmegaTailSet n := by
  ext A
  constructor
  · intro hA
    rw [infiniteSubsetsOmegaSet] at hA
    rw [Set.mem_iInter]
    intro n
    rcases hA.exists_gt n with ⟨m, hmA, hnm⟩
    exact ⟨m, le_of_lt hnm, hmA⟩
  · intro hA
    change Set.Infinite (A : Set ℕ)
    rw [Set.infinite_iff_exists_gt]
    intro n
    have hn : A ∈ infiniteSubsetsOmegaTailSet (n + 1) := Set.mem_iInter.1 hA (n + 1)
    rcases hn with ⟨m, hnm, hmA⟩
    exact ⟨m, hmA, Nat.lt_of_succ_le hnm⟩

/-- The space of infinite subsets is a `Gδ` subspace of Cantor space. -/
theorem infiniteSubsetsOmegaSet_isGdelta :
    IsGδ infiniteSubsetsOmegaSet := by
  rw [infiniteSubsetsOmegaGdeltaPresentationFact]
  exact IsGδ.iInter_of_isOpen infiniteSubsetsOmegaTailSet_isOpen

/-- The infinite-subsets model is Polish as a `Gδ` subspace of Cantor space. -/
theorem infiniteSubsetsOmega_polish :
    PolishSpace infiniteSubsetsOmega := by
  have : PolishSpace cantor_space := cantor_space_polish
  have : PolishSpace powersetOmega := powersetOmegaEquivCantorSpace.polishSpace_induced
  exact gdelta_subspace_polish infiniteSubsetsOmegaSet_isGdelta

/-- Infinite subsets as Cantor-space points through their characteristic functions. -/
noncomputable def infiniteSubsetsOmegaCantorEmbedding (A : infiniteSubsetsOmega) :
    cantor_space :=
  powersetOmegaHomeomorphCantorSpace (A : powersetOmega)

theorem infiniteSubsetsOmegaCantorEmbedding_apply (A : infiniteSubsetsOmega) :
    infiniteSubsetsOmegaCantorEmbedding A = subsetCharacteristic (A : powersetOmega) := by
  simp [infiniteSubsetsOmegaCantorEmbedding, powersetOmegaHomeomorphCantorSpace_apply]

theorem infiniteSubsetsOmegaCantorEmbedding_continuous :
    Continuous infiniteSubsetsOmegaCantorEmbedding :=
  powersetOmegaHomeomorphCantorSpace.continuous.comp continuous_subtype_val

theorem infiniteSubsetsOmegaCantorEmbedding_injective :
    Function.Injective infiniteSubsetsOmegaCantorEmbedding := by
  intro A B h
  apply Subtype.ext
  exact powersetOmegaHomeomorphCantorSpace.injective h

/-- The characteristic-function inclusion realizes the infinite-subsets model as a
subspace of Cantor-space coordinates. -/
theorem infiniteSubsetsOmegaCantorEmbedding_isEmbedding :
    Topology.IsEmbedding infiniteSubsetsOmegaCantorEmbedding := by
  change Topology.IsEmbedding
    (powersetOmegaHomeomorphCantorSpace ∘
      (fun A : infiniteSubsetsOmega => (A : powersetOmega)))
  exact powersetOmegaHomeomorphCantorSpace.isEmbedding.comp Topology.IsEmbedding.subtypeVal

/-!
### Change points of binary branches

This is the set-level part of the book's identification of non-eventually-constant
Stern-Brocot boundary branches with infinite subsets of `ω`.
-/

open scoped Classical

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Each $b \in S$
    has infinitely many \termdefineas{change point}{change points}
    $$
    \Delta(b) := \{n \in \omega : b_n \ne b_{n+1}\},
    $$
    and $b$ is recovered from $b_0$ together with $\Delta(b)$ by flipping the bit exactly at those positions.
-/
/-- Change points of a binary sequence: positions where the next bit differs. -/
def cantorChangePointSet (b : cantor_space) : Set ℕ :=
  {n | b n ≠ b (n + 1)}

/-- The change-point map as a point of `\PowerSet{\omega}`. -/
def cantorChangePointMap (b : cantor_space) : powersetOmega :=
  cantorChangePointSet b

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The \termdefine{non-eventually-constant branches} are their complement
    $$S \;:=\; \SetDifference{\CantorSpace}{\{b \concat \wordRepeat{L}{\omega},\; b \concat \wordRepeat{R}{\omega} : b \in
    \finseq{2}\}}.$$
-/
/-- Non-eventually-constant binary branches, represented by having infinitely many
change points. -/
def cantorNonEventuallyConstantSet : Set cantor_space :=
  {b | Set.Infinite (cantorChangePointMap b : Set ℕ)}

/-- A binary branch is eventually constant if all sufficiently late coordinates have
one fixed value. -/
def cantorEventuallyConstant (b : cantor_space) : Prop :=
  ∃ N : ℕ, ∃ ε : Bool, ∀ n : ℕ, N ≤ n → b n = ε

theorem cantorEventuallyConstant_of_finite_changePoints
    (b : cantor_space) (hfin : (cantorChangePointMap b : Set ℕ).Finite) :
    cantorEventuallyConstant b := by
  classical
  let N : ℕ := hfin.toFinset.sup id + 1
  have hbound : ∀ n : ℕ, n ∈ (cantorChangePointMap b : Set ℕ) → n < N := by
    intro n hn
    have hnmem : n ∈ hfin.toFinset := hfin.mem_toFinset.2 hn
    exact Nat.lt_succ_of_le (Finset.le_sup (s := hfin.toFinset) (f := id) hnmem)
  have hnoChange : ∀ n : ℕ, N ≤ n → b n = b (n + 1) := by
    intro n hnN
    by_contra hne
    exact (not_lt_of_ge hnN) (hbound n hne)
  refine ⟨N, b N, ?_⟩
  intro n hnN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnN
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.add_succ]
      exact (hnoChange (N + k) (Nat.le_add_right N k)).symm.trans
        (ih (Nat.le_add_right N k))

theorem cantorChangePointMap_finite_of_eventuallyConstant
    (b : cantor_space) (heventual : cantorEventuallyConstant b) :
    (cantorChangePointMap b : Set ℕ).Finite := by
  rcases heventual with ⟨N, ε, hconst⟩
  refine (Finset.range N).finite_toSet.subset ?_
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hNn
  have hnN : N ≤ n := not_lt.mp hNn
  have hn_succ : N ≤ n + 1 := hnN.trans (Nat.le_succ n)
  exact hn ((hconst n hnN).trans (hconst (n + 1) hn_succ).symm)

theorem cantorEventuallyConstant_iff_finite_changePoints
    (b : cantor_space) :
    cantorEventuallyConstant b ↔ (cantorChangePointMap b : Set ℕ).Finite :=
  ⟨cantorChangePointMap_finite_of_eventuallyConstant b,
    cantorEventuallyConstant_of_finite_changePoints b⟩

theorem cantorNonEventuallyConstantSet_iff_not_eventuallyConstant
    (b : cantor_space) :
    b ∈ cantorNonEventuallyConstantSet ↔ ¬ cantorEventuallyConstant b := by
  constructor
  · intro hinf heventual
    rcases heventual with ⟨N, ε, hconst⟩
    rcases hinf.exists_gt N with ⟨n, hnChange, hNn⟩
    have hn : N ≤ n := le_of_lt hNn
    have hn_succ : N ≤ n + 1 := hn.trans (Nat.le_succ n)
    exact hnChange ((hconst n hn).trans (hconst (n + 1) hn_succ).symm)
  · intro hnot
    by_contra hnotInf
    exact hnot (cantorEventuallyConstant_of_finite_changePoints b (Set.not_infinite.mp hnotInf))

/-- The non-eventually-constant branches are exactly the complement of the eventually
constant branches. -/
theorem cantorNonEventuallyConstantSet_eq_compl_eventuallyConstant :
    cantorNonEventuallyConstantSet =
      {b : cantor_space | ¬ cantorEventuallyConstant b} := by
  ext b
  exact cantorNonEventuallyConstantSet_iff_not_eventuallyConstant b

/-- Eventually constant branches lie outside the non-eventually-constant boundary `S`. -/
theorem cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
    {b : cantor_space} (hb : cantorEventuallyConstant b) :
    b ∉ cantorNonEventuallyConstantSet := by
  intro hS
  exact (cantorNonEventuallyConstantSet_iff_not_eventuallyConstant b).1 hS hb

/-- A branch with only finitely many changes lies outside the
non-eventually-constant boundary `S`. -/
theorem cantorFiniteChangePoints_not_mem_nonEventuallyConstantSet
    {b : cantor_space} (hfin : (cantorChangePointMap b : Set ℕ).Finite) :
    b ∉ cantorNonEventuallyConstantSet := by
  exact cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
    (cantorEventuallyConstant_of_finite_changePoints b hfin)

/-- Interpret a Stern--Brocot direction as the corresponding Cantor-space bit:
`L` is `false` and `R` is `true`. -/
def sternBrocotDirectionBool : sternBrocotDirection → Bool
  | sternBrocotDirection.left => false
  | sternBrocotDirection.right => true

@[simp]
theorem sternBrocotDirectionBool_left :
    sternBrocotDirectionBool sternBrocotDirection.left = false :=
  rfl

@[simp]
theorem sternBrocotDirectionBool_right :
    sternBrocotDirectionBool sternBrocotDirection.right = true :=
  rfl

/-- The Cantor-space finite word associated to a finite Stern--Brocot L/R word. -/
def sternBrocotWordBool (w : sternBrocotWord) : finseq Bool :=
  w.map sternBrocotDirectionBool

@[simp]
theorem sternBrocotWordBool_length (w : sternBrocotWord) :
    (sternBrocotWordBool w).length = w.length := by
  simp [sternBrocotWordBool]

theorem sternBrocotWordBool_append (u v : sternBrocotWord) :
    sternBrocotWordBool (u ++ v) =
      sternBrocotWordBool u ++ sternBrocotWordBool v := by
  simp [sternBrocotWordBool]

/-- Interpret a Cantor-space bit as the corresponding Stern--Brocot direction. -/
def sternBrocotBoolDirection : Bool → sternBrocotDirection
  | false => sternBrocotDirection.left
  | true => sternBrocotDirection.right

@[simp]
theorem sternBrocotBoolDirection_false :
    sternBrocotBoolDirection false = sternBrocotDirection.left :=
  rfl

@[simp]
theorem sternBrocotBoolDirection_true :
    sternBrocotBoolDirection true = sternBrocotDirection.right :=
  rfl

/-- Convert a finite Cantor-space word to the corresponding finite L/R word. -/
def sternBrocotWordOfBool (w : finseq Bool) : sternBrocotWord :=
  w.map sternBrocotBoolDirection

@[simp]
theorem sternBrocotWordBool_ofBool (w : finseq Bool) :
    sternBrocotWordBool (sternBrocotWordOfBool w) = w := by
  induction w with
  | nil =>
      simp [sternBrocotWordOfBool, sternBrocotWordBool]
  | cons b bs ih =>
      cases b <;> simpa [sternBrocotWordOfBool, sternBrocotWordBool] using ih

@[simp]
theorem sternBrocotWordOfBool_wordBool (w : sternBrocotWord) :
    sternBrocotWordOfBool (sternBrocotWordBool w) = w := by
  induction w with
  | nil =>
      simp [sternBrocotWordOfBool, sternBrocotWordBool]
  | cons d ds ih =>
      cases d <;> simpa [sternBrocotWordOfBool, sternBrocotWordBool] using ih

theorem sternBrocotWordBool_injective :
    Function.Injective sternBrocotWordBool := by
  intro u v h
  have h' := congrArg sternBrocotWordOfBool h
  simpa using h'

/-- The branch with finite prefix `w` and constant tail `tail`. -/
def finiteWordConstantTailBranch (w : finseq Bool) (tail : Bool) : cantor_space :=
  fun n => if h : n < w.length then w.get ⟨n, h⟩ else tail

theorem finiteWordConstantTailBranch_of_lt
    (w : finseq Bool) (tail : Bool) {n : ℕ} (hn : n < w.length) :
    finiteWordConstantTailBranch w tail n = w.get ⟨n, hn⟩ := by
  simp [finiteWordConstantTailBranch, hn]

theorem finiteWordConstantTailBranch_of_length_le
    (w : finseq Bool) (tail : Bool) {n : ℕ} (hn : w.length ≤ n) :
    finiteWordConstantTailBranch w tail n = tail := by
  simp [finiteWordConstantTailBranch, not_lt.mpr hn]

theorem finiteWordConstantTailBranch_mem_cyl
    (w : finseq Bool) (tail : Bool) :
    finiteWordConstantTailBranch w tail ∈ cyl w := by
  intro n hn
  exact finiteWordConstantTailBranch_of_lt w tail hn

theorem finiteWordConstantTailBranch_eventuallyConstant
    (w : finseq Bool) (tail : Bool) :
    cantorEventuallyConstant (finiteWordConstantTailBranch w tail) :=
  ⟨w.length, tail, fun _ hn => finiteWordConstantTailBranch_of_length_le w tail hn⟩

theorem finiteWordConstantTailBranch_seqPrefix_eventuallyConstant
    {b : cantor_space} {N : ℕ} {tail : Bool}
    (hconst : ∀ n : ℕ, N ≤ n → b n = tail) :
    finiteWordConstantTailBranch (seqPrefix b N) tail = b := by
  funext n
  by_cases hn : n < (seqPrefix b N).length
  · rw [finiteWordConstantTailBranch_of_lt _ _ hn]
    exact seqPrefix_get b hn
  · have hlen : (seqPrefix b N).length ≤ n := not_lt.mp hn
    have hN : N ≤ n := by simpa [seqPrefix_length] using hlen
    rw [finiteWordConstantTailBranch_of_length_le _ _ hlen]
    exact (hconst n hN).symm

theorem finiteWordConstantTailBranch_seqPrefix_concat_eq_of_tail
    {b : cantor_space} {m : ℕ} {bit tail : Bool}
    (hbit : b m = bit)
    (hconst : ∀ n : ℕ, m + 1 ≤ n → b n = tail) :
    finiteWordConstantTailBranch (seqPrefix b m ++ [bit]) tail = b := by
  funext n
  by_cases hn : n < (seqPrefix b m ++ [bit]).length
  · have hnle : n ≤ m := by
      simpa [seqPrefix_length] using Nat.le_of_lt_succ (by simpa [seqPrefix_length] using hn)
    rcases Nat.lt_or_eq_of_le hnle with hnlt | rfl
    · rw [finiteWordConstantTailBranch_of_lt _ _ hn]
      simp [seqPrefix, hnlt]
    · rw [finiteWordConstantTailBranch_of_lt _ _ hn]
      simp [seqPrefix_length, hbit]
  · have htail_len : (seqPrefix b m ++ [bit]).length ≤ n := not_lt.mp hn
    have hm : m + 1 ≤ n := by simpa [seqPrefix_length] using htail_len
    rw [finiteWordConstantTailBranch_of_length_le _ _ htail_len]
    exact (hconst n hm).symm

theorem cantorEventuallyConstant_eq_finiteWordConstantTailBranch
    {b : cantor_space} (hb : cantorEventuallyConstant b) :
    ∃ w : finseq Bool, ∃ tail : Bool, b = finiteWordConstantTailBranch w tail := by
  rcases hb with ⟨N, tail, hconst⟩
  exact ⟨seqPrefix b N, tail,
    (finiteWordConstantTailBranch_seqPrefix_eventuallyConstant hconst).symm⟩

theorem cantorEventuallyConstant_eq_finiteSternBrocotWordConstantTailBranch
    {b : cantor_space} (hb : cantorEventuallyConstant b) :
    ∃ w : sternBrocotWord, ∃ tail : Bool,
      b = finiteWordConstantTailBranch (sternBrocotWordBool w) tail := by
  rcases cantorEventuallyConstant_eq_finiteWordConstantTailBranch hb with
    ⟨w, tail, hbw⟩
  exact ⟨sternBrocotWordOfBool w, tail, by simpa using hbw⟩

theorem cantorEventuallyConstant_iff_exists_finiteWordConstantTailBranch
    (b : cantor_space) :
    cantorEventuallyConstant b ↔
      ∃ w : finseq Bool, ∃ tail : Bool, b = finiteWordConstantTailBranch w tail := by
  constructor
  · exact cantorEventuallyConstant_eq_finiteWordConstantTailBranch
  · rintro ⟨w, tail, rfl⟩
    exact finiteWordConstantTailBranch_eventuallyConstant w tail

theorem cantorNotMemNonEventuallyConstantSet_iff_exists_finiteWordConstantTailBranch
    (b : cantor_space) :
    b ∉ cantorNonEventuallyConstantSet ↔
      ∃ w : finseq Bool, ∃ tail : Bool, b = finiteWordConstantTailBranch w tail := by
  constructor
  · intro hnotS
    have hb : cantorEventuallyConstant b := by
      by_contra hnot
      exact hnotS ((cantorNonEventuallyConstantSet_iff_not_eventuallyConstant b).2 hnot)
    exact cantorEventuallyConstant_eq_finiteWordConstantTailBranch hb
  · rintro ⟨w, tail, rfl⟩
    exact cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
      (finiteWordConstantTailBranch_eventuallyConstant w tail)

theorem cantorNotMemNonEventuallyConstantSet_iff_exists_finiteSternBrocotWordConstantTailBranch
    (b : cantor_space) :
    b ∉ cantorNonEventuallyConstantSet ↔
      ∃ w : sternBrocotWord, ∃ tail : Bool,
        b = finiteWordConstantTailBranch (sternBrocotWordBool w) tail := by
  constructor
  · intro hnotS
    have hb : cantorEventuallyConstant b := by
      by_contra hnot
      exact hnotS ((cantorNonEventuallyConstantSet_iff_not_eventuallyConstant b).2 hnot)
    exact cantorEventuallyConstant_eq_finiteSternBrocotWordConstantTailBranch hb
  · rintro ⟨w, tail, rfl⟩
    exact cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
      (finiteWordConstantTailBranch_eventuallyConstant (sternBrocotWordBool w) tail)

/-- Exact complement form of the book's definition of the non-eventually-constant
Stern--Brocot boundary `S`. -/
theorem cantorNonEventuallyConstantSet_iff_not_exists_finiteSternBrocotWordConstantTailBranch
    (b : cantor_space) :
    b ∈ cantorNonEventuallyConstantSet ↔
      ¬ ∃ w : sternBrocotWord, ∃ tail : Bool,
        b = finiteWordConstantTailBranch (sternBrocotWordBool w) tail := by
  constructor
  · intro hb hshape
    exact (cantorNotMemNonEventuallyConstantSet_iff_exists_finiteSternBrocotWordConstantTailBranch
      b).2 hshape hb
  · intro hnot
    by_contra hb
    exact hnot
      ((cantorNotMemNonEventuallyConstantSet_iff_exists_finiteSternBrocotWordConstantTailBranch
        b).1 hb)

theorem finiteWordConstantTailBranch_not_mem_nonEventuallyConstantSet
    (w : finseq Bool) (tail : Bool) :
    finiteWordConstantTailBranch w tail ∉ cantorNonEventuallyConstantSet :=
  cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
    (finiteWordConstantTailBranch_eventuallyConstant w tail)

/-- Book-facing statement for the LHS sentence that eventually constant branches
are exactly finite L/R words followed by a constant tail. -/
def ConcreteSternBrocotEventuallyConstantBranchStatement : Prop :=
    (∀ b : cantor_space,
      cantorEventuallyConstant b ↔
        ∃ w : finseq Bool, ∃ tail : Bool,
          b = finiteWordConstantTailBranch w tail) ∧
      (∀ b : cantor_space,
        cantorEventuallyConstant b →
          ∃ w : sternBrocotWord, ∃ tail : Bool,
            b = finiteWordConstantTailBranch (sternBrocotWordBool w) tail) ∧
      (∀ b : cantor_space,
        b ∉ cantorNonEventuallyConstantSet ↔
          ∃ w : finseq Bool, ∃ tail : Bool,
            b = finiteWordConstantTailBranch w tail) ∧
      (∀ b : cantor_space,
        b ∉ cantorNonEventuallyConstantSet ↔
          ∃ w : sternBrocotWord, ∃ tail : Bool,
            b = finiteWordConstantTailBranch (sternBrocotWordBool w) tail)

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The boundary of the binary tree is the Cantor space $\CantorSpace$ of infinite L/R words. The eventually-constant
    branches are those of the form $b \concat \wordRepeat{L}{\omega}$ or $b \concat \wordRepeat{R}{\omega}$ for some $b \in
    \finseq{2}$.
-/
/-- Book-facing package proving the eventually-constant branch statement. -/
theorem concreteSternBrocotEventuallyConstantBranchFacts :
    ConcreteSternBrocotEventuallyConstantBranchStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    exact cantorEventuallyConstant_iff_exists_finiteWordConstantTailBranch b
  · intro b hb
    exact cantorEventuallyConstant_eq_finiteSternBrocotWordConstantTailBranch hb
  · intro b
    exact cantorNotMemNonEventuallyConstantSet_iff_exists_finiteWordConstantTailBranch b
  · intro b
    exact cantorNotMemNonEventuallyConstantSet_iff_exists_finiteSternBrocotWordConstantTailBranch b

/-- The constant `L^ω` Stern--Brocot boundary branch, represented by `false`. -/
def sternBrocotAllLeftBranch : cantor_space :=
  finiteWordConstantTailBranch [] false

/-- The constant `R^ω` Stern--Brocot boundary branch, represented by `true`. -/
def sternBrocotAllRightBranch : cantor_space :=
  finiteWordConstantTailBranch [] true

@[simp]
theorem sternBrocotAllLeftBranch_apply (n : ℕ) :
    sternBrocotAllLeftBranch n = false := by
  simp [sternBrocotAllLeftBranch, finiteWordConstantTailBranch]

@[simp]
theorem sternBrocotAllRightBranch_apply (n : ℕ) :
    sternBrocotAllRightBranch n = true := by
  simp [sternBrocotAllRightBranch, finiteWordConstantTailBranch]

theorem sternBrocotAllLeftBranch_eventuallyConstant :
    cantorEventuallyConstant sternBrocotAllLeftBranch :=
  finiteWordConstantTailBranch_eventuallyConstant [] false

theorem sternBrocotAllRightBranch_eventuallyConstant :
    cantorEventuallyConstant sternBrocotAllRightBranch :=
  finiteWordConstantTailBranch_eventuallyConstant [] true

theorem sternBrocotAllLeftBranch_not_mem_nonEventuallyConstantSet :
    sternBrocotAllLeftBranch ∉ cantorNonEventuallyConstantSet :=
  cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
    sternBrocotAllLeftBranch_eventuallyConstant

theorem sternBrocotAllRightBranch_not_mem_nonEventuallyConstantSet :
    sternBrocotAllRightBranch ∉ cantorNonEventuallyConstantSet :=
  cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
    sternBrocotAllRightBranch_eventuallyConstant

theorem sternBrocotAllLeftBranch_ne_allRightBranch :
    sternBrocotAllLeftBranch ≠ sternBrocotAllRightBranch := by
  intro h
  have hcoord := congrFun h 0
  simp at hcoord

/-- Book-facing branch statement for the two special endpoint clauses
`L^ω` and `R^ω`. The later mediant-limit map is expected to send these
branches to `0` and `∞`, respectively. -/
def ConcreteSternBrocotSpecialEndpointBranchStatement : Prop :=
    (∀ n : ℕ, sternBrocotAllLeftBranch n = false) ∧
      (∀ n : ℕ, sternBrocotAllRightBranch n = true) ∧
      cantorEventuallyConstant sternBrocotAllLeftBranch ∧
      cantorEventuallyConstant sternBrocotAllRightBranch ∧
      sternBrocotAllLeftBranch ∉ cantorNonEventuallyConstantSet ∧
      sternBrocotAllRightBranch ∉ cantorNonEventuallyConstantSet ∧
      sternBrocotAllLeftBranch ≠ sternBrocotAllRightBranch

/-- Book-facing package proving the two special endpoint branch clauses. -/
theorem concreteSternBrocotSpecialEndpointBranchFacts :
    ConcreteSternBrocotSpecialEndpointBranchStatement := by
  refine ⟨?_, ?_, sternBrocotAllLeftBranch_eventuallyConstant,
    sternBrocotAllRightBranch_eventuallyConstant,
    sternBrocotAllLeftBranch_not_mem_nonEventuallyConstantSet,
    sternBrocotAllRightBranch_not_mem_nonEventuallyConstantSet,
    sternBrocotAllLeftBranch_ne_allRightBranch⟩
  · intro n
    exact sternBrocotAllLeftBranch_apply n
  · intro n
    exact sternBrocotAllRightBranch_apply n

/-- The lower endpoint branch attached to a finite Stern--Brocot word `w`:
`wL R^ω` in the book's notation. -/
def sternBrocotEndpointBelowBranch (w : sternBrocotWord) : cantor_space :=
  finiteWordConstantTailBranch
    (sternBrocotWordBool (w ++ [sternBrocotDirection.left])) true

/-- The upper endpoint branch attached to a finite Stern--Brocot word `w`:
`wR L^ω` in the book's notation. -/
def sternBrocotEndpointAboveBranch (w : sternBrocotWord) : cantor_space :=
  finiteWordConstantTailBranch
    (sternBrocotWordBool (w ++ [sternBrocotDirection.right])) false

theorem sternBrocotEndpointBelowBranch_ofBool (w : finseq Bool) :
    sternBrocotEndpointBelowBranch (sternBrocotWordOfBool w) =
      finiteWordConstantTailBranch (w ++ [false]) true := by
  rw [sternBrocotEndpointBelowBranch, sternBrocotWordBool_append,
    sternBrocotWordBool_ofBool]
  simp [sternBrocotWordBool]

theorem sternBrocotEndpointAboveBranch_ofBool (w : finseq Bool) :
    sternBrocotEndpointAboveBranch (sternBrocotWordOfBool w) =
      finiteWordConstantTailBranch (w ++ [true]) false := by
  rw [sternBrocotEndpointAboveBranch, sternBrocotWordBool_append,
    sternBrocotWordBool_ofBool]
  simp [sternBrocotWordBool]

theorem sternBrocotEndpointBelowBranch_mem_cyl (w : sternBrocotWord) :
    sternBrocotEndpointBelowBranch w ∈
      cyl (sternBrocotWordBool (w ++ [sternBrocotDirection.left])) :=
  finiteWordConstantTailBranch_mem_cyl _ _

theorem sternBrocotEndpointAboveBranch_mem_cyl (w : sternBrocotWord) :
    sternBrocotEndpointAboveBranch w ∈
      cyl (sternBrocotWordBool (w ++ [sternBrocotDirection.right])) :=
  finiteWordConstantTailBranch_mem_cyl _ _

theorem sternBrocotEndpointBelowBranch_prefix
    (w : sternBrocotWord) {n : ℕ} (hn : n < w.length) :
    sternBrocotEndpointBelowBranch w n =
      (sternBrocotWordBool w).get ⟨n, by simpa [sternBrocotWordBool_length] using hn⟩ := by
  have hlt :
      n < (sternBrocotWordBool (w ++ [sternBrocotDirection.left])).length := by
    simpa [sternBrocotWordBool_length] using Nat.lt_succ_of_lt hn
  have hprefix := (sternBrocotEndpointBelowBranch_mem_cyl w) n hlt
  have hnbool : n < (sternBrocotWordBool w).length := by
    simpa [sternBrocotWordBool_length] using hn
  have hget :
      (sternBrocotWordBool (w ++ [sternBrocotDirection.left])).get ⟨n, hlt⟩ =
        (sternBrocotWordBool w).get ⟨n, hnbool⟩ := by
    simpa [sternBrocotWordBool_append] using
      (List.getElem_append_left (as := sternBrocotWordBool w)
        (bs := sternBrocotWordBool [sternBrocotDirection.left]) (i := n) hnbool)
  exact hprefix.trans hget

theorem sternBrocotEndpointAboveBranch_prefix
    (w : sternBrocotWord) {n : ℕ} (hn : n < w.length) :
    sternBrocotEndpointAboveBranch w n =
      (sternBrocotWordBool w).get ⟨n, by simpa [sternBrocotWordBool_length] using hn⟩ := by
  have hlt :
      n < (sternBrocotWordBool (w ++ [sternBrocotDirection.right])).length := by
    simpa [sternBrocotWordBool_length] using Nat.lt_succ_of_lt hn
  have hprefix := (sternBrocotEndpointAboveBranch_mem_cyl w) n hlt
  have hnbool : n < (sternBrocotWordBool w).length := by
    simpa [sternBrocotWordBool_length] using hn
  have hget :
      (sternBrocotWordBool (w ++ [sternBrocotDirection.right])).get ⟨n, hlt⟩ =
        (sternBrocotWordBool w).get ⟨n, hnbool⟩ := by
    simpa [sternBrocotWordBool_append] using
      (List.getElem_append_left (as := sternBrocotWordBool w)
        (bs := sternBrocotWordBool [sternBrocotDirection.right]) (i := n) hnbool)
  exact hprefix.trans hget

theorem sternBrocotEndpointBelowBranch_tail
    (w : sternBrocotWord) {n : ℕ} (hn : w.length + 1 ≤ n) :
    sternBrocotEndpointBelowBranch w n = true := by
  have hlen :
      (sternBrocotWordBool (w ++ [sternBrocotDirection.left])).length ≤ n := by
    simpa using hn
  exact finiteWordConstantTailBranch_of_length_le _ true hlen

theorem sternBrocotEndpointAboveBranch_tail
    (w : sternBrocotWord) {n : ℕ} (hn : w.length + 1 ≤ n) :
    sternBrocotEndpointAboveBranch w n = false := by
  have hlen :
      (sternBrocotWordBool (w ++ [sternBrocotDirection.right])).length ≤ n := by
    simpa using hn
  exact finiteWordConstantTailBranch_of_length_le _ false hlen

theorem sternBrocotEndpointBelowBranch_splitCoordinate
    (w : sternBrocotWord) :
    sternBrocotEndpointBelowBranch w w.length = false := by
  have hlt :
      w.length < (sternBrocotWordBool (w ++ [sternBrocotDirection.left])).length := by
    simp
  rw [sternBrocotEndpointBelowBranch,
    finiteWordConstantTailBranch_of_lt _ true hlt]
  simp [sternBrocotWordBool]

theorem sternBrocotEndpointAboveBranch_splitCoordinate
    (w : sternBrocotWord) :
    sternBrocotEndpointAboveBranch w w.length = true := by
  have hlt :
      w.length < (sternBrocotWordBool (w ++ [sternBrocotDirection.right])).length := by
    simp
  rw [sternBrocotEndpointAboveBranch,
    finiteWordConstantTailBranch_of_lt _ false hlt]
  simp [sternBrocotWordBool]

theorem sternBrocotEndpointBelowBranch_eventuallyConstant
    (w : sternBrocotWord) :
    cantorEventuallyConstant (sternBrocotEndpointBelowBranch w) :=
  finiteWordConstantTailBranch_eventuallyConstant _ _

theorem sternBrocotEndpointAboveBranch_eventuallyConstant
    (w : sternBrocotWord) :
    cantorEventuallyConstant (sternBrocotEndpointAboveBranch w) :=
  finiteWordConstantTailBranch_eventuallyConstant _ _

theorem sternBrocotEndpointBelowBranch_not_mem_nonEventuallyConstantSet
    (w : sternBrocotWord) :
    sternBrocotEndpointBelowBranch w ∉ cantorNonEventuallyConstantSet :=
  cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
    (sternBrocotEndpointBelowBranch_eventuallyConstant w)

theorem sternBrocotEndpointAboveBranch_not_mem_nonEventuallyConstantSet
    (w : sternBrocotWord) :
    sternBrocotEndpointAboveBranch w ∉ cantorNonEventuallyConstantSet :=
  cantorEventuallyConstant_not_mem_nonEventuallyConstantSet
    (sternBrocotEndpointAboveBranch_eventuallyConstant w)

theorem sternBrocotEndpointBranches_ne (w : sternBrocotWord) :
    sternBrocotEndpointBelowBranch w ≠ sternBrocotEndpointAboveBranch w := by
  intro h
  have hcoord := congrFun h w.length
  rw [sternBrocotEndpointBelowBranch_splitCoordinate,
    sternBrocotEndpointAboveBranch_splitCoordinate] at hcoord
  exact Bool.noConfusion hcoord

theorem sternBrocotEndpointBelowBranch_false_le_length
    (w : sternBrocotWord) {n : ℕ}
    (hfalse : sternBrocotEndpointBelowBranch w n = false) :
    n ≤ w.length := by
  by_contra hn
  have htail : sternBrocotEndpointBelowBranch w n = true :=
    sternBrocotEndpointBelowBranch_tail w (by omega)
  rw [htail] at hfalse
  exact Bool.noConfusion hfalse

theorem sternBrocotEndpointAboveBranch_true_le_length
    (w : sternBrocotWord) {n : ℕ}
    (htrue : sternBrocotEndpointAboveBranch w n = true) :
    n ≤ w.length := by
  by_contra hn
  have htail : sternBrocotEndpointAboveBranch w n = false :=
    sternBrocotEndpointAboveBranch_tail w (by omega)
  rw [htail] at htrue
  exact Bool.noConfusion htrue

theorem sternBrocotEndpointBelowBranch_injective :
    Function.Injective sternBrocotEndpointBelowBranch := by
  intro u v h
  have hle_uv : u.length ≤ v.length := by
    apply sternBrocotEndpointBelowBranch_false_le_length v
    rw [← congrFun h u.length]
    exact sternBrocotEndpointBelowBranch_splitCoordinate u
  have hle_vu : v.length ≤ u.length := by
    apply sternBrocotEndpointBelowBranch_false_le_length u
    rw [congrFun h v.length]
    exact sternBrocotEndpointBelowBranch_splitCoordinate v
  have hlen : u.length = v.length := le_antisymm hle_uv hle_vu
  apply sternBrocotWordBool_injective
  apply List.ext_get
  · simpa [sternBrocotWordBool_length] using hlen
  · intro n hu hv
    have hu' : n < u.length := by simpa [sternBrocotWordBool_length] using hu
    have hv' : n < v.length := by simpa [sternBrocotWordBool_length] using hv
    have hcoord := congrFun h n
    rw [sternBrocotEndpointBelowBranch_prefix u hu',
      sternBrocotEndpointBelowBranch_prefix v hv'] at hcoord
    exact hcoord

theorem sternBrocotEndpointAboveBranch_injective :
    Function.Injective sternBrocotEndpointAboveBranch := by
  intro u v h
  have hle_uv : u.length ≤ v.length := by
    apply sternBrocotEndpointAboveBranch_true_le_length v
    rw [← congrFun h u.length]
    exact sternBrocotEndpointAboveBranch_splitCoordinate u
  have hle_vu : v.length ≤ u.length := by
    apply sternBrocotEndpointAboveBranch_true_le_length u
    rw [congrFun h v.length]
    exact sternBrocotEndpointAboveBranch_splitCoordinate v
  have hlen : u.length = v.length := le_antisymm hle_uv hle_vu
  apply sternBrocotWordBool_injective
  apply List.ext_get
  · simpa [sternBrocotWordBool_length] using hlen
  · intro n hu hv
    have hu' : n < u.length := by simpa [sternBrocotWordBool_length] using hu
    have hv' : n < v.length := by simpa [sternBrocotWordBool_length] using hv
    have hcoord := congrFun h n
    rw [sternBrocotEndpointAboveBranch_prefix u hu',
      sternBrocotEndpointAboveBranch_prefix v hv'] at hcoord
    exact hcoord

theorem sternBrocotEndpointBelowBranch_ne_endpointAboveBranch
    (u v : sternBrocotWord) :
    sternBrocotEndpointBelowBranch u ≠ sternBrocotEndpointAboveBranch v := by
  intro h
  let n : ℕ := max (u.length + 1) (v.length + 1)
  have hu : u.length + 1 ≤ n := by
    exact le_max_left _ _
  have hv : v.length + 1 ≤ n := by
    exact le_max_right _ _
  have hcoord := congrFun h n
  rw [sternBrocotEndpointBelowBranch_tail u hu,
    sternBrocotEndpointAboveBranch_tail v hv] at hcoord
  exact Bool.noConfusion hcoord

theorem sternBrocotAllLeftBranch_ne_endpointBelowBranch
    (w : sternBrocotWord) :
    sternBrocotAllLeftBranch ≠ sternBrocotEndpointBelowBranch w := by
  intro h
  have hcoord := congrFun h (w.length + 1)
  rw [sternBrocotAllLeftBranch_apply,
    sternBrocotEndpointBelowBranch_tail w le_rfl] at hcoord
  exact Bool.noConfusion hcoord

theorem sternBrocotAllLeftBranch_ne_endpointAboveBranch
    (w : sternBrocotWord) :
    sternBrocotAllLeftBranch ≠ sternBrocotEndpointAboveBranch w := by
  intro h
  have hcoord := congrFun h w.length
  rw [sternBrocotAllLeftBranch_apply,
    sternBrocotEndpointAboveBranch_splitCoordinate w] at hcoord
  exact Bool.noConfusion hcoord

theorem sternBrocotAllRightBranch_ne_endpointBelowBranch
    (w : sternBrocotWord) :
    sternBrocotAllRightBranch ≠ sternBrocotEndpointBelowBranch w := by
  intro h
  have hcoord := congrFun h w.length
  rw [sternBrocotAllRightBranch_apply,
    sternBrocotEndpointBelowBranch_splitCoordinate w] at hcoord
  exact Bool.noConfusion hcoord

theorem sternBrocotAllRightBranch_ne_endpointAboveBranch
    (w : sternBrocotWord) :
    sternBrocotAllRightBranch ≠ sternBrocotEndpointAboveBranch w := by
  intro h
  have hcoord := congrFun h (w.length + 1)
  rw [sternBrocotAllRightBranch_apply,
    sternBrocotEndpointAboveBranch_tail w le_rfl] at hcoord
  exact Bool.noConfusion hcoord

theorem sternBrocotEndpointBelowBranch_eq_of_lastSwitchToRight
    {b : cantor_space} {m : ℕ}
    (hm : b m = false)
    (hconst : ∀ n : ℕ, m + 1 ≤ n → b n = true) :
    b = sternBrocotEndpointBelowBranch (sternBrocotWordOfBool (seqPrefix b m)) := by
  rw [sternBrocotEndpointBelowBranch_ofBool]
  exact (finiteWordConstantTailBranch_seqPrefix_concat_eq_of_tail hm hconst).symm

theorem sternBrocotEndpointAboveBranch_eq_of_lastSwitchToLeft
    {b : cantor_space} {m : ℕ}
    (hm : b m = true)
    (hconst : ∀ n : ℕ, m + 1 ≤ n → b n = false) :
    b = sternBrocotEndpointAboveBranch (sternBrocotWordOfBool (seqPrefix b m)) := by
  rw [sternBrocotEndpointAboveBranch_ofBool]
  exact (finiteWordConstantTailBranch_seqPrefix_concat_eq_of_tail hm hconst).symm

/-- Book-facing package for the local form of the rational endpoint branch
description: a branch whose last switch is from `L` to an eventual `R` tail is
`wL R^ω`, and a branch whose last switch is from `R` to an eventual `L` tail is
`wR L^ω`. -/
theorem concreteSternBrocotLastSwitchEndpointBranchFacts :
    (∀ b : cantor_space, ∀ m : ℕ,
      b m = false →
        (∀ n : ℕ, m + 1 ≤ n → b n = true) →
          b = sternBrocotEndpointBelowBranch (sternBrocotWordOfBool (seqPrefix b m))) ∧
      (∀ b : cantor_space, ∀ m : ℕ,
        b m = true →
          (∀ n : ℕ, m + 1 ≤ n → b n = false) →
            b = sternBrocotEndpointAboveBranch (sternBrocotWordOfBool (seqPrefix b m))) := by
  refine ⟨?_, ?_⟩
  · intro b m hm hconst
    exact sternBrocotEndpointBelowBranch_eq_of_lastSwitchToRight hm hconst
  · intro b m hm hconst
    exact sternBrocotEndpointAboveBranch_eq_of_lastSwitchToLeft hm hconst

theorem sternBrocotEndpointBelowBranch_exists_of_eventuallyRight_not_allRight
    {b : cantor_space}
    (hevent : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → b n = true)
    (hnotRight : b ≠ sternBrocotAllRightBranch) :
    ∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w := by
  rcases hevent with ⟨N, htail⟩
  have hfalse_exists : ∃ i : ℕ, b i = false := by
    by_contra hnone
    have hall : b = sternBrocotAllRightBranch := by
      funext n
      cases hbn : b n
      · exact False.elim (hnone ⟨n, hbn⟩)
      · simp
    exact hnotRight hall
  rcases hfalse_exists with ⟨i, hiFalse⟩
  have hiN : i < N := by
    by_contra hnot
    have hNi : N ≤ i := not_lt.mp hnot
    have hitrue := htail i hNi
    rw [hiFalse] at hitrue
    simp at hitrue
  let F : Finset ℕ := Finset.filter (fun n : ℕ => b n = false) (Finset.range N)
  have hFne : F.Nonempty := by
    refine ⟨i, ?_⟩
    simp [F, hiN, hiFalse]
  let m : ℕ := F.max' hFne
  have hm_mem : m ∈ F := by
    exact Finset.max'_mem F hFne
  have hmFalse : b m = false := (Finset.mem_filter.mp hm_mem).2
  have hlast : ∀ n : ℕ, m + 1 ≤ n → b n = true := by
    intro n hmn
    by_cases hNn : N ≤ n
    · exact htail n hNn
    · have hnN : n < N := not_le.mp hNn
      by_cases hnFalse : b n = false
      · have hn_mem : n ∈ F := by
          simp [F, hnN, hnFalse]
        have hn_le_m : n ≤ m := by
          exact Finset.le_max' F n hn_mem
        omega
      · cases hbn : b n
        · exact False.elim (hnFalse hbn)
        · rfl
  exact ⟨sternBrocotWordOfBool (seqPrefix b m),
    sternBrocotEndpointBelowBranch_eq_of_lastSwitchToRight hmFalse hlast⟩

theorem sternBrocotEndpointAboveBranch_exists_of_eventuallyLeft_not_allLeft
    {b : cantor_space}
    (hevent : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → b n = false)
    (hnotLeft : b ≠ sternBrocotAllLeftBranch) :
    ∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w := by
  rcases hevent with ⟨N, htail⟩
  have htrue_exists : ∃ i : ℕ, b i = true := by
    by_contra hnone
    have hall : b = sternBrocotAllLeftBranch := by
      funext n
      cases hbn : b n
      · simp
      · exact False.elim (hnone ⟨n, hbn⟩)
    exact hnotLeft hall
  rcases htrue_exists with ⟨i, hiTrue⟩
  have hiN : i < N := by
    by_contra hnot
    have hNi : N ≤ i := not_lt.mp hnot
    have hifalse := htail i hNi
    rw [hiTrue] at hifalse
    simp at hifalse
  let F : Finset ℕ := Finset.filter (fun n : ℕ => b n = true) (Finset.range N)
  have hFne : F.Nonempty := by
    refine ⟨i, ?_⟩
    simp [F, hiN, hiTrue]
  let m : ℕ := F.max' hFne
  have hm_mem : m ∈ F := by
    exact Finset.max'_mem F hFne
  have hmTrue : b m = true := (Finset.mem_filter.mp hm_mem).2
  have hlast : ∀ n : ℕ, m + 1 ≤ n → b n = false := by
    intro n hmn
    by_cases hNn : N ≤ n
    · exact htail n hNn
    · have hnN : n < N := not_le.mp hNn
      by_cases hnTrue : b n = true
      · have hn_mem : n ∈ F := by
          simp [F, hnN, hnTrue]
        have hn_le_m : n ≤ m := by
          exact Finset.le_max' F n hn_mem
        omega
      · cases hbn : b n
        · rfl
        · exact False.elim (hnTrue hbn)
  exact ⟨sternBrocotWordOfBool (seqPrefix b m),
    sternBrocotEndpointAboveBranch_eq_of_lastSwitchToLeft hmTrue hlast⟩

theorem cantorEventuallyConstant_nonconstant_endpointBranch
    {b : cantor_space} (hb : cantorEventuallyConstant b)
    (hnotLeft : b ≠ sternBrocotAllLeftBranch)
    (hnotRight : b ≠ sternBrocotAllRightBranch) :
    (∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w) ∨
      (∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w) := by
  rcases hb with ⟨N, tail, htail⟩
  cases tail
  · right
    exact sternBrocotEndpointAboveBranch_exists_of_eventuallyLeft_not_allLeft
      ⟨N, htail⟩ hnotLeft
  · left
    exact sternBrocotEndpointBelowBranch_exists_of_eventuallyRight_not_allRight
      ⟨N, htail⟩ hnotRight

/-- Book-facing package for the nonconstant part of `CantorSpace \ S`: after
removing the two constant branches, every eventually constant branch has one of
the two rational endpoint shapes. -/
theorem concreteSternBrocotNonconstantEventuallyConstantEndpointFacts :
    (∀ b : cantor_space,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → b n = true) →
        b ≠ sternBrocotAllRightBranch →
          ∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w) ∧
      (∀ b : cantor_space,
        (∃ N : ℕ, ∀ n : ℕ, N ≤ n → b n = false) →
          b ≠ sternBrocotAllLeftBranch →
            ∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w) ∧
      (∀ b : cantor_space,
        cantorEventuallyConstant b →
          b ≠ sternBrocotAllLeftBranch →
            b ≠ sternBrocotAllRightBranch →
              (∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w) ∨
                (∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hevent hnotRight
    exact sternBrocotEndpointBelowBranch_exists_of_eventuallyRight_not_allRight
      hevent hnotRight
  · intro b hevent hnotLeft
    exact sternBrocotEndpointAboveBranch_exists_of_eventuallyLeft_not_allLeft
      hevent hnotLeft
  · intro b hb hnotLeft hnotRight
    exact cantorEventuallyConstant_nonconstant_endpointBranch hb hnotLeft hnotRight

theorem cantorEventuallyConstant_iff_specialOrEndpointBranch
    (b : cantor_space) :
    cantorEventuallyConstant b ↔
      b = sternBrocotAllLeftBranch ∨
        b = sternBrocotAllRightBranch ∨
          (∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w) ∨
            ∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w := by
  constructor
  · intro hb
    by_cases hleft : b = sternBrocotAllLeftBranch
    · exact Or.inl hleft
    · by_cases hright : b = sternBrocotAllRightBranch
      · exact Or.inr (Or.inl hright)
      · rcases cantorEventuallyConstant_nonconstant_endpointBranch hb hleft hright with
          hbelow | habove
        · exact Or.inr (Or.inr (Or.inl hbelow))
        · exact Or.inr (Or.inr (Or.inr habove))
  · rintro (rfl | hright | hbelow | habove)
    · exact sternBrocotAllLeftBranch_eventuallyConstant
    · rw [hright]
      exact sternBrocotAllRightBranch_eventuallyConstant
    · rcases hbelow with ⟨w, rfl⟩
      exact sternBrocotEndpointBelowBranch_eventuallyConstant w
    · rcases habove with ⟨w, rfl⟩
      exact sternBrocotEndpointAboveBranch_eventuallyConstant w

theorem cantorNotMemNonEventuallyConstantSet_iff_specialOrEndpointBranch
    (b : cantor_space) :
    b ∉ cantorNonEventuallyConstantSet ↔
      b = sternBrocotAllLeftBranch ∨
        b = sternBrocotAllRightBranch ∨
          (∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w) ∨
            ∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w := by
  constructor
  · intro hnotS
    have hb : cantorEventuallyConstant b := by
      by_contra hnot
      exact hnotS ((cantorNonEventuallyConstantSet_iff_not_eventuallyConstant b).2 hnot)
    exact (cantorEventuallyConstant_iff_specialOrEndpointBranch b).1 hb
  · intro hshape
    have hb : cantorEventuallyConstant b :=
      (cantorEventuallyConstant_iff_specialOrEndpointBranch b).2 hshape
    exact cantorEventuallyConstant_not_mem_nonEventuallyConstantSet hb

/-- Book-facing structural statement classifying the complement of `S`: it is the
two special constant branches together with the two finite endpoint-branch
families. This is the branch-level part of the mediant-limit paragraph before
the numeric values of `\Phi` are assigned. -/
def ConcreteSternBrocotComplementEndpointBranchStatement : Prop :=
    (∀ b : cantor_space,
      cantorEventuallyConstant b ↔
        b = sternBrocotAllLeftBranch ∨
          b = sternBrocotAllRightBranch ∨
            (∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w) ∨
              ∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w) ∧
      (∀ b : cantor_space,
        b ∉ cantorNonEventuallyConstantSet ↔
          b = sternBrocotAllLeftBranch ∨
            b = sternBrocotAllRightBranch ∨
              (∃ w : sternBrocotWord, b = sternBrocotEndpointBelowBranch w) ∨
                ∃ w : sternBrocotWord, b = sternBrocotEndpointAboveBranch w)

/-- Book-facing package proving the structural classification of the complement of `S`. -/
theorem concreteSternBrocotComplementEndpointBranchFacts :
    ConcreteSternBrocotComplementEndpointBranchStatement := by
  refine ⟨?_, ?_⟩
  · intro b
    exact cantorEventuallyConstant_iff_specialOrEndpointBranch b
  · intro b
    exact cantorNotMemNonEventuallyConstantSet_iff_specialOrEndpointBranch b

/-- The lower endpoint branch attached to a finite continued-fraction cylinder
label. This is the branch `bL R^ω` at the finite Stern--Brocot node coded by
`(a₀, pref)`. -/
def sternBrocotFiniteCylinderEndpointBelowBranch
    (a₀ : ℕ) (pref : finseq positiveNat) : cantor_space :=
  sternBrocotEndpointBelowBranch (sternBrocotRunLengthWord a₀ pref)

/-- The upper endpoint branch attached to a finite continued-fraction cylinder
label. This is the branch `bR L^ω` at the finite Stern--Brocot node coded by
`(a₀, pref)`. -/
def sternBrocotFiniteCylinderEndpointAboveBranch
    (a₀ : ℕ) (pref : finseq positiveNat) : cantor_space :=
  sternBrocotEndpointAboveBranch (sternBrocotRunLengthWord a₀ pref)

theorem sternBrocotFiniteCylinderEndpointBelowBranch_not_mem_nonEventuallyConstantSet
    (a₀ : ℕ) (pref : finseq positiveNat) :
    sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∉ cantorNonEventuallyConstantSet :=
  sternBrocotEndpointBelowBranch_not_mem_nonEventuallyConstantSet _

theorem sternBrocotFiniteCylinderEndpointAboveBranch_not_mem_nonEventuallyConstantSet
    (a₀ : ℕ) (pref : finseq positiveNat) :
    sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref ∉ cantorNonEventuallyConstantSet :=
  sternBrocotEndpointAboveBranch_not_mem_nonEventuallyConstantSet _

theorem sternBrocotFiniteCylinderEndpointBranches_ne
    (a₀ : ℕ) (pref : finseq positiveNat) :
    sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ≠
      sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref :=
  sternBrocotEndpointBranches_ne _

theorem sternBrocotFiniteCylinderEndpointBelowBranch_ne_aboveBranch
    (a₀ b₀ : ℕ) (pref qref : finseq positiveNat) :
    sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ≠
      sternBrocotFiniteCylinderEndpointAboveBranch b₀ qref :=
  sternBrocotEndpointBelowBranch_ne_endpointAboveBranch
    (sternBrocotRunLengthWord a₀ pref) (sternBrocotRunLengthWord b₀ qref)

theorem sternBrocotFiniteCylinderEndpointBelowBranch_eq_iff_runLengthWord_eq
    (a₀ b₀ : ℕ) (pref qref : finseq positiveNat) :
    sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref =
        sternBrocotFiniteCylinderEndpointBelowBranch b₀ qref ↔
      sternBrocotRunLengthWord a₀ pref = sternBrocotRunLengthWord b₀ qref := by
  constructor
  · intro h
    exact sternBrocotEndpointBelowBranch_injective
      (by simpa [sternBrocotFiniteCylinderEndpointBelowBranch] using h)
  · intro h
    simp [sternBrocotFiniteCylinderEndpointBelowBranch, h]

theorem sternBrocotFiniteCylinderEndpointAboveBranch_eq_iff_runLengthWord_eq
    (a₀ b₀ : ℕ) (pref qref : finseq positiveNat) :
    sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref =
        sternBrocotFiniteCylinderEndpointAboveBranch b₀ qref ↔
      sternBrocotRunLengthWord a₀ pref = sternBrocotRunLengthWord b₀ qref := by
  constructor
  · intro h
    exact sternBrocotEndpointAboveBranch_injective
      (by simpa [sternBrocotFiniteCylinderEndpointAboveBranch] using h)
  · intro h
    simp [sternBrocotFiniteCylinderEndpointAboveBranch, h]

theorem sternBrocotFiniteCylinderLabel_eq_of_endpointBelowBranch_eq
    {a₀ b₀ : ℕ} {pref qref : finseq positiveNat}
    (h :
      sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref =
        sternBrocotFiniteCylinderEndpointBelowBranch b₀ qref) :
    sternBrocotFiniteCylinderLabel a₀ pref =
      sternBrocotFiniteCylinderLabel b₀ qref :=
  sternBrocotFiniteCylinderLabel_eq_of_runLengthWord_eq
    ((sternBrocotFiniteCylinderEndpointBelowBranch_eq_iff_runLengthWord_eq
      a₀ b₀ pref qref).1 h)

theorem sternBrocotFiniteCylinderLabel_eq_of_endpointAboveBranch_eq
    {a₀ b₀ : ℕ} {pref qref : finseq positiveNat}
    (h :
      sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref =
        sternBrocotFiniteCylinderEndpointAboveBranch b₀ qref) :
    sternBrocotFiniteCylinderLabel a₀ pref =
      sternBrocotFiniteCylinderLabel b₀ qref :=
  sternBrocotFiniteCylinderLabel_eq_of_runLengthWord_eq
    ((sternBrocotFiniteCylinderEndpointAboveBranch_eq_iff_runLengthWord_eq
      a₀ b₀ pref qref).1 h)

theorem sternBrocotEndpointBelowBranch_exists_finiteCylinder
    (w : sternBrocotWord) :
    ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
      sternBrocotEndpointBelowBranch w =
        sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref := by
  rcases sternBrocotRunLengthWord_surjective w with ⟨a₀, pref, hword⟩
  refine ⟨a₀, pref, ?_⟩
  rw [sternBrocotFiniteCylinderEndpointBelowBranch, hword]

theorem sternBrocotEndpointAboveBranch_exists_finiteCylinder
    (w : sternBrocotWord) :
    ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
      sternBrocotEndpointAboveBranch w =
        sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref := by
  rcases sternBrocotRunLengthWord_surjective w with ⟨a₀, pref, hword⟩
  refine ⟨a₀, pref, ?_⟩
  rw [sternBrocotFiniteCylinderEndpointAboveBranch, hword]

/-- Book-facing statement bridging arbitrary finite L/R nodes to finite continued-
fraction cylinder nodes. The LHS writes the rational endpoint clause using an
arbitrary finite node `b`; the numeric Lean specification indexes those same
nodes by finite run-length data. -/
def ConcreteSternBrocotFiniteWordRunLengthBridgeStatement : Prop :=
    (∀ w : sternBrocotWord,
      ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
        sternBrocotRunLengthWord a₀ pref = w) ∧
      Function.Bijective sternBrocotFiniteCylinderRunLengthWord ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotRunLengthWord a₀ pref = [] ↔ a₀ = 0 ∧ pref = []) ∧
      (∀ a : positiveNat, ∀ tail : List positiveNat, ∀ b₀ : ℕ,
        ∀ qref : finseq positiveNat,
          sternBrocotRunLengthWord 0 (a :: tail) ≠
            sternBrocotRunLengthWord (b₀ + 1) qref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        sternBrocotRunLengthWord a₀ pref =
          sternBrocotRunLengthWord b₀ qref →
            a₀ = b₀ ∧ pref = qref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        sternBrocotRunLengthWord a₀ pref =
          sternBrocotRunLengthWord b₀ qref →
            sternBrocotFiniteCylinderLabel a₀ pref =
              sternBrocotFiniteCylinderLabel b₀ qref) ∧
      (∀ w : sternBrocotWord,
        ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
          sternBrocotEndpointBelowBranch w =
            sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref) ∧
      (∀ w : sternBrocotWord,
        ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
          sternBrocotEndpointAboveBranch w =
            sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref =
            sternBrocotFiniteCylinderEndpointBelowBranch b₀ qref ↔
          sternBrocotRunLengthWord a₀ pref = sternBrocotRunLengthWord b₀ qref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref =
            sternBrocotFiniteCylinderEndpointAboveBranch b₀ qref ↔
          sternBrocotRunLengthWord a₀ pref = sternBrocotRunLengthWord b₀ qref)

/-- Book-facing package proving the finite L/R word run-length bridge statement. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The mediant $m$ is the label of the node $w$. Indeed, successive L moves replace the upper endpoint by
    $(c+ka)/(d+kb)$, and successive R moves replace the lower endpoint by $(a+kc)/(b+kd)$. Substitution in the
    continued-fraction recurrence $(*)$ gives the run-length labels above.
-/
theorem concreteSternBrocotFiniteWordRunLengthBridgeFacts :
    ConcreteSternBrocotFiniteWordRunLengthBridgeStatement := by
  refine ⟨?_, sternBrocotFiniteCylinderRunLengthWord_bijective, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    exact sternBrocotRunLengthWord_surjective w
  · intro a₀ pref
    exact sternBrocotRunLengthWord_eq_nil_iff a₀ pref
  · intro a tail b₀ qref
    exact sternBrocotRunLengthWord_zero_cons_ne_succ a tail b₀ qref
  · intro a₀ b₀ pref qref h
    exact sternBrocotRunLengthWord_injective h
  · intro a₀ b₀ pref qref h
    exact sternBrocotFiniteCylinderLabel_eq_of_runLengthWord_eq h
  · intro w
    exact sternBrocotEndpointBelowBranch_exists_finiteCylinder w
  · intro w
    exact sternBrocotEndpointAboveBranch_exists_finiteCylinder w
  · intro a₀ b₀ pref qref
    exact sternBrocotFiniteCylinderEndpointBelowBranch_eq_iff_runLengthWord_eq
      a₀ b₀ pref qref
  · intro a₀ b₀ pref qref
    exact sternBrocotFiniteCylinderEndpointAboveBranch_eq_iff_runLengthWord_eq
      a₀ b₀ pref qref

/-- Every positive rational finite label comes with the two endpoint branches
attached to one realizing finite Stern--Brocot node. This is the branch-level
existence half of the book's rational endpoint clause, before assigning the
common mediant-limit value. -/
theorem sternBrocotPositiveRat_endpointBranches_exist
    (q : ℚ) (hq : 0 < q) :
    ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
      sternBrocotFiniteCylinderLabel a₀ pref = q ∧
        sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∉
          cantorNonEventuallyConstantSet ∧
        sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref ∉
          cantorNonEventuallyConstantSet ∧
        sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ≠
          sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref := by
  rcases sternBrocotFiniteCylinderLabel_surjective_positiveRat q hq with
    ⟨a₀, pref, hlabel⟩
  exact ⟨a₀, pref, hlabel,
    sternBrocotFiniteCylinderEndpointBelowBranch_not_mem_nonEventuallyConstantSet a₀ pref,
    sternBrocotFiniteCylinderEndpointAboveBranch_not_mem_nonEventuallyConstantSet a₀ pref,
    sternBrocotFiniteCylinderEndpointBranches_ne a₀ pref⟩

/-- Every positive rational has a pair of distinct eventually constant endpoint
branches outside `S`, attached to a finite Stern--Brocot node with that rational
label. The later mediant-limit map is expected to identify this pair to the
same value. -/
theorem sternBrocotPositiveRat_two_distinct_endpointBranches
    (q : ℚ) (hq : 0 < q) :
    ∃ bBelow bAbove : cantor_space,
      bBelow ∉ cantorNonEventuallyConstantSet ∧
        bAbove ∉ cantorNonEventuallyConstantSet ∧
        bBelow ≠ bAbove ∧
        ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
          sternBrocotFiniteCylinderLabel a₀ pref = q ∧
            bBelow = sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∧
            bAbove = sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref := by
  rcases sternBrocotPositiveRat_endpointBranches_exist q hq with
    ⟨a₀, pref, hlabel, hbelowS, haboveS, hne⟩
  refine ⟨sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref,
    sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref,
    hbelowS, haboveS, hne, a₀, pref, hlabel, rfl, rfl⟩

/-- Book-facing statement for the branch shapes in the rational endpoint clause of
the mediant-limit paragraph: a finite word has two eventually constant endpoint
branches, `wL R^ω` and `wR L^ω`, both agree with `w` before the closing
opposite letter, and both lie outside `S`. -/
def ConcreteSternBrocotRationalEndpointBranchStatement : Prop :=
    (∀ w : sternBrocotWord,
      sternBrocotEndpointBelowBranch w ∈
        cyl (sternBrocotWordBool (w ++ [sternBrocotDirection.left]))) ∧
      (∀ w : sternBrocotWord,
        sternBrocotEndpointAboveBranch w ∈
          cyl (sternBrocotWordBool (w ++ [sternBrocotDirection.right]))) ∧
      (∀ w : sternBrocotWord, ∀ n : ℕ, ∀ hn : n < w.length,
        sternBrocotEndpointBelowBranch w n =
          (sternBrocotWordBool w).get
            ⟨n, by simpa [sternBrocotWordBool_length] using hn⟩) ∧
      (∀ w : sternBrocotWord, ∀ n : ℕ, ∀ hn : n < w.length,
        sternBrocotEndpointAboveBranch w n =
          (sternBrocotWordBool w).get
            ⟨n, by simpa [sternBrocotWordBool_length] using hn⟩) ∧
      (∀ w : sternBrocotWord, ∀ n : ℕ, w.length + 1 ≤ n →
        sternBrocotEndpointBelowBranch w n = true) ∧
      (∀ w : sternBrocotWord, ∀ n : ℕ, w.length + 1 ≤ n →
        sternBrocotEndpointAboveBranch w n = false) ∧
      (∀ w : sternBrocotWord,
        sternBrocotEndpointBelowBranch w w.length = false) ∧
      (∀ w : sternBrocotWord,
        sternBrocotEndpointAboveBranch w w.length = true) ∧
      (∀ w : sternBrocotWord,
        cantorEventuallyConstant (sternBrocotEndpointBelowBranch w)) ∧
      (∀ w : sternBrocotWord,
        cantorEventuallyConstant (sternBrocotEndpointAboveBranch w)) ∧
      (∀ w : sternBrocotWord,
        sternBrocotEndpointBelowBranch w ∉ cantorNonEventuallyConstantSet) ∧
      (∀ w : sternBrocotWord,
        sternBrocotEndpointAboveBranch w ∉ cantorNonEventuallyConstantSet) ∧
      (∀ w : sternBrocotWord,
        sternBrocotEndpointBelowBranch w ≠ sternBrocotEndpointAboveBranch w) ∧
      Function.Injective sternBrocotEndpointBelowBranch ∧
      Function.Injective sternBrocotEndpointAboveBranch ∧
      (∀ u v : sternBrocotWord,
        sternBrocotEndpointBelowBranch u ≠ sternBrocotEndpointAboveBranch v) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∉
          cantorNonEventuallyConstantSet) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref ∉
          cantorNonEventuallyConstantSet) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ≠
          sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) ∧
      (∀ a₀ b₀ : ℕ, ∀ pref qref : finseq positiveNat,
        sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ≠
          sternBrocotFiniteCylinderEndpointAboveBranch b₀ qref) ∧
      (∀ q : ℚ, 0 < q →
        ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
          sternBrocotFiniteCylinderLabel a₀ pref = q ∧
            sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∉
              cantorNonEventuallyConstantSet ∧
            sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref ∉
              cantorNonEventuallyConstantSet ∧
            sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ≠
              sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) ∧
      (∀ q : ℚ, 0 < q →
        ∃ bBelow bAbove : cantor_space,
          bBelow ∉ cantorNonEventuallyConstantSet ∧
            bAbove ∉ cantorNonEventuallyConstantSet ∧
            bBelow ≠ bAbove ∧
            ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
              sternBrocotFiniteCylinderLabel a₀ pref = q ∧
                bBelow = sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∧
                bAbove = sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref)

/-- Book-facing package proving the rational endpoint-branch shape statement. -/
theorem concreteSternBrocotRationalEndpointBranchFacts :
    ConcreteSternBrocotRationalEndpointBranchStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro w
    exact sternBrocotEndpointBelowBranch_mem_cyl w
  · intro w
    exact sternBrocotEndpointAboveBranch_mem_cyl w
  · intro w n hn
    exact sternBrocotEndpointBelowBranch_prefix w hn
  · intro w n hn
    exact sternBrocotEndpointAboveBranch_prefix w hn
  · intro w n hn
    exact sternBrocotEndpointBelowBranch_tail w hn
  · intro w n hn
    exact sternBrocotEndpointAboveBranch_tail w hn
  · intro w
    exact sternBrocotEndpointBelowBranch_splitCoordinate w
  · intro w
    exact sternBrocotEndpointAboveBranch_splitCoordinate w
  · intro w
    exact sternBrocotEndpointBelowBranch_eventuallyConstant w
  · intro w
    exact sternBrocotEndpointAboveBranch_eventuallyConstant w
  · intro w
    exact sternBrocotEndpointBelowBranch_not_mem_nonEventuallyConstantSet w
  · intro w
    exact sternBrocotEndpointAboveBranch_not_mem_nonEventuallyConstantSet w
  · intro w
    exact sternBrocotEndpointBranches_ne w
  · exact sternBrocotEndpointBelowBranch_injective
  · exact sternBrocotEndpointAboveBranch_injective
  · intro u v
    exact sternBrocotEndpointBelowBranch_ne_endpointAboveBranch u v
  · intro a₀ pref
    exact sternBrocotFiniteCylinderEndpointBelowBranch_not_mem_nonEventuallyConstantSet a₀ pref
  · intro a₀ pref
    exact sternBrocotFiniteCylinderEndpointAboveBranch_not_mem_nonEventuallyConstantSet a₀ pref
  · intro a₀ pref
    exact sternBrocotFiniteCylinderEndpointBranches_ne a₀ pref
  · intro a₀ b₀ pref qref
    exact sternBrocotFiniteCylinderEndpointBelowBranch_ne_aboveBranch a₀ b₀ pref qref
  · intro q hq
    exact sternBrocotPositiveRat_endpointBranches_exist q hq
  · intro q hq
    exact sternBrocotPositiveRat_two_distinct_endpointBranches q hq

/-- Reconstruct a binary branch from its initial bit and its set of change points. -/
noncomputable def branchFromChangePoints (ε : Bool) (A : powersetOmega) : cantor_space
  | 0 => ε
  | n + 1 => by
      classical
      exact
      if n ∈ (A : Set ℕ) then
        !(branchFromChangePoints ε A n)
      else
        branchFromChangePoints ε A n

@[simp]
theorem branchFromChangePoints_zero (ε : Bool) (A : powersetOmega) :
    branchFromChangePoints ε A 0 = ε :=
  rfl

theorem branchFromChangePoints_succ (ε : Bool) (A : powersetOmega) (n : ℕ) :
    branchFromChangePoints ε A (n + 1) =
      if n ∈ (A : Set ℕ) then
        !(branchFromChangePoints ε A n)
      else
        branchFromChangePoints ε A n :=
  rfl

theorem branchFromChangePoints_change_iff (ε : Bool) (A : powersetOmega) (n : ℕ) :
    branchFromChangePoints ε A n ≠ branchFromChangePoints ε A (n + 1) ↔
      n ∈ (A : Set ℕ) := by
  rw [branchFromChangePoints_succ]
  by_cases hn : n ∈ (A : Set ℕ)
  · cases branchFromChangePoints ε A n <;> simp [hn]
  · simp [hn]

theorem cantorChangePointMap_branchFromChangePoints (ε : Bool) (A : powersetOmega) :
    cantorChangePointMap (branchFromChangePoints ε A) = A := by
  ext n
  exact branchFromChangePoints_change_iff ε A n

theorem branchFromChangePoints_cantorChangePointMap (b : cantor_space) :
    branchFromChangePoints (b 0) (cantorChangePointMap b) = b := by
  funext n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases hn : n ∈ (cantorChangePointMap b : Set ℕ)
      · rw [branchFromChangePoints_succ]
        simp [hn]
        rw [ih]
        have hne : b n ≠ b (n + 1) := hn
        cases hbn : b n <;> cases hbs : b (n + 1) <;> simp [hbn, hbs] at hne ⊢
      · have hsame : b n = b (n + 1) := by
          by_contra hne
          exact hn hne
        rw [branchFromChangePoints_succ]
        simp [hn]
        rw [ih]
        exact hsame

theorem branchFromChangePoints_eq_of_agree_below (ε : Bool) {A B : powersetOmega} :
    ∀ n : ℕ,
      (∀ m : ℕ, m < n → (m ∈ (A : Set ℕ) ↔ m ∈ (B : Set ℕ))) →
        branchFromChangePoints ε A n = branchFromChangePoints ε B n := by
  intro n
  induction n with
  | zero =>
      intro hagree
      simp
  | succ n ih =>
      intro hagree
      have hprev :
          branchFromChangePoints ε A n = branchFromChangePoints ε B n :=
        ih fun m hm => hagree m (Nat.lt_trans hm (Nat.lt_succ_self n))
      have hn : n ∈ (A : Set ℕ) ↔ n ∈ (B : Set ℕ) :=
        hagree n (Nat.lt_succ_self n)
      rw [branchFromChangePoints_succ, branchFromChangePoints_succ]
      by_cases hA : n ∈ (A : Set ℕ)
      · have hB : n ∈ (B : Set ℕ) := hn.1 hA
        simp [hA, hB, hprev]
      · have hB : n ∉ (B : Set ℕ) := fun h => hA (hn.2 h)
        simp [hA, hB, hprev]

/-- Boolean operation detecting whether two adjacent branch bits differ. -/
def boolChange (p : Bool × Bool) : Bool :=
  if p.1 = p.2 then false else true

/-- Boolean operation that flips the current bit exactly when the membership flag is true. -/
def boolFlipIf (p : Bool × Bool) : Bool :=
  if p.1 then !p.2 else p.2

theorem powersetMembership_continuous (n : ℕ) :
    Continuous (fun A : powersetOmega => subsetCharacteristic A n) :=
  (continuous_apply n).comp powersetOmegaHomeomorphCantorSpace.continuous

theorem cantorChangePointMap_coordinate_eq_boolChange (n : ℕ) :
    (fun b : cantor_space => subsetCharacteristic (cantorChangePointMap b) n) =
      fun b : cantor_space => boolChange (b n, b (n + 1)) := by
  funext b
  cases hbn : b n <;> cases hbs : b (n + 1) <;>
    simp [subsetCharacteristic, cantorChangePointMap, cantorChangePointSet,
      boolChange, hbn, hbs]

theorem cantorChangePointMap_mem_iff (b : cantor_space) (n : ℕ) :
    n ∈ (cantorChangePointMap b : Set ℕ) ↔ b n ≠ b (n + 1) := by
  rfl

theorem cantorChangePointMap_mem_congr_of_eq_adjacent {b c : cantor_space} {n : ℕ}
    (h₀ : b n = c n) (h₁ : b (n + 1) = c (n + 1)) :
    n ∈ (cantorChangePointMap b : Set ℕ) ↔ n ∈ (cantorChangePointMap c : Set ℕ) := by
  rw [cantorChangePointMap_mem_iff, cantorChangePointMap_mem_iff, h₀, h₁]

theorem cantorChangePointMap_eq_on_lt_of_eq_on_succ {b c : cantor_space} {N : ℕ}
    (hagree : ∀ m : ℕ, m < N + 1 → b m = c m) :
    ∀ n : ℕ, n < N →
      (n ∈ (cantorChangePointMap b : Set ℕ) ↔ n ∈ (cantorChangePointMap c : Set ℕ)) := by
  intro n hn
  exact cantorChangePointMap_mem_congr_of_eq_adjacent
    (hagree n (Nat.lt_trans hn (Nat.lt_succ_self N)))
    (hagree (n + 1) (Nat.succ_lt_succ hn))

theorem cantorChangePointMap_continuous :
    Continuous cantorChangePointMap := by
  rw [← powersetOmegaHomeomorphCantorSpace.comp_continuous_iff]
  change Continuous (fun b : cantor_space => powersetOmegaHomeomorphCantorSpace
    (cantorChangePointMap b))
  rw [show (fun b : cantor_space => powersetOmegaHomeomorphCantorSpace
      (cantorChangePointMap b)) =
        fun b : cantor_space => subsetCharacteristic (cantorChangePointMap b) by
    funext b
    simp [powersetOmegaHomeomorphCantorSpace_apply]]
  refine continuous_pi ?_
  intro n
  rw [cantorChangePointMap_coordinate_eq_boolChange n]
  exact (continuous_of_discreteTopology (f := boolChange)).comp
    ((continuous_apply n).prodMk (continuous_apply (n + 1)))

theorem branchFromChangePoints_coordinate_eq_boolFlipIf (ε : Bool) (n : ℕ) :
    (fun A : powersetOmega => branchFromChangePoints ε A (n + 1)) =
      fun A : powersetOmega =>
        boolFlipIf (subsetCharacteristic A n, branchFromChangePoints ε A n) := by
  funext A
  by_cases hn : n ∈ (A : Set ℕ)
  · simp [branchFromChangePoints_succ, boolFlipIf, subsetCharacteristic, hn]
  · simp [branchFromChangePoints_succ, boolFlipIf, subsetCharacteristic, hn]

theorem branchFromChangePoints_coordinate_continuous (ε : Bool) :
    ∀ n : ℕ, Continuous (fun A : powersetOmega => branchFromChangePoints ε A n) := by
  intro n
  induction n with
  | zero =>
      simpa using continuous_const
  | succ n ih =>
      rw [branchFromChangePoints_coordinate_eq_boolFlipIf ε n]
      exact (continuous_of_discreteTopology (f := boolFlipIf)).comp
        ((powersetMembership_continuous n).prodMk ih)

theorem branchFromChangePoints_continuous (ε : Bool) :
    Continuous (branchFromChangePoints ε) := by
  refine continuous_pi ?_
  intro n
  exact branchFromChangePoints_coordinate_continuous ε n

/-- Change points of the reconstructed branch recover the original infinite set. -/
theorem cantorChangePointMap_branchFromInfiniteSubset (ε : Bool) (A : infiniteSubsetsOmega) :
    cantorChangePointMap (branchFromChangePoints ε (A : powersetOmega)) = (A : powersetOmega) :=
  cantorChangePointMap_branchFromChangePoints ε (A : powersetOmega)

/-- Reconstructing from an infinite set gives a non-eventually-constant branch with the
prescribed initial bit. -/
noncomputable def branchFromInfiniteSubset (ε : Bool) (A : infiniteSubsetsOmega) :
    {b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε} :=
  ⟨branchFromChangePoints ε (A : powersetOmega),
    by
      constructor
      · change Set.Infinite
          (cantorChangePointMap (branchFromChangePoints ε (A : powersetOmega)) : Set ℕ)
        rw [cantorChangePointMap_branchFromInfiniteSubset]
        exact A.2
      · simp⟩

/-- The reconstructed branch `H_ε(A)` starts with the prescribed initial bit. -/
@[simp]
theorem branchFromInfiniteSubset_zero (ε : Bool) (A : infiniteSubsetsOmega) :
    (branchFromInfiniteSubset ε A).1 0 = ε :=
  rfl

/-- The reconstructed branch flips after coordinate `n` exactly when `n ∈ A`. -/
theorem branchFromInfiniteSubset_succ (ε : Bool) (A : infiniteSubsetsOmega) (n : ℕ) :
    (branchFromInfiniteSubset ε A).1 (n + 1) =
      if n ∈ (A : Set ℕ) then
        !((branchFromInfiniteSubset ε A).1 n)
      else
        (branchFromInfiniteSubset ε A).1 n := by
  rfl

/-- Equivalently, the change-point set of `H_ε(A)` is detected coordinatewise by
membership in `A`. -/
theorem branchFromInfiniteSubset_change_iff (ε : Bool) (A : infiniteSubsetsOmega) (n : ℕ) :
    (branchFromInfiniteSubset ε A).1 n ≠ (branchFromInfiniteSubset ε A).1 (n + 1) ↔
      n ∈ (A : Set ℕ) := by
  exact branchFromChangePoints_change_iff ε (A : powersetOmega) n

theorem branchFromInfiniteSubset_eq_of_agree_below (ε : Bool)
    {A B : infiniteSubsetsOmega} {n : ℕ}
    (hagree : ∀ m : ℕ, m < n → (m ∈ (A : Set ℕ) ↔ m ∈ (B : Set ℕ))) :
    (branchFromInfiniteSubset ε A).1 n = (branchFromInfiniteSubset ε B).1 n := by
  exact branchFromChangePoints_eq_of_agree_below ε n hagree

/-- Book-facing finite-prefix form: the first `k` reconstructed bits depend only
on membership below `k`. -/
theorem branchFromInfiniteSubset_eq_on_lt_of_agree_below (ε : Bool)
    {A B : infiniteSubsetsOmega} {k : ℕ}
    (hagree : ∀ m : ℕ, m < k → (m ∈ (A : Set ℕ) ↔ m ∈ (B : Set ℕ))) :
    ∀ i : ℕ, i < k →
      (branchFromInfiniteSubset ε A).1 i = (branchFromInfiniteSubset ε B).1 i := by
  intro i hi
  exact branchFromInfiniteSubset_eq_of_agree_below ε
    (fun m hm => hagree m (Nat.lt_trans hm hi))

/-- The change-point map restricted to one initial-bit half of the non-eventually-constant
branches. -/
noncomputable def infiniteSubsetFromBranchChanges (ε : Bool)
    (b : {b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε}) :
    infiniteSubsetsOmega :=
  ⟨cantorChangePointMap b.1, b.2.1⟩

theorem branchFromInfiniteSubset_continuous (ε : Bool) :
    Continuous (branchFromInfiniteSubset ε) :=
  ((branchFromChangePoints_continuous ε).comp continuous_subtype_val).subtype_mk _

theorem infiniteSubsetFromBranchChanges_continuous (ε : Bool) :
    Continuous (infiniteSubsetFromBranchChanges ε) :=
  (cantorChangePointMap_continuous.comp continuous_subtype_val).subtype_mk _

theorem infiniteSubsetFromBranchChanges_branchFromInfiniteSubset
    (ε : Bool) (A : infiniteSubsetsOmega) :
    infiniteSubsetFromBranchChanges ε (branchFromInfiniteSubset ε A) = A := by
  apply Subtype.ext
  exact cantorChangePointMap_branchFromInfiniteSubset ε A

theorem branchFromInfiniteSubset_infiniteSubsetFromBranchChanges
    (ε : Bool)
    (b : {b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε}) :
    branchFromInfiniteSubset ε (infiniteSubsetFromBranchChanges ε b) = b := by
  apply Subtype.ext
  change branchFromChangePoints ε (cantorChangePointMap b.1) = b.1
  simpa [b.2.2] using branchFromChangePoints_cantorChangePointMap b.1

/-- For each fixed initial bit, change points give a set-level equivalence between the
corresponding half of the non-eventually-constant binary branches and infinite subsets of
`ω`. -/
noncomputable def branchChangePointEquiv (ε : Bool) :
    {b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε} ≃
      infiniteSubsetsOmega where
  toFun := infiniteSubsetFromBranchChanges ε
  invFun := branchFromInfiniteSubset ε
  left_inv := branchFromInfiniteSubset_infiniteSubsetFromBranchChanges ε
  right_inv := infiniteSubsetFromBranchChanges_branchFromInfiniteSubset ε

/-- For each fixed initial bit, the change-point map is a homeomorphism from that half
of the non-eventually-constant binary branches to the space of infinite subsets of `ω`. -/
noncomputable def branchChangePointHomeomorph (ε : Bool) :
    {b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε} ≃ₜ
      infiniteSubsetsOmega where
  toEquiv := branchChangePointEquiv ε
  continuous_toFun := infiniteSubsetFromBranchChanges_continuous ε
  continuous_invFun := branchFromInfiniteSubset_continuous ε

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For the topology, fix an initial letter $\varepsilon\in\{L,R\}$ and define
    $$H_\varepsilon:\infiniteSubsets{\omega}\to\{b\in S:b_0=\varepsilon\}$$
    by starting with $H_\varepsilon(A)_0=\varepsilon$ and flipping the letter between positions $n$ and $n+1$ exactly when
    $n\in A$. Then $\Delta(H_\varepsilon(A))=A$, and $\Delta$ is the inverse of $H_\varepsilon$ on the $\varepsilon$-half of
    $S$. The map $H_\varepsilon$ is continuous because the first $k$ bits of $H_\varepsilon(A)$ depend only on $A\cap k$.
-/
theorem branchChangePointHomeomorphismFact (ε : Bool) :
    Nonempty ({b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε} ≃ₜ
      infiniteSubsetsOmega) :=
  ⟨branchChangePointHomeomorph ε⟩

/-- Non-eventually-constant binary branches, as a subspace of Cantor space. -/
abbrev cantorNonEventuallyConstantBranches : Type :=
  cantorNonEventuallyConstantSet

def cantorNonEventuallyConstantInitialBitHalf (ε : Bool) :
    Set cantorNonEventuallyConstantBranches :=
  {b | b.1 0 = ε}

theorem isClopen_cantorNonEventuallyConstantInitialBitHalf (ε : Bool) :
    IsClopen (cantorNonEventuallyConstantInitialBitHalf ε) := by
  exact (isClopen_discrete ({ε} : Set Bool)).preimage
    ((continuous_apply 0).comp continuous_subtype_val)

theorem cantorNonEventuallyConstantInitialBitHalf_false_union_true :
    cantorNonEventuallyConstantInitialBitHalf false ∪
      cantorNonEventuallyConstantInitialBitHalf true =
        (Set.univ : Set cantorNonEventuallyConstantBranches) := by
  ext b
  cases b.1 0 <;> simp [cantorNonEventuallyConstantInitialBitHalf]

theorem disjoint_cantorNonEventuallyConstantInitialBitHalves :
    Disjoint (cantorNonEventuallyConstantInitialBitHalf false)
      (cantorNonEventuallyConstantInitialBitHalf true) := by
  rw [Set.disjoint_left]
  intro b hbfalse hbtrue
  simp [cantorNonEventuallyConstantInitialBitHalf] at hbfalse hbtrue
  exact Bool.noConfusion (hbfalse.symm.trans hbtrue)

/-- The global change-point map records the initial bit and the infinite set of
change points. -/
noncomputable def branchChangePointProductMap
    (b : cantorNonEventuallyConstantBranches) :
    Bool × infiniteSubsetsOmega :=
  (b.1 0, ⟨cantorChangePointMap b.1, b.2⟩)

/-- Reconstruct a non-eventually-constant branch from its initial bit and its infinite
set of change points. -/
noncomputable def branchFromInitialAndChanges
    (p : Bool × infiniteSubsetsOmega) :
    cantorNonEventuallyConstantBranches :=
  ⟨branchFromChangePoints p.1 (p.2 : powersetOmega),
    by
      change Set.Infinite
        (cantorChangePointMap (branchFromChangePoints p.1 (p.2 : powersetOmega)) : Set ℕ)
      rw [cantorChangePointMap_branchFromChangePoints]
      exact p.2.2⟩

theorem branchChangePointProductMap_branchFromInitialAndChanges
    (p : Bool × infiniteSubsetsOmega) :
    branchChangePointProductMap (branchFromInitialAndChanges p) = p := by
  cases p with
  | mk ε A =>
      apply Prod.ext
      · simp [branchChangePointProductMap, branchFromInitialAndChanges]
      · apply Subtype.ext
        exact cantorChangePointMap_branchFromChangePoints ε (A : powersetOmega)

theorem branchFromInitialAndChanges_branchChangePointProductMap
    (b : cantorNonEventuallyConstantBranches) :
    branchFromInitialAndChanges (branchChangePointProductMap b) = b := by
  apply Subtype.ext
  change branchFromChangePoints (b.1 0) (cantorChangePointMap b.1) = b.1
  exact branchFromChangePoints_cantorChangePointMap b.1

/-- The set-level split of non-eventually-constant branches by their initial bit and
change-point set. -/
noncomputable def branchChangePointProductEquiv :
    cantorNonEventuallyConstantBranches ≃ Bool × infiniteSubsetsOmega where
  toFun := branchChangePointProductMap
  invFun := branchFromInitialAndChanges
  left_inv := branchFromInitialAndChanges_branchChangePointProductMap
  right_inv := branchChangePointProductMap_branchFromInitialAndChanges

theorem branchChangePointProductMap_continuous :
    Continuous branchChangePointProductMap := by
  exact ((continuous_apply 0).comp continuous_subtype_val).prodMk
    ((cantorChangePointMap_continuous.comp continuous_subtype_val).subtype_mk _)

theorem branchFromInitialAndChanges_coordinate_continuous :
    ∀ n : ℕ, Continuous (fun p : Bool × infiniteSubsetsOmega =>
      branchFromChangePoints p.1 (p.2 : powersetOmega) n) := by
  intro n
  induction n with
  | zero =>
      simpa using continuous_fst
  | succ n ih =>
      rw [show (fun p : Bool × infiniteSubsetsOmega =>
          branchFromChangePoints p.1 (p.2 : powersetOmega) (n + 1)) =
            fun p : Bool × infiniteSubsetsOmega =>
              boolFlipIf
                (subsetCharacteristic (p.2 : powersetOmega) n,
                  branchFromChangePoints p.1 (p.2 : powersetOmega) n) by
        funext p
        simpa using congrFun
          (branchFromChangePoints_coordinate_eq_boolFlipIf p.1 n)
          (p.2 : powersetOmega)]
      exact (continuous_of_discreteTopology (f := boolFlipIf)).comp
        (((powersetMembership_continuous n).comp
            (continuous_subtype_val.comp continuous_snd)).prodMk ih)

theorem branchFromInitialAndChanges_continuous :
    Continuous branchFromInitialAndChanges :=
  (continuous_pi branchFromInitialAndChanges_coordinate_continuous).subtype_mk _

/-- The homeomorphic split
`S ≅ 2 × infiniteSubsetsOmega` from the book's change-point construction. -/
noncomputable def branchChangePointProductHomeomorph :
    cantorNonEventuallyConstantBranches ≃ₜ Bool × infiniteSubsetsOmega where
  toEquiv := branchChangePointProductEquiv
  continuous_toFun := branchChangePointProductMap_continuous
  continuous_invFun := branchFromInitialAndChanges_continuous

theorem branchChangePointProductHomeomorph_apply
    (b : cantorNonEventuallyConstantBranches) :
    branchChangePointProductHomeomorph b =
      (b.1 0, ⟨cantorChangePointMap b.1, b.2⟩) :=
  rfl

theorem branchChangePointProductHomeomorph_apply_initialBit
    (b : cantorNonEventuallyConstantBranches) :
    (branchChangePointProductHomeomorph b).1 = b.1 0 :=
  rfl

theorem branchChangePointProductHomeomorph_apply_changePoints
    (b : cantorNonEventuallyConstantBranches) :
    (branchChangePointProductHomeomorph b).2 = ⟨cantorChangePointMap b.1, b.2⟩ :=
  rfl

theorem branchChangePointProductHomeomorph_symm_apply
    (p : Bool × infiniteSubsetsOmega) :
    branchChangePointProductHomeomorph.symm p = branchFromInitialAndChanges p :=
  rfl

theorem branchChangePointProductHomeomorph_symm_apply_initialBit
    (p : Bool × infiniteSubsetsOmega) :
    (branchChangePointProductHomeomorph.symm p).1 0 = p.1 := by
  cases p
  rfl

theorem branchChangePointProductHomeomorph_symm_apply_changePoints
    (p : Bool × infiniteSubsetsOmega) :
    cantorChangePointMap (branchChangePointProductHomeomorph.symm p).1 =
      (p.2 : powersetOmega) := by
  rw [branchChangePointProductHomeomorph_symm_apply]
  cases p with
  | mk ε A =>
      exact cantorChangePointMap_branchFromChangePoints ε (A : powersetOmega)

/-- The product split sends each clopen initial-bit half of `S` onto the
corresponding product slice. -/
theorem branchChangePointProductHomeomorph_image_initialBitHalf (ε : Bool) :
    branchChangePointProductHomeomorph '' cantorNonEventuallyConstantInitialBitHalf ε =
      {p : Bool × infiniteSubsetsOmega | p.1 = ε} := by
  ext p
  constructor
  · rintro ⟨b, hb, hp⟩
    rw [← hp]
    simpa [cantorNonEventuallyConstantInitialBitHalf, branchChangePointProductHomeomorph,
      branchChangePointProductEquiv, branchChangePointProductMap] using hb
  · intro hp
    refine ⟨branchChangePointProductHomeomorph.symm p, ?_, ?_⟩
    · change (branchChangePointProductHomeomorph.symm p).1 0 = ε
      exact (branchChangePointProductHomeomorph_symm_apply_initialBit p).trans hp
    · exact branchChangePointProductHomeomorph.apply_symm_apply p

theorem branchChangePointProductHomeomorphismFact :
    Nonempty (cantorNonEventuallyConstantBranches ≃ₜ Bool × infiniteSubsetsOmega) :=
  ⟨branchChangePointProductHomeomorph⟩

/-- The increasing enumeration of an infinite subset of `ω`. -/
noncomputable def infiniteSubsetsOmegaNth (A : infiniteSubsetsOmega) (n : ℕ) : ℕ :=
  Nat.nth (fun m => m ∈ (A : Set ℕ)) n

theorem infiniteSubsetsOmegaNth_mem (A : infiniteSubsetsOmega) (n : ℕ) :
    infiniteSubsetsOmegaNth A n ∈ (A : Set ℕ) := by
  exact Nat.nth_mem_of_infinite (show Set.Infinite (A : Set ℕ) from A.2) n

theorem infiniteSubsetsOmegaNth_strictMono (A : infiniteSubsetsOmega) :
    StrictMono (infiniteSubsetsOmegaNth A) := by
  exact Nat.nth_strictMono (show Set.Infinite (A : Set ℕ) from A.2)

theorem infiniteSubsetsOmegaNth_eq_of_agree_below {A B : infiniteSubsetsOmega} {N k : ℕ}
    (hagree : ∀ m, m < N → (m ∈ (B : Set ℕ) ↔ m ∈ (A : Set ℕ)))
    (hkN : infiniteSubsetsOmegaNth A k < N) :
    infiniteSubsetsOmegaNth B k = infiniteSubsetsOmegaNth A k := by
  classical
  let p : ℕ → Prop := fun m => m ∈ (A : Set ℕ)
  let q : ℕ → Prop := fun m => m ∈ (B : Set ℕ)
  have hpInf : (Set.ofPred p).Infinite := by
    simpa [p] using (show Set.Infinite (A : Set ℕ) from A.2)
  have hq_at : q (infiniteSubsetsOmegaNth A k) :=
    (hagree _ hkN).2 (infiniteSubsetsOmegaNth_mem A k)
  have hcount_eq :
      Nat.count q (infiniteSubsetsOmegaNth A k) =
        Nat.count p (infiniteSubsetsOmegaNth A k) := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    ext m
    constructor
    · intro hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
      exact ⟨hm.1, (hagree m (hm.1.trans hkN)).1 hm.2⟩
    · intro hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
      exact ⟨hm.1, (hagree m (hm.1.trans hkN)).2 hm.2⟩
  have hcount_q : Nat.count q (infiniteSubsetsOmegaNth A k) = k := by
    rw [hcount_eq]
    simpa [p, infiniteSubsetsOmegaNth] using Nat.count_nth_of_infinite hpInf k
  calc
    infiniteSubsetsOmegaNth B k = Nat.nth q k := by
          rfl
    _ = Nat.nth q (Nat.count q (infiniteSubsetsOmegaNth A k)) := by
          rw [hcount_q]
    _ = infiniteSubsetsOmegaNth A k := by
          rw [Nat.nth_count]
          exact hq_at

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    If $A=\{a_0<a_1<a_2<\cdots\}$, the \termforward{gap map} sends
    $$
    A\longmapsto(a_0,\;a_1-a_0-1,\;a_2-a_1-1,\ldots)\in\BaireSpace
    $$
    and has inverse
    $$
    (g_0,g_1,g_2,\ldots)\longmapsto\{g_0,\;g_0+g_1+1,\;g_0+g_1+g_2+2,\ldots\}.
    $$
-/
/-- The book's gap map from an infinite subset to Baire space. -/
noncomputable def infiniteSubsetsOmegaGapMap (A : infiniteSubsetsOmega) : baire_space
  | 0 => infiniteSubsetsOmegaNth A 0
  | n + 1 => infiniteSubsetsOmegaNth A (n + 1) - infiniteSubsetsOmegaNth A n - 1

@[simp]
theorem infiniteSubsetsOmegaGapMap_zero (A : infiniteSubsetsOmega) :
    infiniteSubsetsOmegaGapMap A 0 = infiniteSubsetsOmegaNth A 0 :=
  rfl

@[simp]
theorem infiniteSubsetsOmegaGapMap_succ (A : infiniteSubsetsOmega) (n : ℕ) :
    infiniteSubsetsOmegaGapMap A (n + 1) =
      infiniteSubsetsOmegaNth A (n + 1) - infiniteSubsetsOmegaNth A n - 1 :=
  rfl

/-- Finite initial-gap data for an infinite subset `A`: the finite word `s` records
`a₀`, then the successive gaps `aᵢ₊₁ - aᵢ - 1`. -/
def infiniteSubsetsOmegaInitialGapData (A : infiniteSubsetsOmega) (s : finseq ℕ) : Prop :=
  (∀ h0 : 0 < s.length, infiniteSubsetsOmegaNth A 0 = s.get ⟨0, h0⟩) ∧
    ∀ n (hn : n + 1 < s.length),
      infiniteSubsetsOmegaNth A (n + 1) - infiniteSubsetsOmegaNth A n - 1 =
        s.get ⟨n + 1, hn⟩

/-- Finite Baire prefixes for the gap map are exactly finite initial-gap data for
infinite subsets of `ω`. -/
theorem infiniteSubsetsOmegaGapMap_mem_cyl_iff_initialGapData
    (A : infiniteSubsetsOmega) (s : finseq ℕ) :
    infiniteSubsetsOmegaGapMap A ∈ cyl s ↔
      infiniteSubsetsOmegaInitialGapData A s := by
  constructor
  · intro h
    constructor
    · intro h0
      simpa [infiniteSubsetsOmegaGapMap] using h 0 h0
    · intro n hn
      simpa [infiniteSubsetsOmegaGapMap] using h (n + 1) hn
  · rintro ⟨h0, hs⟩ i hi
    cases i with
    | zero =>
        simpa [infiniteSubsetsOmegaGapMap] using h0 hi
    | succ n =>
        simpa [infiniteSubsetsOmegaGapMap] using hs n hi

theorem infiniteSubsetsOmegaGapMap_eq_of_agree_below {A B : infiniteSubsetsOmega}
    {N i : ℕ}
    (hagree : ∀ m, m < N → (m ∈ (B : Set ℕ) ↔ m ∈ (A : Set ℕ)))
    (hiN : infiniteSubsetsOmegaNth A i < N) :
    infiniteSubsetsOmegaGapMap B i = infiniteSubsetsOmegaGapMap A i := by
  cases i with
  | zero =>
      have hi_eq :
          infiniteSubsetsOmegaNth B 0 = infiniteSubsetsOmegaNth A 0 :=
        infiniteSubsetsOmegaNth_eq_of_agree_below (A := A) (B := B) (N := N)
          hagree hiN
      simp [infiniteSubsetsOmegaGapMap, hi_eq]
  | succ i =>
      have hi_eq :
          infiniteSubsetsOmegaNth B (i + 1) = infiniteSubsetsOmegaNth A (i + 1) :=
        infiniteSubsetsOmegaNth_eq_of_agree_below (A := A) (B := B) (N := N)
          hagree hiN
      have hpredN : infiniteSubsetsOmegaNth A i < N :=
        (infiniteSubsetsOmegaNth_strictMono A (Nat.lt_succ_self i)).trans hiN
      have hpred_eq :
          infiniteSubsetsOmegaNth B i = infiniteSubsetsOmegaNth A i :=
        infiniteSubsetsOmegaNth_eq_of_agree_below (A := A) (B := B) (N := N)
          hagree hpredN
      simp [infiniteSubsetsOmegaGapMap, hi_eq, hpred_eq]

theorem infiniteSubsetsOmegaGapMap_eq_on_lt_of_agree_below {A B : infiniteSubsetsOmega}
    {N k : ℕ}
    (hagree : ∀ m, m < N → (m ∈ (B : Set ℕ) ↔ m ∈ (A : Set ℕ)))
    (hkN : ∀ i : ℕ, i < k → infiniteSubsetsOmegaNth A i < N) :
    ∀ i : ℕ, i < k → infiniteSubsetsOmegaGapMap B i = infiniteSubsetsOmegaGapMap A i := by
  intro i hi
  exact infiniteSubsetsOmegaGapMap_eq_of_agree_below (A := A) (B := B) (N := N)
    hagree (hkN i hi)

/-- Book-facing local form of gap-map continuity: agreement with `A` below
`a_{k-1}+1` fixes the first `k` selected elements and hence the first `k` gap
coordinates; for `k = 0` the conclusion is vacuous. -/
theorem infiniteSubsetsOmegaGapMap_eq_on_initialSegment_of_agree_below
    {A B : infiniteSubsetsOmega} (k : ℕ)
    (hagree :
      ∀ m, m < infiniteSubsetsOmegaNth A (k - 1) + 1 →
        (m ∈ (B : Set ℕ) ↔ m ∈ (A : Set ℕ))) :
    ∀ i : ℕ, i < k → infiniteSubsetsOmegaGapMap B i = infiniteSubsetsOmegaGapMap A i := by
  apply infiniteSubsetsOmegaGapMap_eq_on_lt_of_agree_below
    (N := infiniteSubsetsOmegaNth A (k - 1) + 1) hagree
  intro i hi
  exact Nat.lt_succ_of_le
    ((infiniteSubsetsOmegaNth_strictMono A).monotone (Nat.le_pred_of_lt hi))

/-- Alternating run lengths of a non-eventually-constant branch, read from its change
points. -/
noncomputable def cantorBranchRunLength
    (b : cantorNonEventuallyConstantBranches) : ℕ → positiveNat
  | 0 => ⟨infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 0 + 1, by omega⟩
  | n + 1 =>
      ⟨infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 (n + 1) -
          infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n,
        by
          have hlt :
              infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n <
                infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 (n + 1) :=
            infiniteSubsetsOmegaNth_strictMono (branchChangePointProductMap b).2
              (Nat.lt_succ_self n)
          exact Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hlt)⟩

/-- The gap map recovers alternating run lengths shifted down by one. -/
theorem cantorBranchRunLength_sub_one_eq_gapMap
    (b : cantorNonEventuallyConstantBranches) (n : ℕ) :
    (cantorBranchRunLength b n).1 - 1 =
      infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 n := by
  cases n with
  | zero =>
      simp [cantorBranchRunLength, infiniteSubsetsOmegaGapMap]
  | succ n =>
      have hlt :=
        infiniteSubsetsOmegaNth_strictMono (branchChangePointProductMap b).2
          (Nat.lt_succ_self n)
      simp [cantorBranchRunLength, infiniteSubsetsOmegaGapMap]

/-- In function form, applying the gap map to the change-point set of a branch recovers
the branch run lengths shifted down by one. -/
theorem infiniteSubsetsOmegaGapMap_branchChangePoints_eq_runLengthSubOne
    (b : cantorNonEventuallyConstantBranches) :
    infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 =
      fun n => (cantorBranchRunLength b n).1 - 1 := by
  funext n
  exact (cantorBranchRunLength_sub_one_eq_gapMap b n).symm

theorem cantorBranchRunLength_eq_gapMap_symm
    (b : cantorNonEventuallyConstantBranches) (n : ℕ) :
    cantorBranchRunLength b n =
      positiveNatEquivNat.symm
        (infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 n) := by
  apply Subtype.ext
  have hpos : 1 ≤ (cantorBranchRunLength b n).1 :=
    (cantorBranchRunLength b n).2
  have h := cantorBranchRunLength_sub_one_eq_gapMap b n
  simp [positiveNatEquivNat]
  omega

/-- The `n`-th change point is the sum of the first `n + 1` run lengths, minus one. -/
theorem cantorBranchChangePointNth_add_one_eq_sum_runLengths
    (b : cantorNonEventuallyConstantBranches) :
    ∀ n : ℕ,
      infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n + 1 =
        Finset.sum (Finset.range (n + 1)) (fun i => (cantorBranchRunLength b i).1) := by
  intro n
  induction n with
  | zero =>
      simp [cantorBranchRunLength]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hlt :
          infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n <
            infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 (n + 1) :=
        infiniteSubsetsOmegaNth_strictMono (branchChangePointProductMap b).2
          (Nat.lt_succ_self n)
      simp [cantorBranchRunLength]
      omega

theorem cantorBranchChangePointNth_eq_sum_runLengths_sub_one
    (b : cantorNonEventuallyConstantBranches) (n : ℕ) :
    infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n =
      Finset.sum (Finset.range (n + 1)) (fun i => (cantorBranchRunLength b i).1) - 1 := by
  have h := cantorBranchChangePointNth_add_one_eq_sum_runLengths b n
  omega

theorem infiniteSubsetsOmegaGapMap_continuous :
    Continuous infiniteSubsetsOmegaGapMap := by
  classical
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro A hAU
  obtain ⟨s, hAs, hsU⟩ := exists_cyl_subset_of_mem_open (A := ℕ) hAU hU
  let N : ℕ :=
    if s.length = 0 then 0 else infiniteSubsetsOmegaNth A (s.length - 1) + 1
  let F : Finset ℕ := (Finset.range N).filter fun n => n ∈ (A : Set ℕ)
  let G : Finset ℕ := (Finset.range N).filter fun n => n ∉ (A : Set ℕ)
  let W : Set infiniteSubsetsOmega := {B | (B : powersetOmega) ∈ membershipDecisionSet F G}
  refine mem_nhds_iff.2 ⟨W, ?_, ?_, ?_⟩
  · intro B hBW
    apply hsU
    intro i hi
    have hlen_pos : 0 < s.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    have hN :
        N = infiniteSubsetsOmegaNth A (s.length - 1) + 1 := by
      simp [N, hlen_pos.ne']
    have hlast : i ≤ s.length - 1 := Nat.le_pred_of_lt hi
    have hiN : infiniteSubsetsOmegaNth A i < N := by
      rw [hN]
      exact Nat.lt_succ_of_le ((infiniteSubsetsOmegaNth_strictMono A).monotone hlast)
    have hagree :
        ∀ m, m < N → (m ∈ (B : Set ℕ) ↔ m ∈ (A : Set ℕ)) := by
      simpa [F, G] using membershipDecisionSet_agree_below (A := (A : powersetOmega))
        (E := (B : powersetOmega)) (N := N) hBW
    have hi_eq :
        infiniteSubsetsOmegaNth B i = infiniteSubsetsOmegaNth A i :=
      infiniteSubsetsOmegaNth_eq_of_agree_below (A := A) (B := B) (N := N) hagree hiN
    cases i with
    | zero =>
        rw [infiniteSubsetsOmegaGapMap, hi_eq]
        exact hAs 0 hi
    | succ i =>
        have hi_pred_lt : i < s.length := Nat.lt_trans (Nat.lt_succ_self i) hi
        have hlast_pred : i ≤ s.length - 1 := Nat.le_pred_of_lt hi_pred_lt
        have hi_pred_N : infiniteSubsetsOmegaNth A i < N := by
          rw [hN]
          exact Nat.lt_succ_of_le
            ((infiniteSubsetsOmegaNth_strictMono A).monotone hlast_pred)
        have hi_pred_eq :
            infiniteSubsetsOmegaNth B i = infiniteSubsetsOmegaNth A i :=
          infiniteSubsetsOmegaNth_eq_of_agree_below (A := A) (B := B) (N := N) hagree
            hi_pred_N
        rw [infiniteSubsetsOmegaGapMap, hi_eq, hi_pred_eq]
        exact hAs (i + 1) hi
  · exact (membershipDecisionSet_isClopen F G).isOpen.preimage continuous_subtype_val
  · simp [W, F, G, membershipDecisionSet]

theorem cantorBranchRunLength_continuous :
    Continuous cantorBranchRunLength := by
  refine continuous_pi fun n => ?_
  have hgap :
      Continuous (fun b : cantorNonEventuallyConstantBranches =>
        infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 n) :=
    (continuous_apply n).comp
      (infiniteSubsetsOmegaGapMap_continuous.comp
        (branchChangePointProductMap_continuous.snd))
  have hcoord :
      Continuous (fun b : cantorNonEventuallyConstantBranches =>
        positiveNatEquivNat.symm
          (infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 n)) :=
    (continuous_of_discreteTopology (f := positiveNatEquivNat.symm)).comp hgap
  convert hcoord using 1
  funext b
  exact cantorBranchRunLength_eq_gapMap_symm b n

/-- Partial sums giving the inverse image of a Baire-space point under the gap map. -/
def gapPartialSum (g : baire_space) : ℕ → ℕ
  | 0 => g 0
  | n + 1 => gapPartialSum g n + g (n + 1) + 1

@[simp]
theorem gapPartialSum_zero (g : baire_space) :
    gapPartialSum g 0 = g 0 :=
  rfl

@[simp]
theorem gapPartialSum_succ (g : baire_space) (n : ℕ) :
    gapPartialSum g (n + 1) = gapPartialSum g n + g (n + 1) + 1 :=
  rfl

theorem gapPartialSum_eq_sum_add (g : baire_space) :
    ∀ n : ℕ, gapPartialSum g n = Finset.sum (Finset.range (n + 1)) g + n := by
  intro n
  induction n with
  | zero =>
      simp [gapPartialSum]
  | succ n ih =>
      calc
        gapPartialSum g (n + 1) =
            gapPartialSum g n + g (n + 1) + 1 := rfl
        _ = (Finset.sum (Finset.range (n + 1)) g + n) + g (n + 1) + 1 := by
              rw [ih]
        _ = (Finset.sum (Finset.range (n + 1)) g + g (n + 1)) + (n + 1) := by
              omega
        _ = Finset.sum (Finset.range (n + 1 + 1)) g + (n + 1) := by
              rw [← Finset.sum_range_succ]

theorem gapPartialSum_eq_of_agree_below {g h : baire_space} {N n : ℕ}
    (hagree : ∀ i, i < N → h i = g i) (hn : n < N) :
    gapPartialSum h n = gapPartialSum g n := by
  induction n with
  | zero =>
      simp [gapPartialSum, hagree 0 hn]
  | succ n ih =>
      have hnN : n < N := Nat.lt_of_succ_lt hn
      simp [gapPartialSum, ih hnN, hagree (n + 1) hn]

theorem gapPartialSum_strictMono (g : baire_space) :
    StrictMono (gapPartialSum g) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  simp [gapPartialSum]

theorem exists_lt_gapPartialSum (g : baire_space) (M : ℕ) :
    ∃ R : ℕ, M < gapPartialSum g R := by
  refine ⟨M + 1, ?_⟩
  have hle : M + 1 ≤ gapPartialSum g (M + 1) :=
    (gapPartialSum_strictMono g).id_le (M + 1)
  omega

theorem gapPartialSum_mem_range_iff_of_agree_below {g h : baire_space} {R m : ℕ}
    (hagree : ∀ i, i < R + 1 → h i = g i) (hmR : m < R) :
    m ∈ Set.range (gapPartialSum h) ↔ m ∈ Set.range (gapPartialSum g) := by
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hjR : j ≤ R
    · exact ⟨j, (gapPartialSum_eq_of_agree_below hagree (Nat.lt_succ_of_le hjR)).symm⟩
    · have hRj : R < j := Nat.lt_of_not_ge hjR
      have hR_le : R ≤ gapPartialSum h R := (gapPartialSum_strictMono h).id_le R
      have hlt : gapPartialSum h R < gapPartialSum h j := gapPartialSum_strictMono h hRj
      omega
  · rintro ⟨j, rfl⟩
    by_cases hjR : j ≤ R
    · exact ⟨j, gapPartialSum_eq_of_agree_below hagree (Nat.lt_succ_of_le hjR)⟩
    · have hRj : R < j := Nat.lt_of_not_ge hjR
      have hR_le : R ≤ gapPartialSum g R := (gapPartialSum_strictMono g).id_le R
      have hlt : gapPartialSum g R < gapPartialSum g j := gapPartialSum_strictMono g hRj
      omega

/-- If two gap sequences agree through coordinate `R`, then their inverse subsets
agree below the `R`-th partial sum. This is the precise finite-information form used
for continuity of the inverse gap map. -/
theorem gapPartialSum_mem_range_iff_of_agree_below_partialSum
    {g h : baire_space} {R m : ℕ}
    (hagree : ∀ i, i < R + 1 → h i = g i) (hmR : m < gapPartialSum g R) :
    m ∈ Set.range (gapPartialSum h) ↔ m ∈ Set.range (gapPartialSum g) := by
  have hsumR : gapPartialSum h R = gapPartialSum g R :=
    gapPartialSum_eq_of_agree_below hagree (Nat.lt_succ_self R)
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hjR : j ≤ R
    · exact ⟨j, (gapPartialSum_eq_of_agree_below hagree (Nat.lt_succ_of_le hjR)).symm⟩
    · have hRj : R < j := Nat.lt_of_not_ge hjR
      have hlt : gapPartialSum h R < gapPartialSum h j := gapPartialSum_strictMono h hRj
      omega
  · rintro ⟨j, rfl⟩
    by_cases hjR : j ≤ R
    · exact ⟨j, gapPartialSum_eq_of_agree_below hagree (Nat.lt_succ_of_le hjR)⟩
    · have hRj : R < j := Nat.lt_of_not_ge hjR
      have hlt : gapPartialSum g R < gapPartialSum g j := gapPartialSum_strictMono g hRj
      omega

/-- The inverse set coded by a Baire-space point. -/
noncomputable def gapsToInfiniteSubset (g : baire_space) : infiniteSubsetsOmega :=
  ⟨Set.range (gapPartialSum g), by
    change Set.Infinite (Set.range (gapPartialSum g))
    exact Set.infinite_range_of_injective (gapPartialSum_strictMono g).injective⟩

theorem gapsToInfiniteSubset_mem_iff_of_agree_below {g h : baire_space} {R m : ℕ}
    (hagree : ∀ i, i < R + 1 → h i = g i) (hmR : m < R) :
    m ∈ (gapsToInfiniteSubset h : Set ℕ) ↔
      m ∈ (gapsToInfiniteSubset g : Set ℕ) := by
  simpa [gapsToInfiniteSubset] using
    gapPartialSum_mem_range_iff_of_agree_below (g := g) (h := h) (R := R)
      (m := m) hagree hmR

theorem gapsToInfiniteSubset_mem_iff_of_agree_below_partialSum
    {g h : baire_space} {R m : ℕ}
    (hagree : ∀ i, i < R + 1 → h i = g i) (hmR : m < gapPartialSum g R) :
    m ∈ (gapsToInfiniteSubset h : Set ℕ) ↔
      m ∈ (gapsToInfiniteSubset g : Set ℕ) := by
  simpa [gapsToInfiniteSubset] using
    gapPartialSum_mem_range_iff_of_agree_below_partialSum (g := g) (h := h) (R := R)
      (m := m) hagree hmR

theorem gapsToInfiniteSubset_continuous :
    Continuous gapsToInfiniteSubset := by
  classical
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro g hgU
  rcases (isOpen_induced_iff.mp hU) with ⟨V, hVopen, hVU⟩
  have hgV : (gapsToInfiniteSubset g : powersetOmega) ∈ V := by
    have : gapsToInfiniteSubset g ∈ Subtype.val ⁻¹' V := by
      simpa [hVU] using hgU
    exact this
  obtain ⟨F, G, hgFG, hFGV⟩ :=
    exists_membershipDecisionSet_subset_of_mem_open hgV hVopen
  let R : ℕ := (F ∪ G).sup id + 1
  let W : Set baire_space := cyl (seqPrefix g (R + 1))
  refine mem_nhds_iff.2 ⟨W, ?_, ?_, ?_⟩
  · intro h hhW
    have hagree : ∀ i, i < R + 1 → h i = g i := by
      intro i hi
      have hi' : i < (seqPrefix g (R + 1)).length := by
        simpa [seqPrefix_length] using hi
      exact (hhW i hi').trans (seqPrefix_get g hi')
    have hmemFG : (gapsToInfiniteSubset h : powersetOmega) ∈ membershipDecisionSet F G := by
      refine ⟨?_, ?_⟩
      · intro n hnF
        have hnR : n < R := by
          have hnle : n ≤ (F ∪ G).sup id := by
            exact Finset.le_sup (s := F ∪ G) (f := id) (by simp [hnF])
          exact Nat.lt_succ_of_le hnle
        have hiff :=
          gapPartialSum_mem_range_iff_of_agree_below (g := g) (h := h) (R := R)
            (m := n) hagree hnR
        have hn_g : n ∈ Set.range (gapPartialSum g) := by
          simpa [gapsToInfiniteSubset] using hgFG.1 n hnF
        simpa [gapsToInfiniteSubset] using hiff.2 hn_g
      · intro n hnG hn_h
        have hnR : n < R := by
          have hnle : n ≤ (F ∪ G).sup id := by
            exact Finset.le_sup (s := F ∪ G) (f := id) (by simp [hnG])
          exact Nat.lt_succ_of_le hnle
        have hiff :=
          gapPartialSum_mem_range_iff_of_agree_below (g := g) (h := h) (R := R)
            (m := n) hagree hnR
        have hn_h' : n ∈ Set.range (gapPartialSum h) := by
          simpa [gapsToInfiniteSubset] using hn_h
        have hn_g : n ∈ Set.range (gapPartialSum g) := hiff.1 hn_h'
        exact hgFG.2 n hnG (by simpa [gapsToInfiniteSubset] using hn_g)
    have hmemV : (gapsToInfiniteSubset h : powersetOmega) ∈ V := hFGV hmemFG
    have : gapsToInfiniteSubset h ∈ Subtype.val ⁻¹' V := hmemV
    simpa [hVU] using this
  · exact isOpen_cyl (A := ℕ) (seqPrefix g (R + 1))
  · exact mem_cyl_seqPrefix g (R + 1)

theorem infiniteSubsetsOmegaNth_gapsToInfiniteSubset (g : baire_space) (n : ℕ) :
    infiniteSubsetsOmegaNth (gapsToInfiniteSubset g) n = gapPartialSum g n := by
  let f : ℕ → ℕ := gapPartialSum g
  have hf : StrictMono f := gapPartialSum_strictMono g
  have hfinite :
      ∀ hfi : ({k : ℕ | k ∈ Set.range f} : Set ℕ).Finite, n < hfi.toFinset.card := by
    intro hfi
    exact False.elim ((Set.infinite_range_of_injective hf.injective) hfi)
  have h :=
    Nat.nth_comp_of_strictMono (p := fun k : ℕ => k ∈ Set.range f) (f := f) hf
      (fun k hk => hk) hfinite
  simpa [infiniteSubsetsOmegaNth, gapsToInfiniteSubset, f] using h.symm

theorem infiniteSubsetsOmegaNth_gapsToInfiniteSubset_eq_sum_add
    (g : baire_space) (n : ℕ) :
    infiniteSubsetsOmegaNth (gapsToInfiniteSubset g) n =
      Finset.sum (Finset.range (n + 1)) g + n := by
  rw [infiniteSubsetsOmegaNth_gapsToInfiniteSubset, gapPartialSum_eq_sum_add]

theorem gapsToInfiniteSubset_mem_iff_exists_sum_add (g : baire_space) (m : ℕ) :
    m ∈ (gapsToInfiniteSubset g : Set ℕ) ↔
      ∃ n : ℕ, m = Finset.sum (Finset.range (n + 1)) g + n := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, gapPartialSum_eq_sum_add g n⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, gapPartialSum_eq_sum_add g n⟩

theorem infiniteSubsetsOmegaGapMap_gapsToInfiniteSubset (g : baire_space) :
    infiniteSubsetsOmegaGapMap (gapsToInfiniteSubset g) = g := by
  funext n
  cases n with
  | zero =>
      simp [infiniteSubsetsOmegaGapMap, infiniteSubsetsOmegaNth_gapsToInfiniteSubset, gapPartialSum]
  | succ n =>
      simp [infiniteSubsetsOmegaGapMap, infiniteSubsetsOmegaNth_gapsToInfiniteSubset, gapPartialSum]
      omega

theorem gapPartialSum_infiniteSubsetsOmegaGapMap (A : infiniteSubsetsOmega) (n : ℕ) :
    gapPartialSum (infiniteSubsetsOmegaGapMap A) n = infiniteSubsetsOmegaNth A n := by
  induction n with
  | zero =>
      simp [gapPartialSum, infiniteSubsetsOmegaGapMap]
  | succ n ih =>
      have hlt : infiniteSubsetsOmegaNth A n < infiniteSubsetsOmegaNth A (n + 1) :=
        infiniteSubsetsOmegaNth_strictMono A (Nat.lt_succ_self n)
      simp [gapPartialSum, infiniteSubsetsOmegaGapMap, ih]
      omega

theorem gapsToInfiniteSubset_infiniteSubsetsOmegaGapMap (A : infiniteSubsetsOmega) :
    gapsToInfiniteSubset (infiniteSubsetsOmegaGapMap A) = A := by
  apply Subtype.ext
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    rw [gapPartialSum_infiniteSubsetsOmegaGapMap]
    exact infiniteSubsetsOmegaNth_mem A n
  · intro hm
    have hInf : ({n : ℕ | n ∈ (A : Set ℕ)} : Set ℕ).Infinite := by
      exact show Set.Infinite (A : Set ℕ) from A.2
    change m ∈ ({n : ℕ | n ∈ (A : Set ℕ)} : Set ℕ) at hm
    rw [← Nat.range_nth_of_infinite hInf] at hm
    rcases hm with ⟨n, hn⟩
    exact ⟨n, by rw [gapPartialSum_infiniteSubsetsOmegaGapMap, infiniteSubsetsOmegaNth, hn]⟩

/-- The set-level gap-map equivalence underlying the book's homeomorphism. -/
noncomputable def infiniteSubsetsOmegaGapEquiv : infiniteSubsetsOmega ≃ baire_space where
  toFun := infiniteSubsetsOmegaGapMap
  invFun := gapsToInfiniteSubset
  left_inv := gapsToInfiniteSubset_infiniteSubsetsOmegaGapMap
  right_inv := infiniteSubsetsOmegaGapMap_gapsToInfiniteSubset

/-- Book-level gap-map homeomorphism between infinite subsets of `ω` and Baire space. -/
noncomputable def infiniteSubsetsOmegaBaireHomeomorph : infiniteSubsetsOmega ≃ₜ baire_space where
  toEquiv := infiniteSubsetsOmegaGapEquiv
  continuous_toFun := by
    simpa [infiniteSubsetsOmegaGapEquiv] using infiniteSubsetsOmegaGapMap_continuous
  continuous_invFun := by
    simpa [infiniteSubsetsOmegaGapEquiv] using gapsToInfiniteSubset_continuous

theorem infiniteSubsetsOmegaBaireHomeomorph_apply (A : infiniteSubsetsOmega) :
    infiniteSubsetsOmegaBaireHomeomorph A = infiniteSubsetsOmegaGapMap A :=
  rfl

/-- The first coordinate of the gap-map homeomorphism is the first selected element. -/
theorem infiniteSubsetsOmegaBaireHomeomorph_apply_zero (A : infiniteSubsetsOmega) :
    infiniteSubsetsOmegaBaireHomeomorph A 0 = infiniteSubsetsOmegaNth A 0 := by
  rw [infiniteSubsetsOmegaBaireHomeomorph_apply, infiniteSubsetsOmegaGapMap_zero]

/-- The successor coordinates of the gap-map homeomorphism are successive gaps. -/
theorem infiniteSubsetsOmegaBaireHomeomorph_apply_succ
    (A : infiniteSubsetsOmega) (n : ℕ) :
    infiniteSubsetsOmegaBaireHomeomorph A (n + 1) =
      infiniteSubsetsOmegaNth A (n + 1) - infiniteSubsetsOmegaNth A n - 1 := by
  rw [infiniteSubsetsOmegaBaireHomeomorph_apply, infiniteSubsetsOmegaGapMap_succ]

theorem infiniteSubsetsOmegaBaireHomeomorph_symm_apply (g : baire_space) :
    infiniteSubsetsOmegaBaireHomeomorph.symm g = gapsToInfiniteSubset g :=
  rfl

/-- The inverse gap-map homeomorphism enumerates the partial sums
`g₀, g₀ + g₁ + 1, g₀ + g₁ + g₂ + 2, ...`. -/
theorem infiniteSubsetsOmegaBaireHomeomorph_symm_nth_eq_sum_add
    (g : baire_space) (n : ℕ) :
    infiniteSubsetsOmegaNth (infiniteSubsetsOmegaBaireHomeomorph.symm g) n =
      Finset.sum (Finset.range (n + 1)) g + n := by
  rw [infiniteSubsetsOmegaBaireHomeomorph_symm_apply]
  exact infiniteSubsetsOmegaNth_gapsToInfiniteSubset_eq_sum_add g n

/-- Agreement on finitely many gap coordinates determines membership below the
corresponding partial-sum bound in the inverse image under the gap-map homeomorphism. -/
theorem infiniteSubsetsOmegaBaireHomeomorph_symm_mem_iff_of_agree_below_partialSum
    {g h : baire_space} {R m : ℕ}
    (hagree : ∀ i, i < R + 1 → h i = g i) (hmR : m < gapPartialSum g R) :
    m ∈ (infiniteSubsetsOmegaBaireHomeomorph.symm h : Set ℕ) ↔
      m ∈ (infiniteSubsetsOmegaBaireHomeomorph.symm g : Set ℕ) := by
  rw [infiniteSubsetsOmegaBaireHomeomorph_symm_apply,
    infiniteSubsetsOmegaBaireHomeomorph_symm_apply]
  exact gapsToInfiniteSubset_mem_iff_of_agree_below_partialSum hagree hmR

/-- Under the gap-map homeomorphism, finite Baire prefixes are exactly finite
initial-gap data for infinite subsets of `ω`. -/
theorem infiniteSubsetsOmegaBaireHomeomorph_mem_cyl_iff_initialGapData
    (A : infiniteSubsetsOmega) (s : finseq ℕ) :
    infiniteSubsetsOmegaBaireHomeomorph A ∈ cyl s ↔
      infiniteSubsetsOmegaInitialGapData A s := by
  rw [infiniteSubsetsOmegaBaireHomeomorph_apply]
  exact infiniteSubsetsOmegaGapMap_mem_cyl_iff_initialGapData A s

/-- Finite initial-gap data index basic clopen sets in the infinite-subset
model, as in the chapter's finite-information table. -/
theorem isClopen_infiniteSubsetsOmegaInitialGapData (s : finseq ℕ) :
    IsClopen {A : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData A s} := by
  rw [show {A : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData A s} =
      infiniteSubsetsOmegaBaireHomeomorph ⁻¹' cyl s by
    ext A
    exact (infiniteSubsetsOmegaBaireHomeomorph_mem_cyl_iff_initialGapData A s).symm]
  exact (isClopen_cyl s).preimage infiniteSubsetsOmegaBaireHomeomorph.continuous

/-- Initial-gap data form a topological basis for the infinite-subsets model. -/
theorem isTopologicalBasis_infiniteSubsetsOmegaInitialGapData :
    IsTopologicalBasis {U : Set infiniteSubsetsOmega |
      ∃ s : finseq ℕ, U = {A : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData A s}} := by
  let H := infiniteSubsetsOmegaBaireHomeomorph
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨s, rfl⟩
    exact (isClopen_infiniteSubsetsOmegaInitialGapData s).isOpen
  · intro A U hAU hU
    have himageOpen : IsOpen (H '' U) := H.isOpenMap U hU
    have hAimage : H A ∈ H '' U := ⟨A, hAU, rfl⟩
    obtain ⟨s, hHs, hsU⟩ := exists_cyl_subset_of_mem_open (A := ℕ) hAimage himageOpen
    refine ⟨{B : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData B s},
      ⟨s, rfl⟩, ?_, ?_⟩
    · exact (infiniteSubsetsOmegaBaireHomeomorph_mem_cyl_iff_initialGapData A s).1 hHs
    · intro B hB
      have hHB : H B ∈ cyl s :=
        (infiniteSubsetsOmegaBaireHomeomorph_mem_cyl_iff_initialGapData B s).2 hB
      rcases hsU hHB with ⟨C, hCU, hCeq⟩
      have hBC : B = C := H.injective hCeq.symm
      simpa [hBC] using hCU

/-- Membership in the inverse image of a Baire gap sequence is exactly membership
among the partial sums `g₀ + ... + gₙ + n`. -/
theorem infiniteSubsetsOmegaBaireHomeomorph_symm_mem_iff_exists_sum_add
    (g : baire_space) (m : ℕ) :
    m ∈ (infiniteSubsetsOmegaBaireHomeomorph.symm g : Set ℕ) ↔
      ∃ n : ℕ, m = Finset.sum (Finset.range (n + 1)) g + n := by
  rw [infiniteSubsetsOmegaBaireHomeomorph_symm_apply]
  exact gapsToInfiniteSubset_mem_iff_exists_sum_add g m

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The concrete homeomorphism with Baire space sends an infinite set to the gaps between its successive elements. For $A
    \in \infiniteSubsets{\omega}$ with increasing enumeration $a_0 < a_1 < a_2 < \cdots$, the \termdefine{gap map} is
    $$A \;\longmapsto\; (a_0,\; a_1 - a_0 - 1,\; a_2 - a_1 - 1, \ldots) \in \BaireSpace,$$
    with inverse
    $$(g_0, g_1, g_2, \ldots) \;\longmapsto\; \{g_0,\; g_0 + g_1 + 1,\; g_0 + g_1 + g_2 + 2, \ldots\}.$$
-/
/-- Book-level gap-map homeomorphism existence for `\infiniteSubsets{\omega} \cong \BaireSpace`. -/
theorem infiniteSubsetsOmegaBaireHomeomorphismFact :
    Nonempty (infiniteSubsetsOmega ≃ₜ baire_space) :=
  ⟨infiniteSubsetsOmegaBaireHomeomorph⟩

/-- Book-facing package for the Baire-space model overview: countable cylinders
give the reference clopen tree, continued-fraction coordinates make the irrational
line a Baire-space model with clopen finite partial-quotient cylinders, and
infinite subsets embed in Cantor coordinates while the gap map is a homeomorphism
whose coordinates are the successive gaps and whose inverse enumerates partial sums. -/
theorem concreteBaireSpaceModelFacts :
    (∀ s : finseq ℕ, IsClopen (cyl s : Set baire_space)) ∧
      (∀ s : finseq ℕ,
        (cyl s : Set baire_space) = ⋃ n : ℕ, cyl (concat s [n]) ∧
          ∀ m n : ℕ, m ≠ n →
            Disjoint (cyl (concat s [m]) : Set baire_space)
              (cyl (concat s [n]))) ∧
      IsTopologicalBasis ({U : Set baire_space | ∃ s : finseq ℕ, U = cyl s}) ∧
      Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat,
        IsClopen (simpleCFPartialQuotientCylinder a₀ s)) ∧
      Topology.IsEmbedding infiniteSubsetsOmegaCantorEmbedding ∧
      Nonempty (infiniteSubsetsOmega ≃ₜ baire_space) ∧
      (∀ A : infiniteSubsetsOmega,
        infiniteSubsetsOmegaBaireHomeomorph A 0 = infiniteSubsetsOmegaNth A 0) ∧
      (∀ A : infiniteSubsetsOmega, ∀ n : ℕ,
        infiniteSubsetsOmegaBaireHomeomorph A (n + 1) =
          infiniteSubsetsOmegaNth A (n + 1) - infiniteSubsetsOmegaNth A n - 1) ∧
      (∀ g : baire_space,
        infiniteSubsetsOmegaBaireHomeomorph.symm g = gapsToInfiniteSubset g) ∧
      (∀ g : baire_space, ∀ n : ℕ,
        infiniteSubsetsOmegaNth (infiniteSubsetsOmegaBaireHomeomorph.symm g) n =
          Finset.sum (Finset.range (n + 1)) g + n) ∧
      (∀ g : baire_space, ∀ m : ℕ,
        m ∈ (infiniteSubsetsOmegaBaireHomeomorph.symm g : Set ℕ) ↔
          ∃ n : ℕ, m = Finset.sum (Finset.range (n + 1)) g + n) ∧
      (∀ A : infiniteSubsetsOmega, ∀ s : finseq ℕ,
        infiniteSubsetsOmegaBaireHomeomorph A ∈ cyl s ↔
          infiniteSubsetsOmegaInitialGapData A s) ∧
      (∀ s : finseq ℕ,
        IsClopen {A : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData A s}) := by
  refine ⟨?_, ?_, isTopologicalBasis_baire_cyl, continuedFractionBaireHomeomorphismFact,
    ?_, infiniteSubsetsOmegaCantorEmbedding_isEmbedding,
    infiniteSubsetsOmegaBaireHomeomorphismFact, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact isClopen_cyl s
  · intro s
    exact ⟨baire_cyl_eq_iUnion_immediate_subcylinders s,
      fun m n hmn => disjoint_baire_immediate_subcylinders s hmn⟩
  · intro a₀ s
    exact isClopen_simpleCFPartialQuotientCylinder a₀ s
  · intro A
    exact infiniteSubsetsOmegaBaireHomeomorph_apply_zero A
  · intro A n
    exact infiniteSubsetsOmegaBaireHomeomorph_apply_succ A n
  · intro g
    exact infiniteSubsetsOmegaBaireHomeomorph_symm_apply g
  · intro g n
    exact infiniteSubsetsOmegaBaireHomeomorph_symm_nth_eq_sum_add g n
  · intro g m
    exact infiniteSubsetsOmegaBaireHomeomorph_symm_mem_iff_exists_sum_add g m
  · intro A s
    exact infiniteSubsetsOmegaBaireHomeomorph_mem_cyl_iff_initialGapData A s
  · intro s
    exact isClopen_infiniteSubsetsOmegaInitialGapData s

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Thus finite Baire prefixes are exactly finite initial-gap data for infinite subsets of $\omega$.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Thus the space
    $\infiniteSubsets{\omega}$ introduced above is the change-point version of the binary realization. Splitting $S$ by the
    initial bit $b_0$ reduces the comparison to the two halves $\{b \in S : b_0 = L\}$ and $\{b \in S : b_0 = R\}$. The
    infinite-subset model is the Stern--Brocot boundary with run lengths re-encoded as switch positions.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The map $\Delta$ is continuous because membership of $n$ in $\Delta(b)$ depends only on the two coordinates $b_n$ and
    $b_{n+1}$. Thus each half of $S$ is homeomorphic to $\infiniteSubsets{\omega}$, and the split by the clopen
    first-coordinate halves gives $S\cong 2\times\infiniteSubsets{\omega}$.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Each set in the intersection is open: once some $m \ge n$ is known to lie in $A$, no later coordinates can destroy that
    witness. Hence $\infiniteSubsets{\omega}$ is Polish by Alexandrov's theorem in §{sec:alexandrov-theorem}.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For the inverse map, write
    $$a_n=n+\sum_{i=0}^{n}g_i\ge n.$$
    Given a bound $M$, choose $n$ with $a_n\ge M$. Fixing $g_0,\ldots,g_n$ fixes $a_0,\ldots,a_n$, and all later
    enumerated elements exceed $a_n$. Thus these finitely many gap coordinates determine membership below $M$,
    which proves continuity of the inverse. For the gap map itself,
    continuity is local: if a basic cylinder in $\BaireSpace$ contains the gap sequence of $A$ and fixes its coordinates
    $0,\ldots,k-1$, then for $k>0$ it is enough to know $A$ below $a_{k-1}+1$. The case $k=0$ is vacuous. Every nearby
    infinite set with the same membership pattern below this finite bound has the same first $k$ selected elements and hence
    the same first $k$ gap coordinates. Therefore the gap map is continuous, and
    $\infiniteSubsets{\omega} \cong \BaireSpace$.
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The gap map is the run-length encoding of §{sec:boundary-mediant-limit-map} in another guise. For $b \in S$, let $r_0,
    r_1, r_2, \ldots$ denote its alternating run lengths starting at position $0$, each $r_i \ge 1$. Then $\Delta(b)$ has
    $i$-th element $r_0 + r_1 + \cdots + r_i - 1$, so applying the gap map to $\Delta(b)$ recovers the run lengths shifted
    down by one to land in $\NN$: $g_i = r_i - 1$.
-/
/-- Book-facing package for the infinite-subsets model: change points split the
non-eventually-constant binary boundary as `2 × infiniteSubsetsOmega`, the
space of infinite subsets is a `Gδ` Polish subspace of Cantor coordinates, the
gap map is a homeomorphism with Baire space, finite initial-gap data give the
basic clopen pieces, and switch positions are the Stern--Brocot run lengths in
gap coordinates. -/
theorem concreteInfiniteSubsetsOmegaModelFacts :
    (∀ ε : Bool,
      Nonempty ({b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε} ≃ₜ
        infiniteSubsetsOmega)) ∧
      (∀ ε : Bool, ∀ A : infiniteSubsetsOmega,
        (branchFromInfiniteSubset ε A).1 0 = ε) ∧
      (∀ ε : Bool, ∀ A : infiniteSubsetsOmega, ∀ n : ℕ,
        (branchFromInfiniteSubset ε A).1 n ≠
            (branchFromInfiniteSubset ε A).1 (n + 1) ↔
          n ∈ (A : Set ℕ)) ∧
      (∀ ε : Bool, ∀ A B : infiniteSubsetsOmega, ∀ k : ℕ,
        (∀ m : ℕ, m < k → (m ∈ (A : Set ℕ) ↔ m ∈ (B : Set ℕ))) →
          ∀ i : ℕ, i < k →
            (branchFromInfiniteSubset ε A).1 i =
              (branchFromInfiniteSubset ε B).1 i) ∧
      (∀ b c : cantor_space, ∀ N : ℕ,
        (∀ m : ℕ, m < N + 1 → b m = c m) →
          ∀ n : ℕ, n < N →
            (n ∈ (cantorChangePointMap b : Set ℕ) ↔
              n ∈ (cantorChangePointMap c : Set ℕ))) ∧
      (∀ ε : Bool, Continuous (branchFromInfiniteSubset ε)) ∧
      (∀ ε : Bool, Continuous (infiniteSubsetFromBranchChanges ε)) ∧
      (∀ ε : Bool, ∀ A : infiniteSubsetsOmega,
        infiniteSubsetFromBranchChanges ε (branchFromInfiniteSubset ε A) = A) ∧
      (∀ ε : Bool,
        ∀ b : {b : cantor_space // cantorNonEventuallyConstantSet b ∧ b 0 = ε},
          branchFromInfiniteSubset ε (infiniteSubsetFromBranchChanges ε b) = b) ∧
      (∀ ε : Bool, IsClopen (cantorNonEventuallyConstantInitialBitHalf ε)) ∧
      cantorNonEventuallyConstantInitialBitHalf false ∪
          cantorNonEventuallyConstantInitialBitHalf true =
        (Set.univ : Set cantorNonEventuallyConstantBranches) ∧
      Disjoint (cantorNonEventuallyConstantInitialBitHalf false)
        (cantorNonEventuallyConstantInitialBitHalf true) ∧
      Nonempty (cantorNonEventuallyConstantBranches ≃ₜ Bool × infiniteSubsetsOmega) ∧
      (∀ ε : Bool,
        branchChangePointProductHomeomorph ''
            cantorNonEventuallyConstantInitialBitHalf ε =
          {p : Bool × infiniteSubsetsOmega | p.1 = ε}) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        branchChangePointProductHomeomorph b =
          (b.1 0, ⟨cantorChangePointMap b.1, b.2⟩)) ∧
      (∀ p : Bool × infiniteSubsetsOmega,
        branchChangePointProductHomeomorph.symm p = branchFromInitialAndChanges p) ∧
      (∀ p : Bool × infiniteSubsetsOmega,
        cantorChangePointMap (branchChangePointProductHomeomorph.symm p).1 =
          (p.2 : powersetOmega)) ∧
      (∀ n : ℕ,
        infiniteSubsetsOmegaTailSet n =
          ⋃ m : {m : ℕ // n ≤ m}, membershipDecisionSet {m.1} ∅) ∧
      infiniteSubsetsOmegaSet = ⋂ n : ℕ, infiniteSubsetsOmegaTailSet n ∧
      (∀ n : ℕ, IsOpen (infiniteSubsetsOmegaTailSet n)) ∧
      IsGδ infiniteSubsetsOmegaSet ∧
      PolishSpace infiniteSubsetsOmega ∧
      Topology.IsEmbedding infiniteSubsetsOmegaCantorEmbedding ∧
      (∀ A : infiniteSubsetsOmega,
        infiniteSubsetsOmegaCantorEmbedding A = subsetCharacteristic (A : powersetOmega)) ∧
      Nonempty (infiniteSubsetsOmega ≃ₜ baire_space) ∧
      (∀ A : infiniteSubsetsOmega,
        infiniteSubsetsOmegaBaireHomeomorph A = infiniteSubsetsOmegaGapMap A) ∧
      (∀ A : infiniteSubsetsOmega,
        infiniteSubsetsOmegaBaireHomeomorph A 0 = infiniteSubsetsOmegaNth A 0) ∧
      (∀ A : infiniteSubsetsOmega, ∀ n : ℕ,
        infiniteSubsetsOmegaBaireHomeomorph A (n + 1) =
          infiniteSubsetsOmegaNth A (n + 1) - infiniteSubsetsOmegaNth A n - 1) ∧
      (∀ g : baire_space,
        infiniteSubsetsOmegaBaireHomeomorph.symm g = gapsToInfiniteSubset g) ∧
      (∀ g : baire_space, ∀ n : ℕ,
        infiniteSubsetsOmegaNth (infiniteSubsetsOmegaBaireHomeomorph.symm g) n =
          Finset.sum (Finset.range (n + 1)) g + n) ∧
      (∀ g : baire_space, ∀ m : ℕ,
        m ∈ (infiniteSubsetsOmegaBaireHomeomorph.symm g : Set ℕ) ↔
          ∃ n : ℕ, m = Finset.sum (Finset.range (n + 1)) g + n) ∧
      (∀ A : infiniteSubsetsOmega, ∀ s : finseq ℕ,
        infiniteSubsetsOmegaBaireHomeomorph A ∈ cyl s ↔
          infiniteSubsetsOmegaInitialGapData A s) ∧
      (∀ s : finseq ℕ,
        IsClopen {A : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData A s}) ∧
      (∀ A B : infiniteSubsetsOmega, ∀ k : ℕ,
        (∀ m, m < infiniteSubsetsOmegaNth A (k - 1) + 1 →
          (m ∈ (B : Set ℕ) ↔ m ∈ (A : Set ℕ))) →
        ∀ i : ℕ, i < k →
          infiniteSubsetsOmegaGapMap B i = infiniteSubsetsOmegaGapMap A i) ∧
      (∀ g h : baire_space, ∀ R m : ℕ,
        (∀ i, i < R + 1 → h i = g i) →
          m < gapPartialSum g R →
            (m ∈ (infiniteSubsetsOmegaBaireHomeomorph.symm h : Set ℕ) ↔
              m ∈ (infiniteSubsetsOmegaBaireHomeomorph.symm g : Set ℕ))) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 =
          fun n => (cantorBranchRunLength b n).1 - 1) ∧
      (∀ b : cantorNonEventuallyConstantBranches, ∀ n : ℕ,
        infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n =
          Finset.sum (Finset.range (n + 1)) (fun i => (cantorBranchRunLength b i).1) - 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    branchChangePointProductHomeomorphismFact,
    ?_, ?_, ?_, ?_, ?_, infiniteSubsetsOmegaGdeltaPresentationFact, ?_,
    infiniteSubsetsOmegaSet_isGdelta, infiniteSubsetsOmega_polish,
    infiniteSubsetsOmegaCantorEmbedding_isEmbedding, ?_, infiniteSubsetsOmegaBaireHomeomorphismFact,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε
    exact branchChangePointHomeomorphismFact ε
  · intro ε A
    exact branchFromInfiniteSubset_zero ε A
  · intro ε A n
    exact branchFromInfiniteSubset_change_iff ε A n
  · intro ε A B k hagree i hi
    exact branchFromInfiniteSubset_eq_on_lt_of_agree_below ε hagree i hi
  · intro b c N hagree n hn
    exact cantorChangePointMap_eq_on_lt_of_eq_on_succ hagree n hn
  · intro ε
    exact branchFromInfiniteSubset_continuous ε
  · intro ε
    exact infiniteSubsetFromBranchChanges_continuous ε
  · intro ε A
    exact infiniteSubsetFromBranchChanges_branchFromInfiniteSubset ε A
  · intro ε b
    exact branchFromInfiniteSubset_infiniteSubsetFromBranchChanges ε b
  · intro ε
    exact isClopen_cantorNonEventuallyConstantInitialBitHalf ε
  · exact cantorNonEventuallyConstantInitialBitHalf_false_union_true
  · exact disjoint_cantorNonEventuallyConstantInitialBitHalves
  · intro ε
    exact branchChangePointProductHomeomorph_image_initialBitHalf ε
  · intro b
    exact branchChangePointProductHomeomorph_apply b
  · intro p
    exact branchChangePointProductHomeomorph_symm_apply p
  · intro p
    exact branchChangePointProductHomeomorph_symm_apply_changePoints p
  · intro n
    exact infiniteSubsetsOmegaTailSet_eq_iUnion_membershipDecisionSet n
  · intro n
    exact infiniteSubsetsOmegaTailSet_isOpen n
  · intro A
    exact infiniteSubsetsOmegaCantorEmbedding_apply A
  · intro A
    exact infiniteSubsetsOmegaBaireHomeomorph_apply A
  · intro A
    exact infiniteSubsetsOmegaBaireHomeomorph_apply_zero A
  · intro A n
    exact infiniteSubsetsOmegaBaireHomeomorph_apply_succ A n
  · intro g
    exact infiniteSubsetsOmegaBaireHomeomorph_symm_apply g
  · intro g n
    exact infiniteSubsetsOmegaBaireHomeomorph_symm_nth_eq_sum_add g n
  · intro g m
    exact infiniteSubsetsOmegaBaireHomeomorph_symm_mem_iff_exists_sum_add g m
  · intro A s
    exact infiniteSubsetsOmegaBaireHomeomorph_mem_cyl_iff_initialGapData A s
  · intro s
    exact isClopen_infiniteSubsetsOmegaInitialGapData s
  · intro A B k hagree i hi
    exact infiniteSubsetsOmegaGapMap_eq_on_initialSegment_of_agree_below
      (A := A) (B := B) k hagree i hi
  · exact fun g h R m hagree hmR =>
      infiniteSubsetsOmegaBaireHomeomorph_symm_mem_iff_of_agree_below_partialSum
        (g := g) (h := h) (R := R) (m := m) hagree hmR
  · intro b
    exact infiniteSubsetsOmegaGapMap_branchChangePoints_eq_runLengthSubOne b
  · intro b n
    exact cantorBranchChangePointNth_eq_sum_runLengths_sub_one b n

/-- Combining the change-point split with the gap map gives the Baire-space
coordinate model for non-eventually-constant branches. -/
noncomputable def cantorNonEventuallyConstantBranchesBaireHomeomorph :
    cantorNonEventuallyConstantBranches ≃ₜ Bool × baire_space :=
  branchChangePointProductHomeomorph.trans
    ((Homeomorph.refl Bool).prodCongr infiniteSubsetsOmegaBaireHomeomorph)

/-- The change-point/gap-coordinate model of `S` records the initial bit and then
the alternating run lengths shifted down by one. This is the Lean form of the
book's statement that the gap map is the run-length encoding in another guise. -/
theorem cantorNonEventuallyConstantBranchesBaireHomeomorph_apply
    (b : cantorNonEventuallyConstantBranches) :
    cantorNonEventuallyConstantBranchesBaireHomeomorph b =
      (b.1 0, fun n => (cantorBranchRunLength b n).1 - 1) := by
  unfold cantorNonEventuallyConstantBranchesBaireHomeomorph
  apply Prod.ext
  · simp [Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
      branchChangePointProductHomeomorph_apply]
  · funext n
    simp [Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
      branchChangePointProductHomeomorph_apply, infiniteSubsetsOmegaBaireHomeomorph_apply]
    change infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 n =
      (cantorBranchRunLength b n).1 - 1
    exact congrFun (infiniteSubsetsOmegaGapMap_branchChangePoints_eq_runLengthSubOne b) n

theorem cantorNonEventuallyConstantBranchesBaireHomeomorphismFact :
    Nonempty (cantorNonEventuallyConstantBranches ≃ₜ Bool × baire_space) :=
  ⟨cantorNonEventuallyConstantBranchesBaireHomeomorph⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    This run-length map
    $$S \longrightarrow \NN \times \funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}}$$
    is a homeomorphism. Indeed, at a point of $S$, any finite list of run lengths is determined by a finite L/R prefix long
    enough to include the next change of letter, so the coordinate maps are continuous. Conversely, the inverse image of a
    binary cylinder under the inverse run-length map only asks for finitely many completed run lengths and possibly a finite
    lower bound on the next run length; this is open in the product of discrete coordinate spaces.
-/
/-- Run-length coordinates for non-eventually-constant binary branches. This is the
homeomorphism form of the Stern--Brocot boundary run-length statement. -/
noncomputable def cantorNonEventuallyConstantBranchesRunLengthHomeomorph :
    cantorNonEventuallyConstantBranches ≃ₜ Bool × (ℕ → positiveNat) :=
  cantorNonEventuallyConstantBranchesBaireHomeomorph.trans
    ((Homeomorph.refl Bool).prodCongr positiveNatSeqHomeomorphBaire.symm)

theorem cantorNonEventuallyConstantBranchesRunLengthHomeomorph_apply
    (b : cantorNonEventuallyConstantBranches) :
    cantorNonEventuallyConstantBranchesRunLengthHomeomorph b =
      (b.1 0, cantorBranchRunLength b) := by
  apply Prod.ext
  · rfl
  · funext n
    exact (cantorBranchRunLength_eq_gapMap_symm b n).symm

/-- Run-length coordinates recoded in the form used by the book: one natural initial
coordinate, followed by positive tail run lengths. -/
noncomputable def cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph :
    cantorNonEventuallyConstantBranches ≃ₜ ℕ × (ℕ → positiveNat) :=
  cantorNonEventuallyConstantBranchesRunLengthHomeomorph.trans
    boolPositiveNatSeqHomeomorphNatPositiveNatSeq

theorem cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply
    (b : cantorNonEventuallyConstantBranches) :
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
      boolPositiveNatSeqEquivNatPositiveNatSeq (b.1 0, cantorBranchRunLength b) := by
  change boolPositiveNatSeqHomeomorphNatPositiveNatSeq
      (cantorNonEventuallyConstantBranchesRunLengthHomeomorph b) =
    boolPositiveNatSeqEquivNatPositiveNatSeq (b.1 0, cantorBranchRunLength b)
  rw [cantorNonEventuallyConstantBranchesRunLengthHomeomorph_apply]
  rfl

/-- On the initial-`false` half, the natural run-length coordinate has integer
part `0`. This is the formal version of the book's `R^0` empty initial run. -/
theorem cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse
    {b : cantorNonEventuallyConstantBranches} (hb : b.1 0 = false) :
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
      (0, cantorBranchRunLength b) := by
  rw [cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply, hb]
  exact boolPositiveNatSeqEquivNatPositiveNatSeq_false (cantorBranchRunLength b)

/-- On the initial-`true` half, the first natural coordinate records the first
run length and the positive tail is shifted. -/
theorem cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue
    {b : cantorNonEventuallyConstantBranches} (hb : b.1 0 = true) :
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
      ((cantorBranchRunLength b 0).1, shiftPositiveNat (cantorBranchRunLength b)) := by
  rw [cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply, hb]
  exact boolPositiveNatSeqEquivNatPositiveNatSeq_true (cantorBranchRunLength b)

/-- In Stern--Brocot run-length coordinates, the initial `false` branch half is
exactly the part whose first natural coordinate is `0`. -/
theorem cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_fst_eq_zero_iff_initialFalse
    (b : cantorNonEventuallyConstantBranches) :
    (cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b).1 = 0 ↔
      b.1 0 = false := by
  constructor
  · intro hzero
    cases hb : b.1 0
    · rfl
    · have htrue :=
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue
          (b := b) hb
      have hfst :
          (cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b).1 =
            (cantorBranchRunLength b 0).1 := by
        simpa using congrArg Prod.fst htrue
      rw [hzero] at hfst
      have hpos : 1 ≤ (cantorBranchRunLength b 0).1 :=
        (cantorBranchRunLength b 0).2
      omega
  · intro hb
    have hfalse :=
      cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse
        (b := b) hb
    simpa using congrArg Prod.fst hfalse

/-- The Stern--Brocot path operation corresponding to the Gauss map on the
`(0,1) \setminus ℚ` row: in run-length coordinates it keeps the branch in the
initial-`false` half and shifts the positive run-length sequence. This is the
run-length form of deleting the initial `L`-run and swapping `L/R` on the tail. -/
noncomputable def sternBrocotLSubtreeGaussPath
    (b : cantorNonEventuallyConstantBranches) :
    cantorNonEventuallyConstantBranches :=
  cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph.symm
    (0, shiftPositiveNat (cantorBranchRunLength b))

theorem sternBrocotLSubtreeGaussPath_coordinate
    (b : cantorNonEventuallyConstantBranches) :
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph
        (sternBrocotLSubtreeGaussPath b) =
      (0, shiftPositiveNat (cantorBranchRunLength b)) := by
  simp [sternBrocotLSubtreeGaussPath]

theorem sternBrocotLSubtreeGaussPath_initialFalse
    (b : cantorNonEventuallyConstantBranches) :
    (sternBrocotLSubtreeGaussPath b).1 0 = false := by
  let c := sternBrocotLSubtreeGaussPath b
  change c.1 0 = false
  cases hc : c.1 0
  · rfl
  · have hcoord : cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph c =
        (0, shiftPositiveNat (cantorBranchRunLength b)) := by
      simpa [c] using sternBrocotLSubtreeGaussPath_coordinate b
    have htrue := cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue
      (b := c) hc
    rw [hcoord] at htrue
    have hfst := congrArg Prod.fst htrue
    have hpos : 1 ≤ (cantorBranchRunLength c 0).1 :=
      (cantorBranchRunLength c 0).2
    simp at hfst
    omega

theorem sternBrocotLSubtreeGaussPath_runLength
    (b : cantorNonEventuallyConstantBranches) :
    cantorBranchRunLength (sternBrocotLSubtreeGaussPath b) =
      shiftPositiveNat (cantorBranchRunLength b) := by
  have hcoord := sternBrocotLSubtreeGaussPath_coordinate b
  have hfalse := sternBrocotLSubtreeGaussPath_initialFalse b
  have hcoordFalse :=
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse
      (b := sternBrocotLSubtreeGaussPath b) hfalse
  rw [hcoord] at hcoordFalse
  exact (congrArg Prod.snd hcoordFalse).symm

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    $$\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\wordRepeat{L}{a_3}\cdots \longmapsto
    \wordRepeat{L}{a_2}\wordRepeat{R}{a_3}\wordRepeat{L}{a_4}\cdots.$$
-/
/-- On Stern--Brocot boundary paths in the L-subtree, the Gauss-path operation
has exactly the shifted positive run-length sequence. In the book's L/R
language, this is the coordinate statement behind deleting the initial `L`-run
and swapping `L/R` on the remaining tail. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    and on Stern--Brocot boundary paths in the L-subtree it deletes the initial L-run and swaps L and R on the tail:
-/
theorem sternBrocotLSubtreeGaussPath_deleteInitialRun_swapTail
    {b : cantorNonEventuallyConstantBranches} (hb : b.1 0 = false) :
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
        (0, cantorBranchRunLength b) ∧
      (sternBrocotLSubtreeGaussPath b).1 0 = false ∧
      cantorBranchRunLength (sternBrocotLSubtreeGaussPath b) =
        shiftPositiveNat (cantorBranchRunLength b) :=
  ⟨cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse hb,
    sternBrocotLSubtreeGaussPath_initialFalse b,
    sternBrocotLSubtreeGaussPath_runLength b⟩

/-- The Stern--Brocot non-eventually-constant boundary is itself a Baire-space model,
via run-length coordinates. -/
noncomputable def sternBrocotBoundaryBaireHomeomorph :
    cantorNonEventuallyConstantBranches ≃ₜ baire_space :=
  cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph.trans
    natPositiveNatSeqHomeomorphBaire

theorem sternBrocotBoundaryBaireHomeomorph_apply
    (b : cantorNonEventuallyConstantBranches) :
    sternBrocotBoundaryBaireHomeomorph b =
      natPositiveNatSeqHomeomorphBaire
        (boolPositiveNatSeqEquivNatPositiveNatSeq (b.1 0, cantorBranchRunLength b)) := by
  rw [← cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply]
  rfl

theorem sternBrocotBoundaryBaireHomeomorphismFact :
    Nonempty (cantorNonEventuallyConstantBranches ≃ₜ baire_space) :=
  ⟨sternBrocotBoundaryBaireHomeomorph⟩

/-- The Stern--Brocot boundary of non-eventually-constant branches is homeomorphic to the
positive irrationals by run-length coordinates followed by continued fractions. -/
noncomputable def sternBrocotBoundaryPositiveIrrationalHomeomorph :
    cantorNonEventuallyConstantBranches ≃ₜ {x : ℝ // Irrational x ∧ 0 < x} :=
  cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph.trans
    simpleCFPositiveCoordinateHomeomorph.symm

theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_apply
    (b : cantorNonEventuallyConstantBranches) :
    sternBrocotBoundaryPositiveIrrationalHomeomorph b =
      simpleCFPositiveCoordinateHomeomorph.symm
        (boolPositiveNatSeqEquivNatPositiveNatSeq (b.1 0, cantorBranchRunLength b)) := by
  rw [← cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply]
  rfl

theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate
    (b : cantorNonEventuallyConstantBranches) :
    simpleCFPositiveCoordinateHomeomorph
        (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
      cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b := by
  simp [sternBrocotBoundaryPositiveIrrationalHomeomorph]

/-- The inverse Stern--Brocot boundary map reads off exactly the continued-fraction
coordinate of the target positive irrational. -/
theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate
    (x : {x : ℝ // Irrational x ∧ 0 < x}) :
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph
        (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x) =
      simpleCFPositiveCoordinateHomeomorph x := by
  simp [sternBrocotBoundaryPositiveIrrationalHomeomorph]

/-- In the initial-`false` Stern--Brocot half, the positive-irrational
continued-fraction coordinate has integer part `0`. This is the Lean form of the
book's `(0,1)` row in the continued-fraction/Stern--Brocot comparison table. -/
theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate_initialFalse
    {b : cantorNonEventuallyConstantBranches} (hb : b.1 0 = false) :
    simpleCFPositiveCoordinateHomeomorph
        (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
      (0, cantorBranchRunLength b) := by
  rw [sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate,
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse hb]

/-- In the initial-`true` Stern--Brocot half, the positive-irrational
continued-fraction coordinate records the first run length as the integer part
and shifts the positive tail. -/
theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate_initialTrue
    {b : cantorNonEventuallyConstantBranches} (hb : b.1 0 = true) :
    simpleCFPositiveCoordinateHomeomorph
        (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
      ((cantorBranchRunLength b 0).1, shiftPositiveNat (cantorBranchRunLength b)) := by
  rw [sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate,
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue hb]

/-- Positive irrationals whose continued-fraction integer part is `0` correspond
to initial-`false` Stern--Brocot boundary branches, with the same positive
run-length tail. This is the inverse form of the book's `(0,1)`/`L`-subtree
correspondence. -/
theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate_initialZero
    {x : {x : ℝ // Irrational x ∧ 0 < x}} {s : ℕ → positiveNat}
    (hx : simpleCFPositiveCoordinateHomeomorph x = (0, s)) :
    (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x).1 0 = false ∧
      cantorBranchRunLength (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x) = s := by
  let b : cantorNonEventuallyConstantBranches :=
    sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x
  have hcoord :
      cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b = (0, s) := by
    simpa [b, hx] using
      sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate x
  have hbfalse : b.1 0 = false := by
    cases hb : b.1 0
    · rfl
    · have htrue :=
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue
          (b := b) hb
      rw [hcoord] at htrue
      have hfst := congrArg Prod.fst htrue
      have hpos : 1 ≤ (cantorBranchRunLength b 0).1 :=
        (cantorBranchRunLength b 0).2
      simp at hfst
      omega
  have hfalse :=
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse
      (b := b) hbfalse
  rw [hcoord] at hfalse
  have hruns : s = cantorBranchRunLength b := congrArg Prod.snd hfalse
  exact ⟨by simpa [b] using hbfalse, by simpa [b] using hruns.symm⟩

/-- Positive irrationals with positive continued-fraction integer part correspond
to Stern--Brocot boundary branches with an initial `true` run. The first run
length is that integer part, and the remaining run lengths are the positive
continued-fraction tail. -/
theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate_positiveIntegerPart
    {x : {x : ℝ // Irrational x ∧ 0 < x}} {a₀ : ℕ} {s : ℕ → positiveNat}
    (ha₀ : 0 < a₀)
    (hx : simpleCFPositiveCoordinateHomeomorph x = (a₀, s)) :
    (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x).1 0 = true ∧
      (cantorBranchRunLength (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x) 0).1 =
        a₀ ∧
      shiftPositiveNat (cantorBranchRunLength
          (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x)) = s := by
  let b : cantorNonEventuallyConstantBranches :=
    sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x
  have hcoord :
      cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b = (a₀, s) := by
    simpa [b, hx] using
      sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate x
  have hbtrue : b.1 0 = true := by
    cases hb : b.1 0
    · have hfalse :=
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse
          (b := b) hb
      rw [hcoord] at hfalse
      have hfst := congrArg Prod.fst hfalse
      simp at hfst
      omega
    · rfl
  have htrue :=
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue
      (b := b) hbtrue
  rw [hcoord] at htrue
  have hfst : a₀ = (cantorBranchRunLength b 0).1 := congrArg Prod.fst htrue
  have hsnd : s = shiftPositiveNat (cantorBranchRunLength b) := congrArg Prod.snd htrue
  exact ⟨by simpa [b] using hbtrue, by simpa [b] using hfst.symm,
    by simpa [b] using hsnd.symm⟩

theorem sternBrocotBoundaryPositiveIrrationalHomeomorphismFact :
    Nonempty (cantorNonEventuallyConstantBranches ≃ₜ
      {x : ℝ // Irrational x ∧ 0 < x}) :=
  ⟨sternBrocotBoundaryPositiveIrrationalHomeomorph⟩

/-- The initial-`false` Stern--Brocot half maps exactly to positive irrationals
below `1`. This is the precise Lean form of the book's
`(0,1) \setminus ℚ` versus `S ∩ cyl L` row. -/
theorem sternBrocotBoundaryPositiveIrrationalHomeomorph_initialFalse_iff_mem_unitInterval
    (b : cantorNonEventuallyConstantBranches) :
    b.1 0 = false ↔ (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 < 1 := by
  have hbranch :=
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_fst_eq_zero_iff_initialFalse b
  have hcoord := sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate b
  have hcf :=
    simpleCFPositiveCoordinateHomeomorph_fst_eq_zero_iff_lt_one
      (sternBrocotBoundaryPositiveIrrationalHomeomorph b)
  calc
    b.1 0 = false ↔
        (cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b).1 = 0 :=
      hbranch.symm
    _ ↔
        (simpleCFPositiveCoordinateHomeomorph
            (sternBrocotBoundaryPositiveIrrationalHomeomorph b)).1 = 0 := by
      rw [hcoord]
    _ ↔ (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 < 1 :=
      hcf

/-- The L-subtree of the Stern--Brocot non-eventually-constant boundary is
homeomorphic to the irrational points of `(0,1)`. -/
noncomputable def sternBrocotLSubtreeUnitIntervalHomeomorph :
    {b : cantorNonEventuallyConstantBranches // b.1 0 = false} ≃ₜ
      {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} :=
  (sternBrocotBoundaryPositiveIrrationalHomeomorph.subtype
    (p := fun b : cantorNonEventuallyConstantBranches => b.1 0 = false)
    (q := fun x : {x : ℝ // Irrational x ∧ 0 < x} => x.1 < 1)
    (fun b =>
      sternBrocotBoundaryPositiveIrrationalHomeomorph_initialFalse_iff_mem_unitInterval b)).trans
    positiveIrrationalLtOneHomeomorphUnitInterval

theorem sternBrocotLSubtreeUnitIntervalHomeomorphismFact :
    Nonempty ({b : cantorNonEventuallyConstantBranches // b.1 0 = false} ≃ₜ
      {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) :=
  ⟨sternBrocotLSubtreeUnitIntervalHomeomorph⟩

/-- Specification for the intended graph of the Stern--Brocot mediant-limit map
to the closed extended half-line `[0,∞]`, represented by `ENNReal`. This is a
specification relation rather than a function: uniqueness of the endpoint value
is the remaining numeric part of the mediant-limit proof. -/
inductive sternBrocotMediantLimitValueSpec : cantor_space → ENNReal → Prop
  | allLeft :
      sternBrocotMediantLimitValueSpec sternBrocotAllLeftBranch 0
  | allRight :
      sternBrocotMediantLimitValueSpec sternBrocotAllRightBranch ⊤
  | finiteEndpointBelow (a₀ : ℕ) (pref : finseq positiveNat) :
      sternBrocotMediantLimitValueSpec
        (sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref)
        (ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ))
  | finiteEndpointAbove (a₀ : ℕ) (pref : finseq positiveNat) :
      sternBrocotMediantLimitValueSpec
        (sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref)
        (ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ))
  | positiveIrrational (b : cantorNonEventuallyConstantBranches) :
      sternBrocotMediantLimitValueSpec b.1
        (ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1)

theorem sternBrocotMediantLimitValueSpec_finiteEndpointPair
    (a₀ : ℕ) (pref : finseq positiveNat) :
    ∃ y : ENNReal,
      sternBrocotMediantLimitValueSpec
          (sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref) y ∧
        sternBrocotMediantLimitValueSpec
          (sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) y ∧
        y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) ∧
        0 < y := by
  let y : ENNReal := ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ)
  have hypos : 0 < y := by
    rw [ENNReal.ofReal_pos]
    exact_mod_cast sternBrocotFiniteCylinderLabel_pos a₀ pref
  exact ⟨y,
    sternBrocotMediantLimitValueSpec.finiteEndpointBelow a₀ pref,
    sternBrocotMediantLimitValueSpec.finiteEndpointAbove a₀ pref,
    rfl, hypos⟩

theorem sternBrocotMediantLimitValueSpec_positiveIrrational_pos
    (b : cantorNonEventuallyConstantBranches) :
    0 < ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 := by
  rw [ENNReal.ofReal_pos]
  exact (sternBrocotBoundaryPositiveIrrationalHomeomorph b).2.2

theorem sternBrocotMediantLimitValueSpec_positiveIrrational
    (b : cantorNonEventuallyConstantBranches) :
    sternBrocotMediantLimitValueSpec b.1
      (ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1) :=
  sternBrocotMediantLimitValueSpec.positiveIrrational b

theorem sternBrocotMediantLimitValueSpec_unique_of_mem_nonEventuallyConstantSet
    {x : cantor_space} (hx : x ∈ cantorNonEventuallyConstantSet) {y : ENNReal}
    (h : sternBrocotMediantLimitValueSpec x y) :
    y = ENNReal.ofReal
      (sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨x, hx⟩).1 := by
  induction h with
  | allLeft =>
      exact False.elim (sternBrocotAllLeftBranch_not_mem_nonEventuallyConstantSet hx)
  | allRight =>
      exact False.elim (sternBrocotAllRightBranch_not_mem_nonEventuallyConstantSet hx)
  | finiteEndpointBelow a₀ pref =>
      exact False.elim
        (sternBrocotFiniteCylinderEndpointBelowBranch_not_mem_nonEventuallyConstantSet
          a₀ pref hx)
  | finiteEndpointAbove a₀ pref =>
      exact False.elim
        (sternBrocotFiniteCylinderEndpointAboveBranch_not_mem_nonEventuallyConstantSet
          a₀ pref hx)
  | positiveIrrational c =>
      have hc : c = ⟨c.1, hx⟩ := by
        apply Subtype.ext
        rfl
      rw [← hc]

theorem sternBrocotMediantLimitValueSpec_unique_on_nonEventuallyConstant
    (b : cantorNonEventuallyConstantBranches) {y : ENNReal}
    (h : sternBrocotMediantLimitValueSpec b.1 y) :
    y = ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 := by
  simpa using
    sternBrocotMediantLimitValueSpec_unique_of_mem_nonEventuallyConstantSet
      b.2 h

theorem sternBrocotMediantLimitValueSpec_unique_of_eq_allLeft
    {x : cantor_space} (hx : x = sternBrocotAllLeftBranch) {y : ENNReal}
    (h : sternBrocotMediantLimitValueSpec x y) :
    y = 0 := by
  induction h with
  | allLeft =>
      rfl
  | allRight =>
      exact False.elim (sternBrocotAllLeftBranch_ne_allRightBranch hx.symm)
  | finiteEndpointBelow a₀ pref =>
      exact False.elim
        (sternBrocotAllLeftBranch_ne_endpointBelowBranch
          (sternBrocotRunLengthWord a₀ pref) hx.symm)
  | finiteEndpointAbove a₀ pref =>
      exact False.elim
        (sternBrocotAllLeftBranch_ne_endpointAboveBranch
          (sternBrocotRunLengthWord a₀ pref) hx.symm)
  | positiveIrrational b =>
      have hb : sternBrocotAllLeftBranch ∈ cantorNonEventuallyConstantSet := by
        rw [← hx]
        exact b.2
      exact False.elim (sternBrocotAllLeftBranch_not_mem_nonEventuallyConstantSet hb)

theorem sternBrocotMediantLimitValueSpec_unique_allLeft
    {y : ENNReal}
    (h : sternBrocotMediantLimitValueSpec sternBrocotAllLeftBranch y) :
    y = 0 :=
  sternBrocotMediantLimitValueSpec_unique_of_eq_allLeft rfl h

theorem sternBrocotMediantLimitValueSpec_unique_of_eq_allRight
    {x : cantor_space} (hx : x = sternBrocotAllRightBranch) {y : ENNReal}
    (h : sternBrocotMediantLimitValueSpec x y) :
    y = ⊤ := by
  induction h with
  | allLeft =>
      exact False.elim (sternBrocotAllLeftBranch_ne_allRightBranch hx)
  | allRight =>
      rfl
  | finiteEndpointBelow a₀ pref =>
      exact False.elim
        (sternBrocotAllRightBranch_ne_endpointBelowBranch
          (sternBrocotRunLengthWord a₀ pref) hx.symm)
  | finiteEndpointAbove a₀ pref =>
      exact False.elim
        (sternBrocotAllRightBranch_ne_endpointAboveBranch
          (sternBrocotRunLengthWord a₀ pref) hx.symm)
  | positiveIrrational b =>
      have hb : sternBrocotAllRightBranch ∈ cantorNonEventuallyConstantSet := by
        rw [← hx]
        exact b.2
      exact False.elim (sternBrocotAllRightBranch_not_mem_nonEventuallyConstantSet hb)

theorem sternBrocotMediantLimitValueSpec_unique_allRight
    {y : ENNReal}
    (h : sternBrocotMediantLimitValueSpec sternBrocotAllRightBranch y) :
    y = ⊤ :=
  sternBrocotMediantLimitValueSpec_unique_of_eq_allRight rfl h

/-- Every positive rational occurs as the common specified mediant-limit value
of the two finite endpoint branches attached to a Stern--Brocot node with that
label. This is the value-level existence half of the book's `2`-to-`1` rational
endpoint clause. -/
theorem sternBrocotMediantLimitValueSpec_positiveRat_endpointPair
    (q : ℚ) (hq : 0 < q) :
    ∃ bBelow bAbove : cantor_space, ∃ y : ENNReal,
      bBelow ∉ cantorNonEventuallyConstantSet ∧
        bAbove ∉ cantorNonEventuallyConstantSet ∧
        bBelow ≠ bAbove ∧
        sternBrocotMediantLimitValueSpec bBelow y ∧
        sternBrocotMediantLimitValueSpec bAbove y ∧
        y = ENNReal.ofReal ((q : ℚ) : ℝ) ∧
        0 < y := by
  rcases sternBrocotPositiveRat_endpointBranches_exist q hq with
    ⟨a₀, pref, hlabel, hbelowS, haboveS, hne⟩
  rcases sternBrocotMediantLimitValueSpec_finiteEndpointPair a₀ pref with
    ⟨y, hbelowValue, haboveValue, hy, hypos⟩
  refine ⟨sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref,
    sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref, y,
    hbelowS, haboveS, hne, hbelowValue, haboveValue, ?_, hypos⟩
  rw [hy, hlabel]

theorem sternBrocotMediantLimitValueSpec_endpointBelow_exists
    (w : sternBrocotWord) :
    ∃ y : ENNReal,
      sternBrocotMediantLimitValueSpec (sternBrocotEndpointBelowBranch w) y ∧
        0 < y := by
  rcases sternBrocotEndpointBelowBranch_exists_finiteCylinder w with
    ⟨a₀, pref, hbranch⟩
  rcases sternBrocotMediantLimitValueSpec_finiteEndpointPair a₀ pref with
    ⟨y, hbelow, _habove, _hy, hypos⟩
  refine ⟨y, ?_, hypos⟩
  rw [hbranch]
  exact hbelow

theorem sternBrocotMediantLimitValueSpec_endpointAbove_exists
    (w : sternBrocotWord) :
    ∃ y : ENNReal,
      sternBrocotMediantLimitValueSpec (sternBrocotEndpointAboveBranch w) y ∧
        0 < y := by
  rcases sternBrocotEndpointAboveBranch_exists_finiteCylinder w with
    ⟨a₀, pref, hbranch⟩
  rcases sternBrocotMediantLimitValueSpec_finiteEndpointPair a₀ pref with
    ⟨y, _hbelow, habove, _hy, hypos⟩
  refine ⟨y, ?_, hypos⟩
  rw [hbranch]
  exact habove

theorem sternBrocotMediantLimitValueSpec_finiteEndpointBelow_no_aboveConstructor
    (a₀ b₀ : ℕ) (pref qref : finseq positiveNat) :
    ¬ sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref =
      sternBrocotFiniteCylinderEndpointAboveBranch b₀ qref :=
  sternBrocotFiniteCylinderEndpointBelowBranch_ne_aboveBranch a₀ b₀ pref qref

theorem sternBrocotMediantLimitValueSpec_finiteEndpointAbove_no_belowConstructor
    (a₀ b₀ : ℕ) (pref qref : finseq positiveNat) :
    ¬ sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref =
      sternBrocotFiniteCylinderEndpointBelowBranch b₀ qref := by
  intro h
  exact sternBrocotFiniteCylinderEndpointBelowBranch_ne_aboveBranch b₀ a₀ qref pref h.symm

theorem sternBrocotMediantLimitValueSpec_unique_of_eq_finiteEndpointBelow
    {x : cantor_space} (a₀ : ℕ) (pref : finseq positiveNat)
    (hx : x = sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref)
    {y : ENNReal} (h : sternBrocotMediantLimitValueSpec x y) :
    y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) := by
  induction h with
  | allLeft =>
      exact False.elim
        (sternBrocotAllLeftBranch_ne_endpointBelowBranch
          (sternBrocotRunLengthWord a₀ pref)
          (by simpa [sternBrocotFiniteCylinderEndpointBelowBranch] using hx))
  | allRight =>
      exact False.elim
        (sternBrocotAllRightBranch_ne_endpointBelowBranch
          (sternBrocotRunLengthWord a₀ pref)
          (by simpa [sternBrocotFiniteCylinderEndpointBelowBranch] using hx))
  | finiteEndpointBelow b₀ qref =>
      have hlabel :
          sternBrocotFiniteCylinderLabel b₀ qref =
            sternBrocotFiniteCylinderLabel a₀ pref :=
        sternBrocotFiniteCylinderLabel_eq_of_endpointBelowBranch_eq hx
      rw [hlabel]
  | finiteEndpointAbove b₀ qref =>
      exact False.elim
        (sternBrocotMediantLimitValueSpec_finiteEndpointAbove_no_belowConstructor
          b₀ a₀ qref pref hx)
  | positiveIrrational b =>
      have hbmem :
          sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∈
            cantorNonEventuallyConstantSet := by
        rw [← hx]
        exact b.2
      exact False.elim
        (sternBrocotFiniteCylinderEndpointBelowBranch_not_mem_nonEventuallyConstantSet
          a₀ pref hbmem)

theorem sternBrocotMediantLimitValueSpec_unique_finiteEndpointBelow
    (a₀ : ℕ) (pref : finseq positiveNat) {y : ENNReal}
    (h :
      sternBrocotMediantLimitValueSpec
        (sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref) y) :
    y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) :=
  sternBrocotMediantLimitValueSpec_unique_of_eq_finiteEndpointBelow a₀ pref rfl h

theorem sternBrocotMediantLimitValueSpec_unique_of_eq_finiteEndpointAbove
    {x : cantor_space} (a₀ : ℕ) (pref : finseq positiveNat)
    (hx : x = sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref)
    {y : ENNReal} (h : sternBrocotMediantLimitValueSpec x y) :
    y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) := by
  induction h with
  | allLeft =>
      exact False.elim
        (sternBrocotAllLeftBranch_ne_endpointAboveBranch
          (sternBrocotRunLengthWord a₀ pref)
          (by simpa [sternBrocotFiniteCylinderEndpointAboveBranch] using hx))
  | allRight =>
      exact False.elim
        (sternBrocotAllRightBranch_ne_endpointAboveBranch
          (sternBrocotRunLengthWord a₀ pref)
          (by simpa [sternBrocotFiniteCylinderEndpointAboveBranch] using hx))
  | finiteEndpointBelow b₀ qref =>
      exact False.elim
        (sternBrocotMediantLimitValueSpec_finiteEndpointBelow_no_aboveConstructor
          b₀ a₀ qref pref hx)
  | finiteEndpointAbove b₀ qref =>
      have hlabel :
          sternBrocotFiniteCylinderLabel b₀ qref =
            sternBrocotFiniteCylinderLabel a₀ pref :=
        sternBrocotFiniteCylinderLabel_eq_of_endpointAboveBranch_eq hx
      rw [hlabel]
  | positiveIrrational b =>
      have hbmem :
          sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref ∈
            cantorNonEventuallyConstantSet := by
        rw [← hx]
        exact b.2
      exact False.elim
        (sternBrocotFiniteCylinderEndpointAboveBranch_not_mem_nonEventuallyConstantSet
          a₀ pref hbmem)

theorem sternBrocotMediantLimitValueSpec_unique_finiteEndpointAbove
    (a₀ : ℕ) (pref : finseq positiveNat) {y : ENNReal}
    (h :
      sternBrocotMediantLimitValueSpec
        (sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) y) :
    y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) :=
  sternBrocotMediantLimitValueSpec_unique_of_eq_finiteEndpointAbove a₀ pref rfl h

theorem sternBrocotMediantLimitValueSpec_unique
    {x : cantor_space} {y z : ENNReal}
    (hy : sternBrocotMediantLimitValueSpec x y)
    (hz : sternBrocotMediantLimitValueSpec x z) :
    y = z := by
  induction hy with
  | allLeft =>
      exact (sternBrocotMediantLimitValueSpec_unique_allLeft hz).symm
  | allRight =>
      exact (sternBrocotMediantLimitValueSpec_unique_allRight hz).symm
  | finiteEndpointBelow a₀ pref =>
      exact (sternBrocotMediantLimitValueSpec_unique_finiteEndpointBelow
        a₀ pref hz).symm
  | finiteEndpointAbove a₀ pref =>
      exact (sternBrocotMediantLimitValueSpec_unique_finiteEndpointAbove
        a₀ pref hz).symm
  | positiveIrrational b =>
      exact (sternBrocotMediantLimitValueSpec_unique_on_nonEventuallyConstant b hz).symm

theorem sternBrocotMediantLimitValueSpec_exists_of_not_mem_nonEventuallyConstantSet
    {b : cantor_space} (hb : b ∉ cantorNonEventuallyConstantSet) :
    ∃ y : ENNReal, sternBrocotMediantLimitValueSpec b y := by
  rcases (cantorNotMemNonEventuallyConstantSet_iff_specialOrEndpointBranch b).1 hb with
    hleft | hright | hbelow | habove
  · exact ⟨0, by rw [hleft]; exact sternBrocotMediantLimitValueSpec.allLeft⟩
  · exact ⟨⊤, by rw [hright]; exact sternBrocotMediantLimitValueSpec.allRight⟩
  · rcases hbelow with ⟨w, rfl⟩
    rcases sternBrocotMediantLimitValueSpec_endpointBelow_exists w with
      ⟨y, hy, _hypos⟩
    exact ⟨y, hy⟩
  · rcases habove with ⟨w, rfl⟩
    rcases sternBrocotMediantLimitValueSpec_endpointAbove_exists w with
      ⟨y, hy, _hypos⟩
    exact ⟨y, hy⟩

theorem sternBrocotMediantLimitValueSpec_exists (b : cantor_space) :
    ∃ y : ENNReal, sternBrocotMediantLimitValueSpec b y := by
  by_cases hb : b ∈ cantorNonEventuallyConstantSet
  · let bS : cantorNonEventuallyConstantBranches := ⟨b, hb⟩
    exact ⟨ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph bS).1,
      sternBrocotMediantLimitValueSpec_positiveIrrational bS⟩
  · exact sternBrocotMediantLimitValueSpec_exists_of_not_mem_nonEventuallyConstantSet hb

/-- The Stern--Brocot mediant-limit map `Φ : 2^ω → [0,∞]`, represented by
`ENNReal`. The graph is the single-valued total specification relation proved
above. The geometric interval construction is formalized separately as
`mediantIntervalLimit`, with existence and uniqueness proved by
`mediantBranchFrame_extended_existsUnique`. The theorem `mediantIntervalLimit_eq_sternBrocotMediantLimitValue` in
`MediantLimitIdentification` identifies the two maps on every branch. -/
noncomputable def sternBrocotMediantLimitValue (b : cantor_space) : ENNReal :=
  Classical.choose (sternBrocotMediantLimitValueSpec_exists b)

theorem sternBrocotMediantLimitValue_spec (b : cantor_space) :
    sternBrocotMediantLimitValueSpec b (sternBrocotMediantLimitValue b) :=
  Classical.choose_spec (sternBrocotMediantLimitValueSpec_exists b)

theorem sternBrocotMediantLimitValue_eq_of_spec
    {b : cantor_space} {y : ENNReal}
    (h : sternBrocotMediantLimitValueSpec b y) :
    sternBrocotMediantLimitValue b = y :=
  sternBrocotMediantLimitValueSpec_unique
    (sternBrocotMediantLimitValue_spec b) h

theorem sternBrocotMediantLimitValue_allLeft :
    sternBrocotMediantLimitValue sternBrocotAllLeftBranch = 0 :=
  sternBrocotMediantLimitValue_eq_of_spec
    sternBrocotMediantLimitValueSpec.allLeft

theorem sternBrocotMediantLimitValue_allRight :
    sternBrocotMediantLimitValue sternBrocotAllRightBranch = ⊤ :=
  sternBrocotMediantLimitValue_eq_of_spec
    sternBrocotMediantLimitValueSpec.allRight

theorem sternBrocotMediantLimitValue_finiteEndpointBelow
    (a₀ : ℕ) (pref : finseq positiveNat) :
    sternBrocotMediantLimitValue
        (sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref) =
      ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) :=
  sternBrocotMediantLimitValue_eq_of_spec
    (sternBrocotMediantLimitValueSpec.finiteEndpointBelow a₀ pref)

theorem sternBrocotMediantLimitValue_finiteEndpointAbove
    (a₀ : ℕ) (pref : finseq positiveNat) :
    sternBrocotMediantLimitValue
        (sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) =
      ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) :=
  sternBrocotMediantLimitValue_eq_of_spec
    (sternBrocotMediantLimitValueSpec.finiteEndpointAbove a₀ pref)

theorem sternBrocotMediantLimitValue_positiveIrrational
    (b : cantorNonEventuallyConstantBranches) :
    sternBrocotMediantLimitValue b.1 =
      ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 :=
  sternBrocotMediantLimitValue_eq_of_spec
    (sternBrocotMediantLimitValueSpec.positiveIrrational b)

/-- On the non-eventually-constant boundary, the mediant-limit map is the
continued-fraction value read from the same run-length coordinates. -/
theorem sternBrocotMediantLimitValue_runLengthCoordinates
    (b : cantorNonEventuallyConstantBranches) :
    sternBrocotMediantLimitValue b.1 =
      ENNReal.ofReal
        (simpleCFPositiveCoordinateHomeomorph.symm
          (cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b)).1 := by
  rw [sternBrocotMediantLimitValue_positiveIrrational,
    sternBrocotBoundaryPositiveIrrationalHomeomorph_apply,
    cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply]

/-- The only branch with mediant-limit value `0` is the all-left branch. -/
theorem sternBrocotMediantLimitValue_eq_zero_iff (b : cantor_space) :
    sternBrocotMediantLimitValue b = 0 ↔ b = sternBrocotAllLeftBranch := by
  constructor
  · intro hb
    by_cases hbS : b ∈ cantorNonEventuallyConstantSet
    · let c : cantorNonEventuallyConstantBranches := ⟨b, hbS⟩
      rw [show b = c.1 by rfl, sternBrocotMediantLimitValue_positiveIrrational c] at hb
      have hpos := sternBrocotMediantLimitValueSpec_positiveIrrational_pos c
      exact False.elim ((ne_of_gt hpos) hb)
    · rcases (cantorNotMemNonEventuallyConstantSet_iff_specialOrEndpointBranch b).1 hbS with
        hleft | hright | hbelow | habove
      · exact hleft
      · rw [hright, sternBrocotMediantLimitValue_allRight] at hb
        exact False.elim (ENNReal.top_ne_zero hb)
      · rcases hbelow with ⟨w, hbshape⟩
        rcases sternBrocotEndpointBelowBranch_exists_finiteCylinder w with
          ⟨a₀, pref, hw⟩
        have hbfinite :
            b = sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref := by
          rw [hbshape, hw]
        rw [hbfinite, sternBrocotMediantLimitValue_finiteEndpointBelow a₀ pref] at hb
        have hpos :
            0 < ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) := by
          rw [ENNReal.ofReal_pos]
          exact_mod_cast sternBrocotFiniteCylinderLabel_pos a₀ pref
        exact False.elim ((ne_of_gt hpos) hb)
      · rcases habove with ⟨w, hbshape⟩
        rcases sternBrocotEndpointAboveBranch_exists_finiteCylinder w with
          ⟨a₀, pref, hw⟩
        have hbfinite :
            b = sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref := by
          rw [hbshape, hw]
        rw [hbfinite, sternBrocotMediantLimitValue_finiteEndpointAbove a₀ pref] at hb
        have hpos :
            0 < ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) := by
          rw [ENNReal.ofReal_pos]
          exact_mod_cast sternBrocotFiniteCylinderLabel_pos a₀ pref
        exact False.elim ((ne_of_gt hpos) hb)
  · intro hb
    rw [hb]
    exact sternBrocotMediantLimitValue_allLeft

/-- The only branch with mediant-limit value `∞` is the all-right branch. -/
theorem sternBrocotMediantLimitValue_eq_top_iff (b : cantor_space) :
    sternBrocotMediantLimitValue b = ⊤ ↔ b = sternBrocotAllRightBranch := by
  constructor
  · intro hb
    by_cases hbS : b ∈ cantorNonEventuallyConstantSet
    · let c : cantorNonEventuallyConstantBranches := ⟨b, hbS⟩
      rw [show b = c.1 by rfl, sternBrocotMediantLimitValue_positiveIrrational c] at hb
      exact False.elim
        ((ENNReal.ofReal_ne_top :
          ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph c).1 ≠ ⊤) hb)
    · rcases (cantorNotMemNonEventuallyConstantSet_iff_specialOrEndpointBranch b).1 hbS with
        hleft | hright | hbelow | habove
      · rw [hleft, sternBrocotMediantLimitValue_allLeft] at hb
        exact False.elim (ENNReal.zero_ne_top hb)
      · exact hright
      · rcases hbelow with ⟨w, hbshape⟩
        rcases sternBrocotEndpointBelowBranch_exists_finiteCylinder w with
          ⟨a₀, pref, hw⟩
        have hbfinite :
            b = sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref := by
          rw [hbshape, hw]
        rw [hbfinite, sternBrocotMediantLimitValue_finiteEndpointBelow a₀ pref] at hb
        exact False.elim
          ((ENNReal.ofReal_ne_top :
            ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) ≠ ⊤) hb)
      · rcases habove with ⟨w, hbshape⟩
        rcases sternBrocotEndpointAboveBranch_exists_finiteCylinder w with
          ⟨a₀, pref, hw⟩
        have hbfinite :
            b = sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref := by
          rw [hbshape, hw]
        rw [hbfinite, sternBrocotMediantLimitValue_finiteEndpointAbove a₀ pref] at hb
        exact False.elim
          ((ENNReal.ofReal_ne_top :
            ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) ≠ ⊤) hb)
  · intro hb
    rw [hb]
    exact sternBrocotMediantLimitValue_allRight

/-- Every positive rational occurs as the common actual mediant-limit value of
the two finite endpoint branches attached to a Stern--Brocot node with that
label. This transfers the specification-level endpoint-pair statement to the
map `sternBrocotMediantLimitValue` used for `Φ`. -/
theorem sternBrocotMediantLimitValue_positiveRat_endpointPair
    (q : ℚ) (hq : 0 < q) :
    ∃ bBelow bAbove : cantor_space,
      bBelow ∉ cantorNonEventuallyConstantSet ∧
        bAbove ∉ cantorNonEventuallyConstantSet ∧
        bBelow ≠ bAbove ∧
        sternBrocotMediantLimitValue bBelow =
          ENNReal.ofReal ((q : ℚ) : ℝ) ∧
        sternBrocotMediantLimitValue bAbove =
          ENNReal.ofReal ((q : ℚ) : ℝ) := by
  rcases sternBrocotMediantLimitValueSpec_positiveRat_endpointPair q hq with
    ⟨bBelow, bAbove, y, hbelowS, haboveS, hne, hbelowValue, haboveValue,
      hy, _hypos⟩
  refine ⟨bBelow, bAbove, hbelowS, haboveS, hne, ?_, ?_⟩
  · rw [sternBrocotMediantLimitValue_eq_of_spec hbelowValue, hy]
  · rw [sternBrocotMediantLimitValue_eq_of_spec haboveValue, hy]

/-- A non-`S` branch whose actual mediant-limit value is a fixed positive
rational is one of the two endpoint branches attached to a finite
Stern--Brocot node with that rational label. This is the uniqueness direction
hidden in the book's `2`-to-`1` rational endpoint clause. -/
theorem sternBrocotMediantLimitValue_positiveRat_preimage_endpoint
    (q : ℚ) (hq : 0 < q) {b : cantor_space}
    (hbS : b ∉ cantorNonEventuallyConstantSet)
    (hbval :
      sternBrocotMediantLimitValue b = ENNReal.ofReal ((q : ℚ) : ℝ)) :
    ∃ a₀ : ℕ, ∃ pref : finseq positiveNat,
      sternBrocotFiniteCylinderLabel a₀ pref = q ∧
        (b = sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref ∨
          b = sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) := by
  have hq_nonneg : 0 ≤ ((q : ℚ) : ℝ) := by
    exact_mod_cast (le_of_lt hq)
  rcases (cantorNotMemNonEventuallyConstantSet_iff_specialOrEndpointBranch b).1 hbS with
    hleft | hright | hbelow | habove
  · rw [hleft, sternBrocotMediantLimitValue_allLeft] at hbval
    have hq_pos : 0 < ENNReal.ofReal ((q : ℚ) : ℝ) := by
      rw [ENNReal.ofReal_pos]
      exact_mod_cast hq
    exact False.elim ((ne_of_lt hq_pos) hbval)
  · rw [hright, sternBrocotMediantLimitValue_allRight] at hbval
    exact False.elim
      ((ENNReal.ofReal_ne_top : ENNReal.ofReal ((q : ℚ) : ℝ) ≠ ⊤) hbval.symm)
  · rcases hbelow with ⟨w, hb⟩
    rcases sternBrocotEndpointBelowBranch_exists_finiteCylinder w with
      ⟨a₀, pref, hw⟩
    have hbfinite :
        b = sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref := by
      rw [hb, hw]
    have hvalue :
        ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) =
          ENNReal.ofReal ((q : ℚ) : ℝ) := by
      rw [hbfinite, sternBrocotMediantLimitValue_finiteEndpointBelow a₀ pref] at hbval
      exact hbval
    have hlabel_nonneg :
        0 ≤ ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) := by
      exact_mod_cast
        (le_of_lt (sternBrocotFiniteCylinderLabel_pos a₀ pref))
    have hlabel_real :
        ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) = ((q : ℚ) : ℝ) :=
      (ENNReal.ofReal_eq_ofReal_iff hlabel_nonneg hq_nonneg).1 hvalue
    have hlabel : sternBrocotFiniteCylinderLabel a₀ pref = q :=
      Rat.cast_injective hlabel_real
    exact ⟨a₀, pref, hlabel, Or.inl hbfinite⟩
  · rcases habove with ⟨w, hb⟩
    rcases sternBrocotEndpointAboveBranch_exists_finiteCylinder w with
      ⟨a₀, pref, hw⟩
    have hbfinite :
        b = sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref := by
      rw [hb, hw]
    have hvalue :
        ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) =
          ENNReal.ofReal ((q : ℚ) : ℝ) := by
      rw [hbfinite, sternBrocotMediantLimitValue_finiteEndpointAbove a₀ pref] at hbval
      exact hbval
    have hlabel_nonneg :
        0 ≤ ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) := by
      exact_mod_cast
        (le_of_lt (sternBrocotFiniteCylinderLabel_pos a₀ pref))
    have hlabel_real :
        ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) = ((q : ℚ) : ℝ) :=
      (ENNReal.ofReal_eq_ofReal_iff hlabel_nonneg hq_nonneg).1 hvalue
    have hlabel : sternBrocotFiniteCylinderLabel a₀ pref = q :=
      Rat.cast_injective hlabel_real
    exact ⟨a₀, pref, hlabel, Or.inr hbfinite⟩

/-- For each positive rational, the non-`S` fiber of the actual mediant-limit map
is exactly the lower and upper endpoint branch of the unique finite node with
that rational label. -/

theorem sternBrocotMediantLimitValue_positiveRat_exact_endpointPair
    (q : ℚ) (hq : 0 < q) :
    ∃ bBelow bAbove : cantor_space,
      bBelow ∉ cantorNonEventuallyConstantSet ∧
        bAbove ∉ cantorNonEventuallyConstantSet ∧
        bBelow ≠ bAbove ∧
        sternBrocotMediantLimitValue bBelow =
          ENNReal.ofReal ((q : ℚ) : ℝ) ∧
        sternBrocotMediantLimitValue bAbove =
          ENNReal.ofReal ((q : ℚ) : ℝ) ∧
        ∀ b : cantor_space,
          b ∉ cantorNonEventuallyConstantSet →
            sternBrocotMediantLimitValue b = ENNReal.ofReal ((q : ℚ) : ℝ) →
              b = bBelow ∨ b = bAbove := by
  rcases sternBrocotPositiveRat_endpointBranches_exist q hq with
    ⟨a₀, pref, hlabel, hbelowS, haboveS, hne⟩
  refine ⟨sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref,
    sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref,
    hbelowS, haboveS, hne, ?_, ?_, ?_⟩
  · rw [sternBrocotMediantLimitValue_finiteEndpointBelow, hlabel]
  · rw [sternBrocotMediantLimitValue_finiteEndpointAbove, hlabel]
  · intro b hbS hbval
    rcases sternBrocotMediantLimitValue_positiveRat_preimage_endpoint q hq hbS hbval with
      ⟨b₀, qref, hbLabel, hshape⟩
    have hparams :
        b₀ = a₀ ∧ qref = pref :=
      sternBrocotFiniteCylinderLabel_injective (hbLabel.trans hlabel.symm)
    rcases hparams with ⟨rfl, rfl⟩
    exact hshape

/-- The actual mediant-limit map is onto the positive irrational line when
restricted to non-eventually-constant branches. -/
theorem sternBrocotMediantLimitValue_positiveIrrational_surjective
    (x : {x : ℝ // Irrational x ∧ 0 < x}) :
    ∃ b : cantorNonEventuallyConstantBranches,
      sternBrocotMediantLimitValue b.1 = ENNReal.ofReal x.1 := by
  refine ⟨sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x, ?_⟩
  simpa using
    sternBrocotMediantLimitValue_positiveIrrational
      (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x)

/-- Each non-eventually-constant branch has a unique positive irrational value
under the actual mediant-limit map. -/
theorem sternBrocotMediantLimitValue_positiveIrrational_unique_value
    (b : cantorNonEventuallyConstantBranches) :
    ∃! x : {x : ℝ // Irrational x ∧ 0 < x},
      sternBrocotMediantLimitValue b.1 = ENNReal.ofReal x.1 := by
  refine ⟨sternBrocotBoundaryPositiveIrrationalHomeomorph b,
    sternBrocotMediantLimitValue_positiveIrrational b, ?_⟩
  intro x hx
  apply Subtype.ext
  rw [sternBrocotMediantLimitValue_positiveIrrational b] at hx
  exact ((ENNReal.ofReal_eq_ofReal_iff
    (le_of_lt (sternBrocotBoundaryPositiveIrrationalHomeomorph b).2.2)
    (le_of_lt x.2.2)).1 hx).symm

/-- The actual mediant-limit map is injective on the
non-eventually-constant boundary `S`. -/
theorem sternBrocotMediantLimitValue_nonEventuallyConstant_injective :
    Function.Injective
      (fun b : cantorNonEventuallyConstantBranches =>
        sternBrocotMediantLimitValue b.1) := by
  intro b c h
  have hvalue :
      ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 =
        ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph c).1 := by
    rw [← sternBrocotMediantLimitValue_positiveIrrational b,
      ← sternBrocotMediantLimitValue_positiveIrrational c]
    exact h
  have hb_nonneg :
      0 ≤ (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 :=
    le_of_lt (sternBrocotBoundaryPositiveIrrationalHomeomorph b).2.2
  have hc_nonneg :
      0 ≤ (sternBrocotBoundaryPositiveIrrationalHomeomorph c).1 :=
    le_of_lt (sternBrocotBoundaryPositiveIrrationalHomeomorph c).2.2
  have hreal :
      (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 =
        (sternBrocotBoundaryPositiveIrrationalHomeomorph c).1 :=
    (ENNReal.ofReal_eq_ofReal_iff hb_nonneg hc_nonneg).1 hvalue
  apply sternBrocotBoundaryPositiveIrrationalHomeomorph.injective
  exact Subtype.ext hreal

/-- Each positive irrational has a unique non-eventually-constant branch whose
actual mediant-limit value is its `ENNReal` value. This is the exact
function-level form of the book's statement that `Φ` is a bijection from `S`
onto the positive irrationals. -/
theorem sternBrocotMediantLimitValue_positiveIrrational_unique_preimage
    (x : {x : ℝ // Irrational x ∧ 0 < x}) :
    ∃! b : cantorNonEventuallyConstantBranches,
      sternBrocotMediantLimitValue b.1 = ENNReal.ofReal x.1 := by
  let b₀ : cantorNonEventuallyConstantBranches :=
    sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x
  have hb₀ :
      sternBrocotMediantLimitValue b₀.1 = ENNReal.ofReal x.1 := by
    simpa [b₀] using sternBrocotMediantLimitValue_positiveIrrational b₀
  refine ⟨b₀, hb₀, ?_⟩
  intro b hb
  exact sternBrocotMediantLimitValue_nonEventuallyConstant_injective
    (hb.trans hb₀.symm)

/-- Book-facing statement for the actual mediant-limit map obtained from the total
single-valued specification relation. -/
def ConcreteSternBrocotMediantLimitMapStatement : Prop :=
    (∀ b : cantor_space,
      sternBrocotMediantLimitValueSpec b (sternBrocotMediantLimitValue b)) ∧
      (∀ b : cantor_space, ∀ y : ENNReal,
        sternBrocotMediantLimitValueSpec b y →
          sternBrocotMediantLimitValue b = y) ∧
      sternBrocotMediantLimitValue sternBrocotAllLeftBranch = 0 ∧
      sternBrocotMediantLimitValue sternBrocotAllRightBranch = ⊤ ∧
      (∀ b : cantor_space,
        sternBrocotMediantLimitValue b = 0 ↔ b = sternBrocotAllLeftBranch) ∧
      (∀ b : cantor_space,
        sternBrocotMediantLimitValue b = ⊤ ↔ b = sternBrocotAllRightBranch) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotMediantLimitValue
            (sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref) =
          ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        sternBrocotMediantLimitValue
            (sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) =
          ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ)) ∧
      (∀ q : ℚ, 0 < q →
        ∃ bBelow bAbove : cantor_space,
          bBelow ∉ cantorNonEventuallyConstantSet ∧
            bAbove ∉ cantorNonEventuallyConstantSet ∧
            bBelow ≠ bAbove ∧
            sternBrocotMediantLimitValue bBelow =
              ENNReal.ofReal ((q : ℚ) : ℝ) ∧
            sternBrocotMediantLimitValue bAbove =
              ENNReal.ofReal ((q : ℚ) : ℝ)) ∧
      (∀ q : ℚ, 0 < q →
        ∃ bBelow bAbove : cantor_space,
          bBelow ∉ cantorNonEventuallyConstantSet ∧
            bAbove ∉ cantorNonEventuallyConstantSet ∧
            bBelow ≠ bAbove ∧
            sternBrocotMediantLimitValue bBelow =
              ENNReal.ofReal ((q : ℚ) : ℝ) ∧
            sternBrocotMediantLimitValue bAbove =
              ENNReal.ofReal ((q : ℚ) : ℝ) ∧
            ∀ b : cantor_space,
              b ∉ cantorNonEventuallyConstantSet →
                sternBrocotMediantLimitValue b = ENNReal.ofReal ((q : ℚ) : ℝ) →
                  b = bBelow ∨ b = bAbove) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        sternBrocotMediantLimitValue b.1 =
          ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        sternBrocotMediantLimitValue b.1 =
          ENNReal.ofReal
            (simpleCFPositiveCoordinateHomeomorph.symm
              (cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b)).1) ∧
      Function.Injective
        (fun b : cantorNonEventuallyConstantBranches =>
          sternBrocotMediantLimitValue b.1) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        ∃! x : {x : ℝ // Irrational x ∧ 0 < x},
          sternBrocotMediantLimitValue b.1 = ENNReal.ofReal x.1) ∧
      (∀ x : {x : ℝ // Irrational x ∧ 0 < x},
        ∃! b : cantorNonEventuallyConstantBranches,
          sternBrocotMediantLimitValue b.1 = ENNReal.ofReal x.1) ∧
      (∀ x : {x : ℝ // Irrational x ∧ 0 < x},
        ∃ b : cantorNonEventuallyConstantBranches,
          sternBrocotMediantLimitValue b.1 = ENNReal.ofReal x.1)


/-- Book-facing package proving the actual mediant-limit map statement. -/
theorem concreteSternBrocotMediantLimitMapFacts :
    ConcreteSternBrocotMediantLimitMapStatement := by
  refine ⟨?_, ?_, sternBrocotMediantLimitValue_allLeft,
    sternBrocotMediantLimitValue_allRight, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact sternBrocotMediantLimitValue_spec b
  · intro b y hy
    exact sternBrocotMediantLimitValue_eq_of_spec hy
  · intro b
    exact sternBrocotMediantLimitValue_eq_zero_iff b
  · intro b
    exact sternBrocotMediantLimitValue_eq_top_iff b
  · intro a₀ pref
    exact sternBrocotMediantLimitValue_finiteEndpointBelow a₀ pref
  · intro a₀ pref
    exact sternBrocotMediantLimitValue_finiteEndpointAbove a₀ pref
  · intro q hq
    exact sternBrocotMediantLimitValue_positiveRat_endpointPair q hq
  · intro q hq
    exact sternBrocotMediantLimitValue_positiveRat_exact_endpointPair q hq
  · intro b
    exact sternBrocotMediantLimitValue_positiveIrrational b
  · intro b
    exact sternBrocotMediantLimitValue_runLengthCoordinates b
  · exact sternBrocotMediantLimitValue_nonEventuallyConstant_injective
  · intro b
    exact sternBrocotMediantLimitValue_positiveIrrational_unique_value b
  · intro x
    exact sternBrocotMediantLimitValue_positiveIrrational_unique_preimage x
  · intro x
    exact sternBrocotMediantLimitValue_positiveIrrational_surjective x

/-- Book-facing statement for the current numeric specification of the
mediant-limit map: constants are assigned `0` and `∞`, paired rational endpoint
branches receive the same positive rational value, and branches in `S` receive
their positive-irrational continued-fraction value. -/
def ConcreteSternBrocotMediantLimitValueSpecStatement : Prop :=
    sternBrocotMediantLimitValueSpec sternBrocotAllLeftBranch 0 ∧
      sternBrocotMediantLimitValueSpec sternBrocotAllRightBranch ⊤ ∧
      (∀ y : ENNReal,
        sternBrocotMediantLimitValueSpec sternBrocotAllLeftBranch y →
          y = 0) ∧
      (∀ y : ENNReal,
        sternBrocotMediantLimitValueSpec sternBrocotAllRightBranch y →
          y = ⊤) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        ∃ y : ENNReal,
          sternBrocotMediantLimitValueSpec
              (sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref) y ∧
            sternBrocotMediantLimitValueSpec
              (sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) y ∧
            y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) ∧
            0 < y) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat, ∀ y : ENNReal,
        sternBrocotMediantLimitValueSpec
            (sternBrocotFiniteCylinderEndpointBelowBranch a₀ pref) y →
          y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ)) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat, ∀ y : ENNReal,
        sternBrocotMediantLimitValueSpec
            (sternBrocotFiniteCylinderEndpointAboveBranch a₀ pref) y →
          y = ENNReal.ofReal ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ)) ∧
      (∀ q : ℚ, 0 < q →
        ∃ bBelow bAbove : cantor_space, ∃ y : ENNReal,
          bBelow ∉ cantorNonEventuallyConstantSet ∧
            bAbove ∉ cantorNonEventuallyConstantSet ∧
            bBelow ≠ bAbove ∧
            sternBrocotMediantLimitValueSpec bBelow y ∧
            sternBrocotMediantLimitValueSpec bAbove y ∧
            y = ENNReal.ofReal ((q : ℚ) : ℝ) ∧
            0 < y) ∧
      (∀ w : sternBrocotWord,
        ∃ y : ENNReal,
          sternBrocotMediantLimitValueSpec (sternBrocotEndpointBelowBranch w) y ∧
            0 < y) ∧
      (∀ w : sternBrocotWord,
        ∃ y : ENNReal,
          sternBrocotMediantLimitValueSpec (sternBrocotEndpointAboveBranch w) y ∧
            0 < y) ∧
      (∀ b : cantor_space, b ∉ cantorNonEventuallyConstantSet →
        ∃ y : ENNReal, sternBrocotMediantLimitValueSpec b y) ∧
      (∀ b : cantor_space,
        ∃ y : ENNReal, sternBrocotMediantLimitValueSpec b y) ∧
      (∀ b : cantor_space, ∀ y z : ENNReal,
        sternBrocotMediantLimitValueSpec b y →
          sternBrocotMediantLimitValueSpec b z →
            y = z) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        sternBrocotMediantLimitValueSpec b.1
            (ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1) ∧
          0 < ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 ∧
          ∀ y : ENNReal, sternBrocotMediantLimitValueSpec b.1 y →
            y = ENNReal.ofReal
              (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1)

/-- Book-facing package proving the current numeric mediant-limit specification. -/
theorem concreteSternBrocotMediantLimitValueSpecFacts :
    ConcreteSternBrocotMediantLimitValueSpecStatement := by
  refine ⟨sternBrocotMediantLimitValueSpec.allLeft,
    sternBrocotMediantLimitValueSpec.allRight, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro y hy
    exact sternBrocotMediantLimitValueSpec_unique_allLeft hy
  · intro y hy
    exact sternBrocotMediantLimitValueSpec_unique_allRight hy
  · intro a₀ pref
    exact sternBrocotMediantLimitValueSpec_finiteEndpointPair a₀ pref
  · intro a₀ pref y hy
    exact sternBrocotMediantLimitValueSpec_unique_finiteEndpointBelow a₀ pref hy
  · intro a₀ pref y hy
    exact sternBrocotMediantLimitValueSpec_unique_finiteEndpointAbove a₀ pref hy
  · intro q hq
    exact sternBrocotMediantLimitValueSpec_positiveRat_endpointPair q hq
  · intro w
    exact sternBrocotMediantLimitValueSpec_endpointBelow_exists w
  · intro w
    exact sternBrocotMediantLimitValueSpec_endpointAbove_exists w
  · intro b hb
    exact sternBrocotMediantLimitValueSpec_exists_of_not_mem_nonEventuallyConstantSet hb
  · intro b
    exact sternBrocotMediantLimitValueSpec_exists b
  · intro b y z hy hz
    exact sternBrocotMediantLimitValueSpec_unique hy hz
  · intro b
    exact ⟨sternBrocotMediantLimitValueSpec_positiveIrrational b,
      sternBrocotMediantLimitValueSpec_positiveIrrational_pos b,
      fun y hy => sternBrocotMediantLimitValueSpec_unique_on_nonEventuallyConstant b hy⟩

/-- Book-facing statement for the Stern--Brocot boundary paragraph: the
non-eventually-constant boundary is the complement of eventually constant
branches, run-length coordinates give a homeomorphism with
`ℕ × (ℕ → positiveNat)`, the same coordinates give the Baire-space and
positive-irrational models in both directions, the initial `L`-subtree is the
unit-interval irrational row, positive integer parts give initial `R`-runs, and
the Gauss-path operation shifts the positive run-length tail. -/
def ConcreteSternBrocotBoundaryRunLengthStatement : Prop :=
    (∀ b : cantor_space,
      b ∈ cantorNonEventuallyConstantSet ↔ ¬ cantorEventuallyConstant b) ∧
      (∀ b : cantor_space,
        b ∈ cantorNonEventuallyConstantSet ↔
          ¬ ∃ w : sternBrocotWord, ∃ tail : Bool,
            b = finiteWordConstantTailBranch (sternBrocotWordBool w) tail) ∧
      (∀ b : cantor_space,
        cantorEventuallyConstant b → b ∉ cantorNonEventuallyConstantSet) ∧
      (∀ b : cantor_space,
        (cantorChangePointMap b : Set ℕ).Finite → b ∉ cantorNonEventuallyConstantSet) ∧
      Nonempty (cantorNonEventuallyConstantBranches ≃ₜ Bool × (ℕ → positiveNat)) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        cantorNonEventuallyConstantBranchesRunLengthHomeomorph b =
          (b.1 0, cantorBranchRunLength b)) ∧
      Continuous cantorBranchRunLength ∧
      Nonempty (cantorNonEventuallyConstantBranches ≃ₜ
        ℕ × (ℕ → positiveNat)) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
          boolPositiveNatSeqEquivNatPositiveNatSeq (b.1 0, cantorBranchRunLength b)) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = false →
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
          (0, cantorBranchRunLength b)) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = true →
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
          ((cantorBranchRunLength b 0).1, shiftPositiveNat (cantorBranchRunLength b))) ∧
      Nonempty (cantorNonEventuallyConstantBranches ≃ₜ baire_space) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        sternBrocotBoundaryBaireHomeomorph b =
          natPositiveNatSeqHomeomorphBaire
            (boolPositiveNatSeqEquivNatPositiveNatSeq (b.1 0, cantorBranchRunLength b))) ∧
      Nonempty (cantorNonEventuallyConstantBranches ≃ₜ
        {x : ℝ // Irrational x ∧ 0 < x}) ∧
      Nonempty ({b : cantorNonEventuallyConstantBranches // b.1 0 = false} ≃ₜ
        {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        b.1 0 = false ↔ (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 < 1) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        sternBrocotBoundaryPositiveIrrationalHomeomorph b =
          simpleCFPositiveCoordinateHomeomorph.symm
            (boolPositiveNatSeqEquivNatPositiveNatSeq (b.1 0, cantorBranchRunLength b))) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        simpleCFPositiveCoordinateHomeomorph
            (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
          cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b) ∧
      (∀ x : {x : ℝ // Irrational x ∧ 0 < x},
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph
            (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x) =
          simpleCFPositiveCoordinateHomeomorph x) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = false →
        simpleCFPositiveCoordinateHomeomorph
            (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
          (0, cantorBranchRunLength b)) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = true →
        simpleCFPositiveCoordinateHomeomorph
            (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
          ((cantorBranchRunLength b 0).1, shiftPositiveNat (cantorBranchRunLength b))) ∧
      (∀ x : {x : ℝ // Irrational x ∧ 0 < x}, ∀ s : ℕ → positiveNat,
        simpleCFPositiveCoordinateHomeomorph x = (0, s) →
          (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x).1 0 = false ∧
            cantorBranchRunLength
                (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x) = s) ∧
      (∀ x : {x : ℝ // Irrational x ∧ 0 < x}, ∀ a₀ : ℕ, ∀ s : ℕ → positiveNat,
        0 < a₀ →
          simpleCFPositiveCoordinateHomeomorph x = (a₀, s) →
            (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x).1 0 = true ∧
              (cantorBranchRunLength
                  (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x) 0).1 =
                a₀ ∧
              shiftPositiveNat (cantorBranchRunLength
                  (sternBrocotBoundaryPositiveIrrationalHomeomorph.symm x)) = s) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = false →
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
            (0, cantorBranchRunLength b) ∧
          (sternBrocotLSubtreeGaussPath b).1 0 = false ∧
          cantorBranchRunLength (sternBrocotLSubtreeGaussPath b) =
            shiftPositiveNat (cantorBranchRunLength b))

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Branches in $S$ use the same run-length coding as finite rational nodes: an irrational
    $$\alpha = [a_0; a_1,a_2,\ldots]$$
    corresponds to
    $$\wordRepeat{R}{a_0}\,\wordRepeat{L}{a_1}\,\wordRepeat{R}{a_2}\,\wordRepeat{L}{a_3}\,\cdots,$$
    with $\wordRepeat{R}{0}$ the empty word, so numbers in $(0,1)$ correspond to branches of the L-subtree.
-/

/-- Book-facing package proving the Stern--Brocot boundary run-length statement. -/
theorem concreteSternBrocotBoundaryRunLengthFacts :
    ConcreteSternBrocotBoundaryRunLengthStatement := by
  refine ⟨?_, ?_, ?_, ?_, ⟨cantorNonEventuallyConstantBranchesRunLengthHomeomorph⟩,
    ?_, cantorBranchRunLength_continuous,
    ⟨cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph⟩,
    ?_, ?_, ?_, sternBrocotBoundaryBaireHomeomorphismFact, ?_,
    sternBrocotBoundaryPositiveIrrationalHomeomorphismFact,
    sternBrocotLSubtreeUnitIntervalHomeomorphismFact, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro b
    exact cantorNonEventuallyConstantSet_iff_not_eventuallyConstant b
  · intro b
    exact cantorNonEventuallyConstantSet_iff_not_exists_finiteSternBrocotWordConstantTailBranch b
  · intro b hb
    exact cantorEventuallyConstant_not_mem_nonEventuallyConstantSet hb
  · intro b hfin
    exact cantorFiniteChangePoints_not_mem_nonEventuallyConstantSet hfin
  · intro b
    exact cantorNonEventuallyConstantBranchesRunLengthHomeomorph_apply b
  · intro b
    exact cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply b
  · intro b hb
    exact cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialFalse hb
  · intro b hb
    exact cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph_apply_initialTrue hb
  · intro b
    exact sternBrocotBoundaryBaireHomeomorph_apply b
  · intro b
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_initialFalse_iff_mem_unitInterval b
  · intro b
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_apply b
  · intro b
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate b
  · intro x
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate x
  · intro b hb
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate_initialFalse hb
  · intro b hb
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate_initialTrue hb
  · intro x s hx
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate_initialZero hx
  · intro x a₀ s ha₀ hx
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_symm_coordinate_positiveIntegerPart
      ha₀ hx
  · intro b hb
    exact sternBrocotLSubtreeGaussPath_deleteInitialRun_swapTail hb

/-- The whole irrational line is the sign product of the Stern--Brocot boundary:
take the sign of `x`, apply the positive boundary model to `|x|`, and remember the
boundary path. This is the Lean form of the comparison table's
`sign times S applied to |x|` row. -/
noncomputable def irrationalLineSignSternBrocotBoundaryHomeomorph :
    {x : ℝ // Irrational x} ≃ₜ Bool × cantorNonEventuallyConstantBranches :=
  irrationalSignAbsHomeomorph.trans
    ((Homeomorph.refl Bool).prodCongr
      sternBrocotBoundaryPositiveIrrationalHomeomorph.symm)

theorem irrationalLineSignSternBrocotBoundaryHomeomorph_apply
    (x : {x : ℝ // Irrational x}) :
    irrationalLineSignSternBrocotBoundaryHomeomorph x =
      (irrationalSign x,
        sternBrocotBoundaryPositiveIrrationalHomeomorph.symm
          (irrationalAbsPositive x)) := by
  rfl

theorem irrationalLineSignSternBrocotBoundaryHomeomorphismFact :
    Nonempty ({x : ℝ // Irrational x} ≃ₜ
      Bool × cantorNonEventuallyConstantBranches) :=
  ⟨irrationalLineSignSternBrocotBoundaryHomeomorph⟩

/-- The irrational-line Baire model is noncompact, by continued-fraction coordinates. -/
theorem irrationals_noncompact_via_continuedFractions :
    NoncompactSpace {x : ℝ // Irrational x} := by
  rw [← not_compactSpace_iff]
  intro hcompact
  have : CompactSpace {x : ℝ // Irrational x} := hcompact
  rcases continuedFractionBaireHomeomorphismFact with ⟨θ⟩
  have : CompactSpace baire_space := θ.compactSpace
  exact (not_compactSpace_iff.mpr baire_space_noncompact) inferInstance

/-- The positive-irrational continued-fraction row is noncompact, because its
coordinates are Baire-space coordinates. -/
theorem positiveIrrationals_noncompact_via_continuedFractions :
    NoncompactSpace {x : ℝ // Irrational x ∧ 0 < x} := by
  rw [← not_compactSpace_iff]
  intro hcompact
  have : CompactSpace {x : ℝ // Irrational x ∧ 0 < x} := hcompact
  have : CompactSpace baire_space := positiveIrrationalBaireHomeomorph.compactSpace
  exact (not_compactSpace_iff.mpr baire_space_noncompact) inferInstance

/-- The `(0,1) \setminus ℚ` continued-fraction row is noncompact, because its
`a₀ = 0` coordinates are Baire-space coordinates. -/
theorem unitIntervalIrrationals_noncompact_via_continuedFractions :
    NoncompactSpace {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} := by
  rw [← not_compactSpace_iff]
  intro hcompact
  have : CompactSpace {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} := hcompact
  have : CompactSpace baire_space := simpleCFUnitIntervalBaireHomeomorph.compactSpace
  exact (not_compactSpace_iff.mpr baire_space_noncompact) inferInstance

/-- The infinite-subsets Baire model is a noncompact subspace of Cantor-space
coordinates. -/
theorem infiniteSubsetsOmega_noncompact :
    NoncompactSpace infiniteSubsetsOmega := by
  rw [← not_compactSpace_iff]
  intro hcompact
  have : CompactSpace infiniteSubsetsOmega := hcompact
  have : CompactSpace baire_space := infiniteSubsetsOmegaBaireHomeomorph.compactSpace
  exact (not_compactSpace_iff.mpr baire_space_noncompact) inferInstance

/-- The Stern--Brocot boundary `S`, although represented as a subspace of Cantor
coordinates, is noncompact because its run-length coordinates are Baire-space
coordinates. -/
theorem sternBrocotBoundary_noncompact :
    NoncompactSpace cantorNonEventuallyConstantBranches := by
  rw [← not_compactSpace_iff]
  intro hcompact
  have : CompactSpace cantorNonEventuallyConstantBranches := hcompact
  have : CompactSpace baire_space := sternBrocotBoundaryBaireHomeomorph.compactSpace
  exact (not_compactSpace_iff.mpr baire_space_noncompact) inferInstance

/-- In each row of the bridge table, the listed finite information indexes
clopen basic pieces: binary prefixes, ternary prefixes, finite membership
decisions, Baire prefixes, continued-fraction prefixes, initial-gap data, and
finite switch-position decisions. -/
theorem concreteBridgeFiniteInformationClopen :
    (∀ s : finseq Bool, IsClopen (cyl s : Set cantor_space)) ∧
      (∀ s : finseq Bool, IsClopen (middleThirdsTernaryPrefixSet s)) ∧
      (∀ F G : Finset ℕ, IsClopen (membershipDecisionSet F G)) ∧
      (∀ s : finseq ℕ, IsClopen (cyl s : Set baire_space)) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat,
        IsClopen (simpleCFPartialQuotientCylinder a₀ s)) ∧
      (∀ s : finseq ℕ,
        IsClopen {A : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData A s}) ∧
      (∀ F G : Finset ℕ,
        IsClopen {A : infiniteSubsetsOmega | (A : powersetOmega) ∈ membershipDecisionSet F G}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact isClopen_cyl s
  · intro s
    have himage : IsClopen (middleThirdsCantorHomeomorph '' cyl s) :=
      ⟨middleThirdsCantorHomeomorph.isClosedMap _ (isClopen_cyl s).isClosed,
        middleThirdsCantorHomeomorph.isOpenMap _ (isClopen_cyl s).isOpen⟩
    simpa [middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet s] using himage
  · intro F G
    exact membershipDecisionSet_isClopen F G
  · intro s
    exact isClopen_cyl s
  · intro a₀ s
    exact isClopen_simpleCFPartialQuotientCylinder a₀ s
  · intro s
    exact isClopen_infiniteSubsetsOmegaInitialGapData s
  · intro F G
    exact (membershipDecisionSet_isClopen F G).preimage continuous_subtype_val

/-- In each row of the bridge table, the listed finite information gives a
topological basis: binary prefixes, ternary prefixes, finite membership
decisions, Baire prefixes, finite continued-fraction prefixes, and finite
initial-gap data. -/
theorem concreteBridgeFiniteInformationBasis :
    IsTopologicalBasis ({U : Set cantor_space | ∃ s : finseq Bool, U = cyl s}) ∧
      IsTopologicalBasis {U : Set middleThirdsCantorSet |
        ∃ s : finseq Bool, U = middleThirdsTernaryPrefixSet s} ∧
      IsTopologicalBasis {U : Set powersetOmega |
        ∃ F G : Finset ℕ, U = membershipDecisionSet F G} ∧
      IsTopologicalBasis ({U : Set baire_space | ∃ s : finseq ℕ, U = cyl s}) ∧
      IsTopologicalBasis {U : Set {x : ℝ // Irrational x} |
        ∃ a₀ : ℤ, ∃ s : finseq positiveNat, U = simpleCFPartialQuotientCylinder a₀ s} ∧
      IsTopologicalBasis {U : Set infiniteSubsetsOmega |
        ∃ s : finseq ℕ, U = {A : infiniteSubsetsOmega |
          infiniteSubsetsOmegaInitialGapData A s}} :=
  ⟨isTopologicalBasis_cantor_cyl, isTopologicalBasis_middleThirdsTernaryPrefixSet,
    isTopologicalBasis_membershipDecisionSet, isTopologicalBasis_baire_cyl,
    isTopologicalBasis_simpleCFPartialQuotientCylinder,
    isTopologicalBasis_infiniteSubsetsOmegaInitialGapData⟩

/-- The chapter's main concrete presentations are homeomorphic to the corresponding
reference spaces: the power-set and middle-thirds Cantor pictures model Cantor
space, while the irrational line, infinite subsets of `ω`, and the Stern--Brocot
boundary model Baire space. -/
theorem concreteModelHomeomorphismFacts :
    Nonempty (powersetOmega ≃ₜ cantor_space) ∧
      Nonempty (cantor_space ≃ₜ middleThirdsCantorSet) ∧
      Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) ∧
      Nonempty (infiniteSubsetsOmega ≃ₜ baire_space) ∧
      Nonempty (cantorNonEventuallyConstantBranches ≃ₜ baire_space) :=
  ⟨⟨powersetOmegaHomeomorphCantorSpace⟩, ⟨middleThirdsCantorHomeomorph⟩,
    continuedFractionBaireHomeomorphismFact, infiniteSubsetsOmegaBaireHomeomorphismFact,
    sternBrocotBoundaryBaireHomeomorphismFact⟩

/-- The three Cantor-space pictures in the bridge table are compact: the
binary-cylinder model, the middle-thirds Cantor set, and the power-set model. -/
theorem concreteCantorPicturesCompact :
    CompactSpace cantor_space ∧ CompactSpace middleThirdsCantorSet ∧
      CompactSpace powersetOmega :=
  ⟨cantor_space_compact, middleThirdsCantorSet_compact, powersetOmega_compact⟩

/-- The Baire-space pictures and the Stern--Brocot boundary bridge in the summary
are noncompact: the cylinder base, the irrational line, infinite subsets of `ω`,
and the non-eventually-constant Stern--Brocot boundary. -/
theorem concreteBairePicturesNoncompact :
    NoncompactSpace baire_space ∧ NoncompactSpace {x : ℝ // Irrational x} ∧
      NoncompactSpace infiniteSubsetsOmega ∧
        NoncompactSpace cantorNonEventuallyConstantBranches :=
  ⟨baire_space_noncompact, irrationals_noncompact_via_continuedFractions,
    infiniteSubsetsOmega_noncompact, sternBrocotBoundary_noncompact⟩

/-- Compactness separates the whole Cantor and Baire spaces in the bridge summary. -/
theorem concreteCantorBaireCompactnessSeparation :
    CompactSpace cantor_space ∧ NoncompactSpace baire_space :=
  ⟨cantor_space_compact, baire_space_noncompact⟩

/-- Compactness forbids identifying the whole Cantor and Baire spaces by a
homeomorphism. -/
theorem no_cantor_space_homeomorph_baire_space :
    ¬ Nonempty (cantor_space ≃ₜ baire_space) := by
  rintro ⟨h⟩
  have : CompactSpace baire_space := h.compactSpace
  exact (not_compactSpace_iff.mpr baire_space_noncompact) inferInstance

/-- The final bridge's embedding of the infinite-subsets Baire model into
Cantor-space coordinates is exactly the characteristic-function inclusion. -/
theorem concreteBaireIntoCantorCoordinateEmbeddingFacts :
    Topology.IsEmbedding infiniteSubsetsOmegaCantorEmbedding ∧
      (∀ A : infiniteSubsetsOmega,
        infiniteSubsetsOmegaCantorEmbedding A =
          subsetCharacteristic (A : powersetOmega)) :=
  ⟨infiniteSubsetsOmegaCantorEmbedding_isEmbedding,
    infiniteSubsetsOmegaCantorEmbedding_apply⟩

/-- Book-facing package for the final bridge and comparison section: finite
information indexes basic clopen pieces, the listed pictures are homeomorphic to
the right reference spaces, the middle-thirds model is the zero/two ternary-digit
model with binary cylinders sent to ternary-prefix pieces, the power-set model is
the characteristic-function model with finite positive and negative membership
requirements, the infinite-subsets model is a `Gδ` Polish subspace and embeds
into Cantor coordinates by characteristic functions, the gap map is the
Baire-space homeomorphism with finite initial-gap cylinders, switch positions
are run-length data shifted down by one, reference cylinders split into
immediate children, simple continued fractions have the expansion theorem
stated in the chapter and the continued-fraction coordinate topology with its
clopen integer-part partition and fixed-cell fractional cylinders, including
the parity-dependent interval calculation and shrinking endpoint lengths,
compactness separates Cantor and Baire space, and the continued-fraction/Stern--Brocot
comparison rows and Gauss-shift rule, including semiconvergent/Farey cylinder
geometry, finite L/R run-length bridge data, finite rational-node labels as
terminating expressions in lowest terms, the displayed initial tree, the `5 / 2`
example, the boundary run-length model, rational endpoint-branch shapes, the
eventually-constant and complement-of-`S` branch classifications, and the
specification and total function for the actual mediant-limit map, are formalized
in coordinates. -/
theorem concretePicturesBridgesComparisonFacts :
    ((∀ s : finseq Bool, IsClopen (cyl s : Set cantor_space)) ∧
      (∀ s : finseq Bool, IsClopen (middleThirdsTernaryPrefixSet s)) ∧
      (∀ F G : Finset ℕ, IsClopen (membershipDecisionSet F G)) ∧
      (∀ s : finseq ℕ, IsClopen (cyl s : Set baire_space)) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat,
        IsClopen (simpleCFPartialQuotientCylinder a₀ s)) ∧
      (∀ s : finseq ℕ,
        IsClopen {A : infiniteSubsetsOmega | infiniteSubsetsOmegaInitialGapData A s}) ∧
      (∀ F G : Finset ℕ,
        IsClopen {A : infiniteSubsetsOmega | (A : powersetOmega) ∈ membershipDecisionSet F G})) ∧
      ((∀ s : finseq Bool,
        (cyl s : Set cantor_space) =
            cyl (concat s [false]) ∪ cyl (concat s [true]) ∧
          Disjoint (cyl (concat s [false]) : Set cantor_space)
            (cyl (concat s [true]))) ∧
        ∀ s : finseq ℕ,
          (cyl s : Set baire_space) = ⋃ n : ℕ, cyl (concat s [n]) ∧
            ∀ m n : ℕ, m ≠ n →
              Disjoint (cyl (concat s [m]) : Set baire_space)
                (cyl (concat s [n]))) ∧
      (IsTopologicalBasis ({U : Set cantor_space | ∃ s : finseq Bool, U = cyl s}) ∧
        IsTopologicalBasis {U : Set middleThirdsCantorSet |
          ∃ s : finseq Bool, U = middleThirdsTernaryPrefixSet s} ∧
        IsTopologicalBasis {U : Set powersetOmega |
          ∃ F G : Finset ℕ, U = membershipDecisionSet F G} ∧
        IsTopologicalBasis ({U : Set baire_space | ∃ s : finseq ℕ, U = cyl s}) ∧
        IsTopologicalBasis {U : Set {x : ℝ // Irrational x} |
          ∃ a₀ : ℤ, ∃ s : finseq positiveNat,
            U = simpleCFPartialQuotientCylinder a₀ s} ∧
        IsTopologicalBasis {U : Set infiniteSubsetsOmega |
          ∃ s : finseq ℕ, U = {A : infiniteSubsetsOmega |
            infiniteSubsetsOmegaInitialGapData A s}}) ∧
      (Nonempty (powersetOmega ≃ₜ cantor_space) ∧
        Nonempty (cantor_space ≃ₜ middleThirdsCantorSet) ∧
        Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) ∧
        Nonempty (infiniteSubsetsOmega ≃ₜ baire_space) ∧
        Nonempty (cantorNonEventuallyConstantBranches ≃ₜ baire_space)) ∧
      SimpleCFExpansionExistsUniquelyForIrrationals ∧
      SimpleCFConverseForPositivePartials ∧
      Nonempty ({x : ℝ // Irrational x} ≃ₜ (ℤ × (ℕ → positiveNat))) ∧
      PolishSpace {x : ℝ // Irrational x} ∧
      IsLocallyConstant (fun x : {x : ℝ // Irrational x} => simpleCFIntegerPart x.1) ∧
      Continuous (fun x : {x : ℝ // Irrational x} => simpleCFIntegerPart x.1) ∧
      (∀ a₀ : ℤ,
        simpleCFIntegerPartCell a₀ =
          {x : {x : ℝ // Irrational x} |
            x.1 ∈ Set.Ioo (a₀ : ℝ) ((a₀ : ℝ) + 1)}) ∧
      (∀ a₀ : ℤ, ∀ x : {x : ℝ // Irrational x},
        x ∈ simpleCFIntegerPartCell a₀ → simpleCFIntegerPart x.1 = a₀) ∧
      (∀ a₀ : ℤ, IsClopen (simpleCFIntegerPartCell a₀)) ∧
      (⋃ a₀ : ℤ, simpleCFIntegerPartCell a₀) = (Set.univ : Set {x : ℝ // Irrational x}) ∧
      (∀ a₀ b₀ : ℤ, a₀ ≠ b₀ →
        Disjoint (simpleCFIntegerPartCell a₀) (simpleCFIntegerPartCell b₀)) ∧
      (∀ a₀ : ℤ,
        Nonempty (simpleCFFractionalInterval a₀ ≃ₜ (ℕ → positiveNat))) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat,
        IsClopen (simpleCFFractionalCylinder a₀ s)) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat,
        simpleCFFractionalCylinder a₀ s =
          ⋃ k : positiveNat, simpleCFFractionalCylinder a₀ (concat s [k])) ∧
      (∀ a₀ : ℤ, ∀ s : finseq positiveNat, ∀ m n : positiveNat, m ≠ n →
        Disjoint (simpleCFFractionalCylinder a₀ (concat s [m]))
          (simpleCFFractionalCylinder a₀ (concat s [n]))) ∧
      (∀ a₀ : ℤ, ∀ A : Set (finseq positiveNat),
        ∀ x : simpleCFFractionalInterval a₀,
          x ∈ simpleCFFractionalCylinderCode a₀ A ↔
            ∃ s : finseq positiveNat, s ∈ A ∧ x ∈ simpleCFFractionalCylinder a₀ s) ∧
      (∀ a₀ : ℤ, ∀ A : Set (finseq positiveNat),
        ∀ V : Set (simpleCFFractionalInterval a₀),
          simpleCFFractionalCylinderCode a₀ A ⊆ V ↔
            A ⊆ simpleCFFractionalOpenCylinderCode a₀ V) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a → Even n →
          ∀ x y : ℝ, 0 < x → x < y →
            simpleCFTailMap a n y < simpleCFTailMap a n x) ∧
      (∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a → Odd n →
          ∀ x y : ℝ, 0 < x → x < y →
            simpleCFTailMap a n x < simpleCFTailMap a n y) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          (fun x : ℝ => (a₀ : ℝ) + simpleCFTailMap a n x) ''
              {x : ℝ | Irrational x ∧ 1 < x} =
            {y : ℝ | Irrational y ∧
              y ∈
                if Even n then
                  Set.Ioo ((a₀ : ℝ) + simpleCFEndpoint a n)
                    ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
                else
                  Set.Ioo ((a₀ : ℝ) + simpleCFAdjacentEndpoint a n)
                    ((a₀ : ℝ) + simpleCFEndpoint a n)}) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ, ∀ n : ℕ,
        SimpleCFPositivePartials a →
          |((a₀ : ℝ) + simpleCFAdjacentEndpoint a n) -
              ((a₀ : ℝ) + simpleCFEndpoint a n)| =
            1 / ((simpleCFDen a (n + 1) : ℝ) *
              ((simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ)))) ∧
      (∀ a₀ : ℤ, ∀ a : ℕ → ℤ,
        SimpleCFPositivePartials a →
          Filter.Tendsto
            (fun n : ℕ =>
              |((a₀ : ℝ) + simpleCFAdjacentEndpoint a n) -
                ((a₀ : ℝ) + simpleCFEndpoint a n)|)
            Filter.atTop (𝓝 0)) ∧
      (∀ x : cantor_space,
        (middleThirdsCantorHomeomorph x : ℝ) =
          Real.ofDigits (fun n => cond (x n) (2 : Fin 3) 0)) ∧
      middleThirdsCantorSet =
        {x | ∃ a : ℕ → Fin 3, (∀ n, a n ≠ 1) ∧ Real.ofDigits a = x} ∧
      (∀ s : finseq Bool,
        middleThirdsCantorHomeomorph '' (cyl s : Set cantor_space) =
          middleThirdsTernaryPrefixSet s) ∧
      (∀ s t : finseq Bool,
        prefixOf s t →
          middleThirdsTernaryPrefixSet t ⊆ middleThirdsTernaryPrefixSet s) ∧
      (∀ E : powersetOmega,
        powersetOmegaHomeomorphCantorSpace E = subsetCharacteristic E) ∧
      (∀ x : cantor_space,
        powersetOmegaHomeomorphCantorSpace.symm x = characteristicSubset x) ∧
      (∀ F G : Finset ℕ,
        membershipDecisionSet F G =
            {E : powersetOmega |
              (F : Set ℕ) ⊆ (E : Set ℕ) ∧ Disjoint (G : Set ℕ) (E : Set ℕ)} ∧
          ((membershipDecisionSet F G).Nonempty ↔ Disjoint (F : Set ℕ) (G : Set ℕ)) ∧
          (¬ Disjoint (F : Set ℕ) (G : Set ℕ) → membershipDecisionSet F G = ∅)) ∧
      ConcreteSternBrocotCylinderGeometryStatement ∧
      ConcreteSternBrocotFiniteWordRunLengthBridgeStatement ∧
      Function.Bijective sternBrocotFiniteCylinderRunLengthWord ∧
      Function.Bijective
        (fun p : Sigma fun _ : ℕ => finseq positiveNat =>
          (⟨sternBrocotFiniteCylinderLabel p.1 p.2,
            sternBrocotFiniteCylinderLabel_pos p.1 p.2⟩ :
            {q : ℚ // 0 < q})) ∧
      (∀ a₀ : ℕ, ∀ pref : finseq positiveNat,
        ((sternBrocotFiniteCylinderLabel a₀ pref : ℚ) : ℝ) =
          simpleCFTerminatingExpressionValue a₀ pref) ∧
      (∀ a₀ : ℕ, ∀ a : ℕ → ℤ, ∀ n : ℕ, ∀ d : ℤ,
        d ∣ simpleCFShiftedSemiconvergentNum (a₀ : ℤ) a n 1 →
          d ∣ simpleCFSemiconvergentDen a n 1 →
            d ∣ (1 : ℤ)) ∧
      ((sternBrocotRunLengthWord 0 [],
          simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 0 1) =
            (([] : sternBrocotWord), (1 : ℚ)) ∧
        (sternBrocotRunLengthWord 0 [⟨1, by omega⟩],
          simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 1 1) =
            ([sternBrocotDirection.left], (1 / 2 : ℚ)) ∧
        (sternBrocotRunLengthWord 0 [⟨2, by omega⟩],
          simpleCFShiftedSemiconvergent 0 sternBrocotOneThirdPartials 1 1) =
            ([sternBrocotDirection.left, sternBrocotDirection.left], (1 / 3 : ℚ)) ∧
        (sternBrocotRunLengthWord 0 [⟨1, by omega⟩, ⟨1, by omega⟩],
          simpleCFShiftedSemiconvergent 0 sternBrocotExamplePartials 2 1) =
            ([sternBrocotDirection.left, sternBrocotDirection.right], (2 / 3 : ℚ)) ∧
        (sternBrocotRunLengthWord 1 [],
          simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 0 1) =
            ([sternBrocotDirection.right], (2 : ℚ)) ∧
        (sternBrocotRunLengthWord 1 [⟨1, by omega⟩],
          simpleCFShiftedSemiconvergent 1 sternBrocotExamplePartials 1 1) =
            ([sternBrocotDirection.right, sternBrocotDirection.left], (3 / 2 : ℚ)) ∧
        (sternBrocotRunLengthWord 2 [],
          simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 0 1) =
            ([sternBrocotDirection.right, sternBrocotDirection.right], (3 : ℚ)) ∧
        (sternBrocotRunLengthWord 2 [⟨1, by omega⟩],
          simpleCFShiftedSemiconvergent 2 sternBrocotExamplePartials 1 1) =
            ([sternBrocotDirection.right, sternBrocotDirection.right,
              sternBrocotDirection.left], (5 / 2 : ℚ))) ∧
      (∀ q : ℚ, sternBrocotLSubtreeLabel q ↔ 0 < q ∧ q < 1) ∧
      (∀ n : ℕ,
        infiniteSubsetsOmegaTailSet n =
          ⋃ m : {m : ℕ // n ≤ m}, membershipDecisionSet {m.1} ∅) ∧
      infiniteSubsetsOmegaSet = ⋂ n : ℕ, infiniteSubsetsOmegaTailSet n ∧
      (∀ n : ℕ, IsOpen (infiniteSubsetsOmegaTailSet n)) ∧
      IsGδ infiniteSubsetsOmegaSet ∧
      PolishSpace infiniteSubsetsOmega ∧
      (∀ A : infiniteSubsetsOmega,
        infiniteSubsetsOmegaBaireHomeomorph A = infiniteSubsetsOmegaGapMap A) ∧
      (∀ g : baire_space,
        infiniteSubsetsOmegaBaireHomeomorph.symm g = gapsToInfiniteSubset g) ∧
      (∀ A : infiniteSubsetsOmega, ∀ s : finseq ℕ,
        infiniteSubsetsOmegaBaireHomeomorph A ∈ cyl s ↔
          infiniteSubsetsOmegaInitialGapData A s) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        infiniteSubsetsOmegaGapMap (branchChangePointProductMap b).2 =
          fun n => (cantorBranchRunLength b n).1 - 1) ∧
      (∀ b : cantorNonEventuallyConstantBranches, ∀ n : ℕ,
        infiniteSubsetsOmegaNth (branchChangePointProductMap b).2 n =
          Finset.sum (Finset.range (n + 1)) (fun i => (cantorBranchRunLength b i).1) - 1) ∧
      (Topology.IsEmbedding infiniteSubsetsOmegaCantorEmbedding ∧
        ∀ A : infiniteSubsetsOmega,
          infiniteSubsetsOmegaCantorEmbedding A =
            subsetCharacteristic (A : powersetOmega)) ∧
      (CompactSpace cantor_space ∧ CompactSpace middleThirdsCantorSet ∧
        CompactSpace powersetOmega) ∧
      (NoncompactSpace baire_space ∧ NoncompactSpace {x : ℝ // Irrational x} ∧
        NoncompactSpace infiniteSubsetsOmega ∧
          NoncompactSpace cantorNonEventuallyConstantBranches) ∧
      (CompactSpace cantor_space ∧ NoncompactSpace baire_space ∧
        ¬ Nonempty (cantor_space ≃ₜ baire_space)) ∧
      Nonempty ({x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ₜ (ℕ → positiveNat)) ∧
      Nonempty ({b : cantorNonEventuallyConstantBranches // b.1 0 = false} ≃ₜ
        {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}) ∧
      Nonempty (cantorNonEventuallyConstantBranches ≃ₜ
        {x : ℝ // Irrational x ∧ 0 < x}) ∧
      ConcreteSternBrocotEventuallyConstantBranchStatement ∧
      ConcreteSternBrocotSpecialEndpointBranchStatement ∧
      ConcreteSternBrocotBoundaryRunLengthStatement ∧
      ConcreteSternBrocotComplementEndpointBranchStatement ∧
      ConcreteSternBrocotRationalEndpointBranchStatement ∧
      ConcreteSternBrocotMediantLimitValueSpecStatement ∧
      ConcreteSternBrocotMediantLimitMapStatement ∧
      sternBrocotMediantLimitValue sternBrocotAllLeftBranch = 0 ∧
      sternBrocotMediantLimitValue sternBrocotAllRightBranch = ⊤ ∧
      (∀ q : ℚ, 0 < q →
        ∃ bBelow bAbove : cantor_space,
          bBelow ∉ cantorNonEventuallyConstantSet ∧
            bAbove ∉ cantorNonEventuallyConstantSet ∧
            bBelow ≠ bAbove ∧
            sternBrocotMediantLimitValue bBelow =
              ENNReal.ofReal ((q : ℚ) : ℝ) ∧
            sternBrocotMediantLimitValue bAbove =
              ENNReal.ofReal ((q : ℚ) : ℝ) ∧
            ∀ b : cantor_space,
              b ∉ cantorNonEventuallyConstantSet →
                sternBrocotMediantLimitValue b = ENNReal.ofReal ((q : ℚ) : ℝ) →
                  b = bBelow ∨ b = bAbove) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        sternBrocotMediantLimitValue b.1 =
          ENNReal.ofReal (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1) ∧
      (∀ x : {x : ℝ // Irrational x ∧ 0 < x},
        ∃! b : cantorNonEventuallyConstantBranches,
          sternBrocotMediantLimitValue b.1 = ENNReal.ofReal x.1) ∧
      Nonempty ({x : ℝ // Irrational x} ≃ₜ
        Bool × cantorNonEventuallyConstantBranches) ∧
      (∀ x : {x : ℝ // Irrational x},
        irrationalLineSignSternBrocotBoundaryHomeomorph x =
          (irrationalSign x,
            sternBrocotBoundaryPositiveIrrationalHomeomorph.symm
              (irrationalAbsPositive x))) ∧
      (∀ b : cantorNonEventuallyConstantBranches,
        b.1 0 = false ↔ (sternBrocotBoundaryPositiveIrrationalHomeomorph b).1 < 1) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = false →
        simpleCFPositiveCoordinateHomeomorph
            (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
          (0, cantorBranchRunLength b)) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = true →
        simpleCFPositiveCoordinateHomeomorph
            (sternBrocotBoundaryPositiveIrrationalHomeomorph b) =
          ((cantorBranchRunLength b 0).1, shiftPositiveNat (cantorBranchRunLength b))) ∧
      (∃ θ : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1} ≃ₜ (ℕ → positiveNat),
        ∀ x : {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1},
          ∃ hx : Irrational (gaussMap x.1) ∧ 0 < gaussMap x.1 ∧ gaussMap x.1 < 1,
            θ ⟨gaussMap x.1, hx⟩ = shiftPositiveNat (θ x)) ∧
      (∀ b : cantorNonEventuallyConstantBranches, b.1 0 = false →
        cantorNonEventuallyConstantBranchesNatRunLengthHomeomorph b =
            (0, cantorBranchRunLength b) ∧
          (sternBrocotLSubtreeGaussPath b).1 0 = false ∧
          cantorBranchRunLength (sternBrocotLSubtreeGaussPath b) =
            shiftPositiveNat (cantorBranchRunLength b)) := by
  refine ⟨concreteBridgeFiniteInformationClopen, ?_, concreteBridgeFiniteInformationBasis,
    concreteModelHomeomorphismFacts, ?_, ?_, continuedFractionCoordinateHomeomorphismFact,
    irrationals_polish_via_continuedFractions, simpleCFIntegerPart_irrational_locallyConstant,
    simpleCFIntegerPart_irrational_continuous, ?_, ?_, ?_, iUnion_simpleCFIntegerPartCell,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    concreteSternBrocotCylinderGeometryFacts, concreteSternBrocotFiniteWordRunLengthBridgeFacts,
    sternBrocotFiniteCylinderRunLengthWord_bijective,
    sternBrocotFiniteCylinderLabel_bijective_positiveRat, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, concreteBaireIntoCantorCoordinateEmbeddingFacts,
    concreteCantorPicturesCompact, concreteBairePicturesNoncompact, ?_,
    ⟨simpleCFUnitIntervalCoordinateHomeomorph⟩,
    sternBrocotLSubtreeUnitIntervalHomeomorphismFact,
    sternBrocotBoundaryPositiveIrrationalHomeomorphismFact,
    concreteSternBrocotEventuallyConstantBranchFacts,
    concreteSternBrocotSpecialEndpointBranchFacts,
    concreteSternBrocotBoundaryRunLengthFacts,
    concreteSternBrocotComplementEndpointBranchFacts,
    concreteSternBrocotRationalEndpointBranchFacts,
    concreteSternBrocotMediantLimitValueSpecFacts,
    concreteSternBrocotMediantLimitMapFacts,
    sternBrocotMediantLimitValue_allLeft, sternBrocotMediantLimitValue_allRight,
    ?_, ?_, ?_, irrationalLineSignSternBrocotBoundaryHomeomorphismFact, ?_, ?_, ?_,
    ?_, gaussMapShiftCorrespondenceFact, ?_⟩
  · exact ⟨fun s =>
      ⟨cantor_cyl_eq_union_immediate_subcylinders s,
        disjoint_cantor_immediate_subcylinders s⟩,
      fun s =>
        ⟨baire_cyl_eq_iUnion_immediate_subcylinders s,
          fun m n hmn => disjoint_baire_immediate_subcylinders s hmn⟩⟩
  · exact simpleCFExpansionExistsUniquelyForIrrationals_of_algorithmExpansion
  · exact simpleCFConverseForPositivePartials_of_positive
  · intro a₀
    exact simpleCFIntegerPartCell_eq_interval a₀
  · intro a₀ x hx
    exact simpleCFIntegerPartCell_value hx
  · intro a₀
    exact isClopen_simpleCFIntegerPartCell a₀
  · intro a₀ b₀ hne
    exact disjoint_simpleCFIntegerPartCell hne
  · intro a₀
    exact fractionalPartContinuedFractionHomeomorphismFact a₀
  · intro a₀ s
    exact isClopen_simpleCFFractionalCylinder a₀ s
  · intro a₀ s
    exact simpleCFFractionalCylinder_eq_iUnion_immediate_subcylinders a₀ s
  · intro a₀ s m n hmn
    exact disjoint_simpleCFFractional_immediate_subcylinders a₀ s hmn
  · intro a₀ A x
    exact mem_simpleCFFractionalCylinderCode (a₀ := a₀) (A := A) (x := x)
  · intro a₀ A V
    exact simpleCFFractionalCylinderCode_subset_iff_subset_openCylinderCode
      (a₀ := a₀) (A := A) (V := V)
  · intro a n ha hn x y hx hxy
    exact simpleCFTailMap_strictAnti_of_even ha hn hx hxy
  · intro a n ha hn x y hx hxy
    exact simpleCFTailMap_strictMono_of_odd ha hn hx hxy
  · intro a₀ a n ha
    exact simpleCFTailImageInterval_eq_of_positive a₀ ha n
  · intro a₀ a n ha
    exact abs_translated_simpleCFAdjacentEndpoint_sub_endpoint ha a₀ n
  · intro a₀ a ha
    exact tendsto_abs_translated_simpleCFAdjacentEndpoint_sub_endpoint_zero ha a₀
  · exact middleThirdsCantorHomeomorph_apply
  · exact middleThirdsCantorSet_eq_zero_two_ofDigits
  · intro s
    exact middleThirdsCantorHomeomorph_image_cyl_eq_ternaryPrefixSet s
  · intro s t hst
    exact middleThirdsTernaryPrefixSet_subset_of_prefix hst
  · exact powersetOmegaHomeomorphCantorSpace_apply
  · intro x
    rfl
  · intro F G
    exact ⟨membershipDecisionSet_disjoint_form F G,
      membershipDecisionSet_nonempty_iff_disjoint F G,
      fun h => membershipDecisionSet_eq_empty_of_not_disjoint h⟩
  · intro a₀ pref
    exact sternBrocotFiniteCylinderLabel_cast_eq_terminatingExpressionValue a₀ pref
  · intro a₀ a n d hnum hden
    exact sternBrocotNodeLabel_lowestTerms a₀ a n hnum hden
  · exact sternBrocotInitialTreeDiagram_labels_and_words
  · intro q
    exact sternBrocotLSubtreeLabel_iff_pos_lt_one q
  · intro n
    exact infiniteSubsetsOmegaTailSet_eq_iUnion_membershipDecisionSet n
  · exact infiniteSubsetsOmegaGdeltaPresentationFact
  · intro n
    exact infiniteSubsetsOmegaTailSet_isOpen n
  · exact infiniteSubsetsOmegaSet_isGdelta
  · exact infiniteSubsetsOmega_polish
  · intro A
    exact infiniteSubsetsOmegaBaireHomeomorph_apply A
  · intro g
    exact infiniteSubsetsOmegaBaireHomeomorph_symm_apply g
  · intro A s
    exact infiniteSubsetsOmegaBaireHomeomorph_mem_cyl_iff_initialGapData A s
  · intro b
    exact infiniteSubsetsOmegaGapMap_branchChangePoints_eq_runLengthSubOne b
  · intro b n
    exact cantorBranchChangePointNth_eq_sum_runLengths_sub_one b n
  · exact ⟨cantor_space_compact, baire_space_noncompact, no_cantor_space_homeomorph_baire_space⟩
  · intro q hq
    exact sternBrocotMediantLimitValue_positiveRat_exact_endpointPair q hq
  · intro b
    exact sternBrocotMediantLimitValue_positiveIrrational b
  · intro x
    exact sternBrocotMediantLimitValue_positiveIrrational_unique_preimage x
  · intro x
    exact irrationalLineSignSternBrocotBoundaryHomeomorph_apply x
  · intro b
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_initialFalse_iff_mem_unitInterval b
  · intro b hb
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate_initialFalse hb
  · intro b hb
    exact sternBrocotBoundaryPositiveIrrationalHomeomorph_coordinate_initialTrue hb
  · intro b hb
    exact sternBrocotLSubtreeGaussPath_deleteInitialRun_swapTail hb

/-! ## Book correspondences for late-chapter constructions

These declarations are the Lean counterparts of the chapter's late constructions:
`cfFractionalLinear` (the book's `F_s` map) and an auxiliary real-valued
restriction of `sternBrocotMediantLimitValue` to the non-eventually-constant
branches, realized through `sternBrocotBoundaryPositiveIrrationalHomeomorph`.
The booklink markers attach them to the book source. -/

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    be the last two convergents computed from this prefix, and write
    $$F_s(x) \;:=\; \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}.$$
-/
/-- Book notation `F_s(x)`: the fractional-linear map on the next complete quotient `x`
attached to a continued-fraction prefix of length `n`, sending `x` to the real with that
prefix. -/
noncomputable def cfFractionalLinear (a : ℕ → ℤ) (n : ℕ) (x : ℝ) : ℝ :=
  (x * (simpleCFNum a (n + 1) : ℝ) + (simpleCFNum a n : ℝ)) /
    (x * (simpleCFDen a (n + 1) : ℝ) + (simpleCFDen a n : ℝ))

/-- Book claim: the boundary value `F_s(1)` is the mediant of the two convergents
`p_{n+1}/q_{n+1}` and `p_n/q_n`. -/
theorem cfFractionalLinear_one_eq_mediant (a : ℕ → ℤ) (n : ℕ) :
    cfFractionalLinear a n 1 =
      ((simpleCFNum a (n + 1) + simpleCFNum a n : ℤ) : ℝ) /
        ((simpleCFDen a (n + 1) + simpleCFDen a n : ℤ) : ℝ) := by
  simp only [cfFractionalLinear, one_mul]
  push_cast
  ring

/-- Auxiliary real-valued version of the mediant-limit map. It agrees with the
full `ENNReal`-valued map on the non-eventually-constant boundary and uses `0`
off that subspace; it is not the book's full closed-half-line map. -/
noncomputable def mediantLimitMap : cantor_space → ℝ :=
  fun b =>
    if h : b ∈ cantorNonEventuallyConstantSet then
      (sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b, h⟩).1
    else 0

/-- Book result: on the non-eventually-constant branches the mediant-limit map is a
bijection onto the positive irrationals. -/
theorem mediantLimitMap_bijOn_nonEventuallyConstant :
    Set.BijOn mediantLimitMap cantorNonEventuallyConstantSet
      {x : ℝ | Irrational x ∧ 0 < x} := by
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo: on the non-eventually-constant branches the value lands in a
    -- positive irrational, by definition of the boundary homeomorphism's codomain.
    intro b hb
    have hval : mediantLimitMap b =
        (sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b, hb⟩).1 := dite_eq_left hb
    rw [Set.mem_ofPred_eq, hval]
    exact (sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b, hb⟩).2
  · -- InjOn: the map is `Subtype.val ∘ homeomorph` on the subtype, a composition
    -- of injective maps.
    intro b₁ hb₁ b₂ hb₂ heq
    have e₁ : mediantLimitMap b₁ =
        (sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b₁, hb₁⟩).1 := dite_eq_left hb₁
    have e₂ : mediantLimitMap b₂ =
        (sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b₂, hb₂⟩).1 := dite_eq_left hb₂
    rw [e₁, e₂] at heq
    have hval : sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b₁, hb₁⟩ =
        sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b₂, hb₂⟩ := Subtype.ext heq
    have hpt : (⟨b₁, hb₁⟩ : cantorNonEventuallyConstantBranches) = ⟨b₂, hb₂⟩ :=
      sternBrocotBoundaryPositiveIrrationalHomeomorph.injective hval
    exact congrArg Subtype.val hpt
  · -- SurjOn: the inverse homeomorphism produces a preimage branch for each
    -- positive irrational.
    intro x hx
    rw [Set.mem_ofPred_eq] at hx
    set xs : {x : ℝ // Irrational x ∧ 0 < x} := ⟨x, hx⟩ with hxs
    set b := sternBrocotBoundaryPositiveIrrationalHomeomorph.symm xs with hb
    have hmem : b.1 ∈ cantorNonEventuallyConstantSet := b.2
    refine ⟨b.1, hmem, ?_⟩
    have e : mediantLimitMap b.1 =
        (sternBrocotBoundaryPositiveIrrationalHomeomorph ⟨b.1, hmem⟩).1 := dite_eq_left hmem
    have hpt : (⟨b.1, hmem⟩ : cantorNonEventuallyConstantBranches) = b := Subtype.ext rfl
    rw [e, hpt, hb, Homeomorph.apply_symm_apply]

/-- Binary digits read as ternary zero/two digits, as in the book's map `h`. -/
def binaryTernaryDigits (x : cantor_space) (n : ℕ) : Fin 3 :=
  if x n then 2 else 0

theorem binaryTernary_prefix_sum_eq {x y : cantor_space} {k : ℕ}
    (h : ∀ i < k, x i = y i) :
    ∑ i ∈ Finset.range k, Real.ofDigitsTerm (binaryTernaryDigits x) i =
      ∑ i ∈ Finset.range k, Real.ofDigitsTerm (binaryTernaryDigits y) i := by
  apply Finset.sum_congr rfl
  intro i hi
  simp [Real.ofDigitsTerm, binaryTernaryDigits, h i (Finset.mem_range.mp hi)]

/-- Fixing the first `k` binary digits changes the ternary value by at most `3⁻ᵏ`. -/
theorem binaryTernary_dist_le_of_agree {x y : cantor_space} {k : ℕ}
    (h : ∀ i < k, x i = y i) :
    dist (Real.ofDigits (binaryTernaryDigits x)) (Real.ofDigits (binaryTernaryDigits y)) ≤
      ((3 : ℝ) ^ k)⁻¹ := by
  rw [Real.dist_eq, Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits x) k,
    Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits y) k, binaryTernary_prefix_sum_eq h, abs_le]
  have hx₀ := Real.ofDigits_nonneg (fun i => binaryTernaryDigits x (i + k))
  have hx₁ := Real.ofDigits_le_one (fun i => binaryTernaryDigits x (i + k))
  have hy₀ := Real.ofDigits_nonneg (fun i => binaryTernaryDigits y (i + k))
  have hy₁ := Real.ofDigits_le_one (fun i => binaryTernaryDigits y (i + k))
  have hp : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
  norm_num only [Nat.cast_ofNat]
  constructor <;> nlinarith

/-- The first differing digit contributes more than the entire possible tail. -/
theorem binaryTernary_first_difference_bound {x y : cantor_space} {k : ℕ}
    (h : ∀ i < k, x i = y i) (hk : x k ≠ y k) :
    ((3 : ℝ) ^ (k + 1))⁻¹ ≤
      dist (Real.ofDigits (binaryTernaryDigits x)) (Real.ofDigits (binaryTernaryDigits y)) := by
  rw [Real.dist_eq, Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits x) (k + 1),
    Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits y) (k + 1), Finset.sum_range_succ,
    Finset.sum_range_succ, binaryTernary_prefix_sum_eq h]
  have hx₀ := Real.ofDigits_nonneg (fun i => binaryTernaryDigits x (i + (k + 1)))
  have hx₁ := Real.ofDigits_le_one (fun i => binaryTernaryDigits x (i + (k + 1)))
  have hy₀ := Real.ofDigits_nonneg (fun i => binaryTernaryDigits y (i + (k + 1)))
  have hy₁ := Real.ofDigits_le_one (fun i => binaryTernaryDigits y (i + (k + 1)))
  have hp : 0 < ((3 : ℝ) ^ (k + 1))⁻¹ := by positivity
  cases hx : x k <;> cases hy : y k <;> simp only [hx, hy] at hk
  all_goals try contradiction
  all_goals
    simp only [Real.ofDigitsTerm, binaryTernaryDigits, hx, hy, Bool.false_eq_true,
      ↓reduceIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero,
      Nat.cast_ofNat, zero_mul, Nat.mod_succ]
    dsimp only [binaryTernaryDigits] at hx₀ hx₁ hy₀ hy₁
    rw [le_abs]
    first | left; nlinarith | right; nlinarith

/-- Injectivity follows from the first differing digit, independently of the
already available Cantor-set homeomorphism. -/
theorem binaryTernary_injective : Function.Injective (fun x : cantor_space =>
    Real.ofDigits (binaryTernaryDigits x)) := by
  intro x y hxy
  dsimp only at hxy
  by_contra hne
  have h : ∃ k, x k ≠ y k := Function.ne_iff.mp hne
  have hk := Nat.find_spec h
  have hbefore : ∀ i < Nat.find h, x i = y i := by
    intro i hi
    by_contra hdiff
    exact Nat.find_min h hi hdiff
  have hbound := binaryTernary_first_difference_bound hbefore hk
  rw [hxy, dist_self] at hbound
  exact (not_le_of_gt (by positivity : 0 < ((3 : ℝ) ^ (Nat.find h + 1))⁻¹)) hbound

end PolishSpaceBook
