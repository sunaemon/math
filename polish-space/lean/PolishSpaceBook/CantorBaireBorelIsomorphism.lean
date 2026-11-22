module

public import PolishSpaceBook.ConcreteCantorBaireModels
public import PolishSpaceBook.CountableBorelPatch
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

/-! # The Cantor--Baire Borel isomorphism by countable patching

The gap homeomorphism matches infinite subsets of the naturals with Baire
space. Eventually zero sequences reserve a countably infinite target part;
finite subsets and its inverse gap image are patched by a countable bijection.
-/
namespace PolishSpaceBook.CantorBaireBorel
open Set TopologicalSpace

/-- The reserved Baire sequences are eventually zero. -/
def R : Set baire_space := {p | ∃ N : ℕ, ∀ n ≥ N, p n = 0}

def zeroPad (s : List ℕ) (n : ℕ) : ℕ := if h : n < s.length then s.get ⟨n, h⟩ else 0

theorem zeroPad_mem (s : List ℕ) : zeroPad s ∈ R := by
  refine ⟨s.length, fun n hn => ?_⟩
  simp [zeroPad, not_lt.mpr hn]

theorem R_eq_range : R = range zeroPad := by
  ext p
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨List.ofFn (fun i : Fin N => p i), ?_⟩
    funext n
    by_cases hn : n < N
    · simp [zeroPad, hn]
    · simp [zeroPad, hn, hN n (not_lt.mp hn)]
  · rintro ⟨s, rfl⟩
    exact zeroPad_mem s

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Each element of $R$ is a finite word followed by zeros, so $R$ is countable.
    The sequences $(k,0,0,\ldots)$ for $k\in\omega$ are distinct elements, so it is countably infinite.
-/
theorem R_countable : R.Countable := R_eq_range ▸ countable_range zeroPad

theorem R_infinite : R.Infinite := by
  let f : ℕ → baire_space := fun m n => if n = 0 then m else 0
  have hinj : Function.Injective f := by
    intro m k h
    simpa [f] using congrFun h 0
  apply (infinite_range_of_injective hinj).mono
  rintro _ ⟨m, rfl⟩
  refine ⟨1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  simp [f, hn0]

noncomputable local instance : MeasurableSpace powersetOmega := borel powersetOmega
local instance : BorelSpace powersetOmega := ⟨rfl⟩
local instance : T2Space powersetOmega := powersetOmegaHomeomorphCantorSpace.symm.t2Space

/-- The large-piece map is the previously proved gap homeomorphism. -/
noncomputable def gap : infiniteSubsetsOmega ≃ᵐ baire_space :=
  infiniteSubsetsOmegaBaireHomeomorph.toMeasurableEquiv

def FinitePart : Set powersetOmega := {A | (A : Set ℕ).Finite}

theorem finitePart_compl : FinitePart = infiniteSubsetsOmegaSetᶜ := by
  ext A
  simp [FinitePart, infiniteSubsetsOmegaSet]

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    is countable, since each finite subset is determined by its increasing finite enumeration.
-/
theorem finitePart_countable : FinitePart.Countable := Countable.ofPred_finite

theorem infinitePart_compl_countable : infiniteSubsetsOmegaSetᶜ.Countable :=
  finitePart_compl ▸ finitePart_countable

def E : Set powersetOmega := CountableBorelPatch.reserved gap R

def L : Set powersetOmega := CountableBorelPatch.leftover gap R

theorem mem_E_iff (A : infiniteSubsetsOmega) : A.val ∈ E ↔ gap A ∈ R := by
  constructor
  · rintro ⟨y, hy, hAy⟩
    have h : gap.symm y = A := Subtype.ext hAy
    simpa [← h] using hy
  · intro hA
    exact ⟨gap A, hA, by simp⟩

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Let $E:=\mathrm{gap}^{-1}(R)\IncludedIn\infiniteSubsets{\omega}$, also countably infinite.
-/
theorem E_countable : E.Countable := R_countable.image _

theorem E_infinite : E.Infinite := by
  have hinj : Function.Injective (fun y => (gap.symm y).val) :=
    Subtype.val_injective.comp gap.symm.injective
  exact R_infinite.image hinj.injOn

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Under the identification $\PowerSet{\omega}\cong\CantorSpace$, the \termuse{gap map} from
    §{sec:infinite-subsets-omega} identifies the infinite-subset part of Cantor space with Baire space:
    $$
    \infiniteSubsets{\omega}
    \;\xrightarrow{\;\mathrm{gap}\;}\;
    \BaireSpace.
    $$
    The complement
    $$
    \mathrm{Fin}:=\{A\IncludedIn\omega:|A|<\omega\}
    $$
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Thus Cantor space splits into a large Baire-like $\Gdelta$ piece plus a countable leftover:
    $$
    \CantorSpace
    =
    \infiniteSubsets{\omega} \internalDisjointUnion \mathrm{Fin}.
    $$
-/
theorem L_eq_union : L = FinitePart ∪ E := by
  rw [finitePart_compl]
  rfl

theorem finitePart_disjoint_E : Disjoint FinitePart E := by
  rw [finitePart_compl]
  exact disjoint_compl_left.mono_right (CountableBorelPatch.reserved_subset gap R)

theorem L_countable : L.Countable :=
  CountableBorelPatch.leftover_countable gap R infinitePart_compl_countable R_countable

theorem L_infinite : L.Infinite := CountableBorelPatch.leftover_infinite gap R R_infinite

/-- Away from the leftovers, the same gap homeomorphism restricts to the large pieces. -/
noncomputable def largeHomeomorph : (Lᶜ : Set powersetOmega) ≃ₜ (Rᶜ : Set baire_space) where
  toEquiv := (CountableBorelPatch.largeEquiv gap R).toEquiv
  continuous_toFun := (infiniteSubsetsOmegaBaireHomeomorph.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    (infiniteSubsetsOmegaBaireHomeomorph.symm.continuous.comp continuous_subtype_val)).subtype_mk _

/-- Choose the bijection of countable leftovers used in the displayed definition. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Choose a bijection
    $$
    e:\mathrm{Fin}\internalDisjointUnion E\;\to\;R.
    $$
-/
noncomputable def e : L ≃ R :=
  CountableBorelPatch.leftoverEquiv gap R infinitePart_compl_countable R_countable R_infinite

/-- The Borel map on subsets of the naturals, before characteristic-function identification. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Define
    $$
    \Phi(A)=
    \begin{cases}
    e(A), & A\in \mathrm{Fin}\internalDisjointUnion E,\\
    \mathrm{gap}(A), & A\in \SetDifference{\infiniteSubsets{\omega}}{E}.
    \end{cases}
    $$
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    To turn this into an actual Borel bijection $\CantorSpace\cong_B\BaireSpace$, reserve a countably infinite Borel subset
    of Baire space, for instance
    $$
    R:=\{p\in\BaireSpace:\exists N\in\omega\;\forall n\ge N\;p(n)=0\}.
    $$
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    The formulas are inverse on each pair of pieces. Both maps are Borel: on the countable pieces every map is Borel,
    and on the remaining pieces they are restrictions of the gap homeomorphism and its inverse.
-/
noncomputable def phi : powersetOmega ≃ᵐ baire_space :=
  CountableBorelPatch.patch gap R infinitePart_compl_countable R_countable e

theorem phi_small {A : powersetOmega} (hA : A ∈ L) : phi A = (e ⟨A, hA⟩).val :=
  CountableBorelPatch.patch_small gap R infinitePart_compl_countable R_countable e hA

theorem phi_large {A : powersetOmega} (hA : A ∉ L) :
    phi A = infiniteSubsetsOmegaGapMap ⟨A, (CountableBorelPatch.outside gap R hA).choose⟩ :=
  CountableBorelPatch.patch_large gap R infinitePart_compl_countable R_countable e hA

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Then $\Phi:\CantorSpace\to\BaireSpace$ is bijective, with inverse
    $$
    \Phi^{-1}(p)=
    \begin{cases}
    e^{-1}(p), & p\in R,\\
    \mathrm{gap}^{-1}(p), & p\notin R.
    \end{cases}
    $$
-/
theorem phi_symm_small {p : baire_space} (hp : p ∈ R) : phi.symm p = (e.symm ⟨p, hp⟩).val :=
  CountableBorelPatch.patch_symm_small gap R infinitePart_compl_countable R_countable e hp

theorem phi_symm_large {p : baire_space} (hp : p ∉ R) : phi.symm p = (gapsToInfiniteSubset p).val :=
  CountableBorelPatch.patch_symm_large gap R infinitePart_compl_countable R_countable e hp

theorem phi_preimage_R : phi ⁻¹' R = L := by
  ext A
  by_cases hA : A ∈ L
  · have hm : phi A ∈ R := by
      rw [phi_small hA]
      exact (e ⟨A, hA⟩).property
    simp only [mem_preimage, hm, hA]
  · have hn : phi A ∉ R := by
      rw [phi_large hA]
      exact (CountableBorelPatch.outside gap R hA).choose_spec
    simp only [mem_preimage, hn, hA]

/-- The actual Cantor--Baire measurable equivalence, built from the gap map and `e`. -/
noncomputable def cantorBaireEquiv : cantor_space ≃ᵐ baire_space :=
  powersetOmegaHomeomorphCantorSpace.symm.toMeasurableEquiv.trans phi

/-- A countable set is the countable union of its closed singletons. -/
theorem countable_isFsigma {Z : Type*} [TopologicalSpace Z] [T1Space Z]
    {A : Set Z} (hA : A.Countable) : IsFsigma A := by
  refine ⟨(fun z : Z => ({z} : Set Z)) '' A, hA.image _, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact isClosed_singleton
  · ext z
    simp

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    The countable leftover pieces are $\mathrm{Fin}\internalDisjointUnion E$, an $\Fsigma$ ($\bSigma^0_2$) subset of
        $\CantorSpace$, and $R$, an $\Fsigma$ ($\bSigma^0_2$) subset of $\BaireSpace$.
-/
theorem small_pieces_isFsigma : IsFsigma L ∧ IsFsigma R :=
  ⟨countable_isFsigma L_countable, countable_isFsigma R_countable⟩

theorem large_piece_eq : Lᶜ = infiniteSubsetsOmegaSet \ E := by
  ext A
  simp [L, CountableBorelPatch.leftover, E, sdiff_eq]

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    The large pieces are $\SetDifference{\infiniteSubsets{\omega}}{E}$ and
        $\SetDifference{\BaireSpace}{R}$. Both are $\Gdelta$ ($\bPi^0_2$): the original large pieces are $\Gdelta$, while
        $E$ and $R$ are countable and hence $\Fsigma$.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Thus this particular isomorphism matches the large $\Gdelta$ pieces and the countable $\Fsigma$ pieces. It should not be
    read as preserving Borel rank for arbitrary sets.
-/
theorem large_pieces_isGdelta : IsGδ (infiniteSubsetsOmegaSet \ E) ∧ IsGδ Rᶜ := by
  rw [← large_piece_eq]
  exact ⟨small_pieces_isFsigma.1.isGdelta_compl, small_pieces_isFsigma.2.isGdelta_compl⟩

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    For every $B\IncludedIn\BaireSpace$, Borelness is preserved in both directions:
    $$
    B\in\mathcal B(\BaireSpace)
    \quad\Longleftrightarrow\quad
    \Phi^{-1}(B)\in\mathcal B(\CantorSpace),
    $$
    and similarly in the other direction.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    The first term is a subset of the countable set $\mathrm{Fin}\internalDisjointUnion E$, hence Borel in
    $\CantorSpace$. The second term is Borel because $\SetDifference{B}{R}$ is Borel and the gap map is continuous on
    $\infiniteSubsets{\omega}$, with
    $\infiniteSubsets{\omega}$ itself Borel in $\CantorSpace$.
-/
theorem phi_preimage_measurable_iff (B : Set baire_space) :
    MeasurableSet (phi ⁻¹' B) ↔ MeasurableSet B := phi.measurableSet_preimage

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    The first term is countable, hence Borel in $\BaireSpace$. The second term is Borel because
    $A\cap(\SetDifference{\infiniteSubsets{\omega}}{E})$ is Borel in the Polish space $\infiniteSubsets{\omega}$, and the
    gap map is
    a homeomorphism $\infiniteSubsets{\omega}\cong\BaireSpace$. Thus $\Phi$ is an isomorphism of Borel $\sigma$-algebras.
-/
theorem phi_image_measurable_iff (A : Set powersetOmega) :
    MeasurableSet (phi '' A) ↔ MeasurableSet A := phi.measurableSet_image

end PolishSpaceBook.CantorBaireBorel
