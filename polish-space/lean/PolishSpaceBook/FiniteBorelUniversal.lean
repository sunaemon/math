module

public import PolishSpaceBook.BorelStructure
public import PolishSpaceBook.CantorBaireSpace
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-!
# Finite-level universal sets

The book's cylinder codes, paired rows of parameters, and diagonal argument.
The recursive index `n` represents the positive Borel level `n + 1`.
-/

namespace PolishSpaceBook

open Set TopologicalSpace
open scoped Ordinal

/-- At a successor level, all terms in the union may be placed at the immediately
preceding multiplicative level, by monotonicity. -/
theorem borelSigma_succ_iff {X : Type*} [MetricSpace X] {α : Ordinal}
    (hα : 1 ≤ α) {S : Set X} :
    S ∈ borelSigma (α + 1) ↔ ∃ F : ℕ → Set X, (∀ k, F k ∈ borelPi α) ∧ S = ⋃ k, F k := by
  have hlt : α < α + 1 := by rw [← Order.succ_eq_add_one]; exact Order.lt_succ α
  rw [borelSigma, ite_eq_right (not_le.mpr (lt_of_le_of_lt hα hlt))]
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨F, fun k => ?_, rfl⟩
    obtain ⟨⟨β, hβ, hβα⟩, hFk⟩ := hF k
    have hle : β ≤ α := by
      apply Order.lt_succ_iff.mp
      simpa only [Order.succ_eq_add_one] using hβα
    exact borelPi_mono hβ hle hFk
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, fun k => ⟨⟨α, hα, hlt⟩, hF k⟩, rfl⟩

/-- Borel classes on an induced subspace are precisely traces of the ambient
classes. The induction follows the definition, commuting preimages with complements
and countable unions; no closedness assumption is needed. -/
theorem borelSigma_lift_inducing {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsInducing f) (α : Ordinal) {S : Set X}
    (hS : S ∈ borelSigma α) : ∃ T : Set Y, T ∈ borelSigma α ∧ f ⁻¹' T = S := by
  revert S
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro S hS
    by_cases hα : α ≤ 1
    · rw [borelSigma, ite_eq_left hα] at hS
      obtain ⟨T, hT, hTS⟩ := hf.isOpen_iff.mp hS
      exact ⟨T, by rwa [borelSigma, ite_eq_left hα], hTS⟩
    · rw [borelSigma, ite_eq_right hα] at hS
      obtain ⟨F, hF, rfl⟩ := hS
      choose β hβ using hF
      choose T hT hTF using fun k => ih (β k).1 (β k).2.2 (hβ k)
      refine ⟨⋃ k, (T k)ᶜ, ?_, ?_⟩
      · rw [borelSigma, ite_eq_right hα]
        exact ⟨fun k => (T k)ᶜ, fun k => ⟨β k, by simpa using hT k⟩, rfl⟩
      · simp only [preimage_iUnion, preimage_compl, hTF, compl_compl]

/-- The multiplicative trace statement follows by lifting the complement. -/
theorem borelPi_lift_inducing {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsInducing f) (α : Ordinal) {S : Set X}
    (hS : S ∈ borelPi α) : ∃ T : Set Y, T ∈ borelPi α ∧ f ⁻¹' T = S := by
  obtain ⟨T, hT, hTS⟩ := borelSigma_lift_inducing f hf α hS
  refine ⟨Tᶜ, ?_, ?_⟩
  · simpa only [borelPi, mem_ofPred_eq, compl_compl] using hT
  · simp only [preimage_compl, hTS, compl_compl]

namespace FiniteBorelUniversal

variable {A : Type*}

/-- The `k`th row of the parameter, read along paired coordinates. -/
def row (a : ℕ → A) (k : ℕ) : ℕ → A := fun j => a (Nat.pair k j)

/-- Assemble a countable family of parameters into one parameter. -/
def pack (a : ℕ → ℕ → A) : ℕ → A := fun i => a (Nat.unpair i).1 (Nat.unpair i).2

@[simp] theorem row_pack (a : ℕ → ℕ → A) (k : ℕ) : row (pack a) k = a k := by
  funext j
  simp [row, pack]

/-- The base parameter selects cylinders; each successor takes the union of
complementary sections whose parameters are the rows of the new parameter. -/
def universal (σ : ℕ → List A) (off : A) : ℕ → Set ((ℕ → A) × (ℕ → A))
  | 0 => ⋃ k, {a | a k ≠ off} ×ˢ cyl (σ k)
  | n + 1 => ⋃ k, (fun z => (row z.1 k, z.2)) ⁻¹' (universal σ off n)ᶜ

variable [TopologicalSpace A]

theorem continuous_row (k : ℕ) : Continuous (fun a : ℕ → A => row a k) :=
  continuous_pi fun j => continuous_apply (Nat.pair k j)

theorem continuous_row_pair (k : ℕ) :
    Continuous (fun z : (ℕ → A) × (ℕ → A) => (row z.1 k, z.2)) :=
  ((continuous_row k).comp continuous_fst).prodMk continuous_snd

variable [DiscreteTopology A]

theorem universal_zero_open (σ : ℕ → List A) (off : A) : IsOpen (universal σ off 0) := by
  apply isOpen_iUnion
  intro k
  exact ((continuous_apply k : Continuous (fun a : ℕ → A => a k)).isOpen_preimage
    {x : A | x ≠ off} (isOpen_discrete _)).prod (isOpen_cyl _)

theorem universal_mem (σ : ℕ → List A) (off : A) (n : ℕ) :
    universal σ off n ∈ borelSigma (↑n + 1) := by
  let := metrizableSpaceMetric ((ℕ → A) × (ℕ → A))
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_add, borelSigma_one, mem_ofPred_eq] using universal_zero_open σ off
  | succ n ih =>
    rw [Nat.cast_succ, borelSigma_succ_iff (by exact le_add_left (le_refl (1 : Ordinal)))]
    refine ⟨fun k => (fun z => (row z.1 k, z.2)) ⁻¹' (universal σ off n)ᶜ, ?_, rfl⟩
    intro k
    apply borelPi_preimage _ (continuous_row_pair k)
    simpa only [borelPi, mem_ofPred_eq, compl_compl] using ih

theorem section_mem (σ : ℕ → List A) (off : A) (n : ℕ) (a : ℕ → A) :
    {p | (a, p) ∈ universal σ off n} ∈ borelSigma (↑n + 1) :=
  borelSigma_preimage (fun p => (a, p)) (continuous_const.prodMk continuous_id) _ (universal_mem σ off n)

/-- Every open set is selected by the characteristic parameter of the cylinders
contained in it. This also represents the empty set, by the constant off-code. -/
theorem universal_zero_surjective (σ : ℕ → List A) (hσ : Function.Surjective σ)
    (off on : A) (hne : on ≠ off) {S : Set (ℕ → A)} (hS : IsOpen S) :
    ∃ a, S = {p | (a, p) ∈ universal σ off 0} := by
  classical
  refine ⟨fun k => if cyl (σ k) ⊆ S then on else off, ?_⟩
  ext p
  simp only [universal, mem_ofPred_eq, mem_iUnion, mem_prod]
  constructor
  · intro hp
    obtain ⟨s, hps, hsS⟩ := exists_cyl_subset_of_mem_open hp hS
    obtain ⟨k, rfl⟩ := hσ s
    exact ⟨k, by simp [hsS, hne], hps⟩
  · rintro ⟨k, hk, hpk⟩
    by_cases hs : cyl (σ k) ⊆ S
    · exact hs hpk
    · simp [hs] at hk

/-- Recursively choose the complementary sections and pack their parameters by
pairing. No computable choice of parameters is asserted. -/
theorem universal_surjective (σ : ℕ → List A) (hσ : Function.Surjective σ)
    (off on : A) (hne : on ≠ off) (n : ℕ) {S : Set (ℕ → A)}
    (hS : S ∈ borelSigma (↑n + 1)) :
    ∃ a, S = {p | (a, p) ∈ universal σ off n} := by
  let := metrizableSpaceMetric (ℕ → A)
  induction n generalizing S with
  | zero =>
    apply universal_zero_surjective σ hσ off on hne
    simpa only [Nat.cast_zero, zero_add, borelSigma_one, mem_ofPred_eq] using hS
  | succ n ih =>
    rw [Nat.cast_succ, borelSigma_succ_iff (by exact le_add_left (le_refl (1 : Ordinal)))] at hS
    obtain ⟨F, hF, rfl⟩ := hS
    choose a ha using fun k => ih (S := (F k)ᶜ) (hF k)
    refine ⟨pack a, ?_⟩
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, universal, mem_preimage, mem_compl_iff, row_pack]
    apply exists_congr
    intro k
    have hk := Set.ext_iff.mp (ha k) p
    simp only [mem_compl_iff, mem_ofPred_eq] at hk
    simpa only [not_not] using (not_congr hk)

/-- Diagonal complementation gives a multiplicative set outside the additive
class at exactly the same positive level. -/
theorem diagonal_separates (σ : ℕ → List A) (hσ : Function.Surjective σ)
    (off on : A) (hne : on ≠ off) (n : ℕ) :
    ∃ D : Set (ℕ → A), D ∈ borelPi (↑n + 1) ∧ D ∉ borelSigma (↑n + 1) := by
  let D : Set (ℕ → A) := {a | (a, a) ∉ universal σ off n}
  refine ⟨D, ?_, ?_⟩
  · change (fun a : ℕ → A => (a, a)) ⁻¹' (universal σ off n)ᶜ ∈ borelPi (↑n + 1)
    apply borelPi_preimage _ (continuous_id.prodMk continuous_id)
    simpa only [borelPi, mem_ofPred_eq, compl_compl] using universal_mem σ off n
  · intro hD
    obtain ⟨a, ha⟩ := universal_surjective σ hσ off on hne n hD
    have h := Set.ext_iff.mp ha a
    change ((a, a) ∉ universal σ off n) ↔ (a, a) ∈ universal σ off n at h
    exact not_iff_self h

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: theorem
  title: Finite-level universal sets
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $n=1$, let $\sigma:\omega\to\finseq{\omega}$ enumerate the finite words and put
    $$
    U_1:=\{(a,p):\exists k\;(a(k)\ne0\text{ and }\sigma(k)\prefixOf p)\}.
    $$
    This is a union of open rectangles, hence open. For an open set $S$, choose $a(k)=1$ when
    $\cyl{\sigma(k)}\IncludedIn S$ and $a(k)=0$ otherwise. Since the cylinders form a basis,
    $S=(U_1)_a$; in particular, the constant zero parameter represents the empty set.
    Fix a bijection $q:\omega\times\omega\to\omega$ and decode each parameter by
    $$a_k(j):=a(q(k,j)).$$
    Every sequence of parameters can be packed in this way: given $\Sequence{b_k}{k\in\omega}$, set $a(q(k,j)):=b_k(j)$.
    For each $k$, the map $a\mapsto a_k$ is continuous because each output coordinate reads one input coordinate.
    Suppose $U_n$ has been constructed, and define
    $$
    (a,p)\in U_{n+1}\quad\Longleftrightarrow\quad
    \exists k\;(a_k,p)\notin U_n.
    $$
    For each $k$, the map $(a,p)\mapsto(a_k,p)$ is continuous. Thus $U_{n+1}$ is a countable union of
    $\bPi^0_n$ sets and belongs to $\bSigma^0_{n+1}$. Conversely, monotonicity of the hierarchy lets us write any
    $S\in\bSigma^0_{n+1}$ as $S=\bigcup_k F_k$ with every $F_k\in\bPi^0_n$, even when its original union uses
    lower levels. Choose $b_k$ so that $\SetDifference{\BaireSpace}{F_k}=(U_n)_{b_k}$, and pack these parameters into $a$.
    Then $S=(U_{n+1})_a$. Every section has the claimed Borel complexity, since $p\mapsto(a,p)$ is continuous.
    On $\CantorSpace$, enumerate finite binary words and use the same formulas. The base parameters are binary,
    and pairing coordinates also packs countably many binary parameters into a binary parameter.
    \end{proof}
-/
/-- Both sequence spaces admit the constructed universal sets: countability is
used only to enumerate finite words, and two symbols encode a characteristic function. -/
theorem exists_universal [Countable A] [Nontrivial A] (n : ℕ) :
    ∃ U : Set ((ℕ → A) × (ℕ → A)), U ∈ borelSigma (↑n + 1) ∧
      ∀ S : Set (ℕ → A), S ∈ borelSigma (↑n + 1) ↔ ∃ a, S = {p | (a, p) ∈ U} := by
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (List A)
  obtain ⟨off, on, hne⟩ := exists_pair_ne A
  refine ⟨universal σ off n, universal_mem σ off n, fun S => ⟨?_, ?_⟩⟩
  · exact universal_surjective σ hσ off on hne.symm n
  · rintro ⟨a, rfl⟩
    exact section_mem σ off n a

theorem exists_diagonal [Countable A] [Nontrivial A] (n : ℕ) :
    ∃ D : Set (ℕ → A), D ∈ borelPi (↑n + 1) ∧ D ∉ borelSigma (↑n + 1) := by
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (List A)
  obtain ⟨off, on, hne⟩ := exists_pair_ne A
  exact diagonal_separates σ hσ off on hne.symm n

/-- Complementing the diagonal witness separates the classes in the other direction. -/
theorem exists_additive_diagonal [Countable A] [Nontrivial A] (n : ℕ) :
    ∃ S : Set (ℕ → A), S ∈ borelSigma (↑n + 1) ∧ S ∉ borelPi (↑n + 1) := by
  obtain ⟨D, hD, hDn⟩ := exists_diagonal (A := A) n
  refine ⟨Dᶜ, hD, ?_⟩
  simpa only [borelPi, mem_ofPred_eq, compl_compl] using hDn

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: statement
  kind: theorem
  title: Finite Borel strictness on sequence spaces
-/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    On $\BaireSpace$, let $U_n$ be the preceding universal set and define
    $$D_n:=\{a\in\BaireSpace:(a,a)\notin U_n\}.$$
    The diagonal map $a\mapsto(a,a)$ is continuous, so $D_n\in\bPi^0_n$. If it were also in $\bSigma^0_n$,
    universality would give $D_n=(U_n)_a$ for some $a$, whence
    $$a\in D_n\quad\Longleftrightarrow\quad(a,a)\in U_n\quad\Longleftrightarrow\quad a\notin D_n,$$
    a contradiction. The same argument on $\CantorSpace$ gives a $\bPi^0_n$ set outside $\bSigma^0_n$ there as well.
    Taking complements gives a $\bSigma^0_n$ set outside $\bPi^0_n$ in each space.
    \end{proof}
-/
/-- The two finite pointclasses are distinct on each countable nontrivial
alphabet, including the natural and binary alphabets of the book. -/
theorem pointclasses_ne [Countable A] [Nontrivial A] (n : ℕ) (hn : 1 ≤ n) :
    borelSigma (Y := ℕ → A) (n : Ordinal) ≠ borelPi (n : Ordinal) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨D, hD, hDn⟩ := exists_diagonal (A := A) m
  rw [Nat.cast_succ]
  intro h
  exact hDn (h.symm ▸ hD)

end FiniteBorelUniversal

/-- Finite Borel strictness on Baire space, with the explicit anti-diagonal witness. -/
theorem finite_borel_strictness_baire (n : ℕ) :
    ∃ D : Set baire_space, D ∈ borelPi (↑n + 1) ∧ D ∉ borelSigma (↑n + 1) :=
  FiniteBorelUniversal.exists_diagonal n

/-- Finite Borel strictness on Cantor space, using binary parameters throughout. -/
theorem finite_borel_strictness_cantor (n : ℕ) :
    ∃ D : Set cantor_space, D ∈ borelPi (↑n + 1) ∧ D ∉ borelSigma (↑n + 1) :=
  FiniteBorelUniversal.exists_diagonal n

end PolishSpaceBook
