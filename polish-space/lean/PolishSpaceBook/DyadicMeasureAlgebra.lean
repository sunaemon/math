module

public import PolishSpaceBook.MeasureAlgebraMetric
public import PolishSpaceBook.MaharamStandardBorel
public import PolishSpaceBook.RandomGenericReals
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Order.Atoms

@[expose] public section

/-!
# The finite dyadic subalgebras of the probability algebra

Prefix projections identify each level with the powerset of the finite set of
binary words. Finite-coordinate approximation makes their increasing union dense.
-/

noncomputable section
namespace PolishSpaceBook.DyadicMeasureAlgebra
open Set Filter Function MeasureTheory MeasurableSpace
open scoped ENNReal symmDiff

abbrev Word (n : ℕ) := Fin n → Bool

def prefixMap (n : ℕ) (x : cantor_space) : Word n := fun i => x i

lemma prefixMap_measurable (n : ℕ) : Measurable (prefixMap n) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply i.val

def levelEvent {n : ℕ} (S : Set (Word n)) : Set cantor_space := prefixMap n ⁻¹' S

lemma levelEvent_measurable {n : ℕ} (S : Set (Word n)) : MeasurableSet (levelEvent S) :=
  (prefixMap_measurable n) (Set.toFinite S).measurableSet

def cell {n : ℕ} (s : Word n) : Set cantor_space := levelEvent {s}

lemma cell_eq_cyl {n : ℕ} (s : Word n) : cell s = cyl (List.ofFn s) := by
  ext x
  constructor
  · intro hx i hi
    have h := congrFun hx ⟨i, by simpa using hi⟩
    simpa [prefixMap] using h
  · intro hx
    change prefixMap n x = s
    funext i
    simpa [prefixMap] using hx i.val (by simp)

lemma cell_mass {n : ℕ} (s : Word n) : fairCoinProduct (cell s) = (1 / 2 : ℝ≥0∞) ^ n := by
  rw [cell_eq_cyl, fairCoinProduct_cyl, List.length_ofFn]

lemma cell_mass_pos {n : ℕ} (s : Word n) : 0 < fairCoinProduct (cell s) := by
  rw [cell_mass]
  exact ENNReal.pow_pos (by norm_num) n

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The map $S\mapsto[\pi_n^{-1}(S)]$ preserves Boolean operations. It is injective: if two sets of words differ,
    the symmetric difference of their inverse images contains a cylinder of measure $2^{-n}>0$.
    Thus $\mathcal A_n$ is isomorphic to the powerset algebra of the $2^n$ binary words of length $n$.
    Its atoms correspond precisely to the singletons, giving the stated atom count and measures.
-/
/-- The quotient class of a union of cells at one level. -/
def levelClass {n : ℕ} (S : Set (Word n)) : MeasureAlgebra fairCoinProduct :=
  MeasureAlgebra.mk (levelEvent S) (levelEvent_measurable S)

lemma levelClass_le_iff {n : ℕ} (S T : Set (Word n)) : levelClass S ≤ levelClass T ↔ S ⊆ T := by
  constructor
  · intro h s hs
    by_contra ht
    have hz : fairCoinProduct (levelEvent S \ levelEvent T) = 0 := ae_le_set.mp h
    have hsub : cell s ⊆ levelEvent S \ levelEvent T := by
      intro x hx
      change prefixMap n x = s at hx
      change prefixMap n x ∈ S ∧ prefixMap n x ∉ T
      rw [hx]
      exact ⟨hs, ht⟩
    exact (cell_mass_pos s).ne' (measure_mono_null hsub hz)
  · intro h
    exact Eventually.of_forall fun _ hx => h hx

lemma levelClass_injective (n : ℕ) : Injective (@levelClass n) := by
  intro S T h
  exact le_antisymm ((levelClass_le_iff S T).mp h.le) ((levelClass_le_iff T S).mp h.ge)

/-- The finite Boolean subalgebra of all unions of length-`n` cylinders. -/
def level (n : ℕ) : BooleanSubalgebra (MeasureAlgebra fairCoinProduct) where
  carrier := range (@levelClass n)
  supClosed' := by
    rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
    exact ⟨S ∪ T, rfl⟩
  infClosed' := by
    rintro _ ⟨S, rfl⟩ _ ⟨T, rfl⟩
    exact ⟨S ∩ T, rfl⟩
  compl_mem' := by
    rintro _ ⟨S, rfl⟩
    exact ⟨Sᶜ, rfl⟩
  bot_mem' := ⟨∅, rfl⟩

lemma level_finite (n : ℕ) : (level n : Set (MeasureAlgebra fairCoinProduct)).Finite :=
  finite_range (@levelClass n)

/-- Identifying a union with the set of cells it contains is a Boolean isomorphism. -/
def levelEquiv (n : ℕ) : Set (Word n) ≃o level n where
  toEquiv := Equiv.ofBijective (fun S => ⟨levelClass S, mem_range_self S⟩)
    ⟨fun S T h => levelClass_injective n (congrArg Subtype.val h), by
      rintro ⟨a, S, rfl⟩
      exact ⟨S, rfl⟩⟩
  map_rel_iff' := by
    intro S T
    exact levelClass_le_iff S T

/-- The atoms at a finite level are precisely its individual cylinder classes. -/
lemma level_isAtom_iff {n : ℕ} (a : level n) :
    IsAtom a ↔ ∃ s : Word n, a = levelEquiv n {s} := by
  rw [← (levelEquiv n).apply_symm_apply a, OrderIso.isAtom_iff, Set.isAtom_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, congrArg (levelEquiv n) hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (levelEquiv n).injective hs⟩

lemma level_le_succ (n : ℕ) : level n ≤ level (n + 1) := by
  rintro _ ⟨S, rfl⟩
  exact ⟨(fun t : Word (n + 1) => fun i : Fin n => t i.castSucc) ⁻¹' S, rfl⟩

lemma level_monotone : Monotone level := monotone_nat_of_le_succ level_le_succ

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For density, let $A$ be Borel and let $\varepsilon>0$. The finite-coordinate events form a generating algebra,
    so the \termuseas{approximation by a generating algebra}{generating-algebra approximation lemma} gives an event $C$
    depending on a finite coordinate set $J$ such that $\lambda(\SymmetricDifference{A}{C})<\varepsilon$.
    Choose $n$ larger than every member of $J$. Then $C=\pi_n^{-1}(S)$ for some $S\IncludedIn\funcspace{n}{2}$, since
    its membership is decided by the first $n$ bits. Therefore $[C]\in\mathcal A_n$ and
    $$\MeasureAlgDistance{\lambda}{[A]}{[C]}<\varepsilon,$$
    which proves density.
-/
/-- Replace an arbitrary finite coordinate set by an initial segment containing it. -/
lemma finite_prefix_approximation {A : Set cantor_space} (hA : MeasurableSet A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (S : Set (Word n)), fairCoinProduct (A ∆ levelEvent S) < ε := by
  obtain ⟨J, T, _, hT⟩ := finite_coordinate_approximation fairCoinProduct hA hε
  let n := J.sup id + 1
  let r : Word n → (J → Bool) := fun s j => s ⟨j, Nat.lt_succ_of_le (Finset.le_sup (f := id) j.2)⟩
  refine ⟨n, r ⁻¹' T, ?_⟩
  exact hT

/-- A countable family of finite Boolean algebras supplies the whole probability algebra densely. -/
lemma levels_countable : (⋃ n, (level n : Set (MeasureAlgebra fairCoinProduct))).Countable :=
  countable_iUnion (fun n => (level_finite n).countable)

lemma levels_dense : Dense (⋃ n, (level n : Set (MeasureAlgebra fairCoinProduct))) := by
  rw [EMetric.dense_iff]
  intro a ε hε
  induction a using Quotient.inductionOn with
  | h A =>
    obtain ⟨n, S, hS⟩ := finite_prefix_approximation A.property hε
    refine ⟨levelClass S, ?_, mem_iUnion.mpr ⟨n, mem_range_self S⟩⟩
    change fairCoinProduct (levelEvent S ∆ (A : Set cantor_space)) < ε
    rw [symmDiff_comm]
    exact hS

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Appending the next bit gives the disjoint partition
    $$\cyl{s}=\cyl{s\concat0}\cup\cyl{s\concat1},\qquad
    \lambda(\cyl{s\concat b})=\tfrac12\lambda(\cyl{s})\quad(b\in2).$$
    Consequently $\mathcal A_n\IncludedIn\mathcal A_{n+1}$. Each level is finite, so
    $\bigcup_n\mathcal A_n$ is countable.
-/
/-- Appending one bit fixes exactly the next coordinate. -/
lemma mem_child_cell {n : ℕ} (s : Word n) (b : Bool) (x : cantor_space) :
    x ∈ cell (Fin.snoc s b) ↔ x ∈ cell s ∧ x n = b := by
  change prefixMap (n + 1) x = Fin.snoc s b ↔ prefixMap n x = s ∧ x n = b
  constructor
  · intro h
    constructor
    · funext i
      simpa [prefixMap] using congrFun h i.castSucc
    · simpa [prefixMap] using congrFun h (Fin.last n)
  · rintro ⟨hp, hb⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [prefixMap] using hb
    · simpa [prefixMap] using congrFun hp j

lemma cell_split {n : ℕ} (s : Word n) : cell s = cell (Fin.snoc s false) ∪ cell (Fin.snoc s true) := by
  ext x
  simp only [mem_union, mem_child_cell]
  cases x n <;> simp

lemma cell_children_disjoint {n : ℕ} (s : Word n) :
    Disjoint (cell (Fin.snoc s false)) (cell (Fin.snoc s true)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hf := (mem_child_cell s false x).mp hx
  have ht := (mem_child_cell s true x).mp hy
  exact Bool.false_ne_true (hf.2.symm.trans ht.2)

lemma child_cell_mass {n : ℕ} (s : Word n) (b : Bool) :
    fairCoinProduct (cell (Fin.snoc s b)) = fairCoinProduct (cell s) / 2 := by
  simp only [cell_mass, pow_succ, div_eq_mul_inv, one_mul]

lemma word_card (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by simp [Word]

lemma level_atom_count (n : ℕ) : Nat.card {a : level n // IsAtom a} = 2 ^ n := by
  let f : Word n → {a : level n // IsAtom a} := fun s =>
    ⟨levelEquiv n {s}, ((levelEquiv n).isAtom_iff {s}).mpr (Set.isAtom_singleton s)⟩
  have hf : Bijective f := by
    constructor
    · intro s t h
      have hst := (levelEquiv n).injective (congrArg Subtype.val h)
      simpa only [singleton_eq_singleton_iff] using hst
    · rintro ⟨a, ha⟩
      obtain ⟨s, hs⟩ := (level_isAtom_iff a).mp ha
      exact ⟨s, Subtype.ext hs.symm⟩
  calc
    Nat.card {a : level n // IsAtom a} = Nat.card (Word n) :=
      Nat.card_congr (Equiv.ofBijective f hf).symm
    _ = 2 ^ n := by simp [Nat.card_eq_fintype_card]

/-- Each cylinder class splits into its two disjoint child classes. -/
lemma levelClass_singleton_split {n : ℕ} (s : Word n) :
    levelClass {s} = levelClass {Fin.snoc s false} ⊔ levelClass {Fin.snoc s true} := by
  apply Quotient.sound
  exact EventuallyEq.of_eq (cell_split s)

lemma levelClass_children_disjoint {n : ℕ} (s : Word n) :
    Disjoint (levelClass {Fin.snoc s false}) (levelClass {Fin.snoc s true}) := by
  rw [disjoint_iff]
  change MeasureAlgebra.mk (cell (Fin.snoc s false) ∩ cell (Fin.snoc s true)) _ = ⊥
  apply (MeasureAlgebra.mk_eq_bot _ _).mpr
  rw [Set.disjoint_iff_inter_eq_empty.mp (cell_children_disjoint s), measure_empty]

variable {X : Type*} [MeasurableSpace X]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Transport each $\mathcal A_n$ by $\Phi$. The finite Boolean structure, atom counts, atom measures, and equal
    splitting are preserved. The union remains countable, and the isometry makes it dense.
-/
/-- Transport the fair-coin algebra to an arbitrary nonatomic standard probability space. -/
def transport (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ] [StandardBorelSpace X] :
    MeasureAlgebra fairCoinProduct ≃o MeasureAlgebra μ := by
  letI : PolishSpace cantor_space := cantor_space_polish
  exact MeasureAlgebra.ofAEEquiv (MaharamStandardBorel.between fairCoinProduct μ)

variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ] [StandardBorelSpace X]

lemma transport_isometry : Isometry (transport μ) := by
  let : PolishSpace cantor_space := cantor_space_polish
  exact MeasureAlgebra.ofAEEquiv_isometry (MaharamStandardBorel.between fairCoinProduct μ)

lemma transport_mass (a : MeasureAlgebra fairCoinProduct) :
    MeasureAlgebra.mass (transport μ a) = MeasureAlgebra.mass a := by
  let : PolishSpace cantor_space := cantor_space_polish
  exact MeasureAlgebra.ofAEEquiv_mass (MaharamStandardBorel.between fairCoinProduct μ) a

/-- Each transported level is a finite Boolean subalgebra. -/
def transportedLevel (n : ℕ) : BooleanSubalgebra (MeasureAlgebra μ) :=
  (level n).map (transport μ)

lemma transportedLevel_finite (n : ℕ) : (transportedLevel μ n : Set (MeasureAlgebra μ)).Finite :=
  (level_finite n).image _

lemma transportedLevel_monotone : Monotone (transportedLevel μ) := by
  intro n m h
  exact Set.image_mono (level_monotone h)

lemma transportedLevels_countable : (⋃ n, (transportedLevel μ n : Set (MeasureAlgebra μ))).Countable :=
  countable_iUnion (fun n => (transportedLevel_finite μ n).countable)

lemma transportedLevels_dense : Dense (⋃ n, (transportedLevel μ n : Set (MeasureAlgebra μ))) := by
  change Dense (⋃ n, (transport μ) '' (level n : Set (MeasureAlgebra fairCoinProduct)))
  rw [← image_iUnion]
  exact (transport μ).surjective.denseRange.dense_image (transport_isometry μ).continuous levels_dense

/-- The order isomorphism restricts to an isomorphism at every finite level. -/
def transportedLevelEquiv (n : ℕ) : level n ≃o transportedLevel μ n where
  toEquiv := Equiv.ofBijective
    (fun a => ⟨transport μ a, mem_image_of_mem _ a.2⟩)
    ⟨fun a b h => Subtype.ext ((transport μ).injective (congrArg Subtype.val h)), by
      rintro ⟨a, b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩⟩
  map_rel_iff' := by
    intro a b
    exact (transport μ).le_iff_le

/-- The same binary-word labels describe the atoms after transport. -/
def transportedWordEquiv (n : ℕ) : Set (Word n) ≃o transportedLevel μ n :=
  (levelEquiv n).trans (transportedLevelEquiv μ n)

lemma transportedLevel_isAtom_iff {n : ℕ} (a : transportedLevel μ n) :
    IsAtom a ↔ ∃ s : Word n, a = transportedWordEquiv μ n {s} := by
  rw [← (transportedWordEquiv μ n).apply_symm_apply a, OrderIso.isAtom_iff, Set.isAtom_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, congrArg (transportedWordEquiv μ n) hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (transportedWordEquiv μ n).injective hs⟩

lemma transported_atom_count (n : ℕ) : Nat.card {a : transportedLevel μ n // IsAtom a} = 2 ^ n := by
  let e := (transportedLevelEquiv μ n).toEquiv.subtypeEquiv
    (fun a => ((transportedLevelEquiv μ n).isAtom_iff a).symm)
  exact (Nat.card_congr e.symm).trans (level_atom_count n)

lemma transported_cell_mass {n : ℕ} (s : Word n) :
    MeasureAlgebra.mass (transport μ (levelClass {s})) = (1 / 2 : ℝ≥0∞) ^ n := by
  rw [transport_mass]
  exact cell_mass s

lemma transported_cell_split {n : ℕ} (s : Word n) :
    transport μ (levelClass {s}) =
      transport μ (levelClass {Fin.snoc s false}) ⊔ transport μ (levelClass {Fin.snoc s true}) := by
  rw [← (transport μ).map_sup, ← levelClass_singleton_split]

lemma transported_children_disjoint {n : ℕ} (s : Word n) :
    Disjoint (transport μ (levelClass {Fin.snoc s false})) (transport μ (levelClass {Fin.snoc s true})) := by
  rw [disjoint_iff, ← (transport μ).map_inf, (levelClass_children_disjoint s).eq_bot,
    (transport μ).map_bot]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: proposition
  title: Dyadic approximation
-/
/-- An increasing sequence of finite Boolean subalgebras with the prescribed
atom counts and masses has countable dense union in every standard nonatomic probability algebra. -/
theorem standard_dyadic_approximation :
    Monotone (transportedLevel μ) ∧
    (∀ n, (transportedLevel μ n : Set (MeasureAlgebra μ)).Finite ∧
      Nat.card {a : transportedLevel μ n // IsAtom a} = 2 ^ n) ∧
    (⋃ n, (transportedLevel μ n : Set (MeasureAlgebra μ))).Countable ∧
    Dense (⋃ n, (transportedLevel μ n : Set (MeasureAlgebra μ))) ∧
    ∀ n (s : Word n), MeasureAlgebra.mass (transport μ (levelClass {s})) = (1 / 2 : ℝ≥0∞) ^ n :=
  ⟨transportedLevel_monotone μ, fun n => ⟨transportedLevel_finite μ n, transported_atom_count μ n⟩,
    transportedLevels_countable μ, transportedLevels_dense μ, fun _ => transported_cell_mass μ⟩

end PolishSpaceBook.DyadicMeasureAlgebra
