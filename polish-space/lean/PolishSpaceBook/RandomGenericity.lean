module

public import PolishSpaceBook.RandomPointFilters

@[expose] public section

/-!
# Ambient random genericity for countable dense requirements

Construct the countable Boolean fragment from antichains and cylinders, extend
its point filter to the full positive algebra, and recover the original point
from cylinder decisions. All exceptional sets are constructed and proved null.
The input is actual density in the ambient order, not internal-model density.
-/

namespace PolishSpaceBook
open Set MeasureTheory Filter
open scoped symmDiff ENNReal

/-- A countable generating family has countable Boolean closure. Finite stages
adjoin binary joins and complements; binary meets follow by De Morgan. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Conull reconstruction from dense requirements
-/
theorem countable_booleanClosure {α : Type*} [BooleanAlgebra α] (S : Set α) (hS : S.Countable) :
    (BooleanSubalgebra.closure S : Set α).Countable := by
  let T : ℕ → Set α := Nat.rec (insert ⊥ S) (fun _ U => U ∪ Set.image2 (· ⊔ ·) U U ∪ Compl.compl '' U)
  have hstep (n) : T n ⊆ T (n + 1) := fun _ h => Or.inl (Or.inl h)
  have hmono : Monotone T := monotone_nat_of_le_succ hstep
  have hc (n) : (T n).Countable := by
    induction n with
    | zero => exact hS.insert ⊥
    | succ n ih => exact (ih.union (ih.image2 ih (· ⊔ ·))).union (ih.image _)
  apply Set.Countable.mono ?_ (countable_iUnion hc)
  intro x hx
  induction hx using BooleanSubalgebra.closure_bot_sup_induction with
  | mem x hx => exact mem_iUnion.mpr ⟨0, mem_insert_of_mem _ hx⟩
  | bot => exact mem_iUnion.mpr ⟨0, mem_insert _ _⟩
  | sup x _ y _ hx hy =>
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨max n m + 1, Or.inl (Or.inr
      ⟨x, hmono (le_max_left _ _) hn, y, hmono (le_max_right _ _) hm, rfl⟩)⟩
  | compl x _ hx =>
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n + 1, Or.inr ⟨x, hn, rfl⟩⟩

namespace MeasureAlgebra
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (A : BooleanSubalgebra (MeasureAlgebra μ))

/-- Inclusion of positive fragment elements in the ambient positive algebra. -/
def fragmentPositiveValue (a : FragmentPositive A) : Positive μ :=
  ⟨a.val.val, fun h => a.property (Subtype.ext h)⟩

/-- Upward closure in the ambient order extends a fragment filter. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Conull reconstruction from dense requirements
-/
def extendFragmentFilter (G : Order.PFilter (FragmentPositive A)) : Order.PFilter (Positive μ) :=
  (Order.IsPFilter.of_def
    (F := {p | ∃ a ∈ G, a.val.val ≤ p.val})
    (by obtain ⟨a, ha⟩ := G.nonempty; exact ⟨fragmentPositiveValue A a, a, ha, le_rfl⟩)
    (by
      rintro p ⟨a, ha, hap⟩ q ⟨b, hb, hbq⟩
      obtain ⟨c, hc, hca, hcb⟩ := G.directed a ha b hb
      exact ⟨fragmentPositiveValue A c, ⟨c, hc, le_rfl⟩,
        (show c.val.val ≤ p.val from le_trans hca hap),
        (show c.val.val ≤ q.val from le_trans hcb hbq)⟩)
    (by rintro p q hpq ⟨a, ha, hap⟩; exact ⟨a, ha, le_trans hap hpq⟩)).toPFilter

@[simp] theorem fragment_mem_extended (G : Order.PFilter (FragmentPositive A)) (a : FragmentPositive A) :
    fragmentPositiveValue A a ∈ extendFragmentFilter A G ↔ a ∈ G := by
  constructor
  · rintro ⟨b, hb, hba⟩
    exact G.mem_of_le (show b ≤ a from hba) hb
  · intro ha
    exact ⟨a, ha, le_rfl⟩

end MeasureAlgebra

open MeasureAlgebra

/-- Cylinder membership in an extended point filter agrees with actual
membership, once the representatives have been aligned with the cylinders. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Conull reconstruction from dense requirements
-/
theorem extended_point_filter_cylinder
    (A : BooleanSubalgebra (MeasureAlgebra fairCoinProduct))
    (hA : ∀ s : List Bool, randomCylinder fairCoinProduct s ∈ A)
    (R : A → MeasuredSets fairCoinProduct)
    (G : Order.PFilter (FragmentPositive A)) (x : ℕ → Bool)
    (hG : ∀ a, a ∈ G ↔ x ∈ (R a.val : Set (ℕ → Bool)))
    (halign : ∀ s, x ∈ (R ⟨randomCylinder fairCoinProduct s, hA s⟩ : Set (ℕ → Bool)) ↔ x ∈ cyl s)
    (s : List Bool) : x ∈ cyl s ↔ randomCoinCylinder s ∈ extendFragmentFilter A G := by
  let a : FragmentPositive A := ⟨⟨randomCylinder fairCoinProduct s, hA s⟩,
    fun h => (randomCoinCylinder s).property (congrArg Subtype.val h)⟩
  have heq : fragmentPositiveValue A a = randomCoinCylinder s := rfl
  rw [← heq, fragment_mem_extended, hG]
  exact (halign s).symm

/-- The ambient extension meets length requirements and its unique real is
the original point. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Conull reconstruction from dense requirements
-/
theorem extended_point_filter_recovers
    (A : BooleanSubalgebra (MeasureAlgebra fairCoinProduct))
    (hA : ∀ s : List Bool, randomCylinder fairCoinProduct s ∈ A)
    (R : A → MeasuredSets fairCoinProduct)
    (G : Order.PFilter (FragmentPositive A)) (x : ℕ → Bool)
    (hG : ∀ a, a ∈ G ↔ x ∈ (R a.val : Set (ℕ → Bool)))
    (halign : ∀ s, x ∈ (R ⟨randomCylinder fairCoinProduct s, hA s⟩ : Set (ℕ → Bool)) ↔ x ∈ cyl s) :
    ∃ hlen : ∀ n, ∃ p ∈ extendFragmentFilter A G, p ∈ randomLengthRequirement fairCoinProduct n,
      randomFilterReal (extendFragmentFilter A G) hlen = x := by
  have hmem := extended_point_filter_cylinder A hA R G x hG halign
  have hlen : ∀ n, ∃ p ∈ extendFragmentFilter A G, p ∈ randomLengthRequirement fairCoinProduct n := by
    intro n
    exact ⟨randomCoinCylinder (seqPrefix x n), (hmem _).mp (mem_cyl_seqPrefix x n),
      seqPrefix x n, seqPrefix_length x n, le_rfl⟩
  refine ⟨hlen, ?_⟩
  funext i
  have hx := (randomCoinFilterReal_mem_cyl (extendFragmentFilter A G) hlen (seqPrefix x (i + 1))).mpr
    ((hmem _).mp (mem_cyl_seqPrefix x (i + 1)))
  exact (hx i (by simp)).trans (seqPrefix_get x _)

/-- Any prescribed sequence of ambient dense sets is met by filters representing
all points outside a Borel null set. The Boolean fragment and representatives
are constructed in the proof, not supplied as hypotheses. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Conull reconstruction from dense requirements
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For each $i$, choose a countable predense antichain $J_i\IncludedIn D_i$. Let $A$ be the Boolean subalgebra generated by all these antichains and all cylinder classes.
    This algebra is countable: start with the countable generating set and zero, then repeatedly adjoin binary joins and complements. Each stage is countable, and the union of the stages is exactly the generated Boolean subalgebra; finite meets are obtained by De Morgan's law.

    Choose representatives $B_a$ on $A$, and form the preceding exceptional set $E$ for the families $J_i$. To align these representatives with the actual cylinders, also exclude
    $$C:=\bigcup_{s\in\finseq{2}}\left(\SymmetricDifference{B_{[\cyl{s}]}}{\cyl{s}}\right).$$
    Each symmetric difference is Borel and null because its two sets represent the same class. There are countably many finite strings, so $N:=E\cup C$ is Borel and null.

    For $r\notin N$, the point filter $G_r^A$ meets every $J_i$. Extend it to the full positive order by upward closure:
    $$G:=\{p\in Q_+:\exists a\in G_r^A\ (a\le p)\}.$$
    This is a filter: it is nonempty and upward closed, and a common strengthening in $G_r^A$ of two witnesses also strengthens the two ambient conditions. Its restriction to the positive part of $A$ is exactly $G_r^A$, by upward closure within that subalgebra. In particular, $G$ meets every $D_i$.

    Since every cylinder class belongs to $A$ and $r$ avoids $C$, we have
    $$[\cyl{s}]\in G\quad\Longleftrightarrow\quad r\in B_{[\cyl{s}]}\quad\Longleftrightarrow\quad r\in\cyl{s}.$$
    For each length, the class of the cylinder containing $r$ therefore lies in $G$ and witnesses that it meets $C_n$. The random filter union lemma now applies, and the displayed cylinder decisions identify its unique real with $r$.
    \end{proof}
-/
theorem conull_random_genericity
    (D : ℕ → Set (Positive fairCoinProduct)) (hd : ∀ n, IsCoinitial (D n)) :
    ∃ N : Set (ℕ → Bool), MeasurableSet N ∧ fairCoinProduct N = 0 ∧ ∀ x ∉ N,
      ∃ G : Order.PFilter (Positive fairCoinProduct),
        (∀ n, ∃ p ∈ G, p ∈ D n) ∧
        ∃ hlen : ∀ n, ∃ p ∈ G, p ∈ randomLengthRequirement fairCoinProduct n,
          randomFilterReal G hlen = x := by
  classical
  choose J hJD hJdisj hJdense using fun n => exists_disjoint_predense_subset (D n) (hd n)
  have hJcount (n) : (J n).Countable := countable_positive_pairwiseDisjoint (J n) (hJdisj n)
  let S : Set (MeasureAlgebra fairCoinProduct) :=
    (⋃ n, Subtype.val '' J n) ∪ Set.range (randomCylinder fairCoinProduct)
  have hS : S.Countable := (countable_iUnion fun n => (hJcount n).image _).union (countable_range _)
  let A := BooleanSubalgebra.closure S
  have : Countable A := (countable_booleanClosure S hS).to_subtype
  have hjA (n) (p) (hp : p ∈ J n) : p.val ∈ A :=
    BooleanSubalgebra.subset_closure (Or.inl (mem_iUnion.mpr ⟨n, p, hp, rfl⟩))
  have hcA (s) : randomCylinder fairCoinProduct s ∈ A :=
    BooleanSubalgebra.subset_closure (Or.inr (mem_range_self s))
  let F : ℕ → Set (FragmentPositive A) := fun n => {a | fragmentPositiveValue A a ∈ J n}
  have hF (n) (p : Positive fairCoinProduct) : ∃ a ∈ F n, p.val ⊓ a.val.val ≠ ⊥ := by
    obtain ⟨q, hq, hpq⟩ := hJdense n p
    let a : FragmentPositive A := ⟨⟨q.val, hjA n q hq⟩, fun h => q.property (congrArg Subtype.val h)⟩
    exact ⟨a, hq, hpq⟩
  let R := fragmentRepresentatives A
  have hR := fragmentRepresentatives_class A
  let C : Set (ℕ → Bool) := ⋃ s : List Bool,
    (R ⟨randomCylinder fairCoinProduct s, hcA s⟩ : Set (ℕ → Bool)) ∆ cyl s
  have hCm : MeasurableSet C := MeasurableSet.iUnion fun s =>
    (R ⟨randomCylinder fairCoinProduct s, hcA s⟩).property.symmDiff (isOpen_cyl s).measurableSet
  have hCnull : fairCoinProduct C = 0 := by
    apply measure_iUnion_null
    intro s
    exact measure_symmDiff_eq_zero_iff.mpr
      ((mk_eq_mk (R ⟨randomCylinder fairCoinProduct s, hcA s⟩).property
        (isOpen_cyl s).measurableSet).mp (hR ⟨randomCylinder fairCoinProduct s, hcA s⟩))
  refine ⟨pointGenericDefect A R F ∪ C,
    (pointGenericDefect_measurable A R F).union hCm,
    measure_union_null (pointGenericDefect_null A R hR F hF) hCnull, ?_⟩
  intro x hx
  have hxE : x ∉ pointGenericDefect A R F := fun h => hx (Or.inl h)
  have hxC : x ∉ C := fun h => hx (Or.inr h)
  obtain ⟨G, hG, hmeet⟩ := pointFragmentFilter_meets A R F x hxE
  have halign (s) : x ∈ (R ⟨randomCylinder fairCoinProduct s, hcA s⟩ : Set (ℕ → Bool)) ↔ x ∈ cyl s := by
    have hn : x ∉ (R ⟨randomCylinder fairCoinProduct s, hcA s⟩ : Set (ℕ → Bool)) ∆ cyl s :=
      fun h => hxC (mem_iUnion.mpr ⟨s, h⟩)
    simp only [mem_symmDiff] at hn
    tauto
  refine ⟨extendFragmentFilter A G, ?_, extended_point_filter_recovers A hcA R G x hG halign⟩
  intro n
  obtain ⟨a, haG, haJ⟩ := hmeet n
  exact ⟨fragmentPositiveValue A a, (fragment_mem_extended A G a).mpr haG, hJD n haJ⟩

end PolishSpaceBook
