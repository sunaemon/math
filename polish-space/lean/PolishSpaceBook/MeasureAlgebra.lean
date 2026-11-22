module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Topology.Order.IsLUB

@[expose] public section

/-!
# Measurable sets modulo null sets

The quotient uses mathlib's measurable-set type and almost-everywhere equality.
Its order is almost-everywhere inclusion. Boolean operations are induced by
union, intersection and complement, as in the random-forcing chapter.
-/

namespace PolishSpaceBook
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {X : Type*} [MeasurableSpace X]

/-- Equality of measurable representatives modulo null sets. -/
@[implicit_reducible] def measureSetoid (μ : Measure X) : Setoid (MeasuredSets μ) where
  r s t := (s : Set X) =ᵐ[μ] (t : Set X)
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- The Boolean algebra of measurable sets modulo null sets. -/
def MeasureAlgebra (μ : Measure X) := Quotient (measureSetoid μ)

namespace MeasureAlgebra
variable {μ : Measure X}

/-- The equivalence class of a measurable set. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\MeasureClass{\mu}{A}$ for the class of a measurable set in the external measure algebra
    $\MeasureAlg{\CantorSpace}{\mu}$.
-/
def mk (s : Set X) (hs : MeasurableSet s) : MeasureAlgebra μ := Quotient.mk _ ⟨s, hs⟩

/-- A measurable representative, used only to construct arbitrary suprema. -/
noncomputable def representative (a : MeasureAlgebra μ) : MeasuredSets μ := Quotient.out a

@[simp] theorem mk_representative (a : MeasureAlgebra μ) :
    mk (representative a : Set X) (representative a).property = a := Quotient.out_eq a

@[simp] theorem mk_eq_mk {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (mk s hs : MeasureAlgebra μ) = mk t ht ↔ s =ᵐ[μ] t := Quotient.eq

instance : LE (MeasureAlgebra μ) where
  le a b := Quotient.liftOn₂ a b (fun s t => (s : Set X) ≤ᵐ[μ] (t : Set X)) (by
    intro s t s' t' hs ht
    apply propext
    constructor <;> intro h
    · filter_upwards [hs, ht, h] with x hs ht h
      simpa only [← hs, ← ht] using h
    · filter_upwards [hs, ht, h] with x hs ht h
      simpa only [hs, ht] using h)

@[simp] theorem mk_le_mk {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (mk s hs : MeasureAlgebra μ) ≤ mk t ht ↔ s ≤ᵐ[μ] t := Iff.rfl

instance : PartialOrder (MeasureAlgebra μ) where
  le_refl a := Quotient.inductionOn a (fun _ => Filter.EventuallyLE.rfl)
  le_trans a b c := Quotient.inductionOn₃ a b c (fun _ _ _ h k => Filter.EventuallyLE.trans h k)
  le_antisymm a b := Quotient.inductionOn₂ a b (fun _ _ h k =>
    Quotient.sound (Filter.EventuallyLE.antisymm h k))

instance : Max (MeasureAlgebra μ) where
  max a b := Quotient.liftOn₂ a b
    (fun s t => mk ((s : Set X) ∪ t) (s.property.union t.property)) (by
      intro s t s' t' hs ht
      exact Quotient.sound (ae_eq_set_union hs ht))

instance : Min (MeasureAlgebra μ) where
  min a b := Quotient.liftOn₂ a b
    (fun s t => mk ((s : Set X) ∩ t) (s.property.inter t.property)) (by
      intro s t s' t' hs ht
      exact Quotient.sound (ae_eq_set_inter hs ht))

instance : Compl (MeasureAlgebra μ) where
  compl a := Quotient.liftOn a
    (fun s => mk (s : Set X)ᶜ s.property.compl) (by
      intro s t h
      exact Quotient.sound (ae_eq_set_compl_compl.mpr h))

instance : Top (MeasureAlgebra μ) := ⟨mk univ MeasurableSet.univ⟩
instance : Bot (MeasureAlgebra μ) := ⟨mk ∅ MeasurableSet.empty⟩

@[simp] theorem mk_sup (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (mk s hs : MeasureAlgebra μ) ⊔ mk t ht = mk (s ∪ t) (hs.union ht) := rfl
@[simp] theorem mk_inf (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (mk s hs : MeasureAlgebra μ) ⊓ mk t ht = mk (s ∩ t) (hs.inter ht) := rfl
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Write $a^c$ for the Boolean complement of $a\in Q$.
-/
@[simp] theorem mk_compl (s : Set X) (hs : MeasurableSet s) :
    (mk s hs : MeasureAlgebra μ)ᶜ = mk sᶜ hs.compl := rfl

instance : DistribLattice (MeasureAlgebra μ) where
  __ := (inferInstance : PartialOrder (MeasureAlgebra μ))
  sup := max
  inf := min
  le_sup_left a b := Quotient.inductionOn₂ a b (fun _ _ =>
    Filter.Eventually.of_forall fun _ => Or.inl)
  le_sup_right a b := Quotient.inductionOn₂ a b (fun _ _ =>
    Filter.Eventually.of_forall fun _ => Or.inr)
  sup_le a b c := Quotient.inductionOn₃ a b c (by
    intro s t u hs ht
    filter_upwards [hs, ht] with x hs ht
    exact fun h => h.elim hs ht)
  inf_le_left a b := Quotient.inductionOn₂ a b (fun _ _ =>
    Filter.Eventually.of_forall fun _ => And.left)
  inf_le_right a b := Quotient.inductionOn₂ a b (fun _ _ =>
    Filter.Eventually.of_forall fun _ => And.right)
  le_inf a b c := Quotient.inductionOn₃ a b c (by
    intro s t u ht hu
    filter_upwards [ht, hu] with x ht hu
    exact fun h => ⟨ht h, hu h⟩)
  le_sup_inf a b c := Quotient.inductionOn₃ a b c (fun _ _ _ =>
    Filter.Eventually.of_forall fun _ => by change (_ ∨ _) ∧ (_ ∨ _) → _ ∨ (_ ∧ _); tauto)

instance : BooleanAlgebra (MeasureAlgebra μ) where
  __ := (inferInstance : DistribLattice (MeasureAlgebra μ))
  compl := Compl.compl
  top := ⊤
  bot := ⊥
  inf_compl_le_bot a := Quotient.inductionOn a (fun _ =>
    Filter.Eventually.of_forall fun _ h => h.2 h.1)
  top_le_sup_compl a := Quotient.inductionOn a (fun _ =>
    Filter.Eventually.of_forall fun _ _ => Classical.em _)
  le_top a := Quotient.inductionOn a (fun _ =>
    Filter.Eventually.of_forall fun _ _ => trivial)
  bot_le a := Quotient.inductionOn a (fun _ =>
    Filter.Eventually.of_forall fun _ h => False.elim h)

/-- Measure is independent of the representative. -/
def mass (a : MeasureAlgebra μ) : ℝ≥0∞ :=
  Quotient.liftOn a (fun s => μ (s : Set X)) (fun _ _ h => measure_congr h)

@[simp] theorem mass_mk (s : Set X) (hs : MeasurableSet s) :
    mass (mk s hs : MeasureAlgebra μ) = μ s := rfl

@[simp] theorem mk_eq_bot (s : Set X) (hs : MeasurableSet s) :
    (mk s hs : MeasureAlgebra μ) = ⊥ ↔ μ s = 0 := by
  change (mk s hs : MeasureAlgebra μ) = mk ∅ MeasurableSet.empty ↔ _
  rw [mk_eq_mk, ae_eq_empty]

/-- Inclusion modulo null sets is precisely the quotient order. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For a finite Borel measure $\mu$ on a Polish space $X$, the \termdefine{measure algebra} is the Boolean algebra
    $$\MeasureAlg{X}{\mu} \;:=\; \mathrm{Borel}(X) / \mathrm{null}_\mu,$$
    the Borel sets modulo $\mu$-null sets, with $[A] \le [B]$ iff $\mu(\SetDifference{A}{B}) = 0$. For non-atomic probability measures, the following theorem
    determines this measure algebra up to isomorphism.
-/
theorem mk_le_mk_iff_null_sdiff (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (mk s hs : MeasureAlgebra μ) ≤ mk t ht ↔ μ (s \ t) = 0 := ae_le_set

/-- Every countable measurable union is a supremum in the quotient. -/
theorem isLUB_mk_iUnion {ι : Type*} [Countable ι] (s : ι → Set X) (hs : ∀ n, MeasurableSet (s n)) :
    IsLUB (Set.range (fun n => (mk (s n) (hs n) : MeasureAlgebra μ)))
      (mk (⋃ n, s n) (MeasurableSet.iUnion hs)) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact Filter.Eventually.of_forall (fun _ h => Set.mem_iUnion.mpr ⟨n, h⟩)
  · intro a
    refine Quotient.inductionOn a ?_
    intro t ht
    have hle (n) : s n ≤ᵐ[μ] (t : Set X) := ht (Set.mem_range_self n)
    filter_upwards [ae_all_iff.mpr hle] with x hx
    intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact hx n hn

/-- Finite unions of members of a family, including the empty union. -/
inductive FiniteUnionOf (S : Set (Set X)) : Set X → Prop
  | empty : FiniteUnionOf S ∅
  | basic {B} : B ∈ S → FiniteUnionOf S B
  | union {A B} : FiniteUnionOf S A → FiniteUnionOf S B → FiniteUnionOf S (A ∪ B)

theorem FiniteUnionOf.measurable {S : Set (Set X)} (hS : ∀ B ∈ S, MeasurableSet B)
    {B : Set X} (hB : FiniteUnionOf S B) : MeasurableSet B := by
  induction hB with
  | empty => exact MeasurableSet.empty
  | basic h => exact hS _ h
  | union _ _ hA hB => exact hA.union hB

theorem FiniteUnionOf.ae_le {S : Set (Set X)} {C : Set X}
    (hC : ∀ B ∈ S, B ≤ᵐ[μ] C) {B : Set X} (hB : FiniteUnionOf S B) : B ≤ᵐ[μ] C := by
  induction hB with
  | empty => exact Filter.Eventually.of_forall (fun _ h => False.elim h)
  | basic h => exact hC _ h
  | union _ _ hA hB =>
    filter_upwards [hA, hB] with x hA hB
    exact fun h => h.elim hA hB

/-- For a finite measure, finite unions admit a countable sequence whose union
is an essential upper bound for the whole family. This is the book's
maximal-mass argument, not a completeness assumption on the quotient. -/
theorem exists_finite_union_essential_upper_bound [IsFiniteMeasure μ]
    (S : Set (Set X)) (hS : ∀ B ∈ S, MeasurableSet B) :
    ∃ V : ℕ → Set X, (∀ n, FiniteUnionOf S (V n)) ∧
      ∀ B ∈ S, B ≤ᵐ[μ] ⋃ n, V n := by
  classical
  let T : Set ℝ≥0∞ := μ '' {B | FiniteUnionOf S B}
  let α := sSup T
  have hT : T.Nonempty := ⟨0, ∅, FiniteUnionOf.empty, measure_empty⟩
  obtain ⟨v, _, _, hvlim, hvmem⟩ := (isLUB_sSup T).exists_seq_monotone_tendsto hT
  choose V hV hv using hvmem
  have hacc (n : ℕ) : FiniteUnionOf S (accumulate V n) := by
    induction n with
    | zero => simpa using hV 0
    | succ n ih => simpa using FiniteUnionOf.union ih (hV (n + 1))
  let U := ⋃ n, V n
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n => (hV n).measurable hS
  have hmass : μ U = α := by
    apply le_antisymm
    · rw [show μ U = ⨆ n, μ (accumulate V n) from measure_iUnion_eq_iSup_accumulate]
      exact iSup_le fun n => le_sSup ⟨_, hacc n, rfl⟩
    · apply le_of_tendsto' hvlim
      intro n
      rw [← hv n]
      exact measure_mono (subset_iUnion V n)
  refine ⟨V, hV, ?_⟩
  intro B hB
  have hunion : μ (U ∪ B) ≤ α := by
    rw [show U ∪ B = ⋃ n, V n ∪ B from iUnion_union B V]
    rw [measure_iUnion_eq_iSup_accumulate]
    apply iSup_le
    intro n
    have haccB : FiniteUnionOf S (accumulate (fun n => V n ∪ B) n) := by
      induction n with
      | zero => simpa using FiniteUnionOf.union (hV 0) (FiniteUnionOf.basic hB)
      | succ n ih =>
        simpa using FiniteUnionOf.union ih (FiniteUnionOf.union (hV (n + 1)) (FiniteUnionOf.basic hB))
    exact le_sSup ⟨_, haccB, rfl⟩
  have heq : (U : Set X) =ᵐ[μ] (U ∪ B : Set X) := ae_eq_of_subset_of_measure_ge subset_union_left
    (hmass ▸ hunion) hU.nullMeasurableSet (measure_ne_top _ _)
  exact union_ae_eq_left_iff_ae_subset.mp heq.symm

/-- Every family of measurable sets has a measurable essential supremum.
The leastness proof retains the finite-union witnesses chosen above. -/
theorem exists_measurable_essential_supremum [IsFiniteMeasure μ]
    (S : Set (Set X)) (hS : ∀ B ∈ S, MeasurableSet B) :
    ∃ U : Set X, MeasurableSet U ∧ (∀ B ∈ S, B ≤ᵐ[μ] U) ∧
      ∀ C : Set X, (∀ B ∈ S, B ≤ᵐ[μ] C) → U ≤ᵐ[μ] C := by
  obtain ⟨V, hV, hupper⟩ := exists_finite_union_essential_upper_bound (μ := μ) S hS
  refine ⟨⋃ n, V n, MeasurableSet.iUnion (fun n => (hV n).measurable hS), hupper, ?_⟩
  intro C hC
  have hVC (n) := (hV n).ae_le hC
  filter_upwards [ae_all_iff.mpr hVC] with x hx
  intro h
  obtain ⟨n, hn⟩ := mem_iUnion.mp h
  exact hx n hn

/-- The arbitrary supremum is constructed from representatives, using the
finite-union maximal-mass proof. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Completeness
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Choose Borel representatives for the elements of $\mathcal F$, and set
    $$
    \alpha:=\sup\{\mu(B_0\cup\cdots\cup B_{k-1}):[B_i]\in\mathcal F,\ k<\omega\},
    $$
    where the empty union is allowed. Choose finite unions $U_n$ from representatives in $\mathcal F$ whose measures increase to $\alpha$; when
    $\alpha=0$, take all of them empty. Put $U:=\bigcup_n U_n$. The sets $U_n$ need not be increasing, but their finite
    partial unions are increasing and still belong to the family used to define $\alpha$. Their measures are bounded
    above by $\alpha$ and below by $\mu(U_n)$. Continuity from below therefore gives
    $$\mu(U)=\alpha.$$
    If $[B]\in\mathcal F$, then
    $$
    \mu(U\cup B)=\lim_N\mu\bigl(B\cup U_0\cup\cdots\cup U_N\bigr)\le\alpha=\mu(U),
    $$
    so $\mu(\SetDifference{B}{U})=0$ and $[B]\le[U]$. Thus $[U]$ is an upper bound. If $[C]$ is any upper bound for
    $\mathcal F$, then every representative from $\mathcal F$ is contained in $C$ modulo null, so each $U_n$ is contained in
    $C$ modulo null. Hence $U\IncludedIn C$ modulo null, and $[U]\le[C]$. Thus $[U]$ is the supremum of $\mathcal F$.
    \end{proof}
-/
theorem exists_isLUB [IsFiniteMeasure μ] (F : Set (MeasureAlgebra μ)) :
    ∃ a : MeasureAlgebra μ, IsLUB F a := by
  classical
  let S : Set (Set X) := {B | ∃ a ∈ F, (representative a : Set X) = B}
  have hS : ∀ B ∈ S, MeasurableSet B := by
    rintro B ⟨a, _, rfl⟩
    exact (representative a).property
  obtain ⟨U, hU, hupper, hleast⟩ := exists_measurable_essential_supremum (μ := μ) S hS
  refine ⟨mk U hU, ?_, ?_⟩
  · intro a ha
    have h := hupper (representative a : Set X) ⟨a, ha, rfl⟩
    change mk (representative a : Set X) (representative a).property ≤ mk U hU at h
    simpa only [mk_representative] using h
  · intro a
    refine Quotient.inductionOn a ?_
    intro C hC
    apply hleast
    rintro B ⟨b, hb, rfl⟩
    have h := hC hb
    rw [← mk_representative b] at h
    exact h

noncomputable instance [IsFiniteMeasure μ] : CompleteLattice (MeasureAlgebra μ) where
  __ := (inferInstance : DistribLattice (MeasureAlgebra μ))
  __ := (inferInstance : BoundedOrder (MeasureAlgebra μ))
  sSup F := Classical.choose (exists_isLUB F)
  sInf F := Classical.choose (exists_isLUB (lowerBounds F))
  isLUB_sSup F := Classical.choose_spec (exists_isLUB F)
  isGLB_sInf F := isLUB_lowerBounds.mp (Classical.choose_spec (exists_isLUB (lowerBounds F)))

noncomputable instance [IsFiniteMeasure μ] : CompleteBooleanAlgebra (MeasureAlgebra μ) where
  __ := (inferInstance : CompleteLattice (MeasureAlgebra μ))
  __ := (inferInstance : BooleanAlgebra (MeasureAlgebra μ))

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For a countable family of Borel sets, the supremum has the simpler form
    $$\bigvee_n[B_n]=\left[\bigcup_n B_n\right].$$
    Indeed, if each $B_n$ is contained in $C$ modulo null, their union is too, since a countable union of null sets is null.
-/
@[simp] theorem mk_iUnion [IsFiniteMeasure μ] {ι : Type*} [Countable ι] (s : ι → Set X)
    (hs : ∀ n, MeasurableSet (s n)) :
    (mk (⋃ n, s n) (MeasurableSet.iUnion hs) : MeasureAlgebra μ) = ⨆ n, mk (s n) (hs n) :=
  (isLUB_mk_iUnion s hs).unique isLUB_iSup

@[simp] theorem mass_eq_zero_iff (a : MeasureAlgebra μ) : mass a = 0 ↔ a = ⊥ :=
  Quotient.inductionOn a (fun s => (mk_eq_bot (s : Set X) s.property).symm)

/-- Positive elements, with the inherited quotient order, are the random conditions. -/
abbrev Positive (μ : Measure X) := {a : MeasureAlgebra μ // a ≠ ⊥}

/-- A common positive refinement exists exactly when the intersection is nonzero. -/
theorem compatible_iff_inf_ne_bot (a b : Positive μ) :
    (∃ c : Positive μ, c ≤ a ∧ c ≤ b) ↔ a.val ⊓ b.val ≠ ⊥ := by
  constructor
  · rintro ⟨c, hca, hcb⟩ h
    apply c.property
    apply le_bot_iff.mp
    calc
      c.val ≤ a.val ⊓ b.val := le_inf hca hcb
      _ = ⊥ := h
  · intro h
    exact ⟨⟨a.val ⊓ b.val, h⟩, (show a.val ⊓ b.val ≤ a.val from inf_le_left),
      (show a.val ⊓ b.val ≤ b.val from inf_le_right)⟩

/-- Pairwise disjoint nonzero elements satisfy the countable chain condition. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Countable chain condition (ccc)
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Let $\{[B_i]:i\in I\}\IncludedIn Q_+$ be an antichain, and choose representatives with pairwise
    null intersections. For each $n\ge1$, only finitely many $i$ can satisfy
    $\mu(B_i)\ge1/n$, because the measures of any finite subfamily sum to at most $1$. Since every positive measure is at
    least $1/n$ for some $n$, the antichain is countable.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Positivity of the measure makes the Boolean algebra ccc:
    for each positive integer $n$, an antichain has only finitely many members of measure at least $1/n$,
    so every antichain is countable.
-/
theorem countable_pairwiseDisjoint [IsFiniteMeasure μ] (S : Set (MeasureAlgebra μ))
    (hS : S.Pairwise Disjoint) (hpos : ⊥ ∉ S) : S.Countable := by
  classical
  let B (a : S) : Set X := representative a.val
  have hB (a : S) : MeasurableSet (B a) := (representative a.val).property
  have hdis : Pairwise (fun a b => AEDisjoint μ (B a) (B b)) := by
    intro a b hab
    have h := (hS a.property b.property (fun h => hab (Subtype.ext h))).eq_bot
    have heq : (mk (B a ∩ B b) ((hB a).inter (hB b)) : MeasureAlgebra μ) = ⊥ := by
      rw [← mk_inf (B a) (B b) (hB a) (hB b), show mk (B a) (hB a) = a.val from mk_representative a.val,
        show mk (B b) (hB b) = b.val from mk_representative b.val]
      exact h
    exact (mk_eq_bot _ _).mp heq
  have hsum : ∑' a : S, μ (B a) ≤ μ univ := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    rw [← measure_biUnion_finset₀ (fun a _ b _ hab => hdis hab)
      (fun a _ => (hB a).nullMeasurableSet)]
    exact measure_mono (subset_univ _)
  have hfinite (n : ℕ) : {a : S | (n : ℝ≥0∞)⁻¹ ≤ μ (B a)}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top (measure_ne_top _ _) hsum)
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))
  have hcover : (univ : Set S) ⊆ ⋃ n : ℕ, {a : S | (n : ℝ≥0∞)⁻¹ ≤ μ (B a)} := by
    intro a _
    have hmass : μ (B a) ≠ 0 := by
      intro hzero
      have hbot := (mk_eq_bot (B a) (hB a)).mpr hzero
      rw [show mk (B a) (hB a) = a.val from mk_representative a.val] at hbot
      exact hpos (hbot ▸ a.property)
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hmass
    exact mem_iUnion.mpr ⟨n, hn.le⟩
  have hcount : (univ : Set S).Countable :=
    (countable_iUnion (fun n => (hfinite n).countable)).mono hcover
  exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hcount)

end MeasureAlgebra
end PolishSpaceBook
