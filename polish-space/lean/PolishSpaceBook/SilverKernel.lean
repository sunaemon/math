module

public import PolishSpaceBook.AnalyticCatalogConstruction

@[expose] public section

/-!
# Countable homogeneous covers and the Silver kernel

A countable cover by homogeneous sets yields only countably many quotient
classes. Removing a countable family of Borel homogeneous hulls therefore
leaves a nonempty Borel set when there are uncountably many classes.
For a fixed countable analytic catalog, all its homogeneous conditions can
be excluded in this way. This does not assert that the resulting kernel is
itself in that catalog, or replace the effective Silver-kernel argument.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

variable {X : Type*}

/-- All points of the set lie in one equivalence class, allowing the empty set. -/
def ERHomogeneous (E : Setoid X) (A : Set X) : Prop := ∀ x ∈ A, ∀ y ∈ A, E.r x y

theorem homogeneous_quotient_image_countable (E : Setoid X) {A : Set X}
    (hA : ERHomogeneous E A) : (Quotient.mk E '' A).Countable := by
  apply Set.Subsingleton.countable
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact Quotient.sound (hA x hx y hy)

/-- A countable homogeneous cover covers the quotient by countably many
sets with at most one member. No Borel assumption is needed for this step. -/
theorem countable_quotient_of_homogeneous_cover {I : Type*} [Countable I]
    (E : Setoid X) (W : I → Set X) (hW : ∀ i, ERHomogeneous E (W i))
    (hcover : ∀ x, ∃ i, x ∈ W i) : Countable (Quotient E) := by
  have hc : (⋃ i, Quotient.mk E '' W i).Countable :=
    Set.countable_iUnion (fun i => homogeneous_quotient_image_countable E (hW i))
  have heq : (⋃ i, Quotient.mk E '' W i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨i, hi⟩ := hcover x
      exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

/-- The remainder after excluding the chosen homogeneous sets. -/
def homogeneousRemainder {I : Type*} (W : I → Set X) : Set X := (⋃ i, W i)ᶜ

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    There are only countably many sets in the union. If $H=\emptyset$, then $E$ has at most countably many classes.
-/
theorem homogeneousRemainder_nonempty {I : Type*} [Countable I]
    (E : Setoid X) [Uncountable (Quotient E)]
    (W : I → Set X) (hW : ∀ i, ERHomogeneous E (W i)) :
    (homogeneousRemainder W).Nonempty := by
  classical
  by_contra h
  have hcover : ∀ x, ∃ i, x ∈ W i := by
    intro x
    by_contra hx
    exact h ⟨x, by simpa [homogeneousRemainder] using hx⟩
  have hc := countable_quotient_of_homogeneous_cover E W hW hcover
  exact not_countable hc

variable [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X] in
/-- Removing countably many Borel homogeneous hulls gives a Borel remainder.
This is ordinary Borel measurability, not the lightface complexity assertion. -/
theorem homogeneousRemainder_measurable {I : Type*} [Countable I]
    (W : I → Set X) (hW : ∀ i, MeasurableSet (W i)) :
    MeasurableSet (homogeneousRemainder W) :=
  (MeasurableSet.iUnion hW).compl

/-- Any fixed countable family of analytic sets has a nonempty Borel
remainder containing none of its nonempty homogeneous members. Separation
constructs each removed hull. No closure of the input family under the
new remainder is assumed or concluded. -/
theorem silver_borel_remainder_for_countable_family (E : Setoid X)
    (hE : AnalyticSet {p : X × X | ¬ E.r p.1 p.2}) [Uncountable (Quotient E)]
    (F : Set (Set X)) (hFc : F.Countable) (hFa : ∀ A ∈ F, AnalyticSet A) :
    ∃ H : Set X, MeasurableSet H ∧ H.Nonempty ∧
      ∀ A ∈ F, A.Nonempty → A ⊆ H → ¬ ERHomogeneous E A := by
  classical
  let I := {A : Set X // A ∈ F ∧ A.Nonempty ∧ ERHomogeneous E A}
  have hc : {A : Set X | A ∈ F ∧ A.Nonempty ∧ ERHomogeneous E A}.Countable :=
    hFc.mono (fun _ h => h.1)
  let : Countable I := hc.to_subtype
  have hh (A : I) : ∃ D : Set X, MeasurableSet D ∧ A.val ⊆ D ∧ ERHomogeneous E D :=
    borel_homogeneous_hull E hE (hFa A.val A.property.1) A.property.2.1 A.property.2.2
  choose W hWb hAW hWh using hh
  refine ⟨homogeneousRemainder W, homogeneousRemainder_measurable W hWb,
    homogeneousRemainder_nonempty E W hWh, ?_⟩
  intro A hAF hAn hAH hAh
  let i : I := ⟨A, hAF, hAn, hAh⟩
  obtain ⟨x, hx⟩ := hAn
  exact hAH hx (Set.mem_iUnion.mpr ⟨i, hAW i hx⟩)

end PolishSpaceBook
