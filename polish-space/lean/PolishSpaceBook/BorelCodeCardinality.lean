module

public import PolishSpaceBook.BorelStructure
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section

/-! # Serializing Borel codes and counting their decoded sets

A code is recorded by the natural-number label at each finite address. Labels
are zero for absence, one for union, two for complement, and `n + 3` for leaf
`n`. This realizes the book's injection of labelled trees into Baire space.
-/
namespace PolishSpaceBook
open Set TopologicalSpace
open scoped Cardinal Ordinal

namespace BorelCode

/-- The label at an address; a complement uses child zero. -/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Fix a countable open basis for $X$. Record each Borel code by the label at every finite address, using $0$ for
    absence, $1$ for a union, $2$ for a complement, and $n+3$ for a leaf naming the $n$th basic open set.
-/
def label : BorelCode → List ℕ → ℕ
  | .leaf n, [] => n + 3
  | .union _, [] => 1
  | .compl _, [] => 2
  | .leaf _, _ :: _ => 0
  | .union f, n :: s => label (f n) s
  | .compl c, n :: s => if n = 0 then label c s else 0
termination_by _ s => s.length

/-- Every constructor and every subtree can be recovered from its address labels. -/
theorem label_injective : Function.Injective label := by
  intro c
  induction c with
  | leaf n =>
    intro d h
    have hr := congrFun h []
    cases d with
    | leaf m => simp only [label] at hr; congr; omega
    | union f => simp only [label] at hr; omega
    | compl d => simp only [label] at hr; omega
  | union f ih =>
    intro d h
    have hr := congrFun h []
    cases d with
    | leaf n => simp only [label] at hr; omega
    | union g =>
      congr 1
      funext n
      apply ih n
      funext s
      simpa [label] using congrFun h (n :: s)
    | compl d => simp only [label] at hr; omega
  | compl c ih =>
    intro d h
    have hr := congrFun h []
    cases d with
    | leaf n => simp only [label] at hr; omega
    | union g => simp only [label] at hr; omega
    | compl d =>
      congr 1
      apply ih
      funext s
      simpa [label] using congrFun h (0 :: s)

/-- Reindex finite addresses by a fixed bijection with the naturals. -/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    A fixed enumeration of the finite addresses turns this record into an element of $\BaireSpace$.
    The record determines the root label and all labelled subtrees, so different codes give different records.
-/
def serialize (c : BorelCode) : ℕ → ℕ := fun n => label c ((Denumerable.eqv (List ℕ)).symm n)

theorem serialize_injective : Function.Injective serialize := by
  intro c d h
  apply label_injective
  funext s
  simpa [serialize] using congrFun h ((Denumerable.eqv (List ℕ)) s)

theorem cardinal_le_continuum : #BorelCode ≤ 𝔠 := by
  have h := Cardinal.mk_le_of_injective serialize_injective
  simpa [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0] using h

/-- Decoding preserves the canonical Borel measurable sets. -/
theorem decode_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {U : ℕ → Set X} (hU : ∀ n, IsOpen (U n)) (c : BorelCode) : MeasurableSet (c.decode U) := by
  induction c with
  | leaf n => exact (hU n).measurableSet
  | union f ih => exact MeasurableSet.iUnion ih
  | compl c ih => exact ih.compl

end BorelCode

/-- Closure at omega-one lets the previously constructed hierarchy contain every Borel set. -/
theorem measurableSet_mem_borelSigma_omega1 {X : Type*} [MetricSpace X]
    [mX : MeasurableSpace X] [BorelSpace X] {A : Set X} (hA : MeasurableSet A) :
    A ∈ borelSigma (Y := X) (ω₁ : Ordinal.{0}) := by
  have h1 : (1 : Ordinal) ≤ ω₁ :=
    (lt_trans Ordinal.one_lt_omega0 Ordinal.omega0_lt_omega_one).le
  let m : MeasurableSpace X := {
    MeasurableSet' := fun s => s ∈ borelSigma (Y := X) (ω₁ : Ordinal.{0})
    measurableSet_empty := borelSigma_mono (le_refl 1) h1 (by rw [borelSigma_one]; exact isOpen_empty)
    measurableSet_compl := fun s hs => borelSigma_omega1_compl hs
    measurableSet_iUnion := fun s hs => borelSigma_omega1_iUnion hs }
  have hb : borel X ≤ m := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact borelSigma_mono (le_refl 1) h1 (by rw [borelSigma_one]; exact hs)
  have hEq : mX = borel X := @BorelSpace.measurable_eq X _ mX _
  rw [hEq] at hA
  exact hb A hA

/-- The code-decoding map into the subtype of Borel sets. -/
def BorelCode.decodeBorel {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n)) (c : BorelCode) : {A : Set X // MeasurableSet A} :=
  ⟨c.decode U, c.decode_measurable hU⟩

theorem BorelCode.decodeBorel_surjective {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : ℕ → Set X)
    (hU : IsTopologicalBasis (range U)) :
    Function.Surjective (decodeBorel U (fun n => hU.isOpen (mem_range_self n))) := by
  intro A
  obtain ⟨c, hc⟩ := BorelCode.exists_decode_eq U hU (measurableSet_mem_borelSigma_omega1 A.property)
  exact ⟨c, Subtype.ext hc⟩

/-- The subset of Baire space consisting of serialized inductive codes. -/
def BorelCode.serializedCodes : Set (ℕ → ℕ) := range BorelCode.serialize

/-- Recover the labelled tree and decode it; the range restriction supplies validity. -/
noncomputable def BorelCode.decodeSerialized {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (p : serializedCodes) : {A : Set X // MeasurableSet A} :=
  decodeBorel U hU ((Equiv.ofInjective serialize serialize_injective).symm p)

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    The coding theorem in §{sec:borel-codes-every-borel} makes the decoding map
    $$D:\BorelCodes\to\mathcal B(X),\qquad c\mapsto A_c$$
    surjective.
-/
theorem BorelCode.decodeSerialized_surjective {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : ℕ → Set X)
    (hU : IsTopologicalBasis (range U)) :
    Function.Surjective (decodeSerialized U (fun n => hU.isOpen (mem_range_self n))) :=
  (decodeBorel_surjective U hU).comp (Equiv.ofInjective serialize serialize_injective).symm.surjective

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Consequently,
    $$|\mathcal B(X)|\le|\BorelCodes|\le|\BaireSpace|=2^{\alephNull}.$$
-/
theorem borelSets_cardinal_le_continuum {X : Type} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] :
    #{A : Set X // MeasurableSet A} ≤ 𝔠 := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  obtain ⟨U, hU⟩ := exists_seq_basis X
  have hc : #BorelCode.serializedCodes ≤ #(ℕ → ℕ) :=
    Cardinal.mk_le_of_injective (Subtype.val_injective (p := BorelCode.serializedCodes))
  have hs := Cardinal.mk_le_of_surjective (BorelCode.decodeSerialized_surjective U hU)
  simpa [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0] using hs.trans hc

end PolishSpaceBook
