module

public import PolishSpaceBook.MeasureAlgebraIsomorphism
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-!
# The symmetric-difference metric on the measure algebra

Null-equivalence is exactly zero distance. The quotient therefore turns the
pseudometric on measurable sets into a metric for every finite measure.
-/

noncomputable section
namespace PolishSpaceBook.MeasureAlgebra
open MeasureTheory Set Filter
open scoped ENNReal symmDiff
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For a finite measure $\mu$, the \termdefine{measure-algebra metric} is
    $$\MeasureAlgDistance{\mu}{[A]}{[B]}:=\mu(\SymmetricDifference{A}{B}).$$
    Changing either representative on a null set does not change this value. It vanishes exactly when $[A]=[B]$;
    symmetry is immediate, and the triangle inequality follows from
    $$\mu(\SymmetricDifference{A}{C})
    \le\mu(\SymmetricDifference{A}{B})+\mu(\SymmetricDifference{B}{C}).$$
    Thus this is a genuine metric on the quotient.
-/
/-- Extended distance, independent of the two measurable representatives. -/
def extendedDist (a b : MeasureAlgebra μ) : ℝ≥0∞ :=
  Quotient.liftOn₂ a b (fun A B => μ ((A : Set X) ∆ B)) (by
    intro A B C D hAC hBD
    exact measure_congr (ae_eq_set_symmDiff hAC hBD))

instance : EMetricSpace (MeasureAlgebra μ) where
  edist := extendedDist
  edist_self a := Quotient.inductionOn a (fun A => by simp [extendedDist])
  edist_comm a b := Quotient.inductionOn₂ a b (fun A B => by simp [extendedDist, symmDiff_comm])
  edist_triangle a b c := Quotient.inductionOn₃ a b c (fun A B C => measure_symmDiff_le _ _ _)
  eq_of_edist_eq_zero := by
    intro a b
    induction a using Quotient.inductionOn with
    | h A =>
      induction b using Quotient.inductionOn with
      | h B => exact fun h => Quotient.sound (measure_symmDiff_eq_zero_iff.mp h)

@[simp] lemma edist_mk (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    edist (mk A hA : MeasureAlgebra μ) (mk B hB) = μ (A ∆ B) := rfl

instance [IsFiniteMeasure μ] : MetricSpace (MeasureAlgebra μ) :=
  EMetricSpace.toMetricSpace (fun a b => Quotient.inductionOn₂ a b
    (fun A B => measure_ne_top μ ((A : Set X) ∆ B)))

@[simp] lemma dist_mk [IsFiniteMeasure μ] (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    dist (mk A hA : MeasureAlgebra μ) (mk B hB) = μ.real (A ∆ B) := rfl

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For a non-atomic standard probability space $(X,\mu)$, choose the isomorphism
    $$\Phi:\MeasureAlg{\CantorSpace}{\lambda}\longrightarrow\MeasureAlg{X}{\mu}$$
    constructed in the proof of \termuseas{Maharam theorem}{Maharam's theorem}. Its inverse-image formula commutes
    with symmetric difference and preserves measure, so
    $$\MeasureAlgDistance{\mu}{\Phi(a)}{\Phi(b)}=\MeasureAlgDistance{\lambda}{a}{b}.$$
-/
/-- The isomorphism obtained from inverse almost-everywhere maps is an isometry. -/
lemma ofAEEquiv_isometry (e : AEMeasureEquiv μ ν) : Isometry (ofAEEquiv e) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      change ν ((e.backward ⁻¹' (A : Set X)) ∆ (e.backward ⁻¹' (B : Set X))) = μ ((A : Set X) ∆ B)
      rw [← preimage_symmDiff]
      exact e.backward_preserving.measure_preimage (A.property.symmDiff B.property).nullMeasurableSet

end PolishSpaceBook.MeasureAlgebra
