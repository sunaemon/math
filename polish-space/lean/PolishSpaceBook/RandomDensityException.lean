module

public import PolishSpaceBook.BorelCylinderLimits
public import PolishSpaceBook.BorelInternalCylinderLimits

@[expose] public section

/-! # The explicit density exception code and null-code avoidance

The cylinder density theorem is an external input. The code below is an actual
Boolean/countable Borel expression, rather than a supplied code for the desired
set. Proving that its entire label graph lies in a particular model remains a
separate construction.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open Set Filter Topology MeasureTheory
open scoped Classical

/-- Normalized measure inside the binary trace of a numbered Baire cylinder. -/
def cylinderDensity (A : Set (ℕ → Bool)) (s : List ℕ) : ℝ :=
  fairCoinProduct.real (A ∩ cantorInclusion ⁻¹' cyl s) /
    fairCoinProduct.real (cantorInclusion ⁻¹' cyl s)

/-- The actual cylinder-density sequence along a point's finite prefixes. -/
def densitySequence (A : Set (ℕ → Bool)) (x : ℕ → Bool) (n : ℕ) : ℝ :=
  cylinderDensity A (seqPrefix (cantorInclusion x) n)

/-- On actual binary prefixes this is exactly normalized cylinder measure. -/
theorem densitySequence_eq (A : Set (ℕ → Bool)) (x : ℕ → Bool) (n : ℕ) :
    densitySequence A x n =
      fairCoinProduct.real (A ∩ cyl (seqPrefix x n)) / (1 / 2 : ℝ)^n := by
  have hp : seqPrefix (cantorInclusion x) n = (seqPrefix x n).map Bool.toNat := by
    simp only [seqPrefix, List.map_ofFn, cantorInclusion, Function.comp_def]
  rw [densitySequence, cylinderDensity, hp, cantorInclusion_preimage_cyl]
  simp only [Measure.real, fairCoinProduct_cyl, seqPrefix_length, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]

namespace Code

/-- Failure of density one on A, or of density zero on its complement. -/
def densityException (c : Code) : Code :=
  sup (inf c (nonconvergence (cylinderDensity c.cantor) 1))
    (inf c.compl (nonconvergence (cylinderDensity c.cantor) 0))

theorem not_mem_densityException (c : Code) (x : ℕ → Bool) :
    x ∉ c.densityException.cantor ↔
      Tendsto (densitySequence c.cantor x) atTop (𝓝 (if x ∈ c.cantor then 1 else 0)) := by
  change x ∉ c.densityException.cantor ↔
    Tendsto (fun n => cylinderDensity c.cantor (seqPrefix (cantorInclusion x) n))
      atTop (𝓝 (if x ∈ c.cantor then 1 else 0))
  rw [densityException, cantor_sup, cantor_inf, cantor_inf, cantor_compl]
  change ¬ ((x ∈ c.cantor ∧ _) ∨ (x ∉ c.cantor ∧ _)) ↔ _
  by_cases hx : x ∈ c.cantor
  · simpa [hx] using not_mem_nonconvergence (cylinderDensity c.cantor) 1 x
  · simpa [hx] using not_mem_nonconvergence (cylinderDensity c.cantor) 0 x

/-- Precisely the imported, almost-everywhere cylinder density assertion. -/
def CylinderDensityTheorem (A : Set (ℕ → Bool)) : Prop :=
  ∀ᵐ x ∂fairCoinProduct,
    Tendsto (densitySequence A x) atTop (𝓝 (if x ∈ A then 1 else 0))

theorem densityException_null (c : Code) (hdensity : CylinderDensityTheorem c.cantor) :
    fairCoinProduct c.densityException.cantor = 0 := by
  have he : c.densityException.cantor =
      {x | ¬ Tendsto (densitySequence c.cantor x) atTop (𝓝 (if x ∈ c.cantor then 1 else 0))} := by
    ext x
    simpa only [not_not, mem_ofPred_eq] using not_congr (c.not_mem_densityException x)
  rw [he]
  exact ae_iff.mp hdensity

end Code

/-- Once internal membership is established, null-code avoidance gives both limits. -/
theorem AvoidsNullCodes.density_limits {M : ZFSet.{u}} {x : ℕ → Bool}
    (hx : AvoidsNullCodes M x) (c : Code) (hc : c.densityException.val.labelGraph ∈ M)
    (hdensity : Code.CylinderDensityTheorem c.cantor) :
    (x ∈ c.cantor → Tendsto (densitySequence c.cantor x) atTop (𝓝 1)) ∧
    (x ∉ c.cantor → Tendsto (densitySequence c.cantor x) atTop (𝓝 0)) := by
  have h := (c.not_mem_densityException x).mp (hx _ hc (c.densityException_null hdensity))
  constructor
  · intro hmem
    simpa only [ite_eq_left hmem] using h
  · intro hmem
    simpa only [ite_eq_right hmem] using h

open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels NamedLambda
universe u

/-- Construct the whole exception code from the two internal deviation-comparison relations.
Their internal construction from the original Borel code remains a separate obligation. -/
theorem Code.densityException_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (c : Code) (hc : c.val.labelGraph ∈ M) (D₀ D₁ : ZFSet.{u}) (hD₀ : D₀ ∈ M) (hD₁ : D₁ ∈ M)
    (hspec : ∀ (t : Bool) k N j,
      pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ (if t then D₁ else D₀) ↔
        N ≤ (NatListCode.decode j).length ∧
          1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) (if t then 1 else 0)) :
    c.densityException.val.labelGraph ∈ M := by
  have hzero := Code.nonconvergence_labelGraph_mem D₀ (cylinderDensity c.cantor) 0
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using hspec false)
    hM hinf hpair hunion hpower hsep hrep hD₀
  have hone := Code.nonconvergence_labelGraph_mem D₁ (cylinderDensity c.cantor) 1
    (by simpa only [↓reduceIte] using hspec true)
    hM hinf hpair hunion hpower hsep hrep hD₁
  exact Code.sup_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ _
    (Code.inf_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ _ hc hone)
    (Code.inf_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ _
      (Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc) hzero)

end PolishSpaceBook.BorelExpression
