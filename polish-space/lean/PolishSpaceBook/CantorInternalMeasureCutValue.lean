module

public import PolishSpaceBook.CantorInternalBorelMeasureFormula

@[expose] public section

/-! # Nonnegative measure values are determined by their internal rational cuts -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
universe u

lemma eq_of_nonneg_fraction_cuts (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ a b : ℕ, 0 < b → ((a : ℝ) / b < x ↔ (a : ℝ) / b < y)) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · obtain ⟨a, b, hb, hxa, hay⟩ :=
      (lt_iff_nat_fraction_margin x ((x + y) / 2) hx).mp (by linarith)
    have hax := (h a b hb).mpr (by linarith)
    linarith
  · obtain ⟨a, b, hb, hya, hax⟩ :=
      (lt_iff_nat_fraction_margin y ((x + y) / 2) hy).mp (by linarith)
    have hay := (h a b hb).mp (by linarith)
    linarith

/-- An external real specified by the model's answers to all nonnegative rational queries.
This predicate does not assume a measure on the external set of old points. -/
def HasInternalBorelMeasureCut (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ a b : ℕ, 0 < b → ∃ p : Fin 10 → M,
    Subtype.val ∘ p = borelMeasureCutValues M c hw a b ∧
      (borelMeasureLowerCutFormula.Realize Empty.elim p ↔ (a : ℝ) / b < r)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: corollary
  title: Determination by internal rational cuts
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The theorem shows that the actual measure satisfies these equivalences. If two nonnegative reals
    were different, a nonnegative rational strictly between them would belong to exactly one of their
    strict lower cuts. This contradicts the assumed equivalences, proving uniqueness.
-/
theorem hasInternalBorelMeasureCut_iff {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (r : ℝ) : HasInternalBorelMeasureCut M c hc.2.2.2.2.2 r ↔
      r = fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  constructor
  · rintro ⟨hr, hcuts⟩
    apply eq_of_nonneg_fraction_cuts r _ hr measureReal_nonneg
    intro a b hb
    obtain ⟨p, hp, hcut⟩ := hcuts a b hb
    exact hcut.symm.trans
      (realize_borelMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM a b hb p hp)
  · rintro rfl
    refine ⟨measureReal_nonneg, ?_⟩
    intro a b hb
    let p (i : Fin 10) : M := ⟨borelMeasureCutValues M c hc.2.2.2.2.2 a b i,
      borelMeasureCutValues_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM a b i⟩
    exact ⟨p, rfl, realize_borelMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
      a b hb p rfl⟩

end PolishSpaceBook.CantorTreeMeasure
