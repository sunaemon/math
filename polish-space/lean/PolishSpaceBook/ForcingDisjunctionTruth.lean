module

public import PolishSpaceBook.ForcingFormulaTruth

@[expose] public section

/-! # The disjunction truth step through negation and conjunction -/
noncomputable section
namespace PolishSpaceBook.ForcingFormulas
open FirstOrder Language ZFSet ForcingNames ForcingAtomic
universe u
variable (P M : ZFSet.{u}) [Preorder (Condition P)]

/-- Density-saturation makes the implication encoding of disjunction agree with
its De Morgan encoding at the level of forcing conditions. -/
lemma force_or_eq_demorgan {n : ℕ} (φ ψ : Formula n) (xs : Fin n → Name P M) :
    force P M (φ ⊔ ψ) xs = force P M ((φ.not ⊓ ψ.not).not) xs := by
  rw [force_not, force_and, force_not, force_not]
  change forcingImp (forcingNeg (force P M φ xs)) (force P M ψ xs) = _
  ext p
  constructor
  · intro hp q hqp hq
    exact hq.2 q le_rfl (hp q hqp hq.1)
  · intro hp q hqp hq
    by_contra hqb
    obtain ⟨r, hrq, hr⟩ := not_forcing_refinement (force_saturated P M ψ xs) hqb
    exact hp r (hrq.trans hqp) ⟨forcingNeg_lower _ hrq hq, hr⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \emph{Disjunction.} $\varphi \lor \psi \equiv \neg(\neg\varphi \land \neg\psi)$ reduces this to negation and
    conjunction. Direct verification from the disjunction clause matches the same outcome.
-/
/-- Apply the negative truth step, the conjunction truth step, then the negative
truth step once more, exactly as in the book's disjunction argument. -/
theorem formula_or_truth_by_demorgan (G : Order.PFilter (Condition P))
    (hG : MeetsFormulaTests P M G) {n : ℕ} (φ ψ : Formula n) (xs : Fin n → Name P M)
    (hφ : (∃ p ∈ G, p ∈ force P M φ xs) ↔
      φ.Realize Empty.elim (fun i => evalName P M G (xs i)))
    (hψ : (∃ p ∈ G, p ∈ force P M ψ xs) ↔
      ψ.Realize Empty.elim (fun i => evalName P M G (xs i))) :
    (∃ p ∈ G, p ∈ force P M (φ ⊔ ψ) xs) ↔
      (φ ⊔ ψ).Realize Empty.elim (fun i => evalName P M G (xs i)) := by
  classical
  have hnφ := formula_not_truth_step P M G hG φ xs hφ
  have hnψ := formula_not_truth_step P M G hG ψ xs hψ
  have ha := formula_and_truth_step P M G φ.not ψ.not xs hnφ hnψ
  have hn := formula_not_truth_step P M G hG (φ.not ⊓ ψ.not) xs ha
  rw [force_or_eq_demorgan P M φ ψ xs]
  simpa only [BoundedFormula.realize_not, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, not_and_or, not_not] using hn

end PolishSpaceBook.ForcingFormulas
