module

public import PolishSpaceBook.FirstOrderHenkinLimit

@[expose] public section

/-!
# Every final-language formula comes from a finite stage

Round trips through positive stages eventually fix every symbol, hence every
finite term and formula. This also covers formulas containing closed parameters.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula Filter
universe u v
variable (L : Language.{u,v})

def henkinRoundTrip (n : ℕ) : henkinLanguage L →ᴸ henkinLanguage L :=
  (henkinInclusion L (n + 1)).comp (henkinRetraction L n)

theorem henkinRoundTrip_old (n : ℕ) :
    (henkinRoundTrip L n).comp (henkinInclusion L 0) = henkinInclusion L 0 := by
  rw [henkinRoundTrip, LHom.comp_assoc, henkinRetraction_stage L n 0 (Nat.zero_le _), henkinInclusion_stageMap]

theorem henkinRoundTrip_constant (a : henkinLabels L) (n : ℕ) (h : a.1 ≤ n) :
    (henkinRoundTrip L n).onFunction ((henkinStage L 0).con a) = (henkinStage L 0).con a := by
  change (henkinInclusion L (n + 1)).onFunction (henkinConstantAt L n a) = _
  rw [henkinConstantAt, dite_eq_left (Nat.succ_le_succ h)]
  change ((henkinInclusion L (n + 1)).comp (henkinStageMap L _)).onFunction _ = _
  rw [henkinInclusion_stageMap]
  rfl

theorem henkinRoundTrip_function {ar : ℕ} (f : (henkinLanguage L).Functions ar) :
    ∀ᶠ n : ℕ in atTop, (henkinRoundTrip L n).onFunction f = f := by
  rcases f with f | c
  · exact Eventually.of_forall (fun n => congrArg (fun g => g.onFunction f) (henkinRoundTrip_old L n))
  · cases ar with
    | zero => exact (eventually_ge_atTop c.1).mono (fun n hn => henkinRoundTrip_constant L c n hn)
    | succ ar => exact isEmptyElim c

theorem henkinRoundTrip_relation {ar : ℕ} (r : (henkinLanguage L).Relations ar) (n : ℕ) :
    (henkinRoundTrip L n).onRelation r = r := by
  rcases r with r | r
  · exact congrArg (fun g => g.onRelation r) (henkinRoundTrip_old L n)
  · exact isEmptyElim r

theorem henkinRoundTrip_term (t : (henkinLanguage L).Term ℕ) :
    ∀ᶠ n : ℕ in atTop, (henkinRoundTrip L n).onTerm t = t := by
  induction t with
  | var x => exact Eventually.of_forall (fun _ => rfl)
  | func f ts ih =>
    have hall := Filter.eventually_all.mpr ih
    filter_upwards [henkinRoundTrip_function L f, hall] with n hf ht
    simp only [LHom.onTerm, hf]
    congr 1
    exact funext ht

theorem henkinRoundTrip_formula (φ : Formula (henkinLanguage L)) :
    ∀ᶠ n : ℕ in atTop, φ.mapLanguage (henkinRoundTrip L n) = φ := by
  induction φ with
  | falsum => exact Eventually.of_forall (fun _ => rfl)
  | equal t r =>
    filter_upwards [henkinRoundTrip_term L t, henkinRoundTrip_term L r] with n ht hr
    simp only [Formula.mapLanguage, ht, hr]
  | rel R ts =>
    have hall := Filter.eventually_all.mpr (fun i => henkinRoundTrip_term L (ts i))
    filter_upwards [hall] with n ht
    simp only [Formula.mapLanguage, henkinRoundTrip_relation]
    congr 1
    exact funext ht
  | binary c φ ψ ihφ ihψ =>
    filter_upwards [ihφ, ihψ] with n hφ hψ
    simp only [Formula.mapLanguage, hφ, hψ]
  | quant q x φ ih =>
    filter_upwards [ih] with n hφ
    simp only [Formula.mapLanguage, hφ]

theorem henkinRoundTrip_alpha (φ : AlphaFormula (henkinLanguage L)) :
    ∀ᶠ n : ℕ in atTop, φ.mapLanguage (henkinRoundTrip L n) = φ := by
  induction φ using Quotient.inductionOn with
  | _ φ =>
    filter_upwards [henkinRoundTrip_formula L φ] with n hφ
    exact congrArg AlphaFormula.mk hφ

/-- A final-language formula has a representative at one positive finite stage. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Every $L_H$-formula belongs to some finite stage. Each symbol was introduced at a finite stage, and each term
    and formula uses only finitely many symbols. More explicitly, mapping to a sufficiently late stage by the
    preceding symbol map and then including back fixes every symbol occurring in the formula. Induction on terms
    and formulas shows that this round trip fixes the formula itself; the same holds for its $\alpha$-class.
    Thus an $L_H$-formula with free variables among $x$ is an $L_n$-formula for some $n$, and its Henkin axiom
    belongs to $T_{n+1}\IncludedIn S$. The construction also shows $T\IncludedIn S$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This covers closed parameters as well. If $\theta(x,\vec y)$ is an $L_H$-formula and $\vec r$ is a tuple of closed
    $L_H$-terms, then $\theta(x,\vec r)$ has free variables only among $x$ and belongs to a finite stage.
    Its Henkin axiom supplies a constant witnessing $\exists x\,\theta(x,\vec r)$.
-/
theorem exists_henkinStage_formula (φ : AlphaFormula (henkinLanguage L)) :
    ∃ (n : ℕ) (ψ : AlphaFormula (henkinStage L (n + 1))), ψ.mapLanguage (henkinInclusion L (n + 1)) = φ := by
  obtain ⟨n, hn⟩ := (henkinRoundTrip_alpha L φ).exists
  exact ⟨n, φ.mapLanguage (henkinRetraction L n), by simpa [mapLanguage_comp, henkinRoundTrip] using hn⟩

end PolishSpaceBook.NamedFirstOrder
