module

public import PolishSpaceBook.LambdaRelativePredicates

@[expose] public section

/-! # Numerical composition with one fixed input parameter -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Feed one numerical output into another program, keeping the same parameter. -/
def relativeComposeProgram (P Q : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app (app P (var 1)) (app (app Q (var 1)) (var 2))))

theorem relativeComposeProgram_closed {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) :
    (relativeComposeProgram P Q).Closed := by
  unfold relativeComposeProgram Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [hP,hQ]
  decide

theorem relativeComposeProgram_runs {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed)
    {ε : ℕ → ℕ} {n m r : ℕ} (hq : OracleRuns ε Q n m) (hp : OracleRuns ε P m r) :
    OracleRuns ε (relativeComposeProgram P Q) n r := by
  have h₁ : Beta (app (relativeComposeProgram P Q) (var 0))
      (lam 2 (app (app P (var 0)) (app (app Q (var 0)) (var 2)))) := by
    have he : (lam 2 (app (app P (var 1)) (app (app Q (var 1)) (var 2)))).subst 1 (var 0) =
        lam 2 (app (app P (var 0)) (app (app Q (var 0)) (var 2))) := by
      rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
      simp [subst_app,subst_var,subst_closed _ _ _ hP,subst_closed _ _ _ hQ]
    rw [← he]
    exact Beta.contract 1 _ _
  have h₂ : Beta
      (app (lam 2 (app (app P (var 0)) (app (app Q (var 0)) (var 2)))) (numeral n))
      (app (app P (var 0)) (app (app Q (var 0)) (numeral n))) := by
    have he : (app (app P (var 0)) (app (app Q (var 0)) (var 2))).subst 2 (numeral n) =
        app (app P (var 0)) (app (app Q (var 0)) (numeral n)) := by
      simp [subst_app,subst_var,subst_closed _ _ _ hP,subst_closed _ _ _ hQ]
    rw [← he]
    exact Beta.contract 2 _ _
  exact (Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
    ((oracle_steps_app_right _ hq).trans hp)
end PolishSpaceBook.NamedLambda.AlphaTerm

namespace PolishSpaceBook.LambdaRelative
open NamedLambda NamedLambda.AlphaTerm
universe u v w

theorem Computes.comp {α : Type u} {β : Type v} {γ : Type w}
    [Encodable α] [Encodable β] [Encodable γ] {ε : ℕ → ℕ} {P Q : AlphaTerm}
    {f : β → γ} {g : α → β} (hP : Computes ε P f) (hQ : Computes ε Q g) :
    Computes ε (relativeComposeProgram P Q) (fun a => f (g a)) :=
  ⟨relativeComposeProgram_closed hP.1 hQ.1,
    fun a => relativeComposeProgram_runs hP.1 hQ.1 (hQ.2 a) (hP.2 (g a))⟩

theorem Decides.precomp {α : Type u} {β : Type v} [Encodable α] [Encodable β]
    {ε : ℕ → ℕ} {P Q : AlphaTerm} {R : β → Prop} {g : α → β}
    (hP : Decides ε P R) (hQ : Computes ε Q g) :
    Decides ε (relativeComposeProgram P Q) (fun a => R (g a)) := by
  refine ⟨relativeComposeProgram_closed hP.1 hQ.1,fun a => ⟨?_,?_⟩⟩
  · intro h
    exact relativeComposeProgram_runs hP.1 hQ.1 (hQ.2 a) ((hP.2 (g a)).1 h)
  · intro h
    exact relativeComposeProgram_runs hP.1 hQ.1 (hQ.2 a) ((hP.2 (g a)).2 h)

/-- Substitute a computable accessor for the old parameter. -/
theorem Decides.changeParameter {α : Type u} [Encodable α]
    {ε δ : ℕ → ℕ} {P Q : AlphaTerm} {R : α → Prop}
    (hP : Decides ε P R) (hQ : Computes δ Q ε) :
    Decides δ (compositionProgram P Q) R := by
  refine ⟨compositionProgram_closed hP.1 hQ.1,fun a => ⟨?_,?_⟩⟩
  · intro h
    exact compositionProgram_runs hP.1 hQ.1 ((hP.2 a).1 h) hQ.2
  · intro h
    exact compositionProgram_runs hP.1 hQ.1 ((hP.2 a).2 h) hQ.2
end PolishSpaceBook.LambdaRelative
