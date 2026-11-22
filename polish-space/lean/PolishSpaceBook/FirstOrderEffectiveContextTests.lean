module

public import PolishSpaceBook.FirstOrderEffectiveContexts

@[expose] public section

/-! # Concrete lambda context tests interpreted over effective signatures -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda NamedLambda.AlphaTerm
open FirstOrderLambdaEncoding
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem context_membership_apply {a e : ℕ} {A : AlphaFormula L} {Γ : Context L}
    (ha : S.FormulaRep a A) (he : S.ContextRep e Γ) :
    letI := Classical.decEq (AlphaFormula L)
    Relation.ReflTransGen Beta (app (app ContextPrograms.memberTerm (numeral a)) (numeral e))
      (numeral (if A ∈ Γ then 1 else 0)) := by
  classical
  simpa only [S.contextRep_member ha he] using ContextPrograms.memberTerm_apply a e

theorem context_equality_apply {e d : ℕ} {Γ Δ : Context L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) :
    letI := Classical.decEq (AlphaFormula L)
    Relation.ReflTransGen Beta (app (app ContextPrograms.equalTerm (numeral e)) (numeral d))
      (numeral (if Γ = Δ then 1 else 0)) := by
  classical
  simpa only [S.contextRep_equal he hd] using ContextPrograms.equalTerm_apply e d

theorem context_freeVariable_apply {e : ℕ} {Γ : Context L} (he : S.ContextRep e Γ) (x : ℕ) :
    Relation.ReflTransGen Beta (app (app ContextPrograms.freeTerm (numeral x)) (numeral e))
      (numeral (if x ∈ Γ.fv then 1 else 0)) := by
  simpa only [S.contextRep_free he x] using ContextPrograms.freeTerm_apply x e

theorem context_substitution_apply {e d a r : ℕ} {Γ Δ : Context L} {A : AlphaFormula L} {t : L.Term ℕ}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (ha : S.FormulaRep a A)
    (hr : (Term.decode r).Alpha (S.encodeTerm t)) (x : ℕ) :
    letI := Classical.decEq (AlphaFormula L)
    Relation.ReflTransGen Beta
      (app (app ContextPrograms.equalTerm (numeral d))
        (numeral (Nat.pair ((Term.decode a).subst x (Term.decode r)).code e + 1)))
      (numeral (if Δ = insert (A.subst x t) Γ then 1 else 0)) := by
  classical
  simpa only [S.contextRep_substitution he hd ha hr x] using
    ContextPrograms.equalTerm_apply d (Nat.pair ((Term.decode a).subst x (Term.decode r)).code e + 1)

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
