module

public import PolishSpaceBook.ArithmeticRosserSyntax

@[expose] public section

/-! # A total lambda program for literal diagonal computation certificates -/

namespace PolishSpaceBook.NamedLambda.AlphaTerm

set_option maxRecDepth 4096

def diagonalCertificateBody (E B S : AlphaTerm) : AlphaTerm :=
  app (app (app certificateTerm S) (app (app programInputCodeTerm E) E))
    (app numeralCodeTerm B)

theorem diagonalCertificateBody_fv (E B S : AlphaTerm) :
    (diagonalCertificateBody E B S).fv = E.fv ∪ B.fv ∪ S.fv := by
  ext x
  simp only [diagonalCertificateBody, fv_app,
    (show certificateTerm.fv = ∅ from certificateTerm_closed),
    (show programInputCodeTerm.fv = ∅ from programInputCodeTerm_closed),
    (show numeralCodeTerm.fv = ∅ from numeralCodeTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem diagonalCertificateBody_subst (E B S W : AlphaTerm) (x : ℕ) :
    (diagonalCertificateBody E B S).subst x W =
      diagonalCertificateBody (E.subst x W) (B.subst x W) (S.subst x W) := by
  simp only [diagonalCertificateBody, subst_app, subst_closed _ _ _ certificateTerm_closed,
    subst_closed _ _ _ programInputCodeTerm_closed, subst_closed _ _ _ numeralCodeTerm_closed]

/-- This checks the supplied certificate `s` itself, without a bounded search. -/
def diagonalCertificateTerm : AlphaTerm :=
  lam 30 (lam 31 (lam 32 (diagonalCertificateBody (var 30) (var 31) (var 32))))

theorem diagonalCertificateTerm_closed : diagonalCertificateTerm.Closed := by
  unfold diagonalCertificateTerm Closed
  simp only [fv_lam, diagonalCertificateBody_fv, fv_var]
  decide

theorem diagonalCertificateTerm_start {E B S : AlphaTerm}
    (hE : E.Closed) (hB : B.Closed) :
    Relation.ReflTransGen Beta (app (app (app diagonalCertificateTerm E) B) S)
      (diagonalCertificateBody E B S) := by
  have hfE : E.fv = ∅ := hE
  have hfB : B.fv = ∅ := hB
  have h₀ : Beta
      (app (lam 30 (lam 31 (lam 32 (diagonalCertificateBody (var 30) (var 31) (var 32))))) E)
      (lam 31 (lam 32 (diagonalCertificateBody E (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (diagonalCertificateBody (var 30) (var 31) (var 32)))) E using 1
    simp [subst_lam_fresh, subst_var, diagonalCertificateBody_subst, hfE]
  have h₁ : Beta (app (lam 31 (lam 32 (diagonalCertificateBody E (var 31) (var 32)))) B)
      (lam 32 (diagonalCertificateBody E B (var 32))) := by
    convert Beta.contract 31 (lam 32 (diagonalCertificateBody E (var 31) (var 32))) B using 1
    simp [subst_lam_fresh, subst_var, diagonalCertificateBody_subst, hfB, subst_closed, hE]
  have h₂ : Beta (app (lam 32 (diagonalCertificateBody E B (var 32))) S)
      (diagonalCertificateBody E B S) := by
    convert Beta.contract 32 (diagonalCertificateBody E B (var 32)) S using 1
    simp [subst_var, diagonalCertificateBody_subst, subst_closed, hE, hB]
  exact (beta_steps_app_left (beta_steps_app_left (.single h₀) B) S).trans
    ((beta_steps_app_left (.single h₁) S).trans (.single h₂))

/-- On all three numerical inputs the closed program reduces to the Boolean
answer of the exact literal-certificate predicate represented in arithmetic. -/
theorem diagonalCertificateTerm_apply (e b s : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app diagonalCertificateTerm (numeral e)) (numeral b)) (numeral s))
      (numeral (if ArithmeticRosser.accepts e b s then 1 else 0)) := by
  apply (diagonalCertificateTerm_start (numeral_closed _) (numeral_closed _)).trans
  apply (beta_steps_app
    (beta_steps_app_right (app certificateTerm (numeral s)) (programInputCodeTerm_apply e e))
    (numeralCodeTerm_apply b)).trans
  have hc := certificateTerm_apply s (Term.app (Term.programSyntax e) (Term.churchNumeral e)).code
    (Term.churchNumeral b).code
  rw [Term.decode_code, Term.decode_code] at hc
  convert hc using 1
  rfl

end PolishSpaceBook.NamedLambda.AlphaTerm
