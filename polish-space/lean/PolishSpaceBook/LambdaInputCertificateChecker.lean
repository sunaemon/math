module

public import PolishSpaceBook.LambdaQuerySuccessors
public import PolishSpaceBook.LambdaBindingCodes

@[expose] public section

/-! # Closed finite-table certificate checker

The table is numerical data. This checker validates the proposed reduction;
checking its stored answers against an input name is a separate operation.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

set_option maxRecDepth 4096

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    The certificate fold can now use this one-step tester. Define
    $$\begin{aligned}
    F(t,a,b,r,e,d)&:=\LambdaZeroTest\,(\LambdaAlphaTest\,e\,a)\,\ChurchNumeral{0}\\
     &\quad\bigl(\LambdaZeroTest\,(\LambdaInputStepTest\,t\,a\,b)\,\ChurchNumeral{0}\,(rbd)\bigr),\\
    H_c&:=\lambdaab{t}{\lambdaab{c}{\lambdaab{r}{\lambdaab{e}{\lambdaab{d}{
     F(t,\LambdaNumericProjection{1}\,c,\LambdaNumericProjection{2}\,c,r,e,d)}}}}},\\
    \LambdaInputCertificateCheck&:=\lambdaab{t}{\lambdaab{c}{
     \LambdaListRecursor\,(H_ct)\,\LambdaAlphaTest\,c}}.
    \end{aligned}$$
    Expand $F$ in the handler. The list-fold value remains a function of the current source and fixed target, so both endpoints are supplied after the table and certificate. The empty certificate compares its endpoints up to alpha-equivalence. At a nonempty certificate, a failed join or failed one-step check returns zero; otherwise the tail function receives the new source. All these terms are closed.
-/
def inputCertificateStepBody (T A B R M N : AlphaTerm) : AlphaTerm :=
  (app (app (app zeroTestTerm (app (app alphaDecisionTerm M) A)) (numeral 0)) (app (app (app zeroTestTerm (app (app (app inputStepTestTerm T) A) B)) (numeral 0)) (app (app R B) N)))

theorem inputCertificateStepBody_fv (T A B R M N : AlphaTerm) :
    (inputCertificateStepBody T A B R M N).fv = T.fv ∪ A.fv ∪ B.fv ∪ R.fv ∪ M.fv ∪ N.fv := by
  ext x
  simp only [inputCertificateStepBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (alphaDecisionTerm).fv = ∅ from alphaDecisionTerm_closed), (show (inputStepTestTerm).fv = ∅ from inputStepTestTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem inputCertificateStepBody_subst (T A B R M N W : AlphaTerm) (x : ℕ) :
    (inputCertificateStepBody T A B R M N).subst x W =
      inputCertificateStepBody (T.subst x W) (A.subst x W) (B.subst x W) (R.subst x W) (M.subst x W) (N.subst x W) := by
  simp only [inputCertificateStepBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ alphaDecisionTerm_closed, subst_closed _ _ _ inputStepTestTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def inputCertificateStepTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody (var 30) (var 31) (var 32) (var 33) (var 34) (var 35))))))))

@[simp] theorem inputCertificateStepTerm_closed : inputCertificateStepTerm.Closed := by
  unfold inputCertificateStepTerm Closed
  simp only [fv_lam, inputCertificateStepBody_fv, fv_var]
  decide

theorem inputCertificateStepTerm_start {T A B R M N : AlphaTerm}
    (hT : T.Closed) (hA : A.Closed) (hB : B.Closed) (hR : R.Closed) (hM : M.Closed) (hN : N.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app (app (app inputCertificateStepTerm T) A) B) R) M) N)
      (inputCertificateStepBody T A B R M N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfA : A.fv = ∅ := hA
  have hfB : B.fv = ∅ := hB
  have hfR : R.fv = ∅ := hR
  have hfM : M.fv = ∅ := hM
  have hfN : N.fv = ∅ := hN
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody (var 30) (var 31) (var 32) (var 33) (var 34) (var 35)))))))) T) (lam 31 (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T (var 31) (var 32) (var 33) (var 34) (var 35))))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody (var 30) (var 31) (var 32) (var 33) (var 34) (var 35))))))) T using 1
    simp [subst_lam_fresh, subst_var, inputCertificateStepBody_subst, hfT]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T (var 31) (var 32) (var 33) (var 34) (var 35))))))) A) (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T A (var 32) (var 33) (var 34) (var 35)))))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T (var 31) (var 32) (var 33) (var 34) (var 35)))))) A using 1
    simp [subst_lam_fresh, subst_var, inputCertificateStepBody_subst, subst_closed, hT, hfA]
  have h2 : Beta (app (lam 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T A (var 32) (var 33) (var 34) (var 35)))))) B) (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T A B (var 33) (var 34) (var 35))))) := by
    convert Beta.contract 32 (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T A (var 32) (var 33) (var 34) (var 35))))) B using 1
    simp [subst_lam_fresh, subst_var, inputCertificateStepBody_subst, subst_closed, hT, hA, hfB]
  have h3 : Beta (app (lam 33 (lam 34 (lam 35 (inputCertificateStepBody T A B (var 33) (var 34) (var 35))))) R) (lam 34 (lam 35 (inputCertificateStepBody T A B R (var 34) (var 35)))) := by
    convert Beta.contract 33 (lam 34 (lam 35 (inputCertificateStepBody T A B (var 33) (var 34) (var 35)))) R using 1
    simp [subst_lam_fresh, subst_var, inputCertificateStepBody_subst, subst_closed, hT, hA, hB, hfR]
  have h4 : Beta (app (lam 34 (lam 35 (inputCertificateStepBody T A B R (var 34) (var 35)))) M) (lam 35 (inputCertificateStepBody T A B R M (var 35))) := by
    convert Beta.contract 34 (lam 35 (inputCertificateStepBody T A B R (var 34) (var 35))) M using 1
    simp [subst_lam_fresh, subst_var, inputCertificateStepBody_subst, subst_closed, hT, hA, hB, hR, hfM]
  have h5 : Beta (app (lam 35 (inputCertificateStepBody T A B R M (var 35))) N) (inputCertificateStepBody T A B R M N) := by
    convert Beta.contract 35 (inputCertificateStepBody T A B R M (var 35)) N using 1
    simp [subst_var, inputCertificateStepBody_subst, subst_closed, hT, hA, hB, hR, hM]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) A) B) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) B) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h2) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h3) M) N).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h4) N).trans
  exact (Relation.ReflTransGen.single h5)

def inputCertificateHandlerBody (T C R M N : AlphaTerm) : AlphaTerm :=
  (app (app (app (app (app (app inputCertificateStepTerm T) (app (numericalProjectionTerm true) C)) (app (numericalProjectionTerm false) C)) R) M) N)

theorem inputCertificateHandlerBody_fv (T C R M N : AlphaTerm) :
    (inputCertificateHandlerBody T C R M N).fv = T.fv ∪ C.fv ∪ R.fv ∪ M.fv ∪ N.fv := by
  ext x
  simp only [inputCertificateHandlerBody, fv_app, (show (inputCertificateStepTerm).fv = ∅ from inputCertificateStepTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem inputCertificateHandlerBody_subst (T C R M N W : AlphaTerm) (x : ℕ) :
    (inputCertificateHandlerBody T C R M N).subst x W =
      inputCertificateHandlerBody (T.subst x W) (C.subst x W) (R.subst x W) (M.subst x W) (N.subst x W) := by
  simp only [inputCertificateHandlerBody, subst_app, subst_closed _ _ _ inputCertificateStepTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def inputCertificateHandlerTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody (var 30) (var 31) (var 32) (var 33) (var 34)))))))

@[simp] theorem inputCertificateHandlerTerm_closed : inputCertificateHandlerTerm.Closed := by
  unfold inputCertificateHandlerTerm Closed
  simp only [fv_lam, inputCertificateHandlerBody_fv, fv_var]
  decide

theorem inputCertificateHandlerTerm_start {T C R M N : AlphaTerm}
    (hT : T.Closed) (hC : C.Closed) (hR : R.Closed) (hM : M.Closed) (hN : N.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app (app inputCertificateHandlerTerm T) C) R) M) N)
      (inputCertificateHandlerBody T C R M N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfC : C.fv = ∅ := hC
  have hfR : R.fv = ∅ := hR
  have hfM : M.fv = ∅ := hM
  have hfN : N.fv = ∅ := hN
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody (var 30) (var 31) (var 32) (var 33) (var 34))))))) T) (lam 31 (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody T (var 31) (var 32) (var 33) (var 34)))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody (var 30) (var 31) (var 32) (var 33) (var 34)))))) T using 1
    simp [subst_lam_fresh, subst_var, inputCertificateHandlerBody_subst, hfT]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody T (var 31) (var 32) (var 33) (var 34)))))) C) (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody T C (var 32) (var 33) (var 34))))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody T (var 31) (var 32) (var 33) (var 34))))) C using 1
    simp [subst_lam_fresh, subst_var, inputCertificateHandlerBody_subst, subst_closed, hT, hfC]
  have h2 : Beta (app (lam 32 (lam 33 (lam 34 (inputCertificateHandlerBody T C (var 32) (var 33) (var 34))))) R) (lam 33 (lam 34 (inputCertificateHandlerBody T C R (var 33) (var 34)))) := by
    convert Beta.contract 32 (lam 33 (lam 34 (inputCertificateHandlerBody T C (var 32) (var 33) (var 34)))) R using 1
    simp [subst_lam_fresh, subst_var, inputCertificateHandlerBody_subst, subst_closed, hT, hC, hfR]
  have h3 : Beta (app (lam 33 (lam 34 (inputCertificateHandlerBody T C R (var 33) (var 34)))) M) (lam 34 (inputCertificateHandlerBody T C R M (var 34))) := by
    convert Beta.contract 33 (lam 34 (inputCertificateHandlerBody T C R (var 33) (var 34))) M using 1
    simp [subst_lam_fresh, subst_var, inputCertificateHandlerBody_subst, subst_closed, hT, hC, hR, hfM]
  have h4 : Beta (app (lam 34 (inputCertificateHandlerBody T C R M (var 34))) N) (inputCertificateHandlerBody T C R M N) := by
    convert Beta.contract 34 (inputCertificateHandlerBody T C R M (var 34)) N using 1
    simp [subst_var, inputCertificateHandlerBody_subst, subst_closed, hT, hC, hR, hM]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) C) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h2) M) N).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h3) N).trans
  exact (Relation.ReflTransGen.single h4)

def inputCertificateBody (T C : AlphaTerm) : AlphaTerm :=
  (app (app (app listRecursorTerm (app inputCertificateHandlerTerm T)) alphaDecisionTerm) C)

theorem inputCertificateBody_fv (T C : AlphaTerm) :
    (inputCertificateBody T C).fv = T.fv ∪ C.fv := by
  ext x
  simp only [inputCertificateBody, fv_app, (show (listRecursorTerm).fv = ∅ from listRecursorTerm_closed), (show (inputCertificateHandlerTerm).fv = ∅ from inputCertificateHandlerTerm_closed), (show (alphaDecisionTerm).fv = ∅ from alphaDecisionTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem inputCertificateBody_subst (T C W : AlphaTerm) (x : ℕ) :
    (inputCertificateBody T C).subst x W =
      inputCertificateBody (T.subst x W) (C.subst x W) := by
  simp only [inputCertificateBody, subst_app, subst_closed _ _ _ listRecursorTerm_closed, subst_closed _ _ _ inputCertificateHandlerTerm_closed, subst_closed _ _ _ alphaDecisionTerm_closed]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We implement the finite-table reduction tests by closed lambda terms. At this stage the answer table is numerical data:
    the programs inspect the stored pairs without querying any input name. Agreement of these stored answers with the actual
    name is the separate finite check in §{sec:lambda-input-certificates}. Choose the distinguished input variable to be
    $o=x_0$, whose syntax code is zero. All other syntax codes are positive.
-/
def inputCertificateTerm : AlphaTerm := (lam 30 (lam 31 (inputCertificateBody (var 30) (var 31))))

@[simp] theorem inputCertificateTerm_closed : inputCertificateTerm.Closed := by
  unfold inputCertificateTerm Closed
  simp only [fv_lam, inputCertificateBody_fv, fv_var]
  decide

theorem inputCertificateTerm_start {T C : AlphaTerm}
    (hT : T.Closed) (hC : C.Closed) :
    Relation.ReflTransGen Beta (app (app inputCertificateTerm T) C)
      (inputCertificateBody T C) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfC : C.fv = ∅ := hC
  have h0 : Beta (app (lam 30 (lam 31 (inputCertificateBody (var 30) (var 31)))) T) (lam 31 (inputCertificateBody T (var 31))) := by
    convert Beta.contract 30 (lam 31 (inputCertificateBody (var 30) (var 31))) T using 1
    simp [subst_lam_fresh, subst_var, inputCertificateBody_subst, hfT]
  have h1 : Beta (app (lam 31 (inputCertificateBody T (var 31))) C) (inputCertificateBody T C) := by
    convert Beta.contract 31 (inputCertificateBody T (var 31)) C using 1
    simp [subst_var, inputCertificateBody_subst, subst_closed, hT]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) C).trans
  exact (Relation.ReflTransGen.single h1)


def inputCertificateValue (t : Term.AnswerTable) : List (Term × Term) → AlphaTerm
  | [] => alphaDecisionTerm
  | (A,B) :: cs => app (app (app inputCertificateHandlerTerm (numeral (Term.answerTableCode t)))
      (numeral (Nat.pair A.code B.code))) (inputCertificateValue t cs)

theorem inputCertificateValue_closed (t : Term.AnswerTable) (cs : List (Term × Term)) :
    (inputCertificateValue t cs).Closed := by
  induction cs with
  | nil => exact alphaDecisionTerm_closed
  | cons c cs ih =>
    cases c
    exact closed_app (closed_app (closed_app inputCertificateHandlerTerm_closed (numeral_closed _))
      (numeral_closed _)) ih

theorem inputCertificateTerm_value (t : Term.AnswerTable) (c : ℕ) :
    Relation.ReflTransGen Beta
      (app (app inputCertificateTerm (numeral (Term.answerTableCode t))) (numeral c))
      (inputCertificateValue t (Term.decodeCertificate c)) := by
  apply (inputCertificateTerm_start (numeral_closed _) (numeral_closed _)).trans
  have h := listRecursorTerm_apply
    (closed_app inputCertificateHandlerTerm_closed (numeral_closed (Term.answerTableCode t)))
    alphaDecisionTerm_closed
    (fun xs => inputCertificateValue t (xs.map (fun a =>
      (Term.decode (Nat.unpair a).1, Term.decode (Nat.unpair a).2)))) .refl
    (fun a xs => by
      simp only [List.map_cons, inputCertificateValue, Term.code_decode, Nat.pair_unpair]
      exact .refl) (NatListCode.decode c)
  simpa only [inputCertificateBody, NatListCode.encode_decode, ← Term.decodeCertificate_eq_listDecode] using h

private theorem inputCertificateStepTerm_code (t : Term.AnswerTable) {R : AlphaTerm} (hc : R.Closed)
    (cs : List (Term × Term))
    (hR : ∀ M N, Relation.ReflTransGen Beta (app (app R (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkInputCertificate t M N cs then 1 else 0))) (A B M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app (app (app (app inputCertificateStepTerm (numeral (Term.answerTableCode t)))
        (numeral A.code)) (numeral B.code)) R) (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkInputCertificate t M N ((A,B) :: cs) then 1 else 0)) := by
  apply (inputCertificateStepTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _) hc
    (numeral_closed _) (numeral_closed _)).trans
  unfold inputCertificateStepBody
  apply (beta_steps_app_left (beta_steps_app_left
    (beta_steps_app_right zeroTestTerm (alphaDecisionTerm_code M A)) _) _).trans
  by_cases ha : M.Alpha A
  · simp only [ite_eq_left ha]
    apply (branch_succ 0 _ _).trans
    apply (beta_steps_app_left (beta_steps_app_left
      (beta_steps_app_right zeroTestTerm (inputStepTestTerm_code t A B)) _) _).trans
    by_cases hb : Term.InputStep t A B
    · have hm := (Term.mem_inputSuccessors_iff t A B).mpr hb
      simp only [ite_eq_left hb]
      apply (branch_succ 0 _ _).trans
      simpa only [Term.checkInputCertificate, decide_eq_true ha, decide_eq_true hm,
        Bool.true_and] using hR B N
    · have hm : B ∉ Term.inputSuccessors t A :=
        fun h => hb ((Term.mem_inputSuccessors_iff t A B).mp h)
      simp only [ite_eq_right hb, Term.checkInputCertificate, decide_eq_true ha, decide_eq_false hm,
        Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false]
      exact branch_zero _ _ (by rw [numeral_closed]; simp)
  · simp only [ite_eq_right ha, Term.checkInputCertificate, decide_eq_false ha, Bool.false_and,
      Bool.false_eq_true, ite_false]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For a fixed table $t$, define closed values recursively by
    $$\begin{aligned}
    W_{t,[]}&:=\LambdaAlphaTest,\\
    W_{t,(A,B)::c}&:=H_c\ChurchNumeral{\LambdaAnswerTableCode{t}}\,
     \ChurchNumeral{\NatPair{\LambdaSyntaxCode{A}}{\LambdaSyntaxCode{B}}}\,W_{t,c}.
    \end{aligned}$$
    List recursion reduces the checker on the table and certificate codes to this value. Induct on the certificate, keeping both endpoints arbitrary. For the empty certificate, alpha-equivalence decision is precisely the required check. In the nonempty case, projections extract the listed source and target. The alpha test checks the source join, the finite-table step program checks the listed step, and the induction hypothesis checks the tail at the new source. These are exactly the three conditions defining the certificate check. Coding and decoding extend the conclusion to arbitrary inputs. If a rejected certificate also reduced to one, it would have the two distinct numeral outputs zero and one, contradicting confluence and numeral injectivity.
    \end{proof}
-/
theorem inputCertificateValue_code (t : Term.AnswerTable) (cs : List (Term × Term)) (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (inputCertificateValue t cs) (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkInputCertificate t M N cs then 1 else 0)) := by
  induction cs generalizing M N with
  | nil =>
    simpa only [inputCertificateValue, Term.checkInputCertificate, decide_eq_true_eq]
      using alphaDecisionTerm_code M N
  | cons c cs ih =>
    obtain ⟨A,B⟩ := c
    apply (inputCertificateHandlerTerm_start (numeral_closed _) (numeral_closed _)
      (inputCertificateValue_closed t cs) (numeral_closed _) (numeral_closed _)).trans
    have hp := beta_steps_app_left (beta_steps_app_left (beta_steps_app_left
      (beta_steps_app
        (beta_steps_app_right (app inputCertificateStepTerm (numeral (Term.answerTableCode t)))
          (numericalProjectionTerm_pair true A.code B.code))
        (numericalProjectionTerm_pair false A.code B.code)) (inputCertificateValue t cs))
      (numeral M.code)) (numeral N.code)
    exact hp.trans (inputCertificateStepTerm_code t (inputCertificateValue_closed t cs) cs ih A B M N)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Finite-table certificate checking by a lambda term
-/
theorem inputCertificateTerm_code (t : Term.AnswerTable) (cs : List (Term × Term)) (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app (app inputCertificateTerm (numeral (Term.answerTableCode t)))
        (numeral (Term.certificateCode cs))) (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkInputCertificate t M N cs then 1 else 0)) := by
  have h := inputCertificateTerm_value t (Term.certificateCode cs)
  rw [Term.decode_certificateCode] at h
  exact (beta_steps_app_left (beta_steps_app_left h _) _).trans (inputCertificateValue_code t cs M N)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We implement the finite-table reduction tests by closed lambda terms. At this stage the answer table is numerical data:
    the programs inspect the stored pairs without querying any input name. Agreement of these stored answers with the actual
    name is the separate finite check in §{sec:lambda-input-certificates}. Choose the distinguished input variable to be
    $o=x_0$, whose syntax code is zero. All other syntax codes are positive.
-/
theorem inputCertificateTerm_apply (t c e d : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app (app inputCertificateTerm (numeral t)) (numeral c)) (numeral e)) (numeral d))
      (numeral (if Term.checkInputCertificate (Term.decodeAnswerTable t) (Term.decode e)
        (Term.decode d) (Term.decodeCertificate c) then 1 else 0)) := by
  have h := inputCertificateTerm_value (Term.decodeAnswerTable t) c
  rw [Term.answerTableCode_decode] at h
  have hc := inputCertificateValue_code (Term.decodeAnswerTable t)
    (Term.decodeCertificate c) (Term.decode e) (Term.decode d)
  simp only [Term.code_decode] at hc
  exact (beta_steps_app_left (beta_steps_app_left h (numeral e)) (numeral d)).trans hc

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Finite-table certificate checking by a lambda term
-/
theorem inputCertificateTerm_accepts_iff (t c e d : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app (app inputCertificateTerm (numeral t)) (numeral c)) (numeral e)) (numeral d))
      (numeral 1) ↔
    Term.checkInputCertificate (Term.decodeAnswerTable t) (Term.decode e)
      (Term.decode d) (Term.decodeCertificate c) = true := by
  have hc := inputCertificateTerm_apply t c e d
  constructor
  · intro h
    have he := numeral_output_unique h hc
    split_ifs at he with ht
    · exact ht
  · intro ht
    simpa only [ht, ite_true] using hc

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: corollary
  title: Input-query reductions certified by a closed checker
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Apply the finite-certificate equivalence of §{sec:lambda-input-certificates} and the exact acceptance assertion just proved. The coding inverses turn the finite witnesses into numerical inputs and recover them in the reverse direction.
    \end{proof}
-/
theorem oracle_steps_iff_lambda_certificate (p : ℕ → ℕ) (M N : Term) :
    Relation.ReflTransGen (OracleStep p) (mk M) (mk N) ↔
      ∃ t c : ℕ, Term.AnswersAgree p (Term.decodeAnswerTable t) ∧
        Relation.ReflTransGen Beta
          (app (app (app (app inputCertificateTerm (numeral t)) (numeral c))
            (numeral M.code)) (numeral N.code)) (numeral 1) := by
  rw [Term.oracle_steps_iff_certificate]
  constructor
  · rintro ⟨t,ht,cs,hcs⟩
    refine ⟨Term.answerTableCode t,Term.certificateCode cs,by simpa using ht,?_⟩
    apply (inputCertificateTerm_accepts_iff _ _ _ _).mpr
    simpa only [Term.decode_answerTableCode, Term.decode_code, Term.decode_certificateCode] using hcs
  · rintro ⟨t,c,ht,hc⟩
    refine ⟨Term.decodeAnswerTable t,ht,Term.decodeCertificate c,?_⟩
    simpa only [Term.decode_code] using (inputCertificateTerm_accepts_iff t c M.code N.code).mp hc

end PolishSpaceBook.NamedLambda.AlphaTerm
