module

public import PolishSpaceBook.LambdaBetaSuccessors
public import PolishSpaceBook.LambdaBindingCodes

@[expose] public section

/-! # Checking finite beta-reduction certificates by a closed lambda term

A fold value is a function of the current source and fixed target. The empty
certificate compares their alpha-classes. Each nonempty step checks its source
join, checks the named beta step, and calls the tail function at the new source.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

-- The nested closed syntax-processing subprograms have deep definitional terms.
set_option maxRecDepth 4096

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Define
    $$\begin{aligned}
    T(a,b,r,e,d)&:=\LambdaZeroTest\,(\LambdaAlphaTest\,e\,a)\,\ChurchNumeral{0}\\
     &\quad\bigl(\LambdaZeroTest\,(\LambdaBetaStepTest\,a\,b)\,\ChurchNumeral{0}\,(rbd)\bigr),\\
    H&:=\lambdaab{c}{\lambdaab{r}{\lambdaab{e}{\lambdaab{d}{
     T(\LambdaNumericProjection{1}\,c,\LambdaNumericProjection{2}\,c,r,e,d)}}}},\\
    \LambdaCertificateCheck&:=\LambdaListFold{\LambdaAlphaTest}{H}.
    \end{aligned}$$
    Expand $T$ in $H$. The fold's base value compares the two endpoints. Its handler extracts the pair at the head, checks the alpha-equivalence at the join and the named beta step, and then passes the new source to the tail function. Either failed check returns zero. All displayed variables in $H$ are bound, so $H$ and $\LambdaCertificateCheck$ are closed.
-/
def certificateStepBody (A B R M N : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app (app alphaDecisionTerm M) A)) (numeral 0))
    (app (app (app zeroTestTerm (app (app betaStepTestTerm A) B)) (numeral 0))
      (app (app R B) N))

theorem certificateStepBody_fv (A B R M N : AlphaTerm) :
    (certificateStepBody A B R M N).fv = A.fv ∪ B.fv ∪ R.fv ∪ M.fv ∪ N.fv := by
  ext x
  simp only [certificateStepBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (alphaDecisionTerm).fv = ∅ from alphaDecisionTerm_closed), (show (betaStepTestTerm).fv = ∅ from betaStepTestTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem certificateStepBody_subst (A B R M N W : AlphaTerm) (x : ℕ) :
    (certificateStepBody A B R M N).subst x W =
      certificateStepBody (A.subst x W) (B.subst x W) (R.subst x W) (M.subst x W) (N.subst x W) := by
  simp only [certificateStepBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ alphaDecisionTerm_closed, subst_closed _ _ _ betaStepTestTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def certificateStepTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (certificateStepBody (var 30) (var 31) (var 32) (var 33) (var 34)))))))

@[simp] theorem certificateStepTerm_closed : certificateStepTerm.Closed := by
  unfold certificateStepTerm Closed
  simp only [fv_lam, certificateStepBody_fv, fv_var]
  decide

theorem certificateStepTerm_start {A B R M N : AlphaTerm}
    (hA : A.Closed) (hB : B.Closed) (hR : R.Closed) (hM : M.Closed) (hN : N.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app (app certificateStepTerm A) B) R) M) N)
      (certificateStepBody A B R M N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfA : A.fv = ∅ := hA
  have hfB : B.fv = ∅ := hB
  have hfR : R.fv = ∅ := hR
  have hfM : M.fv = ∅ := hM
  have hfN : N.fv = ∅ := hN
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (certificateStepBody (var 30) (var 31) (var 32) (var 33) (var 34))))))) A) (lam 31 (lam 32 (lam 33 (lam 34 (certificateStepBody A (var 31) (var 32) (var 33) (var 34)))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (lam 34 (certificateStepBody (var 30) (var 31) (var 32) (var 33) (var 34)))))) A using 1

    simp [subst_lam_fresh, subst_var, certificateStepBody_subst, hfA]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (lam 34 (certificateStepBody A (var 31) (var 32) (var 33) (var 34)))))) B) (lam 32 (lam 33 (lam 34 (certificateStepBody A B (var 32) (var 33) (var 34))))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (lam 34 (certificateStepBody A (var 31) (var 32) (var 33) (var 34))))) B using 1

    simp [subst_lam_fresh, subst_var, certificateStepBody_subst, subst_closed, hA, hfB]
  have h2 : Beta (app (lam 32 (lam 33 (lam 34 (certificateStepBody A B (var 32) (var 33) (var 34))))) R) (lam 33 (lam 34 (certificateStepBody A B R (var 33) (var 34)))) := by
    convert Beta.contract 32 (lam 33 (lam 34 (certificateStepBody A B (var 32) (var 33) (var 34)))) R using 1

    simp [subst_lam_fresh, subst_var, certificateStepBody_subst, subst_closed, hA, hB, hfR]
  have h3 : Beta (app (lam 33 (lam 34 (certificateStepBody A B R (var 33) (var 34)))) M) (lam 34 (certificateStepBody A B R M (var 34))) := by
    convert Beta.contract 33 (lam 34 (certificateStepBody A B R (var 33) (var 34))) M using 1

    simp [subst_lam_fresh, subst_var, certificateStepBody_subst, subst_closed, hA, hB, hR, hfM]
  have h4 : Beta (app (lam 34 (certificateStepBody A B R M (var 34))) N) (certificateStepBody A B R M N) := by
    convert Beta.contract 34 (certificateStepBody A B R M (var 34)) N using 1

    simp [subst_var, certificateStepBody_subst, subst_closed, hA, hB, hR, hM]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) B) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h2) M) N).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h3) N).trans
  exact (Relation.ReflTransGen.single h4)

def certificateHandlerBody (C R M N : AlphaTerm) : AlphaTerm :=
  app (app (app (app (app certificateStepTerm
    (app (numericalProjectionTerm true) C)) (app (numericalProjectionTerm false) C)) R) M) N

theorem certificateHandlerBody_fv (C R M N : AlphaTerm) :
    (certificateHandlerBody C R M N).fv = C.fv ∪ R.fv ∪ M.fv ∪ N.fv := by
  ext x
  simp only [certificateHandlerBody, fv_app, (show (certificateStepTerm).fv = ∅ from certificateStepTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem certificateHandlerBody_subst (C R M N W : AlphaTerm) (x : ℕ) :
    (certificateHandlerBody C R M N).subst x W =
      certificateHandlerBody (C.subst x W) (R.subst x W) (M.subst x W) (N.subst x W) := by
  simp only [certificateHandlerBody, subst_app, subst_closed _ _ _ certificateStepTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def certificateHandlerTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (certificateHandlerBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem certificateHandlerTerm_closed : certificateHandlerTerm.Closed := by
  unfold certificateHandlerTerm Closed
  simp only [fv_lam, certificateHandlerBody_fv, fv_var]
  decide

theorem certificateHandlerTerm_start {C R M N : AlphaTerm}
    (hC : C.Closed) (hR : R.Closed) (hM : M.Closed) (hN : N.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app certificateHandlerTerm C) R) M) N)
      (certificateHandlerBody C R M N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfC : C.fv = ∅ := hC
  have hfR : R.fv = ∅ := hR
  have hfM : M.fv = ∅ := hM
  have hfN : N.fv = ∅ := hN
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (certificateHandlerBody (var 30) (var 31) (var 32) (var 33)))))) C) (lam 31 (lam 32 (lam 33 (certificateHandlerBody C (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (certificateHandlerBody (var 30) (var 31) (var 32) (var 33))))) C using 1

    simp [subst_lam_fresh, subst_var, certificateHandlerBody_subst, hfC]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (certificateHandlerBody C (var 31) (var 32) (var 33))))) R) (lam 32 (lam 33 (certificateHandlerBody C R (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (certificateHandlerBody C (var 31) (var 32) (var 33)))) R using 1

    simp [subst_lam_fresh, subst_var, certificateHandlerBody_subst, subst_closed, hC, hfR]
  have h2 : Beta (app (lam 32 (lam 33 (certificateHandlerBody C R (var 32) (var 33)))) M) (lam 33 (certificateHandlerBody C R M (var 33))) := by
    convert Beta.contract 32 (lam 33 (certificateHandlerBody C R (var 32) (var 33))) M using 1

    simp [subst_lam_fresh, subst_var, certificateHandlerBody_subst, subst_closed, hC, hR, hfM]
  have h3 : Beta (app (lam 33 (certificateHandlerBody C R M (var 33))) N) (certificateHandlerBody C R M N) := by
    convert Beta.contract 33 (certificateHandlerBody C R M (var 33)) N using 1

    simp [subst_var, certificateHandlerBody_subst, subst_closed, hC, hR, hM]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) R) M) N).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) M) N).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) N).trans
  exact (Relation.ReflTransGen.single h3)

def certificateValue : List (Term × Term) → AlphaTerm
  | [] => alphaDecisionTerm
  | (A, B) :: cs => app (app certificateHandlerTerm (numeral (Nat.pair A.code B.code))) (certificateValue cs)

theorem certificateValue_closed (cs : List (Term × Term)) : (certificateValue cs).Closed := by
  induction cs with
  | nil => exact alphaDecisionTerm_closed
  | cons c cs ih => cases c; exact closed_app (closed_app certificateHandlerTerm_closed (numeral_closed _)) ih

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We now implement the preceding tests by closed lambda terms. A certificate code is the list code of its paired term
    codes, so the list recursor applies directly. Its value for a tail will be a function of two further inputs: the current
    source code and the fixed target code. Keeping these inputs open allows the source to change after each checked step.
-/
def certificateTerm : AlphaTerm := listFold alphaDecisionTerm certificateHandlerTerm

@[simp] theorem certificateTerm_closed : certificateTerm.Closed :=
  listFold_closed alphaDecisionTerm_closed certificateHandlerTerm_closed

theorem certificateTerm_value (c : ℕ) :
    Relation.ReflTransGen Beta (app certificateTerm (numeral c)) (certificateValue (Term.decodeCertificate c)) := by
  have h := listFold_apply alphaDecisionTerm_closed certificateHandlerTerm_closed
    (fun xs => certificateValue (xs.map (fun a =>
      (Term.decode (Nat.unpair a).1, Term.decode (Nat.unpair a).2)))) .refl
    (fun a xs => by
      simp only [List.map_cons, certificateValue, Term.code_decode, Nat.pair_unpair]
      exact .refl) (NatListCode.decode c)
  simpa only [certificateTerm, NatListCode.encode_decode, ← Term.decodeCertificate_eq_listDecode] using h

private theorem certificateStepTerm_code {R : AlphaTerm} (hc : R.Closed)
    (cs : List (Term × Term))
    (hR : ∀ M N, Relation.ReflTransGen Beta (app (app R (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkBetaCertificate M N cs then 1 else 0))) (A B M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app (app (app certificateStepTerm (numeral A.code)) (numeral B.code)) R)
        (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkBetaCertificate M N ((A, B) :: cs) then 1 else 0)) := by
  apply (certificateStepTerm_start (numeral_closed _) (numeral_closed _) hc
    (numeral_closed _) (numeral_closed _)).trans
  unfold certificateStepBody
  apply (beta_steps_app_left (beta_steps_app_left
    (beta_steps_app_right zeroTestTerm (alphaDecisionTerm_code M A)) _) _).trans
  by_cases ha : M.Alpha A
  · simp only [ite_eq_left ha]
    apply (branch_succ 0 _ _).trans
    apply (beta_steps_app_left (beta_steps_app_left
      (beta_steps_app_right zeroTestTerm (betaStepTestTerm_code A B)) _) _).trans
    by_cases hb : Term.Beta A B
    · have hm := (Term.mem_betaSuccessors_iff A B).mpr hb
      simp only [ite_eq_left hb]
      apply (branch_succ 0 _ _).trans
      simpa only [Term.checkBetaCertificate, decide_eq_true ha, decide_eq_true hm,
        Bool.true_and] using hR B N
    · have hm : B ∉ A.betaSuccessors := fun h => hb ((Term.mem_betaSuccessors_iff A B).mp h)
      simp only [ite_eq_right hb, Term.checkBetaCertificate, decide_eq_true ha, decide_eq_false hm,
        Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false]
      exact branch_zero _ _ (by rw [numeral_closed]; simp)
  · simp only [ite_eq_right ha, Term.checkBetaCertificate, decide_eq_false ha, Bool.false_and,
      Bool.false_eq_true, ite_false]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For each certificate $c$, define a closed term $W_c$ recursively by
    $$W_{[]}:=\LambdaAlphaTest,\qquad
    W_{(A,B)::c}:=H\ChurchNumeral{\NatPair{\LambdaSyntaxCode{A}}{\LambdaSyntaxCode{B}}}W_c.$$
    The list-recursion theorem gives the reduction of the checker on the certificate code to $W_c$. Induct on $c$, keeping both endpoints arbitrary, to compute the value of $W_c$ at their codes. For the empty list, the alpha-equivalence program gives exactly the acceptance condition. For a nonempty list, the two numerical projections extract the codes of $A,B$. If the source is not alpha-equivalent to $A$, the first test returns zero. Otherwise the second test checks membership of $B$ in the named reduct list of $A$. Failure again returns zero; success leaves $W_c$ applied to the codes of $B,N$, to which the induction hypothesis applies. These are exactly the three acceptance requirements for a nonempty certificate. The coding and decoding identities extend the calculation to all numerical inputs.
-/
theorem certificateValue_code (cs : List (Term × Term)) (M N : Term) :
    Relation.ReflTransGen Beta (app (app (certificateValue cs) (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkBetaCertificate M N cs then 1 else 0)) := by
  induction cs generalizing M N with
  | nil =>
    simpa only [certificateValue, Term.checkBetaCertificate, decide_eq_true_eq]
      using alphaDecisionTerm_code M N
  | cons c cs ih =>
    obtain ⟨A, B⟩ := c
    apply (certificateHandlerTerm_start (numeral_closed _) (certificateValue_closed cs)
      (numeral_closed _) (numeral_closed _)).trans
    have hp := beta_steps_app_left (beta_steps_app_left (beta_steps_app_left
      (beta_steps_app
        (beta_steps_app_right certificateStepTerm (numericalProjectionTerm_pair true A.code B.code))
        (numericalProjectionTerm_pair false A.code B.code)) (certificateValue cs)) (numeral M.code)) (numeral N.code)
    exact hp.trans (certificateStepTerm_code (certificateValue_closed cs) cs ih A B M N)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Certificate checking by a lambda term
-/
theorem certificateTerm_code (cs : List (Term × Term)) (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app certificateTerm (numeral (Term.certificateCode cs))) (numeral M.code)) (numeral N.code))
      (numeral (if Term.checkBetaCertificate M N cs then 1 else 0)) := by
  have h := certificateTerm_value (Term.certificateCode cs)
  rw [Term.decode_certificateCode] at h
  exact (beta_steps_app_left (beta_steps_app_left h _) _).trans (certificateValue_code cs M N)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Certificate checking by a lambda term
-/
theorem certificateTerm_apply (c e d : ℕ) :
    Relation.ReflTransGen Beta (app (app (app certificateTerm (numeral c)) (numeral e)) (numeral d))
      (numeral (if Term.checkBetaCertificate (Term.decode e) (Term.decode d) (Term.decodeCertificate c)
        then 1 else 0)) := by
  have h := (beta_steps_app_left (beta_steps_app_left (certificateTerm_value c) (numeral e)) (numeral d))
  apply h.trans
  simpa only [Term.code_decode] using certificateValue_code (Term.decodeCertificate c) (Term.decode e) (Term.decode d)


/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The finite-stage test is obtained by numerical primitive recursion. Set
    $$\begin{aligned}
    G&:=\lambdaab{e}{\lambdaab{d}{\lambdaab{k}{\lambdaab{r}{
     \LambdaZeroTest\,r\,(\LambdaCertificateCheck\,k\,e\,d)\,\ChurchNumeral{1}}}}},\\
    \LambdaBoundedBetaProgram&:=\lambdaab{e}{\lambdaab{d}{\lambdaab{s}{
     \LambdaRecursor\,(Ged)\,\ChurchNumeral{0}\,s}}}.
    \end{aligned}$$
    The initial value is zero because no certificate has yet been checked. At step $k$, a previous success is retained; otherwise the certificate with code $k$ is checked. Both programs are closed.
-/
def boundedBetaStepBody (E D K R : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm R)
    (app (app (app certificateTerm K) E) D)) (numeral 1)

theorem boundedBetaStepBody_fv (E D K R : AlphaTerm) :
    (boundedBetaStepBody E D K R).fv = E.fv ∪ D.fv ∪ K.fv ∪ R.fv := by
  ext x
  simp only [boundedBetaStepBody, fv_app, (show zeroTestTerm.fv = ∅ from zeroTestTerm_closed), (show certificateTerm.fv = ∅ from certificateTerm_closed) ,(show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem boundedBetaStepBody_subst (E D K R W : AlphaTerm) (x : ℕ) :
    (boundedBetaStepBody E D K R).subst x W =
      boundedBetaStepBody (E.subst x W) (D.subst x W) (K.subst x W) (R.subst x W) := by
  simp only [boundedBetaStepBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ certificateTerm_closed ,subst_closed _ _ _ (numeral_closed 1)]

def boundedBetaStepTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (boundedBetaStepBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem boundedBetaStepTerm_closed : boundedBetaStepTerm.Closed := by
  unfold boundedBetaStepTerm Closed
  simp only [fv_lam, boundedBetaStepBody_fv, fv_var]
  decide

theorem boundedBetaStepTerm_start {E D K R : AlphaTerm}
    (hE : E.Closed) (hD : D.Closed) (hK : K.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app boundedBetaStepTerm E) D) K) R)
      (boundedBetaStepBody E D K R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfD : D.fv = ∅ := hD
  have hfK : K.fv = ∅ := hK
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (boundedBetaStepBody (var 30) (var 31) (var 32) (var 33)))))) E) (lam 31 (lam 32 (lam 33 (boundedBetaStepBody E (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (boundedBetaStepBody (var 30) (var 31) (var 32) (var 33))))) E using 1

    simp [subst_lam_fresh, subst_var, boundedBetaStepBody_subst, hfE]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (boundedBetaStepBody E (var 31) (var 32) (var 33))))) D) (lam 32 (lam 33 (boundedBetaStepBody E D (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (boundedBetaStepBody E (var 31) (var 32) (var 33)))) D using 1

    simp [subst_lam_fresh, subst_var, boundedBetaStepBody_subst, subst_closed, hE, hfD]
  have h2 : Beta (app (lam 32 (lam 33 (boundedBetaStepBody E D (var 32) (var 33)))) K) (lam 33 (boundedBetaStepBody E D K (var 33))) := by
    convert Beta.contract 32 (lam 33 (boundedBetaStepBody E D (var 32) (var 33))) K using 1

    simp [subst_lam_fresh, subst_var, boundedBetaStepBody_subst, subst_closed, hE, hD, hfK]
  have h3 : Beta (app (lam 33 (boundedBetaStepBody E D K (var 33))) R) (boundedBetaStepBody E D K R) := by
    convert Beta.contract 33 (boundedBetaStepBody E D K (var 33)) R using 1

    simp [subst_var, boundedBetaStepBody_subst, subst_closed, hE, hD, hK]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) D) K) R).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) K) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) R).trans
  exact (Relation.ReflTransGen.single h3)

def boundedBetaBody (E D S : AlphaTerm) : AlphaTerm :=
  app (app (app recursorTerm (app (app boundedBetaStepTerm E) D)) (numeral 0)) S

theorem boundedBetaBody_fv (E D S : AlphaTerm) :
    (boundedBetaBody E D S).fv = E.fv ∪ D.fv ∪ S.fv := by
  ext x
  simp only [boundedBetaBody, fv_app, (show recursorTerm.fv = ∅ from recursorTerm_closed), (show boundedBetaStepTerm.fv = ∅ from boundedBetaStepTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem boundedBetaBody_subst (E D S W : AlphaTerm) (x : ℕ) :
    (boundedBetaBody E D S).subst x W =
      boundedBetaBody (E.subst x W) (D.subst x W) (S.subst x W) := by
  simp only [boundedBetaBody, subst_app, subst_closed _ _ _ recursorTerm_closed, subst_closed _ _ _ boundedBetaStepTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def boundedBetaTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (boundedBetaBody (var 30) (var 31) (var 32)))))

@[simp] theorem boundedBetaTerm_closed : boundedBetaTerm.Closed := by
  unfold boundedBetaTerm Closed
  simp only [fv_lam, boundedBetaBody_fv, fv_var]
  decide

theorem boundedBetaTerm_start {E D S : AlphaTerm}
    (hE : E.Closed) (hD : D.Closed) (hS : S.Closed) :
    Relation.ReflTransGen Beta (app (app (app boundedBetaTerm E) D) S)
      (boundedBetaBody E D S) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfD : D.fv = ∅ := hD
  have hfS : S.fv = ∅ := hS
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (boundedBetaBody (var 30) (var 31) (var 32))))) E) (lam 31 (lam 32 (boundedBetaBody E (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (boundedBetaBody (var 30) (var 31) (var 32)))) E using 1

    simp [subst_lam_fresh, subst_var, boundedBetaBody_subst, hfE]
  have h1 : Beta (app (lam 31 (lam 32 (boundedBetaBody E (var 31) (var 32)))) D) (lam 32 (boundedBetaBody E D (var 32))) := by
    convert Beta.contract 31 (lam 32 (boundedBetaBody E (var 31) (var 32))) D using 1

    simp [subst_lam_fresh, subst_var, boundedBetaBody_subst, subst_closed, hE, hfD]
  have h2 : Beta (app (lam 32 (boundedBetaBody E D (var 32))) S) (boundedBetaBody E D S) := by
    convert Beta.contract 32 (boundedBetaBody E D (var 32)) S using 1

    simp [subst_var, boundedBetaBody_subst, subst_closed, hE, hD]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) D) S).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) S).trans
  exact (Relation.ReflTransGen.single h2)

theorem boundedBetaTest_zero (M N : Term) : Term.boundedBetaTest M N 0 = false := rfl

theorem boundedBetaTest_succ (M N : Term) (k : ℕ) :
    Term.boundedBetaTest M N (k + 1) =
      (Term.boundedBetaTest M N k || Term.checkBetaCertificate M N (Term.decodeCertificate k)) := by
  simp only [Term.boundedBetaTest, List.range_succ, List.any_append,
    List.any_cons, List.any_nil, Bool.or_false]

private theorem boundedBetaStepTerm_code (M N : Term) (k : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app (app boundedBetaStepTerm (numeral M.code)) (numeral N.code)) (numeral k))
        (numeral (if Term.boundedBetaTest M N k then 1 else 0)))
      (numeral (if Term.boundedBetaTest M N (k + 1) then 1 else 0)) := by
  apply (boundedBetaStepTerm_start (numeral_closed _) (numeral_closed _)
    (numeral_closed _) (numeral_closed _)).trans
  unfold boundedBetaStepBody
  rw [boundedBetaTest_succ]
  cases h : Term.boundedBetaTest M N k with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Bool.false_or]
    apply (branch_zero _ _ (by rw [fv_app, fv_app, fv_app, certificateTerm_closed,
      numeral_closed, numeral_closed, numeral_closed]; simp)).trans
    simpa only [Term.decode_code] using certificateTerm_apply k M.code N.code
  | true =>
    simp only [Bool.true_or, ite_true]
    exact branch_succ 0 _ _

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    The stage-zero test is false. The test at stage $k+1$ is the disjunction of the test at stage $k$ and acceptance of the certificate with code $k$. The step program computes precisely this disjunction by the certificate-checking theorem and zero testing. Apply numerical primitive recursion with the numeral of this Boolean value as the state. It gives the asserted finite reduction for every stage, including stage zero. Decode arbitrary endpoint codes to obtain the general input statement.

    For the last equivalence, a finite reduction has a certificate, which is detected once the stage exceeds its code. Conversely, if $D_{M,N,s}$ reduces to $\ChurchNumeral{1}$, uniqueness of numeral outputs forces the stage test to be true: a false test would also give a reduction to $\ChurchNumeral{0}$. The finite-certificate criterion then gives the desired reduction of alpha-classes.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Finite-stage reduction testing by a lambda term
-/
theorem boundedBetaTerm_code (M N : Term) (s : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app boundedBetaTerm (numeral M.code)) (numeral N.code)) (numeral s))
      (numeral (if Term.boundedBetaTest M N s then 1 else 0)) := by
  apply (boundedBetaTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  have h := recursorTerm_apply
    (closed_app (closed_app boundedBetaStepTerm_closed (numeral_closed _)) (numeral_closed _))
    (fun k => numeral (if Term.boundedBetaTest M N k then 1 else 0))
    (fun _ => numeral_closed _) (boundedBetaStepTerm_code M N) s
  simpa only [boundedBetaBody, boundedBetaTest_zero, Bool.false_eq_true, ite_false] using h

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Finite-stage reduction testing by a lambda term
-/
theorem boundedBetaTerm_apply (e d s : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app boundedBetaTerm (numeral e)) (numeral d)) (numeral s))
      (numeral (if Term.boundedBetaTest (Term.decode e) (Term.decode d) s then 1 else 0)) := by
  simpa only [Term.code_decode] using boundedBetaTerm_code (Term.decode e) (Term.decode d) s

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Finite-stage reduction testing by a lambda term
-/
theorem beta_steps_iff_boundedBetaTerm (M N : Term) :
    Relation.ReflTransGen Beta (mk M) (mk N) ↔
      ∃ s, Relation.ReflTransGen Beta
        (app (app (app boundedBetaTerm (numeral M.code)) (numeral N.code)) (numeral s))
        (numeral 1) := by
  rw [Term.beta_steps_iff_bounded_test]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, by simpa only [hs, ite_true] using boundedBetaTerm_code M N s⟩
  · rintro ⟨s, hs⟩
    have h := numeral_output_unique (boundedBetaTerm_code M N s) hs
    refine ⟨s, ?_⟩
    cases hb : Term.boundedBetaTest M N s <;> simp_all

end PolishSpaceBook.NamedLambda.AlphaTerm
