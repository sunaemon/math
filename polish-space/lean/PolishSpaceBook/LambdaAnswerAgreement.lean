module

public import PolishSpaceBook.LambdaOracleLists
public import PolishSpaceBook.LambdaInputCertificateChecker

@[expose] public section

/-! # Comparing a finite answer table with an actual input name -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

set_option maxRecDepth 4096

theorem Closed.input_fv {M : AlphaTerm} (hM : M.Closed) : M.fv ⊆ {0} := by
  rw [hM]
  exact Finset.empty_subset _

def answerAgreementHandlerBody (O C R : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app (app equalityTerm (app O (app (numericalProjectionTerm true) C))) (app (numericalProjectionTerm false) C))) (numeral 0)) R

theorem answerAgreementHandlerBody_fv (O C R : AlphaTerm) :
    (answerAgreementHandlerBody O C R).fv = O.fv ∪ C.fv ∪ R.fv := by
  ext x
  simp only [answerAgreementHandlerBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (equalityTerm).fv = ∅ from equalityTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem answerAgreementHandlerBody_subst (O C R W : AlphaTerm) (x : ℕ) :
    (answerAgreementHandlerBody O C R).subst x W =
      answerAgreementHandlerBody (O.subst x W) (C.subst x W) (R.subst x W) := by
  simp only [answerAgreementHandlerBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ equalityTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false) ,subst_closed _ _ _ (numeral_closed 0)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following closed terms, expanding the displayed bodies before abstraction and keeping all internal binders
    fresh:
    $$\begin{aligned}
    H_a&:=\lambdaab{o}{\lambdaab{c}{\lambdaab{r}{
     \LambdaZeroTest\,
      \bigl(\LambdaEqual\,(o(\LambdaNumericProjection{1}\,c))
                             (\LambdaNumericProjection{2}\,c)\bigr)
      \,\ChurchNumeral{0}\,r}}},\\
    \LambdaAnswerAgreementCheck&:=\lambdaab{o}{\lambdaab{t}{
     \LambdaListRecursor\,(H_ao)\,\ChurchNumeral{1}\,t}}.
    \end{aligned}$$
    An entry code $c$ supplies a query address and a proposed answer. The handler compares the actual answer with the
    proposed one, returning zero on a mismatch and otherwise retaining the tail result. The empty table returns one.
    Repeated addresses require no special treatment: every listed answer must agree with the same input name.
-/
def answerAgreementHandlerTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (answerAgreementHandlerBody (var 30) (var 31) (var 32)))))

@[simp] theorem answerAgreementHandlerTerm_closed : answerAgreementHandlerTerm.Closed := by
  unfold answerAgreementHandlerTerm Closed
  simp only [fv_lam, answerAgreementHandlerBody_fv, fv_var]
  decide

theorem answerAgreementHandlerTerm_start {O C R : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hC : C.fv ⊆ {0}) (hR : R.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app answerAgreementHandlerTerm O) C) R)
      (answerAgreementHandlerBody O C R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfC (n : ℕ) (hn : n ≠ 0) := input_fresh hC hn
  have hfR (n : ℕ) (hn : n ≠ 0) := input_fresh hR hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (answerAgreementHandlerBody (var 30) (var 31) (var 32))))) O) (lam 31 (lam 32 (answerAgreementHandlerBody O (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (answerAgreementHandlerBody (var 30) (var 31) (var 32)))) O using 1
    simp [subst_lam_fresh, subst_var, answerAgreementHandlerBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (answerAgreementHandlerBody O (var 31) (var 32)))) C) (lam 32 (answerAgreementHandlerBody O C (var 32))) := by
    convert Beta.contract 31 (lam 32 (answerAgreementHandlerBody O (var 31) (var 32))) C using 1
    simp [subst_lam_fresh, subst_var, answerAgreementHandlerBody_subst, subst_not_free, hfO, hfC]
  have h2 : Beta (app (lam 32 (answerAgreementHandlerBody O C (var 32))) R) (answerAgreementHandlerBody O C R) := by
    convert Beta.contract 32 (answerAgreementHandlerBody O C (var 32)) R using 1
    simp [subst_var, answerAgreementHandlerBody_subst, subst_not_free, hfO, hfC]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) C) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) R).trans
  exact (Relation.ReflTransGen.single h2)

def answerAgreementBody (O T : AlphaTerm) : AlphaTerm :=
  app (app (app listRecursorTerm (app answerAgreementHandlerTerm O)) (numeral 1)) T

theorem answerAgreementBody_fv (O T : AlphaTerm) :
    (answerAgreementBody O T).fv = O.fv ∪ T.fv := by
  ext x
  simp only [answerAgreementBody, fv_app, (show (listRecursorTerm).fv = ∅ from listRecursorTerm_closed), (show (answerAgreementHandlerTerm).fv = ∅ from answerAgreementHandlerTerm_closed) ,(show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem answerAgreementBody_subst (O T W : AlphaTerm) (x : ℕ) :
    (answerAgreementBody O T).subst x W =
      answerAgreementBody (O.subst x W) (T.subst x W) := by
  simp only [answerAgreementBody, subst_app, subst_closed _ _ _ listRecursorTerm_closed, subst_closed _ _ _ answerAgreementHandlerTerm_closed ,subst_closed _ _ _ (numeral_closed 1)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following closed terms, expanding the displayed bodies before abstraction and keeping all internal binders
    fresh:
    $$\begin{aligned}
    H_a&:=\lambdaab{o}{\lambdaab{c}{\lambdaab{r}{
     \LambdaZeroTest\,
      \bigl(\LambdaEqual\,(o(\LambdaNumericProjection{1}\,c))
                             (\LambdaNumericProjection{2}\,c)\bigr)
      \,\ChurchNumeral{0}\,r}}},\\
    \LambdaAnswerAgreementCheck&:=\lambdaab{o}{\lambdaab{t}{
     \LambdaListRecursor\,(H_ao)\,\ChurchNumeral{1}\,t}}.
    \end{aligned}$$
    An entry code $c$ supplies a query address and a proposed answer. The handler compares the actual answer with the
    proposed one, returning zero on a mismatch and otherwise retaining the tail result. The empty table returns one.
    Repeated addresses require no special treatment: every listed answer must agree with the same input name.
-/
def answerAgreementTerm : AlphaTerm := (lam 30 (lam 31 (answerAgreementBody (var 30) (var 31))))

@[simp] theorem answerAgreementTerm_closed : answerAgreementTerm.Closed := by
  unfold answerAgreementTerm Closed
  simp only [fv_lam, answerAgreementBody_fv, fv_var]
  decide

theorem answerAgreementTerm_start {O T : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hT : T.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app answerAgreementTerm O) T)
      (answerAgreementBody O T) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfT (n : ℕ) (hn : n ≠ 0) := input_fresh hT hn
  have h0 : Beta (app (lam 30 (lam 31 (answerAgreementBody (var 30) (var 31)))) O) (lam 31 (answerAgreementBody O (var 31))) := by
    convert Beta.contract 30 (lam 31 (answerAgreementBody (var 30) (var 31))) O using 1
    simp [subst_lam_fresh, subst_var, answerAgreementBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (answerAgreementBody O (var 31))) T) (answerAgreementBody O T) := by
    convert Beta.contract 31 (answerAgreementBody O (var 31)) T using 1
    simp [subst_var, answerAgreementBody_subst, subst_not_free, hfO]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) T).trans
  exact (Relation.ReflTransGen.single h1)

def inputCandidateBody (O M N E : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app (app answerAgreementTerm O) (app (numericalProjectionTerm true) E))) (numeral 0)) (app (app (app (app inputCertificateTerm (app (numericalProjectionTerm true) E)) (app (numericalProjectionTerm false) E)) M) N)

theorem inputCandidateBody_fv (O M N E : AlphaTerm) :
    (inputCandidateBody O M N E).fv = O.fv ∪ M.fv ∪ N.fv ∪ E.fv := by
  ext x
  simp only [inputCandidateBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (answerAgreementTerm).fv = ∅ from answerAgreementTerm_closed), (show (inputCertificateTerm).fv = ∅ from inputCertificateTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem inputCandidateBody_subst (O M N E W : AlphaTerm) (x : ℕ) :
    (inputCandidateBody O M N E).subst x W =
      inputCandidateBody (O.subst x W) (M.subst x W) (N.subst x W) (E.subst x W) := by
  simp only [inputCandidateBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ answerAgreementTerm_closed, subst_closed _ _ _ inputCertificateTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false) ,subst_closed _ _ _ (numeral_closed 0)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Combine this comparison with the closed certificate checker. Using numerical codes throughout, put
    $$\begin{aligned}
    D(o,e,d,t,c)&:=\LambdaZeroTest\,(\LambdaAnswerAgreementCheck\,o\,t)
     \,\ChurchNumeral{0}\\
     &\quad(\LambdaInputCertificateCheck\,t\,c\,e\,d),\\
    \LambdaInputCandidateCheck&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{b}{
     D(o,e,d,\LambdaNumericProjection{1}\,b,\LambdaNumericProjection{2}\,b)}}}}.
    \end{aligned}$$
    Expand $D$ in the last line. For a candidate code $b$, this program returns one exactly when its decoded table agrees
    with $p$ and its decoded certificate passes the finite-table check for the decoded endpoints $e,d$; otherwise it returns
    zero. Indeed, the projections extract the two codes, the preceding proposition checks agreement, and
    §{sec:lambda-input-certificate-programs} supplies the certificate result. Zero testing forms their conjunction.
-/
def inputCandidateTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (inputCandidateBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem inputCandidateTerm_closed : inputCandidateTerm.Closed := by
  unfold inputCandidateTerm Closed
  simp only [fv_lam, inputCandidateBody_fv, fv_var]
  decide

theorem inputCandidateTerm_start {O M N E : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hM : M.fv ⊆ {0}) (hN : N.fv ⊆ {0}) (hE : E.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app (app inputCandidateTerm O) M) N) E)
      (inputCandidateBody O M N E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfM (n : ℕ) (hn : n ≠ 0) := input_fresh hM hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have hfE (n : ℕ) (hn : n ≠ 0) := input_fresh hE hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (inputCandidateBody (var 30) (var 31) (var 32) (var 33)))))) O) (lam 31 (lam 32 (lam 33 (inputCandidateBody O (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (inputCandidateBody (var 30) (var 31) (var 32) (var 33))))) O using 1
    simp [subst_lam_fresh, subst_var, inputCandidateBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (inputCandidateBody O (var 31) (var 32) (var 33))))) M) (lam 32 (lam 33 (inputCandidateBody O M (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (inputCandidateBody O (var 31) (var 32) (var 33)))) M using 1
    simp [subst_lam_fresh, subst_var, inputCandidateBody_subst, subst_not_free, hfO, hfM]
  have h2 : Beta (app (lam 32 (lam 33 (inputCandidateBody O M (var 32) (var 33)))) N) (lam 33 (inputCandidateBody O M N (var 33))) := by
    convert Beta.contract 32 (lam 33 (inputCandidateBody O M (var 32) (var 33))) N using 1
    simp [subst_lam_fresh, subst_var, inputCandidateBody_subst, subst_not_free, hfO, hfM, hfN]
  have h3 : Beta (app (lam 33 (inputCandidateBody O M N (var 33))) E) (inputCandidateBody O M N E) := by
    convert Beta.contract 33 (inputCandidateBody O M N (var 33)) E using 1
    simp [subst_var, inputCandidateBody_subst, subst_not_free, hfO, hfM, hfN]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) M) N) E).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) N) E).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) E).trans
  exact (Relation.ReflTransGen.single h3)

def boundedInputHandlerBody (O M N K R : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm R) (app (app (app (app inputCandidateTerm O) M) N) K)) (numeral 1)

theorem boundedInputHandlerBody_fv (O M N K R : AlphaTerm) :
    (boundedInputHandlerBody O M N K R).fv = O.fv ∪ M.fv ∪ N.fv ∪ K.fv ∪ R.fv := by
  ext x
  simp only [boundedInputHandlerBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (inputCandidateTerm).fv = ∅ from inputCandidateTerm_closed) ,(show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem boundedInputHandlerBody_subst (O M N K R W : AlphaTerm) (x : ℕ) :
    (boundedInputHandlerBody O M N K R).subst x W =
      boundedInputHandlerBody (O.subst x W) (M.subst x W) (N.subst x W) (K.subst x W) (R.subst x W) := by
  simp only [boundedInputHandlerBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ inputCandidateTerm_closed ,subst_closed _ _ _ (numeral_closed 1)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Finally use the recursor of §{sec:lambda-input-recursion} to test all candidate codes below a supplied bound:
    $$\begin{aligned}
    H_b&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{k}{\lambdaab{r}{
     \LambdaZeroTest\,r\,(\LambdaInputCandidateCheck\,o\,e\,d\,k)
     \,\ChurchNumeral{1}}}}}},\\
    \LambdaBoundedInputCheck&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{s}{
     \LambdaRecursor\,(H_b\,o\,e\,d)\,\ChurchNumeral{0}\,s}}}}.
    \end{aligned}$$
    The initial value says that no candidate has yet succeeded. At stage $k$, keep an earlier success; if there is none, use
    the answer for candidate $k$. These definitions give closed terms.
-/
def boundedInputHandlerTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody (var 30) (var 31) (var 32) (var 33) (var 34)))))))

@[simp] theorem boundedInputHandlerTerm_closed : boundedInputHandlerTerm.Closed := by
  unfold boundedInputHandlerTerm Closed
  simp only [fv_lam, boundedInputHandlerBody_fv, fv_var]
  decide

theorem boundedInputHandlerTerm_start {O M N K R : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hM : M.fv ⊆ {0}) (hN : N.fv ⊆ {0}) (hK : K.fv ⊆ {0}) (hR : R.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app (app (app boundedInputHandlerTerm O) M) N) K) R)
      (boundedInputHandlerBody O M N K R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfM (n : ℕ) (hn : n ≠ 0) := input_fresh hM hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have hfK (n : ℕ) (hn : n ≠ 0) := input_fresh hK hn
  have hfR (n : ℕ) (hn : n ≠ 0) := input_fresh hR hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody (var 30) (var 31) (var 32) (var 33) (var 34))))))) O) (lam 31 (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody O (var 31) (var 32) (var 33) (var 34)))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody (var 30) (var 31) (var 32) (var 33) (var 34)))))) O using 1
    simp [subst_lam_fresh, subst_var, boundedInputHandlerBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody O (var 31) (var 32) (var 33) (var 34)))))) M) (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody O M (var 32) (var 33) (var 34))))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody O (var 31) (var 32) (var 33) (var 34))))) M using 1
    simp [subst_lam_fresh, subst_var, boundedInputHandlerBody_subst, subst_not_free, hfO, hfM]
  have h2 : Beta (app (lam 32 (lam 33 (lam 34 (boundedInputHandlerBody O M (var 32) (var 33) (var 34))))) N) (lam 33 (lam 34 (boundedInputHandlerBody O M N (var 33) (var 34)))) := by
    convert Beta.contract 32 (lam 33 (lam 34 (boundedInputHandlerBody O M (var 32) (var 33) (var 34)))) N using 1
    simp [subst_lam_fresh, subst_var, boundedInputHandlerBody_subst, subst_not_free, hfO, hfM, hfN]
  have h3 : Beta (app (lam 33 (lam 34 (boundedInputHandlerBody O M N (var 33) (var 34)))) K) (lam 34 (boundedInputHandlerBody O M N K (var 34))) := by
    convert Beta.contract 33 (lam 34 (boundedInputHandlerBody O M N (var 33) (var 34))) K using 1
    simp [subst_lam_fresh, subst_var, boundedInputHandlerBody_subst, subst_not_free, hfO, hfM, hfN, hfK]
  have h4 : Beta (app (lam 34 (boundedInputHandlerBody O M N K (var 34))) R) (boundedInputHandlerBody O M N K R) := by
    convert Beta.contract 34 (boundedInputHandlerBody O M N K (var 34)) R using 1
    simp [subst_var, boundedInputHandlerBody_subst, subst_not_free, hfO, hfM, hfN, hfK]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) M) N) K) R).trans
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) N) K) R).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h2) K) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h3) R).trans
  exact (Relation.ReflTransGen.single h4)

def boundedInputBody (O M N S : AlphaTerm) : AlphaTerm :=
  app (app (app recursorTerm (app (app (app boundedInputHandlerTerm O) M) N)) (numeral 0)) S

theorem boundedInputBody_fv (O M N S : AlphaTerm) :
    (boundedInputBody O M N S).fv = O.fv ∪ M.fv ∪ N.fv ∪ S.fv := by
  ext x
  simp only [boundedInputBody, fv_app, (show (recursorTerm).fv = ∅ from recursorTerm_closed), (show (boundedInputHandlerTerm).fv = ∅ from boundedInputHandlerTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem boundedInputBody_subst (O M N S W : AlphaTerm) (x : ℕ) :
    (boundedInputBody O M N S).subst x W =
      boundedInputBody (O.subst x W) (M.subst x W) (N.subst x W) (S.subst x W) := by
  simp only [boundedInputBody, subst_app, subst_closed _ _ _ recursorTerm_closed, subst_closed _ _ _ boundedInputHandlerTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Finally use the recursor of §{sec:lambda-input-recursion} to test all candidate codes below a supplied bound:
    $$\begin{aligned}
    H_b&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{k}{\lambdaab{r}{
     \LambdaZeroTest\,r\,(\LambdaInputCandidateCheck\,o\,e\,d\,k)
     \,\ChurchNumeral{1}}}}}},\\
    \LambdaBoundedInputCheck&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{s}{
     \LambdaRecursor\,(H_b\,o\,e\,d)\,\ChurchNumeral{0}\,s}}}}.
    \end{aligned}$$
    The initial value says that no candidate has yet succeeded. At stage $k$, keep an earlier success; if there is none, use
    the answer for candidate $k$. These definitions give closed terms.
-/
def boundedInputTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (boundedInputBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem boundedInputTerm_closed : boundedInputTerm.Closed := by
  unfold boundedInputTerm Closed
  simp only [fv_lam, boundedInputBody_fv, fv_var]
  decide

theorem boundedInputTerm_start {O M N S : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hM : M.fv ⊆ {0}) (hN : N.fv ⊆ {0}) (hS : S.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app (app boundedInputTerm O) M) N) S)
      (boundedInputBody O M N S) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfM (n : ℕ) (hn : n ≠ 0) := input_fresh hM hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have hfS (n : ℕ) (hn : n ≠ 0) := input_fresh hS hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (boundedInputBody (var 30) (var 31) (var 32) (var 33)))))) O) (lam 31 (lam 32 (lam 33 (boundedInputBody O (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (boundedInputBody (var 30) (var 31) (var 32) (var 33))))) O using 1
    simp [subst_lam_fresh, subst_var, boundedInputBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (boundedInputBody O (var 31) (var 32) (var 33))))) M) (lam 32 (lam 33 (boundedInputBody O M (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (boundedInputBody O (var 31) (var 32) (var 33)))) M using 1
    simp [subst_lam_fresh, subst_var, boundedInputBody_subst, subst_not_free, hfO, hfM]
  have h2 : Beta (app (lam 32 (lam 33 (boundedInputBody O M (var 32) (var 33)))) N) (lam 33 (boundedInputBody O M N (var 33))) := by
    convert Beta.contract 32 (lam 33 (boundedInputBody O M (var 32) (var 33))) N using 1
    simp [subst_lam_fresh, subst_var, boundedInputBody_subst, subst_not_free, hfO, hfM, hfN]
  have h3 : Beta (app (lam 33 (boundedInputBody O M N (var 33))) S) (boundedInputBody O M N S) := by
    convert Beta.contract 33 (boundedInputBody O M N (var 33)) S using 1
    simp [subst_var, boundedInputBody_subst, subst_not_free, hfO, hfM, hfN]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) M) N) S).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) N) S).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) S).trans
  exact (Relation.ReflTransGen.single h3)


theorem answerAgreementHandlerTerm_apply (p : ℕ → ℕ) (c r : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app answerAgreementHandlerTerm (var 0)) (numeral c)) (numeral r))
      (numeral (if p (Nat.unpair c).1 = (Nat.unpair c).2 then r else 0)) := by
  apply (beta_steps_oracle (answerAgreementHandlerTerm_start
    (by simp [fv_var]) (numeral_closed c).input_fv (numeral_closed r).input_fv)).trans
  have hi := (oracle_steps_app_right (var 0)
    (beta_steps_oracle (numericalProjectionTerm_apply true c))).trans
      (Relation.ReflTransGen.single (OracleStep.query (p := p) (Nat.unpair c).1))
  have hv := beta_steps_oracle (p := p) (numericalProjectionTerm_apply false c)
  have he := (oracle_steps_app (oracle_steps_app_right equalityTerm hi) hv).trans
    (beta_steps_oracle (equalityTerm_apply (p (Nat.unpair c).1) (Nat.unpair c).2))
  apply (oracle_steps_app_left (oracle_steps_app_left
    (oracle_steps_app_right zeroTestTerm he) (numeral 0)) (numeral r)).trans
  split_ifs with h
  · exact beta_steps_oracle (branch_succ 0 _ _)
  · exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Comparing a table with the input
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    At a nonempty entry, the projections return its address and proposed answer. One input-query step returns the actual answer, and equality testing decides whether the two numbers coincide. Apply the list-recursion lemma with $V_l$ equal to one or zero according as every decoded pair in $l$ agrees with $p$ or not. The empty case is one, and the handler has exactly the required conjunction behavior. The numerical coding inverses give the arbitrary-code assertion. Confluence with input queries excludes reduction to one when the computed answer is zero.
    \end{proof}
-/
theorem answerAgreementTerm_apply (p : ℕ → ℕ) (t : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app answerAgreementTerm (var 0)) (numeral t))
      (numeral (if Term.answersAgreeTest p (Term.decodeAnswerTable t) then 1 else 0)) := by
  apply (beta_steps_oracle (answerAgreementTerm_start
    (by simp [fv_var]) (numeral_closed t).input_fv)).trans
  have hh : (app answerAgreementHandlerTerm (var 0)).fv ⊆ {0} := by
    rw [fv_app, answerAgreementHandlerTerm_closed, Finset.empty_union, fv_var]
  let f (xs : List ℕ) := numeral (if Term.answersAgreeTest p (xs.map Nat.unpair) then 1 else 0)
  have h := listRecursorTerm_oracle_apply hh (numeral_closed 1).input_fv f
    (by simp [f, Term.answersAgreeTest]; exact .refl)
    (fun a xs => by
      have h := answerAgreementHandlerTerm_apply p a
        (if Term.answersAgreeTest p (xs.map Nat.unpair) then 1 else 0)
      simpa [f, Term.answersAgreeTest, Bool.and_eq_true, ite_and] using h)
    (NatListCode.decode t)
  simp only [NatListCode.encode_decode] at h
  exact h

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following closed terms, expanding the displayed bodies before abstraction and keeping all internal binders
    fresh:
    $$\begin{aligned}
    H_a&:=\lambdaab{o}{\lambdaab{c}{\lambdaab{r}{
     \LambdaZeroTest\,
      \bigl(\LambdaEqual\,(o(\LambdaNumericProjection{1}\,c))
                             (\LambdaNumericProjection{2}\,c)\bigr)
      \,\ChurchNumeral{0}\,r}}},\\
    \LambdaAnswerAgreementCheck&:=\lambdaab{o}{\lambdaab{t}{
     \LambdaListRecursor\,(H_ao)\,\ChurchNumeral{1}\,t}}.
    \end{aligned}$$
    An entry code $c$ supplies a query address and a proposed answer. The handler compares the actual answer with the
    proposed one, returning zero on a mismatch and otherwise retaining the tail result. The empty table returns one.
    Repeated addresses require no special treatment: every listed answer must agree with the same input name.
-/
theorem answerAgreementTerm_accepts_iff (p : ℕ → ℕ) (t : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app answerAgreementTerm (var 0)) (numeral t)) (numeral 1) ↔
    Term.AnswersAgree p (Term.decodeAnswerTable t) := by
  rw [← Term.answersAgreeTest_spec]
  have hc := answerAgreementTerm_apply p t
  constructor
  · intro h
    have he := oracle_numeral_output_unique h hc
    split_ifs at he with ht
    · exact ht
  · intro ht
    simpa only [ht, ite_true] using hc

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Combine this comparison with the closed certificate checker. Using numerical codes throughout, put
    $$\begin{aligned}
    D(o,e,d,t,c)&:=\LambdaZeroTest\,(\LambdaAnswerAgreementCheck\,o\,t)
     \,\ChurchNumeral{0}\\
     &\quad(\LambdaInputCertificateCheck\,t\,c\,e\,d),\\
    \LambdaInputCandidateCheck&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{b}{
     D(o,e,d,\LambdaNumericProjection{1}\,b,\LambdaNumericProjection{2}\,b)}}}}.
    \end{aligned}$$
    Expand $D$ in the last line. For a candidate code $b$, this program returns one exactly when its decoded table agrees
    with $p$ and its decoded certificate passes the finite-table check for the decoded endpoints $e,d$; otherwise it returns
    zero. Indeed, the projections extract the two codes, the preceding proposition checks agreement, and
    §{sec:lambda-input-certificate-programs} supplies the certificate result. Zero testing forms their conjunction.
-/
theorem inputCandidateTerm_apply (p : ℕ → ℕ) (m n e : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (app inputCandidateTerm (var 0)) (numeral m)) (numeral n)) (numeral e))
      (numeral (if Term.inputCertificateTest p (Term.decode m) (Term.decode n) e then 1 else 0)) := by
  apply (beta_steps_oracle (inputCandidateTerm_start (by simp [fv_var])
    (numeral_closed m).input_fv (numeral_closed n).input_fv (numeral_closed e).input_fv)).trans
  have ht := beta_steps_oracle (p := p) (numericalProjectionTerm_apply true e)
  have hc := beta_steps_oracle (p := p) (numericalProjectionTerm_apply false e)
  have ha := (oracle_steps_app_right (app answerAgreementTerm (var 0)) ht).trans
    (answerAgreementTerm_apply p (Nat.unpair e).1)
  have hi := (oracle_steps_app_left (oracle_steps_app_left
    (oracle_steps_app (oracle_steps_app_right inputCertificateTerm ht) hc)
      (numeral m)) (numeral n)).trans
    (beta_steps_oracle (inputCertificateTerm_apply (Nat.unpair e).1 (Nat.unpair e).2 m n))
  apply (oracle_steps_app
    (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm ha) (numeral 0)) hi).trans
  unfold Term.inputCertificateTest
  cases hb : Term.answersAgreeTest p (Term.decodeAnswerTable (Nat.unpair e).1) <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and]
  · exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  · exact beta_steps_oracle (branch_succ 0 _ _)

theorem boundedInputHandlerTerm_apply (p : ℕ → ℕ) (m n k r : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (app (app boundedInputHandlerTerm (var 0)) (numeral m))
        (numeral n)) (numeral k)) (numeral r))
      (numeral (if r = 0 then
        if Term.inputCertificateTest p (Term.decode m) (Term.decode n) k then 1 else 0
        else 1)) := by
  apply (beta_steps_oracle (boundedInputHandlerTerm_start (by simp [fv_var])
    (numeral_closed m).input_fv (numeral_closed n).input_fv
    (numeral_closed k).input_fv (numeral_closed r).input_fv)).trans
  apply (oracle_steps_app_left (oracle_steps_app_right (app zeroTestTerm (numeral r))
    (inputCandidateTerm_apply p m n k)) (numeral 1)).trans
  cases r with
  | zero => exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | succ r => exact beta_steps_oracle (branch_succ r _ _)


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Bounded input-certificate checking by a lambda term
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induct on $s$ using primitive recursion with the input name. At zero there are no candidate codes below the bound, so the answer is zero. Increasing the bound from $k$ to $k+1$ adds precisely candidate $k$. The handler therefore computes the disjunction of the previous result and the new candidate result, which is the defining recurrence for the bounded test. Each stage terminates by the candidate computation above. Confluence with input queries excludes any other numeral output.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Finally use the recursor of §{sec:lambda-input-recursion} to test all candidate codes below a supplied bound:
    $$\begin{aligned}
    H_b&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{k}{\lambdaab{r}{
     \LambdaZeroTest\,r\,(\LambdaInputCandidateCheck\,o\,e\,d\,k)
     \,\ChurchNumeral{1}}}}}},\\
    \LambdaBoundedInputCheck&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{d}{\lambdaab{s}{
     \LambdaRecursor\,(H_b\,o\,e\,d)\,\ChurchNumeral{0}\,s}}}}.
    \end{aligned}$$
    The initial value says that no candidate has yet succeeded. At stage $k$, keep an earlier success; if there is none, use
    the answer for candidate $k$. These definitions give closed terms.
-/
theorem boundedInputTerm_apply (p : ℕ → ℕ) (m n s : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (app boundedInputTerm (var 0)) (numeral m)) (numeral n)) (numeral s))
      (numeral (if Term.boundedInputTest p (Term.decode m) (Term.decode n) s then 1 else 0)) := by
  apply (beta_steps_oracle (boundedInputTerm_start (by simp [fv_var])
    (numeral_closed m).input_fv (numeral_closed n).input_fv (numeral_closed s).input_fv)).trans
  have hh : (app (app (app boundedInputHandlerTerm (var 0)) (numeral m)) (numeral n)).fv ⊆ {0} := by
    simp only [fv_app, (show boundedInputHandlerTerm.fv = ∅ from boundedInputHandlerTerm_closed),
      (show (numeral m).fv = ∅ from numeral_closed m),
      (show (numeral n).fv = ∅ from numeral_closed n), fv_var,
      Finset.empty_union, Finset.union_empty]
    exact Finset.Subset.refl _
  let f (k : ℕ) := numeral (if Term.boundedInputTest p (Term.decode m) (Term.decode n) k then 1 else 0)
  have h := recursorTerm_oracle_apply (p := p) hh f (fun _ => numeral_closed _)
    (fun k => by
      have h := boundedInputHandlerTerm_apply p m n k
        (if Term.boundedInputTest p (Term.decode m) (Term.decode n) k then 1 else 0)
      have hk : Term.boundedInputTest p (Term.decode m) (Term.decode n) (k + 1) =
          (Term.boundedInputTest p (Term.decode m) (Term.decode n) k ||
            Term.inputCertificateTest p (Term.decode m) (Term.decode n) k) := by
        simp only [Term.boundedInputTest, List.range_succ, List.any_append,
          List.any_cons, List.any_nil, Bool.or_false]
      cases hb : Term.boundedInputTest p (Term.decode m) (Term.decode n) k <;>
        simpa only [f, hk, hb, Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.true_or,
          Nat.one_ne_zero] using h) s
  simpa only [boundedInputBody, f, Term.boundedInputTest, List.range_zero, List.any_nil, Bool.false_eq_true, ite_false] using h

theorem boundedInputTerm_accepts_iff (p : ℕ → ℕ) (m n s : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (app boundedInputTerm (var 0)) (numeral m)) (numeral n)) (numeral s)) (numeral 1) ↔
    Term.boundedInputTest p (Term.decode m) (Term.decode n) s = true := by
  have hc := boundedInputTerm_apply p m n s
  constructor
  · intro h
    have he := oracle_numeral_output_unique h hc
    split_ifs at he with ht
    · exact ht
  · intro ht
    simpa only [ht, ite_true] using hc


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: corollary
  title: Reduction detected by a bounded lambda program
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The finite-stage detection theorem in §{sec:lambda-input-certificates} characterizes the left side by success of some bounded test. Apply the exact acceptance statement just proved. The existential bound concerns finite certificate codes; it imposes no predetermined bound on the length of a reduction.
    \end{proof}
-/
theorem oracle_steps_iff_bounded_program (p : ℕ → ℕ) (M N : Term) :
    Relation.ReflTransGen (OracleStep p) (mk M) (mk N) ↔
    ∃ s, Relation.ReflTransGen (OracleStep p)
      (app (app (app (app boundedInputTerm (var 0)) (numeral M.code)) (numeral N.code)) (numeral s))
        (numeral 1) := by
  simp only [boundedInputTerm_accepts_iff, Term.decode_code]
  exact Term.oracle_steps_iff_bounded_input_test p M N

end PolishSpaceBook.NamedLambda.AlphaTerm
