module

public import PolishSpaceBook.LambdaAnswerAgreement
public import PolishSpaceBook.LambdaOracleSearchResult
public import PolishSpaceBook.LambdaProgramCodes

@[expose] public section

/-! # Exact universal evaluation with an input name -/
namespace PolishSpaceBook.NamedLambda
namespace Term

def oracleProgramInput (e n : ℕ) : Term :=
  .app (.app (programSyntax e) (.var 0)) (churchNumeral n)

def oracleOutputCandidate (p : ℕ → ℕ) (e n k : ℕ) : Bool :=
  boundedInputTest p (oracleProgramInput e n) (churchNumeral (Nat.unpair k).1) (Nat.unpair k).2

end Term
namespace AlphaTerm
set_option maxRecDepth 4096

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1

def oracleInputCodeBody (E N : AlphaTerm) : AlphaTerm :=
  app (app applicationCodeTerm (app (app applicationCodeTerm (app programCodeTerm E)) (numeral 0))) (app numeralCodeTerm N)

theorem oracleInputCodeBody_fv (E N : AlphaTerm) :
    (oracleInputCodeBody E N).fv = E.fv ∪ N.fv := by
  ext x
  simp only [oracleInputCodeBody, fv_app, (show (applicationCodeTerm).fv = ∅ from applicationCode_closed), (show (programCodeTerm).fv = ∅ from programCodeTerm_closed), (show (numeralCodeTerm).fv = ∅ from numeralCodeTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem oracleInputCodeBody_subst (E N W : AlphaTerm) (x : ℕ) :
    (oracleInputCodeBody E N).subst x W =
      oracleInputCodeBody (E.subst x W) (N.subst x W) := by
  simp only [oracleInputCodeBody, subst_app, subst_closed _ _ _ applicationCode_closed, subst_closed _ _ _ programCodeTerm_closed, subst_closed _ _ _ numeralCodeTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def oracleInputCodeTerm : AlphaTerm := (lam 30 (lam 31 (oracleInputCodeBody (var 30) (var 31))))

@[simp] theorem oracleInputCodeTerm_closed : oracleInputCodeTerm.Closed := by
  unfold oracleInputCodeTerm Closed
  simp only [fv_lam, oracleInputCodeBody_fv, fv_var]
  decide

theorem oracleInputCodeTerm_start {E N : AlphaTerm}
    (hE : E.fv ⊆ {0}) (hN : N.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app oracleInputCodeTerm E) N)
      (oracleInputCodeBody E N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE (n : ℕ) (hn : n ≠ 0) := input_fresh hE hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have h0 : Beta (app (lam 30 (lam 31 (oracleInputCodeBody (var 30) (var 31)))) E) (lam 31 (oracleInputCodeBody E (var 31))) := by
    convert Beta.contract 30 (lam 31 (oracleInputCodeBody (var 30) (var 31))) E using 1
    simp [subst_lam_fresh, subst_var, oracleInputCodeBody_subst, subst_not_free, hfE]
  have h1 : Beta (app (lam 31 (oracleInputCodeBody E (var 31))) N) (oracleInputCodeBody E N) := by
    convert Beta.contract 31 (oracleInputCodeBody E (var 31)) N using 1
    simp [subst_var, oracleInputCodeBody_subst, subst_not_free, hfE]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) N).trans
  exact (Relation.ReflTransGen.single h1)

def oracleOutputCandidateBody (O E N K : AlphaTerm) : AlphaTerm :=
  app (app (app (app boundedInputTerm O) (app (app oracleInputCodeTerm E) N)) (app numeralCodeTerm (app (numericalProjectionTerm true) K))) (app (numericalProjectionTerm false) K)

theorem oracleOutputCandidateBody_fv (O E N K : AlphaTerm) :
    (oracleOutputCandidateBody O E N K).fv = O.fv ∪ E.fv ∪ N.fv ∪ K.fv := by
  ext x
  simp only [oracleOutputCandidateBody, fv_app, (show (boundedInputTerm).fv = ∅ from boundedInputTerm_closed), (show (oracleInputCodeTerm).fv = ∅ from oracleInputCodeTerm_closed), (show (numeralCodeTerm).fv = ∅ from numeralCodeTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem oracleOutputCandidateBody_subst (O E N K W : AlphaTerm) (x : ℕ) :
    (oracleOutputCandidateBody O E N K).subst x W =
      oracleOutputCandidateBody (O.subst x W) (E.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [oracleOutputCandidateBody, subst_app, subst_closed _ _ _ boundedInputTerm_closed, subst_closed _ _ _ oracleInputCodeTerm_closed, subst_closed _ _ _ numeralCodeTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def oracleOutputCandidateTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (oracleOutputCandidateBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem oracleOutputCandidateTerm_closed : oracleOutputCandidateTerm.Closed := by
  unfold oracleOutputCandidateTerm Closed
  simp only [fv_lam, oracleOutputCandidateBody_fv, fv_var]
  decide

theorem oracleOutputCandidateTerm_start {O E N K : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hE : E.fv ⊆ {0}) (hN : N.fv ⊆ {0}) (hK : K.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app (app oracleOutputCandidateTerm O) E) N) K)
      (oracleOutputCandidateBody O E N K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfE (n : ℕ) (hn : n ≠ 0) := input_fresh hE hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have hfK (n : ℕ) (hn : n ≠ 0) := input_fresh hK hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (oracleOutputCandidateBody (var 30) (var 31) (var 32) (var 33)))))) O) (lam 31 (lam 32 (lam 33 (oracleOutputCandidateBody O (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (oracleOutputCandidateBody (var 30) (var 31) (var 32) (var 33))))) O using 1
    simp [subst_lam_fresh, subst_var, oracleOutputCandidateBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (oracleOutputCandidateBody O (var 31) (var 32) (var 33))))) E) (lam 32 (lam 33 (oracleOutputCandidateBody O E (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (oracleOutputCandidateBody O (var 31) (var 32) (var 33)))) E using 1
    simp [subst_lam_fresh, subst_var, oracleOutputCandidateBody_subst, subst_not_free, hfO, hfE]
  have h2 : Beta (app (lam 32 (lam 33 (oracleOutputCandidateBody O E (var 32) (var 33)))) N) (lam 33 (oracleOutputCandidateBody O E N (var 33))) := by
    convert Beta.contract 32 (lam 33 (oracleOutputCandidateBody O E (var 32) (var 33))) N using 1
    simp [subst_lam_fresh, subst_var, oracleOutputCandidateBody_subst, subst_not_free, hfO, hfE, hfN]
  have h3 : Beta (app (lam 33 (oracleOutputCandidateBody O E N (var 33))) K) (oracleOutputCandidateBody O E N K) := by
    convert Beta.contract 33 (oracleOutputCandidateBody O E N (var 33)) K using 1
    simp [subst_var, oracleOutputCandidateBody_subst, subst_not_free, hfO, hfE, hfN]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) E) N) K).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) N) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) K).trans
  exact (Relation.ReflTransGen.single h3)

def oracleOutputSearchTestBody (O E N K : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app (app (app (app oracleOutputCandidateTerm O) E) N) K)) (numeral 1)) (numeral 0)

theorem oracleOutputSearchTestBody_fv (O E N K : AlphaTerm) :
    (oracleOutputSearchTestBody O E N K).fv = O.fv ∪ E.fv ∪ N.fv ∪ K.fv := by
  ext x
  simp only [oracleOutputSearchTestBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (oracleOutputCandidateTerm).fv = ∅ from oracleOutputCandidateTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), (show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem oracleOutputSearchTestBody_subst (O E N K W : AlphaTerm) (x : ℕ) :
    (oracleOutputSearchTestBody O E N K).subst x W =
      oracleOutputSearchTestBody (O.subst x W) (E.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [oracleOutputSearchTestBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ oracleOutputCandidateTerm_closed ,subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Reverse the test answers and use the output projection only in the successful branch:
    $$\begin{aligned}
    T_q&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
     \LambdaZeroTest\,(\LambdaQueryOutputCandidate\,o\,e\,n\,k)
     \,\ChurchNumeral{1}\,\ChurchNumeral{0}}}}},\\
    \LambdaQueryOutputSearch&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{n}{
     \LambdaResultSearch\,(T_q\,o\,e\,n)\,\LambdaNumericProjection{1}}}}.
    \end{aligned}$$
    All displayed variables are bound, so both terms are closed and work uniformly for every input name.
-/
def oracleOutputSearchTestTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (oracleOutputSearchTestBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem oracleOutputSearchTestTerm_closed : oracleOutputSearchTestTerm.Closed := by
  unfold oracleOutputSearchTestTerm Closed
  simp only [fv_lam, oracleOutputSearchTestBody_fv, fv_var]
  decide

theorem oracleOutputSearchTestTerm_start {O E N K : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hE : E.fv ⊆ {0}) (hN : N.fv ⊆ {0}) (hK : K.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app (app oracleOutputSearchTestTerm O) E) N) K)
      (oracleOutputSearchTestBody O E N K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfE (n : ℕ) (hn : n ≠ 0) := input_fresh hE hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have hfK (n : ℕ) (hn : n ≠ 0) := input_fresh hK hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (oracleOutputSearchTestBody (var 30) (var 31) (var 32) (var 33)))))) O) (lam 31 (lam 32 (lam 33 (oracleOutputSearchTestBody O (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (oracleOutputSearchTestBody (var 30) (var 31) (var 32) (var 33))))) O using 1
    simp [subst_lam_fresh, subst_var, oracleOutputSearchTestBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (oracleOutputSearchTestBody O (var 31) (var 32) (var 33))))) E) (lam 32 (lam 33 (oracleOutputSearchTestBody O E (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (oracleOutputSearchTestBody O (var 31) (var 32) (var 33)))) E using 1
    simp [subst_lam_fresh, subst_var, oracleOutputSearchTestBody_subst, subst_not_free, hfO, hfE]
  have h2 : Beta (app (lam 32 (lam 33 (oracleOutputSearchTestBody O E (var 32) (var 33)))) N) (lam 33 (oracleOutputSearchTestBody O E N (var 33))) := by
    convert Beta.contract 32 (lam 33 (oracleOutputSearchTestBody O E (var 32) (var 33))) N using 1
    simp [subst_lam_fresh, subst_var, oracleOutputSearchTestBody_subst, subst_not_free, hfO, hfE, hfN]
  have h3 : Beta (app (lam 33 (oracleOutputSearchTestBody O E N (var 33))) K) (oracleOutputSearchTestBody O E N K) := by
    convert Beta.contract 33 (oracleOutputSearchTestBody O E N (var 33)) K using 1
    simp [subst_var, oracleOutputSearchTestBody_subst, subst_not_free, hfO, hfE, hfN]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) E) N) K).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) N) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) K).trans
  exact (Relation.ReflTransGen.single h3)

def oracleOutputSearchBody (O E N : AlphaTerm) : AlphaTerm :=
  app (app resultSearchTerm (app (app (app oracleOutputSearchTestTerm O) E) N)) (numericalProjectionTerm true)

theorem oracleOutputSearchBody_fv (O E N : AlphaTerm) :
    (oracleOutputSearchBody O E N).fv = O.fv ∪ E.fv ∪ N.fv := by
  ext x
  simp only [oracleOutputSearchBody, fv_app, (show (resultSearchTerm).fv = ∅ from resultSearchTerm_closed), (show (oracleOutputSearchTestTerm).fv = ∅ from oracleOutputSearchTestTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem oracleOutputSearchBody_subst (O E N W : AlphaTerm) (x : ℕ) :
    (oracleOutputSearchBody O E N).subst x W =
      oracleOutputSearchBody (O.subst x W) (E.subst x W) (N.subst x W) := by
  simp only [oracleOutputSearchBody, subst_app, subst_closed _ _ _ resultSearchTerm_closed, subst_closed _ _ _ oracleOutputSearchTestTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Reverse the test answers and use the output projection only in the successful branch:
    $$\begin{aligned}
    T_q&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
     \LambdaZeroTest\,(\LambdaQueryOutputCandidate\,o\,e\,n\,k)
     \,\ChurchNumeral{1}\,\ChurchNumeral{0}}}}},\\
    \LambdaQueryOutputSearch&:=\lambdaab{o}{\lambdaab{e}{\lambdaab{n}{
     \LambdaResultSearch\,(T_q\,o\,e\,n)\,\LambdaNumericProjection{1}}}}.
    \end{aligned}$$
    All displayed variables are bound, so both terms are closed and work uniformly for every input name.
-/
def oracleOutputSearchTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (oracleOutputSearchBody (var 30) (var 31) (var 32)))))

@[simp] theorem oracleOutputSearchTerm_closed : oracleOutputSearchTerm.Closed := by
  unfold oracleOutputSearchTerm Closed
  simp only [fv_lam, oracleOutputSearchBody_fv, fv_var]
  decide

theorem oracleOutputSearchTerm_start {O E N : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hE : E.fv ⊆ {0}) (hN : N.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app oracleOutputSearchTerm O) E) N)
      (oracleOutputSearchBody O E N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfE (n : ℕ) (hn : n ≠ 0) := input_fresh hE hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (oracleOutputSearchBody (var 30) (var 31) (var 32))))) O) (lam 31 (lam 32 (oracleOutputSearchBody O (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (oracleOutputSearchBody (var 30) (var 31) (var 32)))) O using 1
    simp [subst_lam_fresh, subst_var, oracleOutputSearchBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (oracleOutputSearchBody O (var 31) (var 32)))) E) (lam 32 (oracleOutputSearchBody O E (var 32))) := by
    convert Beta.contract 31 (lam 32 (oracleOutputSearchBody O (var 31) (var 32))) E using 1
    simp [subst_lam_fresh, subst_var, oracleOutputSearchBody_subst, subst_not_free, hfO, hfE]
  have h2 : Beta (app (lam 32 (oracleOutputSearchBody O E (var 32))) N) (oracleOutputSearchBody O E N) := by
    convert Beta.contract 32 (oracleOutputSearchBody O E (var 32)) N using 1
    simp [subst_var, oracleOutputSearchBody_subst, subst_not_free, hfO, hfE]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) E) N).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) N).trans
  exact (Relation.ReflTransGen.single h2)



/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Retain the indexed closed programs $P_e$ and their fixed named representatives from §{sec:lambda-program-input-codes}. The initial term on numerical input $n$ is now $P_eo\ChurchNumeral{n}$. Its named syntax code is computed by the closed term
    $$\begin{aligned}
    \LambdaQueryInputCodeProgram:=\lambdaab{e}{\lambdaab{n}{
     \LambdaTaggedCode{1}\,
     (\LambdaTaggedCode{1}\,(\LambdaProgramCode\,e)\,\ChurchNumeral{0})
     \, (\LambdaNumeralCodeProgram\,n)}}.
    \end{aligned}$$
    Here zero is the syntax code of $o=x_0$. Two applications of the application-code constructor, together with the program-code and numeral-code programs, therefore give the required code by finite beta-reduction. The table checks below still use named syntax codes and alpha-equivalence at joins.
-/
theorem oracleInputCodeTerm_apply (e n : ℕ) :
    Relation.ReflTransGen Beta (app (app oracleInputCodeTerm (numeral e)) (numeral n))
      (numeral (Term.oracleProgramInput e n).code) := by
  apply (oracleInputCodeTerm_start (numeral_closed e).input_fv (numeral_closed n).input_fv).trans
  have hi := (beta_steps_app_left (beta_steps_app_right applicationCodeTerm (programCodeTerm_apply e))
    (numeral 0)).trans (applicationCodeTerm_apply (Term.programSyntax e) (.var 0))
  exact (beta_steps_app (beta_steps_app_right applicationCodeTerm hi) (numeralCodeTerm_apply n)).trans
    (applicationCodeTerm_apply (.app (Term.programSyntax e) (.var 0)) (Term.churchNumeral n))


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Decode a candidate number $k$ as a proposed output $m$ and a certificate-search bound $s$. The closed candidate tester is
    $$\begin{aligned}
    \LambdaQueryOutputCandidate:=\lambdaab{o}{\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
     \LambdaBoundedInputCheck\,o\,
     (\LambdaQueryInputCodeProgram\,e\,n)\\
     \qquad(\LambdaNumeralCodeProgram\,(\LambdaNumericProjection{1}\,k))
     \, (\LambdaNumericProjection{2}\,k)}}}}.
    \end{aligned}$$
    For every $p,e,n,k$, it returns one or zero according as the bounded test for the initial term and the proposed output numeral succeeds or fails. The coding programs compute the two endpoints, and §{sec:lambda-input-check-programs} proves the exact result of the bounded checker. Hence this is a total numerical test for each input name. A program returns $m$ if and only if some candidate with first component $m$ succeeds. Every successful candidate has the same first component, by confluence of the original program's reductions.
-/
theorem oracleOutputCandidateTerm_apply (p : ℕ → ℕ) (e n k : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (app oracleOutputCandidateTerm (var 0)) (numeral e)) (numeral n)) (numeral k))
      (numeral (if Term.oracleOutputCandidate p e n k then 1 else 0)) := by
  apply (beta_steps_oracle (oracleOutputCandidateTerm_start (by simp [fv_var])
    (numeral_closed e).input_fv (numeral_closed n).input_fv (numeral_closed k).input_fv)).trans
  have hs := beta_steps_oracle (p := p) (numericalProjectionTerm_apply false k)
  have hn := (beta_steps_app_right numeralCodeTerm (numericalProjectionTerm_apply true k)).trans
    (numeralCodeTerm_apply (Nat.unpair k).1)
  have hi := oracle_steps_app (oracle_steps_app
    (oracle_steps_app_right (app boundedInputTerm (var 0)) (beta_steps_oracle (oracleInputCodeTerm_apply e n)))
      (beta_steps_oracle hn)) hs
  have hc := boundedInputTerm_apply p (Term.oracleProgramInput e n).code
    (Term.churchNumeral (Nat.unpair k).1).code (Nat.unpair k).2
  simp only [Term.decode_code] at hc
  exact hi.trans hc

theorem oracleOutputSearchTestTerm_apply (p : ℕ → ℕ) (e n k : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (app oracleOutputSearchTestTerm (var 0)) (numeral e)) (numeral n)) (numeral k))
      (numeral (if Term.oracleOutputCandidate p e n k then 0 else 1)) := by
  apply (beta_steps_oracle (oracleOutputSearchTestTerm_start (by simp [fv_var])
    (numeral_closed e).input_fv (numeral_closed n).input_fv (numeral_closed k).input_fv)).trans
  apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm
    (oracleOutputCandidateTerm_apply p e n k)) (numeral 1)) (numeral 0)).trans
  cases h : Term.oracleOutputCandidate p e n k with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | true =>
    simp only [ite_true]
    exact beta_steps_oracle (branch_succ 0 _ _)

theorem oracleOutputSearchTest_input_fv (e n : ℕ) :
    (app (app (app oracleOutputSearchTestTerm (var 0)) (numeral e)) (numeral n)).fv ⊆ {0} := by
  rw [fv_app,fv_app,fv_app,oracleOutputSearchTestTerm_closed,numeral_closed,numeral_closed,fv_var]
  simp

theorem oracleOutputSearchTerm_hit (p : ℕ → ℕ) (e n j : ℕ)
    (hj : Term.oracleOutputCandidate p e n j = true)
    (hbefore : ∀ k < j, Term.oracleOutputCandidate p e n k = false) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app oracleOutputSearchTerm (var 0)) (numeral e)) (numeral n))
      (numeral (Nat.unpair j).1) := by
  apply (beta_steps_oracle (oracleOutputSearchTerm_start (by simp [fv_var])
    (numeral_closed e).input_fv (numeral_closed n).input_fv)).trans
  have hs := resultSearchTerm_oracle_hit (oracleOutputSearchTest_input_fv e n)
    (numericalProjectionTerm_closed true).input_fv j
    (by simpa only [hj,ite_true] using oracleOutputSearchTestTerm_apply p e n j)
    (fun k hk => ⟨0,by simpa only [hbefore k hk,Bool.false_eq_true,ite_false]
      using oracleOutputSearchTestTerm_apply p e n k⟩)
  exact hs.trans (beta_steps_oracle (numericalProjectionTerm_apply true j))

theorem oracle_outputTest_exists_iff (p : ℕ → ℕ) (e n m : ℕ) :
    (∃ s, Term.boundedInputTest p (Term.oracleProgramInput e n) (Term.churchNumeral m) s = true) ↔
    OracleRuns p (Term.closedProgram e) n m := by
  rw [← Term.oracle_steps_iff_bounded_input_test]
  change Relation.ReflTransGen (OracleStep p)
    (app (app (mk (Term.programSyntax e)) (var 0)) (mk (Term.churchNumeral n)))
    (mk (Term.churchNumeral m)) ↔ _
  simp only [Term.mk_programSyntax,Term.mk_churchNumeral]
  rfl

theorem oracle_accepted_candidate_outputs_equal {p : ℕ → ℕ} {e n k l : ℕ}
    (hk : Term.oracleOutputCandidate p e n k = true)
    (hl : Term.oracleOutputCandidate p e n l = true) : (Nat.unpair k).1 = (Nat.unpair l).1 :=
  OracleRuns.output_unique
    ((oracle_outputTest_exists_iff p e n _).mp ⟨_,hk⟩)
    ((oracle_outputTest_exists_iff p e n _).mp ⟨_,hl⟩)

theorem oracleOutputSearchTerm_complete {p : ℕ → ℕ} {e n m : ℕ}
    (h : OracleRuns p (Term.closedProgram e) n m) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app oracleOutputSearchTerm (var 0)) (numeral e)) (numeral n)) (numeral m) := by
  obtain ⟨s,hs⟩ := (oracle_outputTest_exists_iff p e n m).mpr h
  have hc : Term.oracleOutputCandidate p e n (Nat.pair m s) = true := by
    simpa only [Term.oracleOutputCandidate,Nat.unpair_pair] using hs
  have hex : ∃ k, Term.oracleOutputCandidate p e n k = true := ⟨_,hc⟩
  have hj := Nat.find_spec hex
  have he : (Nat.unpair (Nat.find hex)).1 = m := by
    simpa only [Nat.unpair_pair] using oracle_accepted_candidate_outputs_equal hj hc
  rw [← he]
  apply oracleOutputSearchTerm_hit p e n (Nat.find hex) hj
  intro k hk
  have hn := Nat.find_min hex hk
  cases hb : Term.oracleOutputCandidate p e n k
  · rfl
  · exact False.elim (hn hb)

theorem oracleOutputSearchTerm_no_output (p : ℕ → ℕ) (e n : ℕ)
    (hn : ∀ m, ¬ OracleRuns p (Term.closedProgram e) n m) (m : ℕ) :
    ¬ Relation.ReflTransGen (OracleStep p)
      (app (app (app oracleOutputSearchTerm (var 0)) (numeral e)) (numeral n)) (numeral m) := by
  have hc (k : ℕ) : Term.oracleOutputCandidate p e n k = false := by
    cases h : Term.oracleOutputCandidate p e n k with
    | false => rfl
    | true => exact False.elim (hn (Nat.unpair k).1
        ((oracle_outputTest_exists_iff p e n _).mp ⟨_,h⟩))
  intro hm
  have hb := oracle_numeral_after_reduction
    (beta_steps_oracle (oracleOutputSearchTerm_start (by simp [fv_var])
      (numeral_closed e).input_fv (numeral_closed n).input_fv)) hm
  apply resultSearchTerm_oracle_no_output (oracleOutputSearchTest_input_fv e n)
    (numericalProjectionTerm_closed true).input_fv _ m hb
  intro k
  exact ⟨0,by simpa only [hc k,Bool.false_eq_true,ite_false]
    using oracleOutputSearchTestTerm_apply p e n k⟩


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Exact universal evaluation with an input name
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    If the indexed program returns $m$, finite-stage detection supplies a successful candidate with output component $m$. Choose the least successful candidate $j$. The reversed test returns one at every earlier candidate and zero at $j$. Search with a result function therefore reaches the first projection of $\ChurchNumeral{j}$, which is $\ChurchNumeral{m}$ because all successful candidates have the same output component.

    If the indexed program has no numeral output, every candidate fails. All reversed tests return one, so the no-output assertion of the preceding search lemma excludes every numeral from the search body. The outer parameter contractions cannot create an additional output: confluence would carry any such numeral output to that same body.

    Finally, when the indexed program has an output, the first argument supplies it from the evaluator as well, and uniqueness excludes a different numeral. Combined with the no-output case, this proves the equivalence for all inputs without a termination assumption. The same single closed term is used throughout; no finite description of $p$ is assumed.
    \end{proof}
-/
theorem oracleOutputSearchTerm_runs_iff (p : ℕ → ℕ) (e n m : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app oracleOutputSearchTerm (var 0)) (numeral e)) (numeral n)) (numeral m) ↔
    OracleRuns p (Term.closedProgram e) n m := by
  classical
  constructor
  · intro hm
    by_cases hex : ∃ r, OracleRuns p (Term.closedProgram e) n r
    · obtain ⟨r,hr⟩ := hex
      have he := oracle_numeral_output_unique hm (oracleOutputSearchTerm_complete hr)
      simpa only [he] using hr
    · exact False.elim (oracleOutputSearchTerm_no_output p e n (fun r hr => hex ⟨r,hr⟩) m hm)
  · exact oracleOutputSearchTerm_complete

theorem oracleOutputSearchTerm_domain_iff (p : ℕ → ℕ) (e n : ℕ) :
    (∃ m, Relation.ReflTransGen (OracleStep p)
      (app (app (app oracleOutputSearchTerm (var 0)) (numeral e)) (numeral n)) (numeral m)) ↔
    (∃ m, OracleRuns p (Term.closedProgram e) n m) :=
  exists_congr (fun m => oracleOutputSearchTerm_runs_iff p e n m)

end AlphaTerm
end PolishSpaceBook.NamedLambda
