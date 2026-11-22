module

public import PolishSpaceBook.LambdaCertificateChecker
public import PolishSpaceBook.LambdaNumeralCodes

@[expose] public section

/-! # Closed program indices and finite tests for numerical outputs

All syntax data describe the same named lambda calculus. An index decoding to
an open term denotes the zero numeral, as in `Term.closedProgram`.
-/
namespace PolishSpaceBook.NamedLambda
namespace Term

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The enumeration $P_e$ in §{sec:lambda-syntax-codes} replaces an open decoded term with the zero numeral. To implement this convention, observe that every free variable $x_i$ of a named term $M$ satisfies $i\le\LambdaSyntaxCode{M}$. At a variable this follows from $i\le3i$. At an application, a free variable belongs to one of the two children, whose code is smaller than the parent code. At an abstraction, removing the binder introduces no new free variable and the body code is again smaller. Structural induction proves the bound. Thus checking the variable indices from zero through the code suffices to decide whether the term is closed.
-/
theorem mem_fv_le_code (M : Term) (x : ℕ) (hx : x ∈ M.fv) : x ≤ M.code := by
  induction M with
  | var y => simp only [fv, Finset.mem_singleton] at hx; subst x; simp only [code]; omega
  | app A B ihA ihB =>
    rcases Finset.mem_union.mp hx with hA | hB
    · exact (ihA hA).trans (code_app_left_lt A B).le
    · exact (ihB hB).trans (code_app_right_lt A B).le
  | lam y A ih => exact (ih (Finset.mem_erase.mp hx).2).trans (code_lam_body_lt y A).le

def hasFreeBelow (M : Term) (k : ℕ) : Bool :=
  (List.range k).any (fun x => decide (x ∈ M.fv))

theorem hasFreeBelow_zero (M : Term) : hasFreeBelow M 0 = false := rfl

theorem hasFreeBelow_succ (M : Term) (k : ℕ) :
    hasFreeBelow M (k + 1) = (hasFreeBelow M k || decide (k ∈ M.fv)) := by
  simp only [hasFreeBelow, List.range_succ, List.any_append,
    List.any_cons, List.any_nil, Bool.or_false]

theorem hasFreeBelow_full (M : Term) : hasFreeBelow M (M.code + 1) = true ↔ M.fv ≠ ∅ := by
  rw [hasFreeBelow, List.any_eq_true, ← Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, of_decide_eq_true hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, List.mem_range.mpr (Nat.lt_succ_of_le (mem_fv_le_code M x hx)), by simp [hx]⟩

/-- A named representative of the closed term assigned to every index. -/
def programSyntax (e : ℕ) : Term :=
  if (decode e).fv = ∅ then decode e else churchNumeral 0

@[simp] theorem mk_programSyntax (e : ℕ) : AlphaTerm.mk (programSyntax e) = closedProgram e := by
  unfold programSyntax closedProgram
  split_ifs <;> simp

@[simp] theorem programSyntax_closed (e : ℕ) : (programSyntax e).fv = ∅ := by
  have h := closedProgram_closed e
  rw [← mk_programSyntax] at h
  exact h

def outputTest (e n m s : ℕ) : Bool :=
  boundedBetaTest (.app (programSyntax e) (churchNumeral n)) (churchNumeral m) s

def outputCandidate (e n k : ℕ) : Bool := outputTest e n (Nat.unpair k).1 (Nat.unpair k).2

end Term
namespace AlphaTerm

set_option maxRecDepth 4096

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Define the closed programs
    $$\begin{aligned}
    J&:=\lambdaab{e}{\lambdaab{i}{\lambdaab{r}{
     \LambdaZeroTest\,r\,(\LambdaFreeVarTest\,e\,i)\,\ChurchNumeral{1}}}},\\
    \LambdaClosedTest&:=\lambdaab{e}{\LambdaZeroTest\,
     \bigl(\LambdaRecursor\,(Je)\,\ChurchNumeral{0}\,(\LambdaSucc\,e)\bigr)
     \,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    \LambdaProgramCode&:=\lambdaab{e}{\LambdaZeroTest\,(\LambdaClosedTest\,e)
     \,\ChurchNumeral{\LambdaSyntaxCode{\ChurchNumeral{0}}}\,e},\\
    \LambdaProgramInputCode&:=\lambdaab{e}{\lambdaab{n}{
     \LambdaTaggedCode{1}\,(\LambdaProgramCode\,e)\,(\LambdaNumeralCodeProgram\,n)}}.
    \end{aligned}$$
    The recurrence records whether a free variable has already been found. The outer zero test reverses this answer to
    obtain the closedness test. The program-code selector then implements the fallback convention, and the final constructor
    attaches the numerical input.
-/
def freePrefixStepBody (E K R : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm R)
    (app (app freeVariableTerm E) K)) (numeral 1)

theorem freePrefixStepBody_fv (E K R : AlphaTerm) :
    (freePrefixStepBody E K R).fv = E.fv ∪ K.fv ∪ R.fv := by
  ext x
  simp only [freePrefixStepBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (freeVariableTerm).fv = ∅ from freeVariableTerm_closed) ,(show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem freePrefixStepBody_subst (E K R W : AlphaTerm) (x : ℕ) :
    (freePrefixStepBody E K R).subst x W =
      freePrefixStepBody (E.subst x W) (K.subst x W) (R.subst x W) := by
  simp only [freePrefixStepBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ freeVariableTerm_closed ,subst_closed _ _ _ (numeral_closed 1)]

def freePrefixStepTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (freePrefixStepBody (var 30) (var 31) (var 32)))))

@[simp] theorem freePrefixStepTerm_closed : freePrefixStepTerm.Closed := by
  unfold freePrefixStepTerm Closed
  simp only [fv_lam, freePrefixStepBody_fv, fv_var]
  decide

theorem freePrefixStepTerm_start {E K R : AlphaTerm}
    (hE : E.Closed) (hK : K.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app freePrefixStepTerm E) K) R)
      (freePrefixStepBody E K R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfK : K.fv = ∅ := hK
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (freePrefixStepBody (var 30) (var 31) (var 32))))) E) (lam 31 (lam 32 (freePrefixStepBody E (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (freePrefixStepBody (var 30) (var 31) (var 32)))) E using 1
    simp [subst_lam_fresh, subst_var, freePrefixStepBody_subst, hfE]
  have h1 : Beta (app (lam 31 (lam 32 (freePrefixStepBody E (var 31) (var 32)))) K) (lam 32 (freePrefixStepBody E K (var 32))) := by
    convert Beta.contract 31 (lam 32 (freePrefixStepBody E (var 31) (var 32))) K using 1
    simp [subst_lam_fresh, subst_var, freePrefixStepBody_subst, subst_closed, hE, hfK]
  have h2 : Beta (app (lam 32 (freePrefixStepBody E K (var 32))) R) (freePrefixStepBody E K R) := by
    convert Beta.contract 32 (freePrefixStepBody E K (var 32)) R using 1
    simp [subst_var, freePrefixStepBody_subst, subst_closed, hE, hK]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) K) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) R).trans
  exact (Relation.ReflTransGen.single h2)

def closedSyntaxBody (E : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm
    (app (app (app recursorTerm (app freePrefixStepTerm E)) (numeral 0)) (app successorTerm E)))
    (numeral 1)) (numeral 0)

theorem closedSyntaxBody_fv (E : AlphaTerm) :
    (closedSyntaxBody E).fv = E.fv := by
  ext x
  simp only [closedSyntaxBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (recursorTerm).fv = ∅ from recursorTerm_closed), (show (freePrefixStepTerm).fv = ∅ from freePrefixStepTerm_closed), (show (successorTerm).fv = ∅ from successorTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), (show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem closedSyntaxBody_subst (E W : AlphaTerm) (x : ℕ) :
    (closedSyntaxBody E).subst x W =
      closedSyntaxBody (E.subst x W) := by
  simp only [closedSyntaxBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ recursorTerm_closed, subst_closed _ _ _ freePrefixStepTerm_closed, subst_closed _ _ _ successorTerm_closed ,subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1)]

def closedSyntaxTerm : AlphaTerm := (lam 30 (closedSyntaxBody (var 30)))

@[simp] theorem closedSyntaxTerm_closed : closedSyntaxTerm.Closed := by
  unfold closedSyntaxTerm Closed
  simp only [fv_lam, closedSyntaxBody_fv, fv_var]
  decide

theorem closedSyntaxTerm_start {E : AlphaTerm}
    (hE : E.Closed) :
    Relation.ReflTransGen Beta (app closedSyntaxTerm E)
      (closedSyntaxBody E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (closedSyntaxBody (var 30))) E) (closedSyntaxBody E) := by
    convert Beta.contract 30 (closedSyntaxBody (var 30)) E using 1
    simp [subst_var, closedSyntaxBody_subst]
  exact (Relation.ReflTransGen.single h0)

theorem freePrefixStepTerm_code (M : Term) (k : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app freePrefixStepTerm (numeral M.code)) (numeral k))
        (numeral (if M.hasFreeBelow k then 1 else 0)))
      (numeral (if M.hasFreeBelow (k + 1) then 1 else 0)) := by
  apply (freePrefixStepTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  unfold freePrefixStepBody
  rw [Term.hasFreeBelow_succ]
  cases h : M.hasFreeBelow k with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Bool.false_or, decide_eq_true_eq]
    apply (branch_zero _ _ (by rw [fv_app, fv_app, freeVariableTerm_closed, numeral_closed, numeral_closed]; simp)).trans
    exact freeVariableTerm_code M k
  | true =>
    simp only [Bool.true_or, ite_true]
    exact branch_succ 0 _ _

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Fix the decoded term $M$. After $i$ iterations, the state is one exactly when some variable with index less than $i$ is
    free in $M$, and zero otherwise. The assertion holds initially. At the next step, $J$ preserves a previous success or
    tests the next variable by the free-variable program. The numerical recursor therefore produces this state after
    $\LambdaSyntaxCode{M}+1$ steps. The free-variable bound shows that the state is zero exactly when $M$ is closed. Zero
    testing gives the first conclusion. The selector then returns either the original code or the code of the fixed zero
    numeral. Finally use the numeral-code and application-code equations. The code-decoding identity makes the argument
    valid for every natural-number index.
-/
theorem closedSyntaxTerm_code (M : Term) :
    Relation.ReflTransGen Beta (app closedSyntaxTerm (numeral M.code))
      (numeral (if M.fv = ∅ then 1 else 0)) := by
  apply (closedSyntaxTerm_start (numeral_closed _)).trans
  unfold closedSyntaxBody
  have h := recursorTerm_apply (closed_app freePrefixStepTerm_closed (numeral_closed _))
    (fun k => numeral (if M.hasFreeBelow k then 1 else 0)) (fun _ => numeral_closed _)
    (freePrefixStepTerm_code M) (M.code + 1)
  simp only [Term.hasFreeBelow_zero, Bool.false_eq_true, ite_false] at h
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm
    ((beta_steps_app_right _ (successorTerm_apply _)).trans h)) _) _).trans
  by_cases hc : M.fv = ∅
  · have hb : M.hasFreeBelow (M.code + 1) = false := by
      cases ht : M.hasFreeBelow (M.code + 1)
      · rfl
      · exact False.elim ((Term.hasFreeBelow_full M).mp ht hc)
    simp only [hc, ite_true, hb, Bool.false_eq_true, ite_false]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)
  · have hb := (Term.hasFreeBelow_full M).mpr hc
    simp only [ite_eq_right hc, hb, ite_true]
    exact branch_succ 0 _ _

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Codes of closed programs and their inputs
-/
theorem closedSyntaxTerm_apply (e : ℕ) :
    Relation.ReflTransGen Beta (app closedSyntaxTerm (numeral e))
      (numeral (if (Term.decode e).fv = ∅ then 1 else 0)) := by
  simpa only [Term.code_decode] using closedSyntaxTerm_code (Term.decode e)

def programCodeBody (E : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app closedSyntaxTerm E))
    (numeral (Term.churchNumeral 0).code)) E

theorem programCodeBody_fv (E : AlphaTerm) :
    (programCodeBody E).fv = E.fv := by
  ext x
  simp only [programCodeBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (closedSyntaxTerm).fv = ∅ from closedSyntaxTerm_closed) ,(show (numeral (Term.churchNumeral 0).code).fv = ∅ from numeral_closed (Term.churchNumeral 0).code), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem programCodeBody_subst (E W : AlphaTerm) (x : ℕ) :
    (programCodeBody E).subst x W =
      programCodeBody (E.subst x W) := by
  simp only [programCodeBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ closedSyntaxTerm_closed ,subst_closed _ _ _ (numeral_closed (Term.churchNumeral 0).code)]

def programCodeTerm : AlphaTerm := (lam 30 (programCodeBody (var 30)))

@[simp] theorem programCodeTerm_closed : programCodeTerm.Closed := by
  unfold programCodeTerm Closed
  simp only [fv_lam, programCodeBody_fv, fv_var]
  decide

theorem programCodeTerm_start {E : AlphaTerm}
    (hE : E.Closed) :
    Relation.ReflTransGen Beta (app programCodeTerm E)
      (programCodeBody E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (programCodeBody (var 30))) E) (programCodeBody E) := by
    convert Beta.contract 30 (programCodeBody (var 30)) E using 1
    simp [subst_var, programCodeBody_subst]
  exact (Relation.ReflTransGen.single h0)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Codes of closed programs and their inputs
-/
theorem programCodeTerm_apply (e : ℕ) :
    Relation.ReflTransGen Beta (app programCodeTerm (numeral e))
      (numeral (Term.programSyntax e).code) := by
  apply (programCodeTerm_start (numeral_closed _)).trans
  unfold programCodeBody
  apply (beta_steps_app_left (beta_steps_app_left
    (beta_steps_app_right zeroTestTerm (closedSyntaxTerm_apply e)) _) _).trans
  unfold Term.programSyntax
  by_cases hc : (Term.decode e).fv = ∅
  · simp only [ite_eq_left hc, Term.code_decode]
    exact branch_succ 0 _ _
  · simp only [ite_eq_right hc]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)

def programInputCodeBody (E N : AlphaTerm) : AlphaTerm :=
  app (app applicationCodeTerm (app programCodeTerm E)) (app numeralCodeTerm N)

theorem programInputCodeBody_fv (E N : AlphaTerm) :
    (programInputCodeBody E N).fv = E.fv ∪ N.fv := by
  ext x
  simp only [programInputCodeBody, fv_app, (show (applicationCodeTerm).fv = ∅ from applicationCode_closed), (show (programCodeTerm).fv = ∅ from programCodeTerm_closed), (show (numeralCodeTerm).fv = ∅ from numeralCodeTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem programInputCodeBody_subst (E N W : AlphaTerm) (x : ℕ) :
    (programInputCodeBody E N).subst x W =
      programInputCodeBody (E.subst x W) (N.subst x W) := by
  simp only [programInputCodeBody, subst_app, subst_closed _ _ _ applicationCode_closed, subst_closed _ _ _ programCodeTerm_closed, subst_closed _ _ _ numeralCodeTerm_closed]

def programInputCodeTerm : AlphaTerm := (lam 30 (lam 31 (programInputCodeBody (var 30) (var 31))))

@[simp] theorem programInputCodeTerm_closed : programInputCodeTerm.Closed := by
  unfold programInputCodeTerm Closed
  simp only [fv_lam, programInputCodeBody_fv, fv_var]
  decide

theorem programInputCodeTerm_start {E N : AlphaTerm}
    (hE : E.Closed) (hN : N.Closed) :
    Relation.ReflTransGen Beta (app (app programInputCodeTerm E) N)
      (programInputCodeBody E N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfN : N.fv = ∅ := hN
  have h0 : Beta (app (lam 30 (lam 31 (programInputCodeBody (var 30) (var 31)))) E) (lam 31 (programInputCodeBody E (var 31))) := by
    convert Beta.contract 30 (lam 31 (programInputCodeBody (var 30) (var 31))) E using 1
    simp [subst_lam_fresh, subst_var, programInputCodeBody_subst, hfE]
  have h1 : Beta (app (lam 31 (programInputCodeBody E (var 31))) N) (programInputCodeBody E N) := by
    convert Beta.contract 31 (programInputCodeBody E (var 31)) N using 1
    simp [subst_var, programInputCodeBody_subst, subst_closed, hE]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) N).trans
  exact (Relation.ReflTransGen.single h1)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Codes of closed programs and their inputs
-/
theorem programInputCodeTerm_apply (e n : ℕ) :
    Relation.ReflTransGen Beta (app (app programInputCodeTerm (numeral e)) (numeral n))
      (numeral (Term.app (Term.programSyntax e) (Term.churchNumeral n)).code) :=
  (programInputCodeTerm_start (numeral_closed _) (numeral_closed _)).trans
    ((beta_steps_app (beta_steps_app_right applicationCodeTerm (programCodeTerm_apply e))
      (numeralCodeTerm_apply n)).trans
      (applicationCodeTerm_apply (Term.programSyntax e) (Term.churchNumeral n)))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    We can now test a proposed numerical output without selecting a single reduction path. Define
    $$\begin{aligned}
    \LambdaOutputTest&:=\lambdaab{e}{\lambdaab{n}{\lambdaab{m}{\lambdaab{s}{
     \LambdaBoundedBetaProgram\,(\LambdaProgramInputCode\,e\,n)
     (\LambdaNumeralCodeProgram\,m)\,s}}}},\\
    \LambdaOutputCandidate&:=\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
     \LambdaOutputTest\,e\,n\,(\LambdaNumericProjection{1}\,k)
     (\LambdaNumericProjection{2}\,k)}}}.
    \end{aligned}$$
    A candidate $k=\NatPair{m}{s}$ combines the proposed output $m$ and the finite search stage $s$. Both displayed programs are closed. Searching such pairs treats every possible output and every finite certificate bound.
-/
def outputTestBody (E N M S : AlphaTerm) : AlphaTerm :=
  app (app (app boundedBetaTerm
    (app (app programInputCodeTerm E) N)) (app numeralCodeTerm M)) S

theorem outputTestBody_fv (E N M S : AlphaTerm) :
    (outputTestBody E N M S).fv = E.fv ∪ N.fv ∪ M.fv ∪ S.fv := by
  ext x
  simp only [outputTestBody, fv_app, (show (boundedBetaTerm).fv = ∅ from boundedBetaTerm_closed), (show (programInputCodeTerm).fv = ∅ from programInputCodeTerm_closed), (show (numeralCodeTerm).fv = ∅ from numeralCodeTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem outputTestBody_subst (E N M S W : AlphaTerm) (x : ℕ) :
    (outputTestBody E N M S).subst x W =
      outputTestBody (E.subst x W) (N.subst x W) (M.subst x W) (S.subst x W) := by
  simp only [outputTestBody, subst_app, subst_closed _ _ _ boundedBetaTerm_closed, subst_closed _ _ _ programInputCodeTerm_closed, subst_closed _ _ _ numeralCodeTerm_closed]

def outputTestTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (outputTestBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem outputTestTerm_closed : outputTestTerm.Closed := by
  unfold outputTestTerm Closed
  simp only [fv_lam, outputTestBody_fv, fv_var]
  decide

theorem outputTestTerm_start {E N M S : AlphaTerm}
    (hE : E.Closed) (hN : N.Closed) (hM : M.Closed) (hS : S.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app outputTestTerm E) N) M) S)
      (outputTestBody E N M S) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfN : N.fv = ∅ := hN
  have hfM : M.fv = ∅ := hM
  have hfS : S.fv = ∅ := hS
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (outputTestBody (var 30) (var 31) (var 32) (var 33)))))) E) (lam 31 (lam 32 (lam 33 (outputTestBody E (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (outputTestBody (var 30) (var 31) (var 32) (var 33))))) E using 1
    simp [subst_lam_fresh, subst_var, outputTestBody_subst, hfE]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (outputTestBody E (var 31) (var 32) (var 33))))) N) (lam 32 (lam 33 (outputTestBody E N (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (outputTestBody E (var 31) (var 32) (var 33)))) N using 1
    simp [subst_lam_fresh, subst_var, outputTestBody_subst, subst_closed, hE, hfN]
  have h2 : Beta (app (lam 32 (lam 33 (outputTestBody E N (var 32) (var 33)))) M) (lam 33 (outputTestBody E N M (var 33))) := by
    convert Beta.contract 32 (lam 33 (outputTestBody E N (var 32) (var 33))) M using 1
    simp [subst_lam_fresh, subst_var, outputTestBody_subst, subst_closed, hE, hN, hfM]
  have h3 : Beta (app (lam 33 (outputTestBody E N M (var 33))) S) (outputTestBody E N M S) := by
    convert Beta.contract 33 (outputTestBody E N M (var 33)) S using 1
    simp [subst_var, outputTestBody_subst, subst_closed, hE, hN, hM]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) N) M) S).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) M) S).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) S).trans
  exact (Relation.ReflTransGen.single h3)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    First compute the code of the program applied to its input and the code of the proposed output numeral. The finite-stage reduction tester gives the first formula. The two projections of a candidate pair supply exactly its output and stage, so the candidate program gives the same result. Uniqueness of numeral outputs shows that a candidate program reduces to one exactly when its Boolean test is true; a false test already yields zero.

    A reduction of $P_e\ChurchNumeral{n}$ to $\ChurchNumeral{m}$ has a finite accepted certificate between the chosen representatives. Some stage exceeds its code, so the corresponding candidate succeeds. Conversely, a successful candidate gives a true finite-stage test and hence the asserted reduction. If two candidates succeed, both proposed numerals are outputs of the same term $P_e\ChurchNumeral{n}$. Uniqueness of numeral outputs makes their numerical values equal.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Finite tests for numerical outputs
-/
theorem outputTestTerm_apply (e n m s : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app (app outputTestTerm (numeral e)) (numeral n)) (numeral m)) (numeral s))
      (numeral (if Term.outputTest e n m s then 1 else 0)) :=
  (outputTestTerm_start (numeral_closed _) (numeral_closed _)
    (numeral_closed _) (numeral_closed _)).trans
    ((beta_steps_app_left (beta_steps_app
      (beta_steps_app_right boundedBetaTerm (programInputCodeTerm_apply e n))
      (numeralCodeTerm_apply m)) _).trans
      (boundedBetaTerm_code (.app (Term.programSyntax e) (Term.churchNumeral n)) (Term.churchNumeral m) s))

def outputCandidateBody (E N K : AlphaTerm) : AlphaTerm :=
  app (app (app (app outputTestTerm E) N)
    (app (numericalProjectionTerm true) K)) (app (numericalProjectionTerm false) K)

theorem outputCandidateBody_fv (E N K : AlphaTerm) :
    (outputCandidateBody E N K).fv = E.fv ∪ N.fv ∪ K.fv := by
  ext x
  simp only [outputCandidateBody, fv_app, (show (outputTestTerm).fv = ∅ from outputTestTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem outputCandidateBody_subst (E N K W : AlphaTerm) (x : ℕ) :
    (outputCandidateBody E N K).subst x W =
      outputCandidateBody (E.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [outputCandidateBody, subst_app, subst_closed _ _ _ outputTestTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def outputCandidateTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (outputCandidateBody (var 30) (var 31) (var 32)))))

@[simp] theorem outputCandidateTerm_closed : outputCandidateTerm.Closed := by
  unfold outputCandidateTerm Closed
  simp only [fv_lam, outputCandidateBody_fv, fv_var]
  decide

theorem outputCandidateTerm_start {E N K : AlphaTerm}
    (hE : E.Closed) (hN : N.Closed) (hK : K.Closed) :
    Relation.ReflTransGen Beta (app (app (app outputCandidateTerm E) N) K)
      (outputCandidateBody E N K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfN : N.fv = ∅ := hN
  have hfK : K.fv = ∅ := hK
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (outputCandidateBody (var 30) (var 31) (var 32))))) E) (lam 31 (lam 32 (outputCandidateBody E (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (outputCandidateBody (var 30) (var 31) (var 32)))) E using 1
    simp [subst_lam_fresh, subst_var, outputCandidateBody_subst, hfE]
  have h1 : Beta (app (lam 31 (lam 32 (outputCandidateBody E (var 31) (var 32)))) N) (lam 32 (outputCandidateBody E N (var 32))) := by
    convert Beta.contract 31 (lam 32 (outputCandidateBody E (var 31) (var 32))) N using 1
    simp [subst_lam_fresh, subst_var, outputCandidateBody_subst, subst_closed, hE, hfN]
  have h2 : Beta (app (lam 32 (outputCandidateBody E N (var 32))) K) (outputCandidateBody E N K) := by
    convert Beta.contract 32 (outputCandidateBody E N (var 32)) K using 1
    simp [subst_var, outputCandidateBody_subst, subst_closed, hE, hN]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) N) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) K).trans
  exact (Relation.ReflTransGen.single h2)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Finite tests for numerical outputs
-/
theorem outputCandidateTerm_apply (e n k : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app outputCandidateTerm (numeral e)) (numeral n)) (numeral k))
      (numeral (if Term.outputCandidate e n k then 1 else 0)) :=
  (outputCandidateTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
    ((beta_steps_app
      (beta_steps_app_right _ (numericalProjectionTerm_apply true k))
      (numericalProjectionTerm_apply false k)).trans
      (outputTestTerm_apply e n (Nat.unpair k).1 (Nat.unpair k).2))

theorem outputTest_exists_iff (e n m : ℕ) :
    (∃ s, Term.outputTest e n m s = true) ↔
      Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m) := by
  simpa only [Term.outputTest, ← app_mk, Term.mk_programSyntax, Term.mk_churchNumeral]
    using (Term.beta_steps_iff_bounded_test
      (.app (Term.programSyntax e) (Term.churchNumeral n)) (Term.churchNumeral m)).symm

theorem outputCandidate_accept_iff (e n k : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app outputCandidateTerm (numeral e)) (numeral n)) (numeral k)) (numeral 1) ↔
      Term.outputCandidate e n k = true := by
  constructor
  · intro h
    have he := numeral_output_unique (outputCandidateTerm_apply e n k) h
    cases hb : Term.outputCandidate e n k <;> simp_all
  · intro h
    simpa only [h, ite_true] using outputCandidateTerm_apply e n k

theorem program_output_iff_candidate (e n m : ℕ) :
    Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m) ↔
      ∃ k, (Nat.unpair k).1 = m ∧
        Relation.ReflTransGen Beta
          (app (app (app outputCandidateTerm (numeral e)) (numeral n)) (numeral k)) (numeral 1) := by
  rw [← outputTest_exists_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨Nat.pair m s, by simp, (outputCandidate_accept_iff _ _ _).mpr ?_⟩
    simpa only [Term.outputCandidate, Nat.unpair_pair] using hs
  · rintro ⟨k, hk, ht⟩
    have h := (outputCandidate_accept_iff _ _ _).mp ht
    exact ⟨(Nat.unpair k).2, by simpa only [Term.outputCandidate, hk] using h⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Finite tests for numerical outputs
-/
theorem program_output_iff_paired_candidate (e n m : ℕ) :
    Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m) ↔
      ∃ s, Relation.ReflTransGen Beta
        (app (app (app outputCandidateTerm (numeral e)) (numeral n)) (numeral (Nat.pair m s)))
        (numeral 1) := by
  rw [program_output_iff_candidate]
  constructor
  · rintro ⟨k, hk, ht⟩
    refine ⟨(Nat.unpair k).2, ?_⟩
    have he : Nat.pair m (Nat.unpair k).2 = k := by rw [← hk, Nat.pair_unpair]
    simpa only [he] using ht
  · rintro ⟨s, hs⟩
    exact ⟨Nat.pair m s, by simp, hs⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Finite tests for numerical outputs
-/
theorem accepted_candidate_outputs_equal {e n k l : ℕ}
    (hk : Term.outputCandidate e n k = true) (hl : Term.outputCandidate e n l = true) :
    (Nat.unpair k).1 = (Nat.unpair l).1 :=
  numeral_output_unique ((outputTest_exists_iff _ _ _).mp ⟨_, hk⟩)
    ((outputTest_exists_iff _ _ _).mp ⟨_, hl⟩)

end AlphaTerm
end PolishSpaceBook.NamedLambda
