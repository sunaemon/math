module

public import PolishSpaceBook.LambdaProgramCodes
public import PolishSpaceBook.LambdaSearchResult

@[expose] public section

/-! # Exact universal evaluation by a closed lambda term

The total candidate tester drives sequential search. The successful branch
projects the output component. Infinite failed stages exclude every numerical
output, so the resulting evaluator has exactly the indexed program's graph.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

set_option maxRecDepth 4096

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The candidate tester returns one on success, whereas search stops when its test returns zero. Reverse the answers and define
    $$\begin{aligned}
    T&:=\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
     \LambdaZeroTest\,(\LambdaOutputCandidate\,e\,n\,k)\,\ChurchNumeral{1}\,\ChurchNumeral{0}}}},\\
    \LambdaOutputSearch&:=\lambdaab{e}{\lambdaab{n}{
     \LambdaResultSearch\,(Ten)\,\LambdaNumericProjection{1}}}.
    \end{aligned}$$
    All constants are closed and all displayed variables are bound. Thus $\LambdaOutputSearch$ is one closed term receiving the program index and its numerical input. It searches the candidate codes in order and extracts the output component in the successful branch.
-/
def outputSearchTestBody (E N K : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm
    (app (app (app outputCandidateTerm E) N) K)) (numeral 1)) (numeral 0)

theorem outputSearchTestBody_fv (E N K : AlphaTerm) :
    (outputSearchTestBody E N K).fv = E.fv ∪ N.fv ∪ K.fv := by
  ext x
  simp only [outputSearchTestBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (outputCandidateTerm).fv = ∅ from outputCandidateTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), (show (numeral 1).fv = ∅ from numeral_closed 1), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem outputSearchTestBody_subst (E N K W : AlphaTerm) (x : ℕ) :
    (outputSearchTestBody E N K).subst x W =
      outputSearchTestBody (E.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [outputSearchTestBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ outputCandidateTerm_closed ,subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1)]

def outputSearchTestTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (outputSearchTestBody (var 30) (var 31) (var 32)))))

@[simp] theorem outputSearchTestTerm_closed : outputSearchTestTerm.Closed := by
  unfold outputSearchTestTerm Closed
  simp only [fv_lam, outputSearchTestBody_fv, fv_var]
  decide

theorem outputSearchTestTerm_start {E N K : AlphaTerm}
    (hE : E.Closed) (hN : N.Closed) (hK : K.Closed) :
    Relation.ReflTransGen Beta (app (app (app outputSearchTestTerm E) N) K)
      (outputSearchTestBody E N K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfN : N.fv = ∅ := hN
  have hfK : K.fv = ∅ := hK
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (outputSearchTestBody (var 30) (var 31) (var 32))))) E) (lam 31 (lam 32 (outputSearchTestBody E (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (outputSearchTestBody (var 30) (var 31) (var 32)))) E using 1
    simp [subst_lam_fresh, subst_var, outputSearchTestBody_subst, hfE]
  have h1 : Beta (app (lam 31 (lam 32 (outputSearchTestBody E (var 31) (var 32)))) N) (lam 32 (outputSearchTestBody E N (var 32))) := by
    convert Beta.contract 31 (lam 32 (outputSearchTestBody E (var 31) (var 32))) N using 1
    simp [subst_lam_fresh, subst_var, outputSearchTestBody_subst, subst_closed, hE, hfN]
  have h2 : Beta (app (lam 32 (outputSearchTestBody E N (var 32))) K) (outputSearchTestBody E N K) := by
    convert Beta.contract 32 (outputSearchTestBody E N (var 32)) K using 1
    simp [subst_var, outputSearchTestBody_subst, subst_closed, hE, hN]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) N) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) K).trans
  exact (Relation.ReflTransGen.single h2)

theorem outputSearchTestTerm_apply (e n k : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app outputSearchTestTerm (numeral e)) (numeral n)) (numeral k))
      (numeral (if Term.outputCandidate e n k then 0 else 1)) := by
  apply (outputSearchTestTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  unfold outputSearchTestBody
  apply (beta_steps_app_left (beta_steps_app_left
    (beta_steps_app_right zeroTestTerm (outputCandidateTerm_apply e n k)) _) _).trans
  cases h : Term.outputCandidate e n k with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)
  | true =>
    simp only [ite_true]
    exact branch_succ 0 _ _

def outputSearchBody (E N : AlphaTerm) : AlphaTerm :=
  app (app resultSearchTerm (app (app outputSearchTestTerm E) N))
    (numericalProjectionTerm true)

theorem outputSearchBody_fv (E N : AlphaTerm) :
    (outputSearchBody E N).fv = E.fv ∪ N.fv := by
  ext x
  simp only [outputSearchBody, fv_app, (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (resultSearchTerm).fv = ∅ from resultSearchTerm_closed), (show (outputSearchTestTerm).fv = ∅ from outputSearchTestTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem outputSearchBody_subst (E N W : AlphaTerm) (x : ℕ) :
    (outputSearchBody E N).subst x W =
      outputSearchBody (E.subst x W) (N.subst x W) := by
  simp only [outputSearchBody, subst_app, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ resultSearchTerm_closed, subst_closed _ _ _ outputSearchTestTerm_closed]

def outputSearchTerm : AlphaTerm := (lam 30 (lam 31 (outputSearchBody (var 30) (var 31))))

@[simp] theorem outputSearchTerm_closed : outputSearchTerm.Closed := by
  unfold outputSearchTerm Closed
  simp only [fv_lam, outputSearchBody_fv, fv_var]
  decide

theorem outputSearchTerm_start {E N : AlphaTerm}
    (hE : E.Closed) (hN : N.Closed) :
    Relation.ReflTransGen Beta (app (app outputSearchTerm E) N)
      (outputSearchBody E N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfN : N.fv = ∅ := hN
  have h0 : Beta (app (lam 30 (lam 31 (outputSearchBody (var 30) (var 31)))) E) (lam 31 (outputSearchBody E (var 31))) := by
    convert Beta.contract 30 (lam 31 (outputSearchBody (var 30) (var 31))) E using 1
    simp [subst_lam_fresh, subst_var, outputSearchBody_subst, hfE]
  have h1 : Beta (app (lam 31 (outputSearchBody E (var 31))) N) (outputSearchBody E N) := by
    convert Beta.contract 31 (outputSearchBody E (var 31)) N using 1
    simp [subst_var, outputSearchBody_subst, subst_closed, hE]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) N).trans
  exact (Relation.ReflTransGen.single h1)

theorem outputSearchTerm_hit (e n j : ℕ)
    (hj : Term.outputCandidate e n j = true)
    (hbefore : ∀ k < j, Term.outputCandidate e n k = false) :
    Relation.ReflTransGen Beta (app (app outputSearchTerm (numeral e)) (numeral n))
      (numeral (Nat.unpair j).1) := by
  apply (outputSearchTerm_start (numeral_closed _) (numeral_closed _)).trans
  have hs := resultSearchTerm_hit
    (closed_app (closed_app outputSearchTestTerm_closed (numeral_closed _)) (numeral_closed _))
    (numericalProjectionTerm_closed true) j
    (by simpa only [hj, ite_true] using outputSearchTestTerm_apply e n j)
    (fun k hk => ⟨0, by simpa only [hbefore k hk, Bool.false_eq_true, ite_false]
      using outputSearchTestTerm_apply e n k⟩)
  exact hs.trans (numericalProjectionTerm_apply true j)

/-- Every actual numerical output is found by the closed search term. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Suppose the indexed program outputs $m$. The candidate-test theorem supplies a successful pair whose output component is $m$. Let $j$ be the least successful candidate code. Every preceding candidate fails, so $T\ChurchNumeral{e}\ChurchNumeral{n}$ returns one before $j$ and zero at $j$. Search with the result function $\LambdaNumericProjection{1}$ reaches the first projection of $\ChurchNumeral{j}$. All successful candidates have the same output component, so this projection reduces to $\ChurchNumeral{m}$.

    If the indexed program has no numerical output, every candidate test fails. The reversed tests all return one, so the no-output part of the search lemma applies. The two outer contractions supplying the index and input preserve any putative numeral output by confluence and normality of numerals; hence the full term has no numerical output either.

    Finally, if the indexed program has an output, completeness produces that same numeral from the search term. Uniqueness of numeral outputs excludes any different value. Together with the no-output case this proves both directions without a termination assumption.
    \end{proof}
-/
theorem outputSearchTerm_complete {e n m : ℕ}
    (h : Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m)) :
    Relation.ReflTransGen Beta (app (app outputSearchTerm (numeral e)) (numeral n))
      (numeral m) := by
  obtain ⟨s, hs⟩ := (outputTest_exists_iff e n m).mpr h
  have hc : Term.outputCandidate e n (Nat.pair m s) = true := by
    simpa only [Term.outputCandidate, Nat.unpair_pair] using hs
  have hex : ∃ k, Term.outputCandidate e n k = true := ⟨_, hc⟩
  have hj := Nat.find_spec hex
  have he : (Nat.unpair (Nat.find hex)).1 = m := by
    simpa only [Nat.unpair_pair] using accepted_candidate_outputs_equal hj hc
  rw [← he]
  apply outputSearchTerm_hit e n (Nat.find hex) hj
  intro k hk
  have hn := Nat.find_min hex hk
  cases hb : Term.outputCandidate e n k
  · rfl
  · exact False.elim (hn hb)

/-- Exactness on the terminating domain, used before handling the empty-output case. -/
theorem outputSearchTerm_runs_iff_of_terminates (e n : ℕ)
    (hex : ∃ r, Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral r))
    (m : ℕ) :
    Relation.ReflTransGen Beta (app (app outputSearchTerm (numeral e)) (numeral n)) (numeral m) ↔
      Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m) := by
  constructor
  · intro hm
    obtain ⟨r, hr⟩ := hex
    have he := numeral_output_unique hm (outputSearchTerm_complete hr)
    simpa only [he] using hr
  · exact outputSearchTerm_complete

/-- Failed candidate tests force infinitely many head stages, excluding every numeral. -/
theorem outputSearchTerm_no_output (e n : ℕ)
    (hn : ∀ m, ¬ Relation.ReflTransGen Beta
      (app (Term.closedProgram e) (numeral n)) (numeral m)) (m : ℕ) :
    ¬ Relation.ReflTransGen Beta
      (app (app outputSearchTerm (numeral e)) (numeral n)) (numeral m) := by
  have hc (k : ℕ) : Term.outputCandidate e n k = false := by
    cases h : Term.outputCandidate e n k with
    | false => rfl
    | true =>
      exact False.elim (hn (Nat.unpair k).1
        ((outputTest_exists_iff e n (Nat.unpair k).1).mp ⟨(Nat.unpair k).2, h⟩))
  intro hm
  have hb := numeral_after_reduction
    (outputSearchTerm_start (numeral_closed e) (numeral_closed n)) hm
  apply resultSearchTerm_no_output
    (closed_app (closed_app outputSearchTestTerm_closed (numeral_closed e)) (numeral_closed n))
    (numericalProjectionTerm_closed true) _ m hb
  intro k
  exact ⟨0, by simpa only [hc k, Bool.false_eq_true, ite_false]
    using outputSearchTestTerm_apply e n k⟩

/-- The constructed ordinary universal evaluator has exactly the original numerical graph. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Exact numerical output search
-/
theorem outputSearchTerm_runs_iff (e n m : ℕ) :
    Relation.ReflTransGen Beta (app (app outputSearchTerm (numeral e)) (numeral n)) (numeral m) ↔
      Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m) := by
  classical
  by_cases hex : ∃ r, Relation.ReflTransGen Beta
      (app (Term.closedProgram e) (numeral n)) (numeral r)
  · exact outputSearchTerm_runs_iff_of_terminates e n hex m
  · have hn : ∀ r, ¬ Relation.ReflTransGen Beta
        (app (Term.closedProgram e) (numeral n)) (numeral r) := by
      intro r hr
      exact hex ⟨r, hr⟩
    exact iff_of_false (outputSearchTerm_no_output e n hn m) (hn m)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For each $e$, define the partial numerical function $\varphi_e$ by
    $$\varphi_e(n)=m\quad\Longleftrightarrow\quad
    P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}.$$
    Uniqueness of numeral outputs makes this a partial function. Write $\simeq$ for equality of partial values: either both sides are undefined or both are defined and equal. The closed term $\LambdaOutputSearch$ just constructed computes a \termdefineas{universal program}{universal evaluator}, a partial function $\PartialFunctionMap{U}{\omega\times\omega}{\omega}$ satisfying
    $$
    U(e,n)\simeq\varphi_e(n).
    $$
    Indeed, the exact-output proposition proves equality of every numerical value and of the domains. The evaluator searches finite reduction certificates and extracts an output only after its certificate is accepted. Thus program indices and the search over computations are both handled by lambda terms on natural-number codes.
-/
theorem outputSearchTerm_domain_iff (e n : ℕ) :
    (∃ m, Relation.ReflTransGen Beta
      (app (app outputSearchTerm (numeral e)) (numeral n)) (numeral m)) ↔
    (∃ m, Relation.ReflTransGen Beta
      (app (Term.closedProgram e) (numeral n)) (numeral m)) :=
  exists_congr (fun m => outputSearchTerm_runs_iff e n m)

end PolishSpaceBook.NamedLambda.AlphaTerm
