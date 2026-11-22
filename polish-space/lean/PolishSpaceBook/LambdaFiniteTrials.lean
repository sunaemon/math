module

public import PolishSpaceBook.LambdaOracleOutputSearch

@[expose] public section

/-! # Total finite trials for the indexed lambda programs

A stage pairs a proposed output with a finite certificate-search bound.
Failure is zero and success with output m is m+1. No instruction language
or cross-model compilation is used.
-/
namespace PolishSpaceBook.NamedLambda
namespace Term

def finiteTrial (p : ℕ → ℕ) (e n k : ℕ) : ℕ :=
  if oracleOutputCandidate p e n k then (Nat.unpair k).1 + 1 else 0

end Term
namespace AlphaTerm
set_option maxRecDepth 4096

def finiteTrialBody (O E N K : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm
    (app (app (app (app oracleOutputCandidateTerm O) E) N) K)) (numeral 0))
    (app successorTerm (app (numericalProjectionTerm true) K))

theorem finiteTrialBody_fv (O E N K : AlphaTerm) :
    (finiteTrialBody O E N K).fv = O.fv ∪ E.fv ∪ N.fv ∪ K.fv := by
  ext x
  simp only [finiteTrialBody, fv_app,
    (show zeroTestTerm.fv = ∅ from zeroTestTerm_closed),
    (show oracleOutputCandidateTerm.fv = ∅ from oracleOutputCandidateTerm_closed),
    (show (numeral 0).fv = ∅ from numeral_closed 0),
    (show successorTerm.fv = ∅ from successorTerm_closed),
    (show (numericalProjectionTerm true).fv = ∅ from numericalProjectionTerm_closed true),
    Finset.mem_union, Finset.notMem_empty]
  tauto

theorem finiteTrialBody_subst (O E N K W : AlphaTerm) (x : ℕ) :
    (finiteTrialBody O E N K).subst x W =
      finiteTrialBody (O.subst x W) (E.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [finiteTrialBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ oracleOutputCandidateTerm_closed,
    subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ successorTerm_closed,
    subst_closed _ _ _ (numericalProjectionTerm_closed true)]

def finiteTrialTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (finiteTrialBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem finiteTrialTerm_closed : finiteTrialTerm.Closed := by
  unfold finiteTrialTerm Closed
  simp only [fv_lam, finiteTrialBody_fv, fv_var]
  decide

theorem finiteTrialTerm_start {O E N K : AlphaTerm}
    (hO : O.fv ⊆ {0}) (hE : E.fv ⊆ {0}) (hN : N.fv ⊆ {0}) (hK : K.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app (app (app finiteTrialTerm O) E) N) K)
      (finiteTrialBody O E N K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfO (n : ℕ) (hn : n ≠ 0) := input_fresh hO hn
  have hfE (n : ℕ) (hn : n ≠ 0) := input_fresh hE hn
  have hfN (n : ℕ) (hn : n ≠ 0) := input_fresh hN hn
  have hfK (n : ℕ) (hn : n ≠ 0) := input_fresh hK hn
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (finiteTrialBody (var 30) (var 31) (var 32) (var 33)))))) O) (lam 31 (lam 32 (lam 33 (finiteTrialBody O (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (finiteTrialBody (var 30) (var 31) (var 32) (var 33))))) O using 1
    simp [subst_lam_fresh, subst_var, finiteTrialBody_subst, subst_not_free, hfO]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (finiteTrialBody O (var 31) (var 32) (var 33))))) E) (lam 32 (lam 33 (finiteTrialBody O E (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (finiteTrialBody O (var 31) (var 32) (var 33)))) E using 1
    simp [subst_lam_fresh, subst_var, finiteTrialBody_subst, subst_not_free, hfO, hfE]
  have h2 : Beta (app (lam 32 (lam 33 (finiteTrialBody O E (var 32) (var 33)))) N) (lam 33 (finiteTrialBody O E N (var 33))) := by
    convert Beta.contract 32 (lam 33 (finiteTrialBody O E (var 32) (var 33))) N using 1
    simp [subst_lam_fresh, subst_var, finiteTrialBody_subst, subst_not_free, hfO, hfE, hfN]
  have h3 : Beta (app (lam 33 (finiteTrialBody O E N (var 33))) K) (finiteTrialBody O E N K) := by
    convert Beta.contract 33 (finiteTrialBody O E N (var 33)) K using 1
    simp [subst_var, finiteTrialBody_subst, subst_not_free, hfO, hfE, hfN]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) E) N) K).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) N) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) K).trans
  exact (Relation.ReflTransGen.single h3)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Uniform finite lambda trials
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Decode $k=\NatPair{m}{s}$. A finite reduction certificate consists of a finite answer table and a finite list of beta/query steps. Inspect all certificate codes below $s$. For each code, check the recorded steps, alpha-equivalence at their joins, the initial term $P_eo\ChurchNumeral{n}$, the final numeral $\ChurchNumeral{m}$, and agreement of every recorded answer with $p$. These are finite checks on lambda syntax and finite lists. Their recursions, numerical comparisons and input queries give a single closed lambda term $C$ returning one exactly when some certificate is accepted, and zero otherwise. The constructions in §{sec:lambda-input-check-programs} and §{sec:lambda-input-universal-evaluation} give this term explicitly. Put
    $$\begin{aligned}
    \LambdaFiniteTrial:=\lambdaab{o}{\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
     \LambdaZeroTest\,(Coenk)\,\ChurchNumeral{0}\,
     (\LambdaSucc(\LambdaNumericProjection{1}\,k))}}}}.
    \end{aligned}$$
    Thus a rejected candidate returns zero, and an accepted candidate returns $m+1$. Every check terminates; the original program need not terminate.

    An accepted certificate gives an actual finite beta/query reduction because all its answers agree with $p$. Conversely, every numeral output has a finite reduction, hence a certificate with a finite code. Some bound $s$ includes it. Finally, only finitely many answer tables occur below $s$; the maximum of their queried addresses, plus one, bounds the prefix needed to determine every test result; take zero if there are no queries. This bound depends on $s$, hence on $k$, before the name is supplied. Failure at one stage asserts neither divergence nor nonmembership.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The finite-trial lemma in §{sec:tte-finite-trials} supplies a closed term $\LambdaFiniteTrial$. On a name $p$,
    program index $e$, input $n$, and stage $k$, it always returns zero for failure or $m+1$ for a certified output $m$.
    Every output of the indexed program is certified at some stage, even though the program itself may be partial.
-/
theorem finiteTrialTerm_apply (p : ℕ → ℕ) (e n k : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (app finiteTrialTerm (var 0)) (numeral e)) (numeral n)) (numeral k))
      (numeral (Term.finiteTrial p e n k)) := by
  apply (beta_steps_oracle (finiteTrialTerm_start (by simp [fv_var])
    (numeral_closed e).input_fv (numeral_closed n).input_fv (numeral_closed k).input_fv)).trans
  apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm
    (oracleOutputCandidateTerm_apply p e n k)) (numeral 0)) _).trans
  cases h : Term.oracleOutputCandidate p e n k with
  | false =>
    simp only [Term.finiteTrial, h, Bool.false_eq_true, ite_false]
    exact beta_steps_oracle (branch_zero _ _ (by rw [numeral_closed]; simp))
  | true =>
    simp only [Term.finiteTrial, h, ite_true]
    apply (beta_steps_oracle (branch_succ 0 _ _)).trans
    exact beta_steps_oracle ((beta_steps_app_right successorTerm
      (numericalProjectionTerm_apply true k)).trans (successorTerm_apply _))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Uniform finite lambda trials
-/
theorem finiteTrial_sound {p : ℕ → ℕ} {e n k m : ℕ}
    (h : Term.finiteTrial p e n k = m + 1) :
    OracleRuns p (Term.closedProgram e) n m := by
  unfold Term.finiteTrial at h
  split_ifs at h with hk
  · have hm : (Nat.unpair k).1 = m := Nat.add_right_cancel h
    subst m
    exact (oracle_outputTest_exists_iff p e n _).mp ⟨(Nat.unpair k).2, hk⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Uniform finite lambda trials
-/
theorem finiteTrial_complete {p : ℕ → ℕ} {e n m : ℕ}
    (h : OracleRuns p (Term.closedProgram e) n m) :
    ∃ k, Term.finiteTrial p e n k = m + 1 := by
  obtain ⟨s,hs⟩ := (oracle_outputTest_exists_iff p e n m).mpr h
  refine ⟨Nat.pair m s, ?_⟩
  simp [Term.finiteTrial, Term.oracleOutputCandidate, Nat.unpair_pair, hs]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Uniform finite lambda trials
-/
theorem finiteTrial_eq_of_prefix {p q : ℕ → ℕ} (e n k : ℕ)
    (h : ∀ i < Term.inputTestBound (Nat.unpair k).2, q i = p i) :
    Term.finiteTrial q e n k = Term.finiteTrial p e n k := by
  unfold Term.finiteTrial Term.oracleOutputCandidate
  rw [Term.boundedInputTest_eq_of_prefix _ _ _ h]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The finite-trial lemma in §{sec:tte-finite-trials} supplies a closed term $\LambdaFiniteTrial$. On a name $p$,
    program index $e$, input $n$, and stage $k$, it always returns zero for failure or $m+1$ for a certified output $m$.
    Every output of the indexed program is certified at some stage, even though the program itself may be partial.
-/
theorem finiteTrial_positive_iff (p : ℕ → ℕ) (e n : ℕ) :
    (∃ k, Term.finiteTrial p e n k ≠ 0) ↔
      ∃ m, OracleRuns p (Term.closedProgram e) n m := by
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact ⟨m,finiteTrial_sound hm⟩
  · rintro ⟨m,hm⟩
    obtain ⟨k,hk⟩ := finiteTrial_complete hm
    exact ⟨k,by rw [hk]; omega⟩

end AlphaTerm
end PolishSpaceBook.NamedLambda
