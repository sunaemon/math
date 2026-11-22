module

public import PolishSpaceBook.LambdaArithmeticTrees
public import PolishSpaceBook.LambdaRelativeEnumerations

@[expose] public section

/-! # Tree presentations of total and nontotal lambda indices

All finite trials terminate, including those for partial input programs.
The two projections encode numerical quantifiers, not a totality decider.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def jointCandidateBody (O Z : AlphaTerm) : AlphaTerm :=
  app (app (app (app oracleOutputCandidateTerm O)
    (app (numericalProjectionTerm true) Z))
    (app (numericalProjectionTerm true) (app (numericalProjectionTerm false) Z)))
    (app (numericalProjectionTerm false) (app (numericalProjectionTerm false) Z))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For totality, the jointly deciding program is
    $$\LambdaTermName{totalityTrial}:=\lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,
     (\LambdaNumericProjection{1}z)\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z))\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z))}}.$$
    Its numerical input is $\NatPair{e}{\NatPair{n}{k}}$.
-/
def jointCandidateProgram : AlphaTerm := lam 70 (lam 71 (jointCandidateBody (var 70) (var 71)))

theorem jointCandidateProgram_closed : jointCandidateProgram.Closed := by
  unfold jointCandidateProgram jointCandidateBody Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [oracleOutputCandidateTerm_closed,numericalProjectionTerm_closed,numericalProjectionTerm_closed]
  decide

theorem jointCandidateProgram_start (z : ℕ) :
    Relation.ReflTransGen Beta (app (app jointCandidateProgram (var 0)) (numeral z))
      (jointCandidateBody (var 0) (numeral z)) := by
  have h₁ : Beta (app jointCandidateProgram (var 0))
      (lam 71 (jointCandidateBody (var 0) (var 71))) := by
    have he : (lam 71 (jointCandidateBody (var 70) (var 71))).subst 70 (var 0) =
        lam 71 (jointCandidateBody (var 0) (var 71)) := by
      rw [subst_lam_fresh _ _ 71 70 (by decide) (by simp [fv_var])]
      simp [jointCandidateBody,subst_app,subst_var,subst_closed _ _ _ oracleOutputCandidateTerm_closed,
        subst_closed _ _ _ (numericalProjectionTerm_closed true),
        subst_closed _ _ _ (numericalProjectionTerm_closed false)]
    change Beta (app (lam 70 (lam 71 (jointCandidateBody (var 70) (var 71)))) (var 0)) _
    rw [← he]; exact Beta.contract _ _ _
  have h₂ : Beta (app (lam 71 (jointCandidateBody (var 0) (var 71))) (numeral z))
      (jointCandidateBody (var 0) (numeral z)) := by
    convert Beta.contract 71 _ (numeral z) using 1
    simp [jointCandidateBody,subst_app,subst_var,subst_closed _ _ _ oracleOutputCandidateTerm_closed,
      subst_closed _ _ _ (numericalProjectionTerm_closed true),
      subst_closed _ _ _ (numericalProjectionTerm_closed false)]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Two beta contractions expose the candidate tester. Numerical projections supply the three arguments
    $e,n,k$. The output-candidate theorem then gives one exactly when the finite trial succeeds and zero
    otherwise. In particular this program terminates even when the indexed program fails to return a
    numeral. Substituting $\LambdaTermName{totalityTrial}$ for $\LambdaTermName{numberPredicate}$ in the preceding
    row construction gives the two trees for totality
    and its complement without deciding an unbounded search.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For totality, the jointly deciding program is
    $$\LambdaTermName{totalityTrial}:=\lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,
     (\LambdaNumericProjection{1}z)\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z))\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z))}}.$$
    Its numerical input is $\NatPair{e}{\NatPair{n}{k}}$.
-/
theorem jointCandidateProgram_computes : UniformNumericalComputes jointCandidateProgram
    (fun ε z => if Term.oracleOutputCandidate ε z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2
      then 1 else 0) := by
  refine ⟨jointCandidateProgram_closed,fun ε z => ?_⟩
  apply (beta_steps_oracle (jointCandidateProgram_start z)).trans
  have hfst := beta_steps_oracle (p := ε) (numericalProjectionTerm_apply true z)
  have hsnd := beta_steps_oracle (p := ε) (numericalProjectionTerm_apply false z)
  have hnfst := (oracle_steps_app_right (numericalProjectionTerm true) hsnd).trans
    (beta_steps_oracle (numericalProjectionTerm_apply true z.unpair.2))
  have hnsnd := (oracle_steps_app_right (numericalProjectionTerm false) hsnd).trans
    (beta_steps_oracle (numericalProjectionTerm_apply false z.unpair.2))
  exact (oracle_steps_app (oracle_steps_app
    (oracle_steps_app_right (app oracleOutputCandidateTerm (var 0)) hfst) hnfst) hnsnd).trans
    (oracleOutputCandidateTerm_apply ε z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2)

end NamedLambda.AlphaTerm
namespace LambdaTree

/-- Numerical totality of an indexed program at the fixed parameter. -/
def TotalIndex (ε : ℕ → ℕ) (e : ℕ) : Prop :=
  ∀ n, ∃ m, OracleRuns ε (Term.closedProgram e) n m

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $R(e,n,k)$ be the finite output-candidate test of §{sec:lambda-input-universal-evaluation}, where
    $k=\NatPair{m}{h}$ specifies the proposed output $m$ and a finite search bound $h$.
    This test terminates on every triple, even if the program with index $e$ does not terminate on input $n$.
    By soundness and completeness of the test, the program with index $e$ is total relative to $\varepsilon$
    exactly when $\forall n\,\exists k\ R(e,n,k)$.
    Apply the preceding lemma. It constructs finite tree tests, not a decision procedure for totality.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set of total computable functions is countable but not closed; totality is a $\lPi^0_2$ condition on indices,
        not a topological closedness condition on points.
-/
theorem totalIndex_iff_candidates (ε : ℕ → ℕ) (e : ℕ) :
    TotalIndex ε e ↔ ∀ n, ∃ k, Term.oracleOutputCandidate ε e n k = true := by
  apply forall_congr'
  intro n
  simpa only [candidateTest,Nat.unpair_pair] using (LambdaRelative.candidateTest_exists_iff ε e n).symm

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set of total computable functions is countable but not closed; totality is a $\lPi^0_2$ condition on indices,
        not a topological closedness condition on points.
-/
theorem jointCandidate_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × ℕ) =>
      Term.oracleOutputCandidate ε z.1 z.2.1 z.2.2 = true) := by
  refine ⟨jointCandidateProgram,jointCandidateProgram_closed,fun z => ⟨?_,?_⟩⟩ <;> intro hz
  · simpa [Encodable.encode,Encodable.encodeSigma,hz]
      using jointCandidateProgram_computes.2 ε (Encodable.encode z)
  · simpa [Encodable.encode,Encodable.encodeSigma,hz]
      using jointCandidateProgram_computes.2 ε (Encodable.encode z)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Tree presentations of total program indices
-/
theorem complemented_totalIndices (ε : ℕ → ℕ) :
    Complemented ε {x | TotalIndex ε (x 0)} := by
  simpa only [totalIndex_iff_candidates] using
    complemented_forall_exists (R := fun e n k => Term.oracleOutputCandidate ε e n k = true)
      (jointCandidate_decidable ε)

end LambdaTree
end PolishSpaceBook
