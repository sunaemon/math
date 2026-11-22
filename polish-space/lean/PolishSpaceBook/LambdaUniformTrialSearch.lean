module

public import PolishSpaceBook.LambdaOracleSearchResult
public import PolishSpaceBook.LambdaProgramSpecialization
public import PolishSpaceBook.LambdaNumericalFunctions
public import PolishSpaceBook.LambdaNumericalSearch

@[expose] public section

/-! # One search compiler for arbitrary total finite oracle trials -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def trialCall (A O N K : AlphaTerm) : AlphaTerm := app (app (app A O) N) K

def trialSearchTest (A O N : AlphaTerm) : AlphaTerm :=
  lam 43 (app reverseZeroTerm (trialCall A O N (var 43)))

def trialSearchResult (A O N : AlphaTerm) : AlphaTerm :=
  lam 43 (app predecessorTerm (trialCall A O N (var 43)))

def trialSearchBody (A O N : AlphaTerm) : AlphaTerm :=
  app (app resultSearchTerm (trialSearchTest A O N)) (trialSearchResult A O N)

def trialSearchCompilerTerm : AlphaTerm :=
  lam 40 (lam 41 (lam 42 (trialSearchBody (var 40) (var 41) (var 42))))

theorem trialSearchBody_fv (A O N : AlphaTerm) :
    (trialSearchBody A O N).fv = (A.fv ∪ O.fv ∪ N.fv).erase 43 := by
  ext x
  simp only [trialSearchBody, trialSearchTest, trialSearchResult, trialCall,
    fv_app, fv_lam, fv_var, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  tauto

@[simp] theorem trialSearchCompilerTerm_closed : trialSearchCompilerTerm.Closed := by
  unfold trialSearchCompilerTerm Closed
  simp only [fv_lam, trialSearchBody_fv, fv_var]
  decide

theorem trialSearchBody_subst (A O N W : AlphaTerm) (x : ℕ)
    (hx : 43 ≠ x) (hW : 43 ∉ W.fv) :
    (trialSearchBody A O N).subst x W =
      trialSearchBody (A.subst x W) (O.subst x W) (N.subst x W) := by
  simp only [trialSearchBody, trialSearchTest, trialSearchResult, trialCall, subst_app,
    subst_lam_fresh _ _ 43 x hx hW, subst_closed _ _ _ resultSearchTerm_closed,
    subst_closed _ _ _ reverseZero_computes.1, subst_closed _ _ _ predecessorTerm_closed,
    subst_var, ite_eq_right hx]

theorem trialSearchCompiler_start {A : AlphaTerm} (hA : A.Closed) (a : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app trialSearchCompilerTerm A) (var 0)) (numeral a))
      (trialSearchBody A (var 0) (numeral a)) := by
  have h1 : Beta (app trialSearchCompilerTerm A)
      (lam 41 (lam 42 (trialSearchBody A (var 41) (var 42)))) := by
    convert Beta.contract 40 (lam 41 (lam 42 (trialSearchBody (var 40) (var 41) (var 42)))) A using 1
    · rfl
    have hf (n : ℕ) : n ∉ A.fv := by rw [hA]; simp
    simp [subst_lam_fresh, trialSearchBody_subst, subst_var, hf]
  have h2 : Beta (app (lam 41 (lam 42 (trialSearchBody A (var 41) (var 42)))) (var 0))
      (lam 42 (trialSearchBody A (var 0) (var 42))) := by
    convert Beta.contract 41 (lam 42 (trialSearchBody A (var 41) (var 42))) (var 0) using 1
    simp [subst_lam_fresh, trialSearchBody_subst, fv_var, subst_var, subst_closed _ _ _ hA]
  have h3 : Beta (app (lam 42 (trialSearchBody A (var 0) (var 42))) (numeral a))
      (trialSearchBody A (var 0) (numeral a)) := by
    convert Beta.contract 42 (trialSearchBody A (var 0) (var 42)) (numeral a) using 1
    rw [trialSearchBody_subst _ _ _ _ _ (by decide) (by rw [numeral_closed]; simp)]
    simp [subst_var, subst_closed _ _ _ hA]
  exact (beta_steps_app_left (beta_steps_app_left (.single h1) _) _).trans
    ((beta_steps_app_left (.single h2) _).trans (.single h3))

theorem trialSearchBranch_input {A B : AlphaTerm} (hA : A.Closed) (hB : B.Closed) (a : ℕ) :
    (lam 43 (app B (trialCall A (var 0) (numeral a) (var 43)))).fv ⊆ {0} := by
  simp only [fv_lam, fv_app, trialCall, fv_var]
  rw [hA, hB, numeral_closed]
  decide

theorem trialSearchBranch_start {A B : AlphaTerm} (hA : A.Closed) (hB : B.Closed)
    (a k : ℕ) : Beta
      (app (lam 43 (app B (trialCall A (var 0) (numeral a) (var 43)))) (numeral k))
      (app B (trialCall A (var 0) (numeral a) (numeral k))) := by
  convert Beta.contract 43 (app B (trialCall A (var 0) (numeral a) (var 43))) (numeral k) using 1
  simp [trialCall, subst_app, subst_var, subst_closed _ _ _ hA, subst_closed _ _ _ hB,
    subst_closed _ _ _ (numeral_closed a)]

/-- A successful trial determines the first search result; previous trials need only fail. -/
theorem trialSearchCompiler_hit {A : AlphaTerm} (hA : A.Closed)
    (t : (ℕ → ℕ) → ℕ → ℕ → ℕ)
    (ht : ∀ p a k, Relation.ReflTransGen (OracleStep p)
      (trialCall A (var 0) (numeral a) (numeral k)) (numeral (t p a k)))
    (p : ℕ → ℕ) (a j v : ℕ) (hj : t p a j = v + 1)
    (hb : ∀ k < j, t p a k = 0) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app trialSearchCompilerTerm A) (var 0)) (numeral a)) (numeral v) := by
  have hG := trialSearchBranch_input hA reverseZero_computes.1 a
  have hF := trialSearchBranch_input hA predecessorTerm_closed a
  have test (k : ℕ) : Relation.ReflTransGen (OracleStep p)
      (app (trialSearchTest A (var 0) (numeral a)) (numeral k))
      (numeral (if t p a k = 0 then 1 else 0)) :=
    (beta_steps_oracle (.single (trialSearchBranch_start hA reverseZero_computes.1 a k))).trans
      ((oracle_steps_app_right _ (ht p a k)).trans (beta_steps_oracle (reverseZero_computes.2 _)))
  apply (beta_steps_oracle (trialSearchCompiler_start hA a)).trans
  apply (resultSearchTerm_oracle_hit hG hF j (by simpa [trialSearchTest, hj] using test j)
    (fun k hk => ⟨0, by simpa [trialSearchTest, hb k hk] using test k⟩)).trans
  apply (beta_steps_oracle (.single (trialSearchBranch_start hA predecessorTerm_closed a j))).trans
  apply (oracle_steps_app_right _ (ht p a j)).trans
  rw [hj]
  simpa using beta_steps_oracle (p := p) (predecessorTerm_apply (v + 1))

/-- No output numeral exists if all stages fail. -/
theorem trialSearchCompiler_no_output {A : AlphaTerm} (hA : A.Closed)
    (t : (ℕ → ℕ) → ℕ → ℕ → ℕ)
    (ht : ∀ p a k, Relation.ReflTransGen (OracleStep p)
      (trialCall A (var 0) (numeral a) (numeral k)) (numeral (t p a k)))
    (p : ℕ → ℕ) (a : ℕ) (hz : ∀ k, t p a k = 0) (v : ℕ) :
    ¬ Relation.ReflTransGen (OracleStep p)
      (app (app (app trialSearchCompilerTerm A) (var 0)) (numeral a)) (numeral v) := by
  intro hout
  have hG := trialSearchBranch_input hA reverseZero_computes.1 a
  have hF := trialSearchBranch_input hA predecessorTerm_closed a
  apply resultSearchTerm_oracle_no_output hG hF ?_ v
    (oracle_numeral_after_reduction (beta_steps_oracle (trialSearchCompiler_start hA a)) hout)
  intro k
  refine ⟨0, ?_⟩
  apply (beta_steps_oracle (.single (trialSearchBranch_start hA reverseZero_computes.1 a k))).trans
  apply (oracle_steps_app_right _ (ht p a k)).trans
  rw [hz k]
  exact beta_steps_oracle (reverseZero_computes.2 0)

end PolishSpaceBook.NamedLambda.AlphaTerm

namespace PolishSpaceBook.NamedLambda.Term
open AlphaTerm

/-- One fixed representative, chosen once, of the closed compiler combinator.
No representative selection depends on the input program code. -/
noncomputable def trialSearchCompilerSyntax : Term := Quotient.out trialSearchCompilerTerm

theorem mk_trialSearchCompilerSyntax : AlphaTerm.mk trialSearchCompilerSyntax =
    trialSearchCompilerTerm := Quotient.out_eq _

theorem trialSearchCompilerSyntax_closed : trialSearchCompilerSyntax.fv = ∅ := by
  have h := trialSearchCompilerTerm_closed
  rw [← mk_trialSearchCompilerSyntax] at h
  exact h

/-- The compiler inserts the input syntax as the argument of a fixed closed term. -/
noncomputable def trialSearchCode (e : ℕ) : ℕ :=
  3 * Nat.pair trialSearchCompilerSyntax.code e + 1

theorem primrec_trialSearchCode : Primrec trialSearchCode :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec₂.natPair.comp (Primrec.const trialSearchCompilerSyntax.code) Primrec.id))
    (Primrec.const 1)

theorem decode_trialSearchCode (e : ℕ) :
    decode (trialSearchCode e) = .app trialSearchCompilerSyntax (decode e) := by
  have h := decode_code (.app trialSearchCompilerSyntax (decode e))
  simpa only [code, code_decode, trialSearchCode] using h

theorem closedProgram_trialSearchCode (e : ℕ) (he : (decode e).fv = ∅) :
    closedProgram (trialSearchCode e) = AlphaTerm.app trialSearchCompilerTerm (closedProgram e) := by
  have hc : (.app trialSearchCompilerSyntax (decode e) : Term).fv = ∅ := by
    simp only [Term.fv, trialSearchCompilerSyntax_closed, he, Finset.union_empty]
  simp only [closedProgram, decode_trialSearchCode, hc, he, ite_true]
  rw [← mk_trialSearchCompilerSyntax]
  rfl

end PolishSpaceBook.NamedLambda.Term

namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- The numerical code transformation is itself computed by a closed lambda term. -/
noncomputable def trialSearchCodeProgram : AlphaTerm :=
  numericalCombine additionTerm
    (numericalCombine multiplicationTerm (numericalConstant 3)
      (numericalCombine numericalPairTerm
        (numericalConstant Term.trialSearchCompilerSyntax.code) numericalIdentity))
    (numericalConstant 1)

theorem trialSearchCodeProgram_computes : NumericalComputes trialSearchCodeProgram
    Term.trialSearchCode := by
  have hp := (numericalConstant_computes Term.trialSearchCompilerSyntax.code).combine
    numericalIdentity_computes numericalPairTerm_closed Nat.pair numericalPairTerm_apply
  have hm := (numericalConstant_computes 3).combine hp multiplicationTerm_closed
    (· * ·) multiplicationTerm_apply
  exact hm.combine (numericalConstant_computes 1) additionTerm_closed (· + ·) additionTerm_apply

end PolishSpaceBook.NamedLambda.AlphaTerm

namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Exact results are the values recorded at the least successful stage. -/
theorem trialSearchCompiler_runs_iff {A : AlphaTerm} (hA : A.Closed)
    (t : (ℕ → ℕ) → ℕ → ℕ → ℕ)
    (ht : ∀ p a k, Relation.ReflTransGen (OracleStep p)
      (trialCall A (var 0) (numeral a) (numeral k)) (numeral (t p a k)))
    (p : ℕ → ℕ) (a v : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app trialSearchCompilerTerm A) (var 0)) (numeral a)) (numeral v) ↔
      ∃ j, t p a j = v + 1 ∧ ∀ k < j, t p a k = 0 := by
  classical
  by_cases hex : ∃ j, t p a j ≠ 0
  · have hj := Nat.find_spec hex
    have hb : ∀ k < Nat.find hex, t p a k = 0 :=
      fun k hk => not_ne_iff.mp (Nat.find_min hex hk)
    have hs : t p a (Nat.find hex) = (t p a (Nat.find hex) - 1) + 1 := by omega
    have hit := trialSearchCompiler_hit hA t ht p a (Nat.find hex) _ hs hb
    constructor
    · intro hv
      have he := oracle_numeral_output_unique hit hv
      exact ⟨Nat.find hex, by omega, hb⟩
    · rintro ⟨j, hj, hb⟩
      exact trialSearchCompiler_hit hA t ht p a j v hj hb
  · have hz : ∀ k, t p a k = 0 := by simpa using hex
    exact iff_of_false (trialSearchCompiler_no_output hA t ht p a hz v)
      (by rintro ⟨j, hj, _⟩; have := hz j; omega)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Uniform search through finite trials
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Write $A$ for the given closed trial term, with failure encoded by zero and success with value $v$ encoded by $v+1$. For
    fixed input variable $o$ and numerical parameter $a$, put
    $$G:=\lambdaab{k}{\LambdaZeroTest\,(Aoak)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
    \qquad F:=\lambdaab{k}{\LambdaPred(Aoak)}.$$
    Use $\LambdaResultSearch\,G\,F$, abstracting $o,a$ to obtain one closed program. At the first successful stage, the test
    is zero and the result function returns the predecessor of a positive numeral, hence the recorded value. Before that
    stage the test is positive. If every stage fails, the no-output part of the result-search lemma excludes every numeral
    output. The predecessor is needed only in the successful branch. All binders can be chosen fresh once in this finite
    construction. Inserting the given syntax into this fixed expression and constructing its binders are primitive-recursive
    operations on syntax codes.
-/
/-- One primitive-recursive code map, computed by one closed lambda program,
works for every closed trial code, every oracle and every numerical parameter. -/
theorem uniform_trial_search_compiler :
    Primrec Term.trialSearchCode ∧
    NumericalComputes trialSearchCodeProgram Term.trialSearchCode ∧
    ∀ e, (Term.decode e).fv = ∅ →
      ∀ (t : (ℕ → ℕ) → ℕ → ℕ → ℕ),
        (∀ p a k, Relation.ReflTransGen (OracleStep p)
          (trialCall (Term.closedProgram e) (var 0) (numeral a) (numeral k))
          (numeral (t p a k))) →
      ∀ p a v, Relation.ReflTransGen (OracleStep p)
        (app (app (Term.closedProgram (Term.trialSearchCode e)) (var 0)) (numeral a))
        (numeral v) ↔ ∃ j, t p a j = v + 1 ∧ ∀ k < j, t p a k = 0 := by
  refine ⟨Term.primrec_trialSearchCode, trialSearchCodeProgram_computes, ?_⟩
  intro e he t ht p a v
  rw [Term.closedProgram_trialSearchCode e he]
  exact trialSearchCompiler_runs_iff (Term.closedProgram_closed e) t ht p a v

end PolishSpaceBook.NamedLambda.AlphaTerm
