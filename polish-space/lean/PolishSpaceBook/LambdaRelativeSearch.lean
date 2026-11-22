module

public import PolishSpaceBook.LambdaRelativeProducts
public import PolishSpaceBook.LambdaOracleSearchResult

@[expose] public section

/-! # Exact semidecision by a relative numerical search

A paired-input test is total at the fixed parameter. The search returns one
on its first successful stage and has no numerical output if all stages fail.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    First make the acceptance convention precise. For a closed paired-input test $T$, expand
    $$\begin{aligned}
    H_T(o,n)&:=\lambdaab{k}{\LambdaZeroTest\,
     \bigl(To(\LambdaNumericPair\,n\,k)\bigr)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    \LambdaRelativeSearch{T}&:=\lambdaab{o}{\lambdaab{n}{
     \LambdaResultSearch\,H_T(o,n)\,(\lambdaab{j}{\ChurchNumeral{1}})}}.
    \end{aligned}$$
    The constant-one function is the result branch of the search and is used only after a successful test.
    All binders are chosen fresh as in §{sec:lambda-input-search}.
-/
def relativeSearchBody (T O N K : AlphaTerm) : AlphaTerm :=
  app reverseZeroTerm (app (app T O) (app (app numericalPairTerm N) K))

theorem relativeSearchBody_fv {T : AlphaTerm} (hT : T.Closed) (O N K : AlphaTerm) :
    (relativeSearchBody T O N K).fv = O.fv ∪ N.fv ∪ K.fv := by
  ext x
  simp only [relativeSearchBody,fv_app,(show T.fv = ∅ from hT),
    (show reverseZeroTerm.fv = ∅ from reverseZero_computes.1),
    (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed),Finset.mem_union,Finset.notMem_empty]
  tauto

theorem relativeSearchBody_subst {T : AlphaTerm} (hT : T.Closed) (O N K W : AlphaTerm) (x : ℕ) :
    (relativeSearchBody T O N K).subst x W =
      relativeSearchBody T (O.subst x W) (N.subst x W) (K.subst x W) := by
  simp only [relativeSearchBody,subst_app,subst_closed _ _ _ hT,
    subst_closed _ _ _ reverseZero_computes.1,subst_closed _ _ _ numericalPairTerm_closed]

def relativeSearchTest (T O N : AlphaTerm) : AlphaTerm :=
  lam 72 (relativeSearchBody T O N (var 72))

theorem relativeSearchTest_fv {T : AlphaTerm} (hT : T.Closed) (O N : AlphaTerm) :
    (relativeSearchTest T O N).fv = (O.fv ∪ N.fv).erase 72 := by
  ext x
  simp only [relativeSearchTest,fv_lam,relativeSearchBody_fv hT,fv_var,
    Finset.mem_erase,Finset.mem_union,Finset.mem_singleton]
  tauto

theorem relativeSearchTest_subst {T : AlphaTerm} (hT : T.Closed) (O N W : AlphaTerm)
    (x : ℕ) (hx : 72 ≠ x) (hw : 72 ∉ W.fv) :
    (relativeSearchTest T O N).subst x W = relativeSearchTest T (O.subst x W) (N.subst x W) := by
  unfold relativeSearchTest
  rw [subst_lam_fresh _ _ 72 x hx hw,relativeSearchBody_subst hT]
  simp only [subst_var,ite_eq_right hx]

def relativeSearchProgram (T : AlphaTerm) : AlphaTerm :=
  lam 70 (lam 71 (app (app resultSearchTerm (relativeSearchTest T (var 70) (var 71))) (numericalConstant 1)))

theorem relativeSearchProgram_closed {T : AlphaTerm} (hT : T.Closed) : (relativeSearchProgram T).Closed := by
  unfold relativeSearchProgram Closed
  simp only [fv_lam,fv_app,relativeSearchTest_fv hT,fv_var,
    (show resultSearchTerm.fv = ∅ from resultSearchTerm_closed),
    (show (numericalConstant 1).fv = ∅ from (numericalConstant_computes 1).1)]
  decide

theorem relativeSearchProgram_start {T : AlphaTerm} (hT : T.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (relativeSearchProgram T) (var 0)) (numeral n))
      (app (app resultSearchTerm (relativeSearchTest T (var 0) (numeral n))) (numericalConstant 1)) := by
  have he : (lam 71 (app (app resultSearchTerm (relativeSearchTest T (var 70) (var 71))) (numericalConstant 1))).subst 70 (var 0) =
      lam 71 (app (app resultSearchTerm (relativeSearchTest T (var 0) (var 71))) (numericalConstant 1)) := by
    rw [subst_lam_fresh _ _ 71 70 (by decide) (by simp [fv_var])]
    simp only [subst_app,subst_closed _ _ _ resultSearchTerm_closed,
      subst_closed _ _ _ (numericalConstant_computes 1).1,
      relativeSearchTest_subst hT _ _ (var 0) 70 (by decide) (by simp [fv_var]),subst_var]
    simp
  have h₁ : Beta (app (relativeSearchProgram T) (var 0))
      (lam 71 (app (app resultSearchTerm (relativeSearchTest T (var 0) (var 71))) (numericalConstant 1))) := by
    rw [← he]; exact Beta.contract 70 _ _
  have h₂ : Beta (app (lam 71
      (app (app resultSearchTerm (relativeSearchTest T (var 0) (var 71))) (numericalConstant 1))) (numeral n))
      (app (app resultSearchTerm (relativeSearchTest T (var 0) (numeral n))) (numericalConstant 1)) := by
    convert Beta.contract 71 (app (app resultSearchTerm (relativeSearchTest T (var 0) (var 71))) (numericalConstant 1))
      (numeral n) using 1
    simp only [subst_app,subst_closed _ _ _ resultSearchTerm_closed,
      subst_closed _ _ _ (numericalConstant_computes 1).1,
      relativeSearchTest_subst hT _ _ (numeral n) 71 (by decide) (by rw [numeral_closed]; simp),subst_var]
    simp
  exact .tail (.single (.app_left _ h₁)) h₂

theorem relativeSearchTest_apply {ε : ℕ → ℕ} {T : AlphaTerm} (hT : T.Closed) (n k v : ℕ)
    (ht : OracleRuns ε T (Nat.pair n k) v) :
    Relation.ReflTransGen (OracleStep ε) (app (relativeSearchTest T (var 0) (numeral n)) (numeral k))
      (numeral (if v = 0 then 1 else 0)) := by
  have hs : Beta (app (relativeSearchTest T (var 0) (numeral n)) (numeral k))
      (relativeSearchBody T (var 0) (numeral n) (numeral k)) := by
    convert Beta.contract 72 (relativeSearchBody T (var 0) (numeral n) (var 72)) (numeral k) using 1 <;> try rfl
    rw [relativeSearchBody_subst hT]
    simp only [subst_var,show (0 : ℕ) ≠ 72 from by decide,ite_false,ite_true,subst_closed _ _ _ (numeral_closed n)]
  exact (Relation.ReflTransGen.single (.beta hs)).trans
    ((oracle_steps_app_right reverseZeroTerm
      ((oracle_steps_app_right (app T (var 0)) (beta_steps_oracle (numericalPairTerm_apply n k))).trans ht)).trans
        (beta_steps_oracle (reverseZero_computes.2 v)))

/-- Numerical output exists exactly on a successful trial, and is always one. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Exact relative search for acceptance
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Two outer beta steps expose the result-search term. At stage $k$, beta reduction, numerical pairing, and the
    assumed computation of $T$ make $H_T$ return zero exactly when $t(\NatPair{n}{k})\ne0$.
    If a successful stage exists, take the least one. Every earlier test returns one, so the search reaches that
    stage and applies its result function, returning one. If every stage fails, the no-output theorem in
    §{sec:lambda-input-search} excludes every normal-form numeral. Output uniqueness excludes a second numerical
    answer in the successful case. These are reductions with the same fixed parameter throughout.
-/
theorem relativeSearchProgram_runs_iff {ε : ℕ → ℕ} {T : AlphaTerm} {t : ℕ → ℕ}
    (ht : PolishSpaceBook.LambdaRelative.Computes ε T t) (n m : ℕ) :
    OracleRuns ε (relativeSearchProgram T) n m ↔ m = 1 ∧ ∃ k, t (Nat.pair n k) ≠ 0 := by
  classical
  have hG : (relativeSearchTest T (var 0) (numeral n)).fv ⊆ {0} := by
    rw [relativeSearchTest_fv ht.1,fv_var,numeral_closed]; simp
  have hF : (numericalConstant 1).fv ⊆ {0} := by rw [(numericalConstant_computes 1).1]; simp
  have hs := beta_steps_oracle (p := ε) (relativeSearchProgram_start ht.1 n)
  have htest (k : ℕ) := relativeSearchTest_apply ht.1 n k (t (Nat.pair n k))
    (by simpa only [Encodable.encode_nat] using ht.2 (Nat.pair n k))
  have hhit (h : ∃ k, t (Nat.pair n k) ≠ 0) : OracleRuns ε (relativeSearchProgram T) n 1 := by
    let j := Nat.find h
    have hj : t (Nat.pair n j) ≠ 0 := Nat.find_spec h
    have hb (k : ℕ) (hk : k < j) : t (Nat.pair n k) = 0 := by simpa using Nat.find_min h hk
    exact hs.trans ((resultSearchTerm_oracle_hit hG hF j
      (by simpa only [hj,ite_false] using htest j)
      (fun k hk => ⟨0,by simpa only [hb k hk,ite_true] using htest k⟩)).trans
        (beta_steps_oracle ((numericalConstant_computes 1).2 j)))
  constructor
  · intro hr
    obtain ⟨k,hk⟩ := resultSearchTerm_oracle_output_requires_hit hG hF _ htest
      (oracle_numeral_after_reduction hs hr)
    have hex : ∃ k, t (Nat.pair n k) ≠ 0 := ⟨k,by simpa using hk⟩
    exact ⟨hr.output_unique (hhit hex),hex⟩
  · rintro ⟨rfl,h⟩
    exact hhit h

end PolishSpaceBook.NamedLambda.AlphaTerm
