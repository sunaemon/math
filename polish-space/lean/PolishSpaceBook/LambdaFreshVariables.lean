module

public import PolishSpaceBook.LambdaFreeVariables
public import PolishSpaceBook.LambdaOracleSearch

@[expose] public section

/-! # Least fresh-variable search by ordinary beta reduction -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- The closed-test instance needs no input-query steps. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Numerical search by beta-reduction
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $S_k:=(\LambdaSearchKernel{G}\,\LambdaSearchKernel{G})\ChurchNumeral{k}$. Two beta steps expose the zero test of $G\ChurchNumeral{k}$. If $k<j$, a positive result selects the continuation and successor gives $S_{k+1}$. At $j$, the zero result selects $\ChurchNumeral{j}$ and discards the continuation. Starting from this final reduction, backward induction through the finitely many preceding candidates gives $S_0\to_\beta^*\ChurchNumeral{j}$. One beta step reduces $\LambdaSearch\,G$ to $S_0$. This proof uses only ordinary beta-reduction.
    \end{proof}
-/
theorem searchFrom_hit_beta {G : AlphaTerm} (hG : G.Closed) (j : ℕ)
    (hzero : Relation.ReflTransGen Beta (app G (numeral j)) (numeral 0))
    (hpos : ∀ k < j, ∃ r, Relation.ReflTransGen Beta (app G (numeral k)) (numeral (r + 1))) :
    ∀ k ≤ j, Relation.ReflTransGen Beta (searchFrom G k) (numeral j) := by
  have hf : G.fv ⊆ {0} := by rw [hG]; simp
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self =>
    apply (searchFrom_unfold hf j).trans
    apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm hzero) _) _).trans
    exact branch_zero _ _ (by rw [numeral_closed]; simp)
  | of_succ k hk ih =>
    obtain ⟨r, hr⟩ := hpos k hk
    apply (searchFrom_unfold hf k).trans
    apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm hr) _) _).trans
    exact (branch_succ r _ _).trans ((beta_steps_app_right _ (successorTerm_apply k)).trans ih)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Numerical search by beta-reduction
-/
theorem searchTerm_hit_beta {G : AlphaTerm} (hG : G.Closed) (j : ℕ)
    (hzero : Relation.ReflTransGen Beta (app G (numeral j)) (numeral 0))
    (hpos : ∀ k < j, ∃ r, Relation.ReflTransGen Beta (app G (numeral k)) (numeral (r + 1))) :
    Relation.ReflTransGen Beta (app searchTerm G) (numeral j) :=
  (Relation.ReflTransGen.single (searchTerm_start (by rw [hG]; simp))).trans
    (searchFrom_hit_beta hG j hzero hpos 0 (Nat.zero_le _))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For term codes $e,d$ and a variable index $i$, define a candidate test and a single closed search program by
    $$\begin{aligned}
    T(e,d,i)&:=\lambdaab{k}{\LambdaAdd\,
    \bigl(\LambdaAdd\,(\LambdaFreeVarTest\,e\,k)\,(\LambdaFreeVarTest\,d\,k)\bigr)
    \,(\LambdaEqual\,i\,k)},\\
    \LambdaFreshVar&:=\lambdaab{e}{\lambdaab{d}{\lambdaab{i}{\LambdaSearch\,T(e,d,i)}}}.
    \end{aligned}$$
    Expand $T$ inside the outer abstractions, using a fresh binder for its candidate. The test adds three zero-or-one answers; it returns zero exactly when the candidate belongs to neither free-variable set and differs from the excluded index.
-/
def freshTestBody (E D X K : AlphaTerm) : AlphaTerm :=
  app (app additionTerm
    (app (app additionTerm (app (app freeVariableTerm E) K)) (app (app freeVariableTerm D) K)))
    (app (app equalityTerm X) K)

theorem freshTestBody_fv (E D X K : AlphaTerm) :
    (freshTestBody E D X K).fv = E.fv ∪ D.fv ∪ X.fv ∪ K.fv := by
  simp only [freshTestBody, fv_app]
  rw [additionTerm_closed, freeVariableTerm_closed, equalityTerm_closed]
  ext x
  simp only [Finset.mem_union, Finset.notMem_empty, false_or]
  tauto

theorem freshTestBody_subst (E D X K W : AlphaTerm) (i : ℕ) :
    (freshTestBody E D X K).subst i W =
      freshTestBody (E.subst i W) (D.subst i W) (X.subst i W) (K.subst i W) := by
  simp only [freshTestBody, subst_app, subst_closed _ _ _ additionTerm_closed,
    subst_closed _ _ _ freeVariableTerm_closed, subst_closed _ _ _ equalityTerm_closed]

def freshTest (E D X : AlphaTerm) : AlphaTerm := lam 17 (freshTestBody E D X (var 17))

theorem freshTest_fv (E D X : AlphaTerm) :
    (freshTest E D X).fv = (E.fv ∪ D.fv ∪ X.fv).erase 17 := by
  simp only [freshTest, fv_lam, freshTestBody_fv, fv_var]
  ext x
  simp

theorem freshTest_closed {E D X : AlphaTerm} (hE : E.Closed) (hD : D.Closed) (hX : X.Closed) :
    (freshTest E D X).Closed := by
  unfold Closed
  rw [freshTest_fv, hE, hD, hX]
  simp

theorem freshTest_subst (E D X W : AlphaTerm) (i : ℕ) (hi : 17 ≠ i) (hW : 17 ∉ W.fv) :
    (freshTest E D X).subst i W = freshTest (E.subst i W) (D.subst i W) (X.subst i W) := by
  unfold freshTest
  rw [subst_lam_fresh _ _ 17 i hi hW, freshTestBody_subst]
  simp [subst_var, hi]

def freshTestValue (e d x k : ℕ) : ℕ :=
  (if k ∈ (Term.decode e).fv then 1 else 0) +
    (if k ∈ (Term.decode d).fv then 1 else 0) + (if x = k then 1 else 0)

theorem freshTest_apply (e d x k : ℕ) :
    Relation.ReflTransGen Beta (app (freshTest (numeral e) (numeral d) (numeral x)) (numeral k))
      (numeral (freshTestValue e d x k)) := by
  have h : Beta (app (freshTest (numeral e) (numeral d) (numeral x)) (numeral k))
      (freshTestBody (numeral e) (numeral d) (numeral x) (numeral k)) := by
    convert Beta.contract 17 (freshTestBody (numeral e) (numeral d) (numeral x) (var 17))
      (numeral k) using 1 <;> try rfl
    simp [freshTestBody_subst, subst_var, subst_closed _ _ _ (numeral_closed e),
      subst_closed _ _ _ (numeral_closed d), subst_closed _ _ _ (numeral_closed x)]
  have he := freeVariableTerm_apply e k
  have hd := freeVariableTerm_apply d k
  have hx := equalityTerm_apply x k
  have hs := (beta_steps_app (beta_steps_app_right additionTerm he) hd).trans (additionTerm_apply _ _)
  exact (Relation.ReflTransGen.single h).trans
    ((beta_steps_app (beta_steps_app_right additionTerm hs) hx).trans (additionTerm_apply _ _))

theorem freshTestValue_zero_iff (e d x k : ℕ) :
    freshTestValue e d x k = 0 ↔ k ∉ (Term.decode e).fv ∪ (Term.decode d).fv ∪ {x} := by
  by_cases he : k ∈ (Term.decode e).fv <;> by_cases hd : k ∈ (Term.decode d).fv <;>
    by_cases hx : x = k <;> simp [freshTestValue, he, hd, hx, eq_comm]

def freshVariableTerm : AlphaTerm := lam 14 (lam 15 (lam 16
  (app searchTerm (freshTest (var 14) (var 15) (var 16)))))

@[simp] theorem freshVariableTerm_closed : freshVariableTerm.Closed := by
  unfold freshVariableTerm Closed
  rw [fv_lam, fv_lam, fv_lam, fv_app, searchTerm_closed, freshTest_fv]
  simp [fv_var]
  decide

theorem freshVariableTerm_start (e d x : ℕ) :
    Relation.ReflTransGen Beta (app (app (app freshVariableTerm (numeral e)) (numeral d)) (numeral x))
      (app searchTerm (freshTest (numeral e) (numeral d) (numeral x))) := by
  have hf (n i : ℕ) : i ∉ (numeral n).fv := by rw [numeral_closed]; simp
  have h₁ : Beta (app freshVariableTerm (numeral e))
      (lam 15 (lam 16 (app searchTerm (freshTest (numeral e) (var 15) (var 16))))) := by
    convert Beta.contract 14 (lam 15 (lam 16 (app searchTerm (freshTest (var 14) (var 15) (var 16)))))
      (numeral e) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 15 14 (by decide) (hf e 15),
      subst_lam_fresh _ _ 16 14 (by decide) (hf e 16)]
    simp [subst_app, subst_closed _ _ _ searchTerm_closed,
      freshTest_subst _ _ _ _ 14 (by decide) (hf e 17), subst_var]
  have h₂ : Beta (app (lam 15 (lam 16 (app searchTerm (freshTest (numeral e) (var 15) (var 16)))))
      (numeral d)) (lam 16 (app searchTerm (freshTest (numeral e) (numeral d) (var 16)))) := by
    convert Beta.contract 15 (lam 16 (app searchTerm (freshTest (numeral e) (var 15) (var 16))))
      (numeral d) using 1
    rw [subst_lam_fresh _ _ 16 15 (by decide) (hf d 16)]
    simp [subst_app, subst_closed _ _ _ searchTerm_closed,
      freshTest_subst _ _ _ _ 15 (by decide) (hf d 17), subst_var,
      subst_closed _ _ _ (numeral_closed e)]
  have h₃ : Beta (app (lam 16 (app searchTerm (freshTest (numeral e) (numeral d) (var 16)))) (numeral x))
      (app searchTerm (freshTest (numeral e) (numeral d) (numeral x))) := by
    convert Beta.contract 16 (app searchTerm (freshTest (numeral e) (numeral d) (var 16)))
      (numeral x) using 1
    simp [subst_app, subst_closed _ _ _ searchTerm_closed,
      freshTest_subst _ _ _ _ 16 (by decide) (hf x 17), subst_var,
      subst_closed _ _ _ (numeral_closed e), subst_closed _ _ _ (numeral_closed d)]
  exact .tail (.tail (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂)) h₃

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Least fresh-variable choice by a lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The excluded set is finite, so an index outside it exists and has a least value $j$. Every candidate test terminates by free-variable decision and equality testing. At $j$ all three answers are zero. At each smaller index, membership in the excluded set makes at least one answer one, so their sum is positive. Apply numerical search to this closed test. Three outer beta steps supply the two codes and excluded index. The result is the required numeral, and the displayed binders show closedness. Since every natural number decodes, the same program works on arbitrary numerical codes as well.
    \end{proof}
-/
theorem freshVariableTerm_apply (e d x : ℕ) :
    Relation.ReflTransGen Beta (app (app (app freshVariableTerm (numeral e)) (numeral d)) (numeral x))
      (numeral (Term.fresh ((Term.decode e).fv ∪ (Term.decode d).fv ∪ {x}))) := by
  let s := (Term.decode e).fv ∪ (Term.decode d).fv ∪ {x}
  let j := Term.fresh s
  apply (freshVariableTerm_start e d x).trans
  apply searchTerm_hit_beta (freshTest_closed (numeral_closed e) (numeral_closed d) (numeral_closed x)) j
  · have hz := (freshTestValue_zero_iff e d x j).mpr (Term.fresh_not_mem s)
    simpa only [hz] using freshTest_apply e d x j
  · intro k hk
    have hmem : k ∈ s := Term.lt_fresh_mem s hk
    have hn : freshTestValue e d x k ≠ 0 := by
      intro h
      exact (freshTestValue_zero_iff e d x k).mp h hmem
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact ⟨r, by simpa only [hr] using freshTest_apply e d x k⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Least fresh-variable choice by a lambda term
-/
theorem freshVariableTerm_code (M N : Term) (x : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app freshVariableTerm (numeral M.code)) (numeral N.code)) (numeral x))
      (numeral (Term.fresh (M.fv ∪ N.fv ∪ {x}))) := by
  simpa only [Term.decode_code] using freshVariableTerm_apply M.code N.code x

end PolishSpaceBook.NamedLambda.AlphaTerm
