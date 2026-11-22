module

public import PolishSpaceBook.LambdaHeadNormalization
public import PolishSpaceBook.LambdaFreshVariables

@[expose] public section

/-! # Sequential numerical search with a result function in the successful branch -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    We need search to produce a result only in its successful branch. For closed terms $G,F$, choose distinct binders $s,k$ fresh for them and put
    $$\LambdaResultSearchKernel{G}{F}:=\lambdaab{s}{\lambdaab{k}{
    \LambdaZeroTest\,(Gk)\,(Fk)\,\bigl((ss)(\LambdaSucc\,k)\bigr)}}.$$
    Define one closed search term by
    $$\LambdaResultSearch:=\lambdaab{g}{\lambdaab{f}{
    (\LambdaResultSearchKernel{g}{f}\,\LambdaResultSearchKernel{g}{f})\ChurchNumeral{0}}}.$$
    Expand the kernels inside the abstractions, with their binders distinct from $g,f$. The test is $G$; the successful branch applies $F$ to the successful candidate. The continuation retains both terms and advances to the next candidate.
-/
def resultSearchKernel (G F : AlphaTerm) : AlphaTerm :=
  lam 3 (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (app F (var 4)))
    (app (app (var 3) (var 3)) (app successorTerm (var 4)))))

def resultSearchFrom (G F : AlphaTerm) (k : ℕ) : AlphaTerm :=
  app (app (resultSearchKernel G F) (resultSearchKernel G F)) (numeral k)

@[simp] theorem resultSearchKernel_fv (G F : AlphaTerm) :
    (resultSearchKernel G F).fv = ((G.fv ∪ F.fv).erase 4).erase 3 := by
  ext x
  simp [resultSearchKernel, fv_lam, fv_app, fv_var]
  tauto

theorem resultSearchKernel_closed {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed) :
    (resultSearchKernel G F).Closed := by
  unfold Closed
  rw [resultSearchKernel_fv, hG, hF]
  simp

theorem subst_resultSearchKernel (G F R : AlphaTerm) (x : ℕ) (hx3 : 3 ≠ x) (hx4 : 4 ≠ x)
    (hR3 : 3 ∉ R.fv) (hR4 : 4 ∉ R.fv) :
    subst (resultSearchKernel G F) x R = resultSearchKernel (subst G x R) (subst F x R) := by
  unfold resultSearchKernel
  rw [subst_lam_fresh _ _ 3 x hx3 hR3, subst_lam_fresh _ _ 4 x hx4 hR4]
  simp [subst_app, subst_var, hx3, hx4,
    subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ successorTerm_closed]

def resultSearchTerm : AlphaTerm := lam 7 (lam 8 (resultSearchFrom (var 7) (var 8) 0))

@[simp] theorem resultSearchTerm_closed : resultSearchTerm.Closed := by
  unfold Closed resultSearchTerm resultSearchFrom
  rw [fv_lam, fv_lam, fv_app, fv_app, numeral_closed]
  simp [fv_var]
  decide

theorem resultSearchTerm_start {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed) :
    Relation.ReflTransGen Beta (app (app resultSearchTerm G) F) (resultSearchFrom G F 0) := by
  have hg (x : ℕ) : x ∉ G.fv := by rw [hG]; simp
  have hf (x : ℕ) : x ∉ F.fv := by rw [hF]; simp
  have h1 : Beta (app resultSearchTerm G) (lam 8 (resultSearchFrom G (var 8) 0)) := by
    convert Beta.contract 7 (lam 8 (resultSearchFrom (var 7) (var 8) 0)) G using 1
    · rfl
    rw [subst_lam_fresh _ _ 8 7 (by decide) (hg 8)]
    simp [resultSearchFrom, subst_app,
      subst_resultSearchKernel _ _ _ _ (by decide : 3 ≠ 7) (by decide : 4 ≠ 7) (hg 3) (hg 4),
      subst_var, subst_closed _ _ _ (numeral_closed 0)]
  have h2 : Beta (app (lam 8 (resultSearchFrom G (var 8) 0)) F) (resultSearchFrom G F 0) := by
    convert Beta.contract 8 (resultSearchFrom G (var 8) 0) F using 1
    simp [resultSearchFrom, subst_app,
      subst_resultSearchKernel _ _ _ _ (by decide : 3 ≠ 8) (by decide : 4 ≠ 8) (hf 3) (hf 4),
      subst_var, subst_closed _ _ _ hG, subst_closed _ _ _ (numeral_closed 0)]
  exact .tail (.single (.app_left F h1)) h2

/-- The two unfolding contractions include a leading head step. -/
theorem resultSearchFrom_unfold {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed) (k : ℕ) :
    ∃ L, HeadStep (resultSearchFrom G F k) L ∧
      Beta L
        (app (app (app zeroTestTerm (app G (numeral k))) (app F (numeral k)))
          (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (numeral k)))) := by
  have hK := resultSearchKernel_closed hG hF
  have hk4 : 4 ∉ (resultSearchKernel G F).fv := by rw [hK]; simp
  have h1 : HeadStep (app (resultSearchKernel G F) (resultSearchKernel G F))
      (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (app F (var 4)))
        (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (var 4))))) := by
    convert HeadStep.contract 3 (lam 4
      (app (app (app zeroTestTerm (app G (var 4))) (app F (var 4)))
        (app (app (var 3) (var 3)) (app successorTerm (var 4))))) (resultSearchKernel G F) using 1
    · rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) hk4]
    simp [subst_app, subst_var, subst_closed _ _ _ hG, subst_closed _ _ _ hF,
      subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ successorTerm_closed]
  have h2 : Beta
      (app (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (app F (var 4)))
        (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (var 4))))) (numeral k))
      (app (app (app zeroTestTerm (app G (numeral k))) (app F (numeral k)))
        (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (numeral k)))) := by
    convert Beta.contract 4
      (app (app (app zeroTestTerm (app G (var 4))) (app F (var 4)))
        (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (var 4))))
      (numeral k) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ hG, subst_closed _ _ _ hF, subst_closed _ _ _ hK,
      subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ successorTerm_closed]
  exact ⟨_, .app_left (numeral k) h1, h2⟩

theorem resultSearchFrom_unfold_steps {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed) (k : ℕ) :
    Relation.ReflTransGen Beta (resultSearchFrom G F k)
      (app (app (app zeroTestTerm (app G (numeral k))) (app F (numeral k)))
        (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (numeral k)))) := by
  obtain ⟨L, hh, hb⟩ := resultSearchFrom_unfold hG hF k
  exact .tail (.single hh.beta) hb

theorem resultSearchFrom_next {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed) (k r : ℕ)
    (ht : Relation.ReflTransGen Beta (app G (numeral k)) (numeral (r + 1))) :
    HeadStage (resultSearchFrom G F k) (resultSearchFrom G F (k + 1)) := by
  obtain ⟨L, hh, hb⟩ := resultSearchFrom_unfold hG hF k
  refine ⟨L, hh, (Relation.ReflTransGen.single hb).trans ?_⟩
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm ht) _) _).trans
  exact (branch_succ r _ _).trans (beta_steps_app_right _ (successorTerm_apply k))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $S_k:=(\LambdaResultSearchKernel{G}{F}\,\LambdaResultSearchKernel{G}{F})\ChurchNumeral{k}$. Two beta steps expose the test, the first being a head step. A positive test followed by successor reduces this term to $S_{k+1}$; a zero test reduces it to $F\ChurchNumeral{k}$. Backward induction from the successful candidate proves the first assertion, after the two outer contractions supplying $G,F$.

    If every test is positive, these reductions give infinitely many stages, each beginning with a head step. The infinite-stage proposition in §{sec:lambda-head-exposure} excludes a numerical output from $S_0$. If the outer search term had a numerical output, confluence would give the same output from $S_0$, since numerals are normal forms. This contradiction proves the second assertion.
    \end{proof}
-/
theorem resultSearchFrom_hit {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed) (j : ℕ)
    (hz : Relation.ReflTransGen Beta (app G (numeral j)) (numeral 0))
    (hp : ∀ k < j, ∃ r, Relation.ReflTransGen Beta (app G (numeral k)) (numeral (r + 1))) :
    ∀ k ≤ j, Relation.ReflTransGen Beta (resultSearchFrom G F k) (app F (numeral j)) := by
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self =>
    apply (resultSearchFrom_unfold_steps hG hF j).trans
    apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm hz) _) _).trans
    exact branch_zero _ _ (by rw [fv_app, hF, numeral_closed]; simp)
  | of_succ k hk ih =>
    obtain ⟨r, hr⟩ := hp k hk
    obtain ⟨L, hh, hb⟩ := resultSearchFrom_next hG hF k r hr
    exact ((Relation.ReflTransGen.single hh.beta).trans hb).trans ih

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Search with a result function
-/
theorem resultSearchTerm_hit {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed) (j : ℕ)
    (hz : Relation.ReflTransGen Beta (app G (numeral j)) (numeral 0))
    (hp : ∀ k < j, ∃ r, Relation.ReflTransGen Beta (app G (numeral k)) (numeral (r + 1))) :
    Relation.ReflTransGen Beta (app (app resultSearchTerm G) F) (app F (numeral j)) :=
  (resultSearchTerm_start hG hF).trans (resultSearchFrom_hit hG hF j hz hp 0 (Nat.zero_le _))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Search with a result function
-/
theorem resultSearchTerm_no_output {G F : AlphaTerm} (hG : G.Closed) (hF : F.Closed)
    (hp : ∀ k, ∃ r, Relation.ReflTransGen Beta (app G (numeral k)) (numeral (r + 1))) (n : ℕ) :
    ¬ Relation.ReflTransGen Beta (app (app resultSearchTerm G) F) (numeral n) := by
  intro hn
  have h0 := numeral_after_reduction (resultSearchTerm_start hG hF) hn
  apply no_numeral_of_head_stages (fun k => resultSearchFrom G F k) _ n h0
  intro k
  obtain ⟨r, hr⟩ := hp k
  exact resultSearchFrom_next hG hF k r hr

end PolishSpaceBook.NamedLambda.AlphaTerm
