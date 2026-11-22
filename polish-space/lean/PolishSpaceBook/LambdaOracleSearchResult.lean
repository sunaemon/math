module

public import PolishSpaceBook.LambdaOracleHeadNormalization
public import PolishSpaceBook.LambdaSearchResult
public import PolishSpaceBook.LambdaOracleRecursion

@[expose] public section

/-! # Exact sequential search with an input name and a successful result branch -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

theorem resultSearchKernel_input_fv {G F : AlphaTerm} (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) :
    (resultSearchKernel G F).fv ⊆ {0} := by
  rw [resultSearchKernel_fv]
  intro x hx
  rcases Finset.mem_union.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2 with hx | hx
  · exact hG hx
  · exact hF hx

theorem resultSearchTerm_input_start {G F : AlphaTerm} (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app resultSearchTerm G) F) (resultSearchFrom G F 0) := by
  have hg (x : ℕ) (hx : x ≠ 0) := input_fresh hG hx
  have hf (x : ℕ) (hx : x ≠ 0) := input_fresh hF hx
  have h1 : Beta (app resultSearchTerm G) (lam 8 (resultSearchFrom G (var 8) 0)) := by
    convert Beta.contract 7 (lam 8 (resultSearchFrom (var 7) (var 8) 0)) G using 1
    · rfl
    rw [subst_lam_fresh _ _ 8 7 (by decide) (hg 8 (by decide))]
    simp [resultSearchFrom, subst_app,
      subst_resultSearchKernel _ _ _ _ (by decide : 3 ≠ 7) (by decide : 4 ≠ 7) (hg 3 (by decide)) (hg 4 (by decide)),
      subst_var, subst_closed _ _ _ (numeral_closed 0)]
  have h2 : Beta (app (lam 8 (resultSearchFrom G (var 8) 0)) F) (resultSearchFrom G F 0) := by
    convert Beta.contract 8 (resultSearchFrom G (var 8) 0) F using 1
    simp [resultSearchFrom, subst_app,
      subst_resultSearchKernel _ _ _ _ (by decide : 3 ≠ 8) (by decide : 4 ≠ 8) (hf 3 (by decide)) (hf 4 (by decide)),
      subst_var, subst_not_free _ _ _ (input_fresh hG (by decide : 8 ≠ 0)), subst_closed _ _ _ (numeral_closed 0)]
  exact .tail (.single (.app_left F h1)) h2

/-- The two unfolding contractions include a leading head step. -/
theorem resultSearchFrom_input_unfold {G F : AlphaTerm} (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) (k : ℕ) :
    ∃ L, HeadStep (resultSearchFrom G F k) L ∧
      Beta L
        (app (app (app zeroTestTerm (app G (numeral k))) (app F (numeral k)))
          (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (numeral k)))) := by
  have hK := resultSearchKernel_input_fv hG hF
  have hk4 : 4 ∉ (resultSearchKernel G F).fv := input_fresh hK (by decide)
  have h1 : HeadStep (app (resultSearchKernel G F) (resultSearchKernel G F))
      (lam 4 (app (app (app zeroTestTerm (app G (var 4))) (app F (var 4)))
        (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (var 4))))) := by
    convert HeadStep.contract 3 (lam 4
      (app (app (app zeroTestTerm (app G (var 4))) (app F (var 4)))
        (app (app (var 3) (var 3)) (app successorTerm (var 4))))) (resultSearchKernel G F) using 1
    · rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) hk4]
    simp [subst_app, subst_var, subst_not_free _ _ _ (input_fresh hG (by decide : 3 ≠ 0)), subst_not_free _ _ _ (input_fresh hF (by decide : 3 ≠ 0)),
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
    simp [subst_app, subst_var, subst_not_free _ _ _ (input_fresh hG (by decide : 4 ≠ 0)), subst_not_free _ _ _ (input_fresh hF (by decide : 4 ≠ 0)), subst_not_free _ _ _ (input_fresh hK (by decide : 4 ≠ 0)),
      subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ successorTerm_closed]
  exact ⟨_, .app_left (numeral k) h1, h2⟩

theorem resultSearchFrom_input_unfold_steps {G F : AlphaTerm} (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) (k : ℕ) :
    Relation.ReflTransGen Beta (resultSearchFrom G F k)
      (app (app (app zeroTestTerm (app G (numeral k))) (app F (numeral k)))
        (app (app (resultSearchKernel G F) (resultSearchKernel G F)) (app successorTerm (numeral k)))) := by
  obtain ⟨L, hh, hb⟩ := resultSearchFrom_input_unfold hG hF k
  exact .tail (.single hh.beta) hb

theorem resultSearchFrom_oracle_next {p : ℕ → ℕ} {G F : AlphaTerm}
    (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) (k r : ℕ)
    (ht : Relation.ReflTransGen (OracleStep p) (app G (numeral k)) (numeral (r + 1))) :
    OracleHeadStage p (resultSearchFrom G F k) (resultSearchFrom G F (k + 1)) := by
  obtain ⟨L,hh,hb⟩ := resultSearchFrom_input_unfold hG hF k
  refine ⟨L,hh.oracleHead p,(Relation.ReflTransGen.single (.beta hb)).trans ?_⟩
  apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm ht) _) _).trans
  exact (beta_steps_oracle (branch_succ r _ _)).trans
    (oracle_steps_app_right _ (beta_steps_oracle (successorTerm_apply k)))

theorem resultSearchFrom_oracle_hit {p : ℕ → ℕ} {G F : AlphaTerm}
    (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) (j : ℕ)
    (hz : Relation.ReflTransGen (OracleStep p) (app G (numeral j)) (numeral 0))
    (hp : ∀ k < j, ∃ r, Relation.ReflTransGen (OracleStep p) (app G (numeral k)) (numeral (r + 1))) :
    ∀ k ≤ j, Relation.ReflTransGen (OracleStep p) (resultSearchFrom G F k) (app F (numeral j)) := by
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self =>
    apply (beta_steps_oracle (resultSearchFrom_input_unfold_steps hG hF j)).trans
    apply (oracle_steps_app_left (oracle_steps_app_left (oracle_steps_app_right zeroTestTerm hz) _) _).trans
    apply beta_steps_oracle (branch_zero _ _ ?_)
    rw [fv_app, numeral_closed, Finset.union_empty]
    exact input_fresh hF (by decide)
  | of_succ k hk ih =>
    obtain ⟨r,hr⟩ := hp k hk
    obtain ⟨L,hh,hb⟩ := resultSearchFrom_oracle_next hG hF k r hr
    exact (hh.oracle_steps.trans hb).trans ih


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Search with an input name and a result function
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The two parameter substitutions and the two contractions unfolding each kernel remain valid because their binders avoid the only possible free variable $o$. Put $S_k:=(\LambdaResultSearchKernel{G}{F}\,\LambdaResultSearchKernel{G}{F})\ChurchNumeral{k}$. The first unfolding contraction is a head step. A positive test selects the continuation, and successor gives $S_{k+1}$. A zero test selects $F\ChurchNumeral{k}$; this branch also avoids capture. Backward induction from $j$ gives the first assertion. If every test is positive, the stages $S_k$ satisfy the infinite-stage proposition in §{sec:lambda-input-head-exposure}. Finally, confluence and the terminality of numerals transfer any putative numeral output of the outer search term to $S_0$, giving a contradiction.
    \end{proof}
-/
theorem resultSearchTerm_oracle_hit {p : ℕ → ℕ} {G F : AlphaTerm}
    (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) (j : ℕ)
    (hz : Relation.ReflTransGen (OracleStep p) (app G (numeral j)) (numeral 0))
    (hp : ∀ k < j, ∃ r, Relation.ReflTransGen (OracleStep p) (app G (numeral k)) (numeral (r + 1))) :
    Relation.ReflTransGen (OracleStep p) (app (app resultSearchTerm G) F) (app F (numeral j)) :=
  (beta_steps_oracle (resultSearchTerm_input_start hG hF)).trans
    (resultSearchFrom_oracle_hit hG hF j hz hp 0 (Nat.zero_le _))


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Search with an input name and a result function
-/
theorem resultSearchTerm_oracle_no_output {p : ℕ → ℕ} {G F : AlphaTerm}
    (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0})
    (hp : ∀ k, ∃ r, Relation.ReflTransGen (OracleStep p) (app G (numeral k)) (numeral (r + 1))) (n : ℕ) :
    ¬ Relation.ReflTransGen (OracleStep p) (app (app resultSearchTerm G) F) (numeral n) := by
  intro hn
  have h0 := oracle_numeral_after_reduction (beta_steps_oracle (resultSearchTerm_input_start hG hF)) hn
  apply no_numeral_of_oracle_head_stages (fun k => resultSearchFrom G F k) _ n h0
  intro k
  obtain ⟨r,hr⟩ := hp k
  exact resultSearchFrom_oracle_next hG hF k r hr

/-- For total numerical tests, producing a numeral requires a zero test result. -/
theorem resultSearchTerm_oracle_output_requires_hit {p : ℕ → ℕ} {G F : AlphaTerm}
    (hG : G.fv ⊆ {0}) (hF : F.fv ⊆ {0}) (g : ℕ → ℕ)
    (hg : ∀ k, Relation.ReflTransGen (OracleStep p) (app G (numeral k)) (numeral (g k)))
    {n : ℕ} (hn : Relation.ReflTransGen (OracleStep p) (app (app resultSearchTerm G) F) (numeral n)) :
    ∃ k, g k = 0 := by
  by_contra h
  apply resultSearchTerm_oracle_no_output hG hF _ n hn
  intro k
  have hk : g k ≠ 0 := fun hk => h ⟨k,hk⟩
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact ⟨r,by simpa only [hr] using hg k⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
