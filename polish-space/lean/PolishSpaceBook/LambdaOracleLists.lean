module

public import PolishSpaceBook.LambdaFiniteLists
public import PolishSpaceBook.LambdaOracleRecursion

@[expose] public section

/-! # Finite-list recursion with an input name

The numerical list representation and fold are unchanged. Their internal
binders avoid the sole free input variable, so handlers may query that input.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

theorem listFold_input_fv {Z H : AlphaTerm} (hZ : Z.fv ⊆ {0}) (hH : H.fv ⊆ {0}) :
    (listFold Z H).fv ⊆ {0} := by
  rw [listFold_fv]
  intro x hx
  rcases Finset.mem_union.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2 with hx | hx
  · exact hZ hx
  · exact hH hx

theorem listFold_input_unfold {Z H : AlphaTerm} (hZ : Z.fv ⊆ {0}) (hH : H.fv ⊆ {0}) (e : ℕ) :
    Relation.ReflTransGen Beta (app (listFold Z H) (numeral e))
      (listFoldBody Z H (listFold Z H) (numeral e)) := by
  let K := listFoldKernel Z H
  have hK : K.fv ⊆ {0} := by
    have h := listFold_input_fv hZ hH
    simpa only [listFold, fv_app, Finset.union_self] using h
  have hR := listFold_input_fv hZ hH
  have h₁ : Beta (app K K) (lam 13 (listFoldBody Z H (app K K) (var 13))) := by
    convert Beta.contract 12 (lam 13 (listFoldBody Z H (app (var 12) (var 12)) (var 13))) K using 1
    · rfl
    · rw [subst_lam_fresh _ _ 13 12 (by decide) (input_fresh hK (by decide)), listFoldBody_subst]
      simp [subst_app, subst_var,
        subst_not_free _ _ _ (input_fresh hZ (by decide : 12 ≠ 0)),
        subst_not_free _ _ _ (input_fresh hH (by decide : 12 ≠ 0))]
  have h₂ : Beta (app (lam 13 (listFoldBody Z H (listFold Z H) (var 13))) (numeral e))
      (listFoldBody Z H (listFold Z H) (numeral e)) := by
    convert Beta.contract 13 (listFoldBody Z H (listFold Z H) (var 13)) (numeral e) using 1
    simp [listFoldBody_subst, subst_var,
      subst_not_free _ _ _ (input_fresh hZ (by decide : 13 ≠ 0)),
      subst_not_free _ _ _ (input_fresh hH (by decide : 13 ≠ 0)),
      subst_not_free _ _ _ (input_fresh hR (by decide : 13 ≠ 0))]
  exact .tail (.single (.app_left _ h₁)) h₂

theorem listFold_input_nil {Z H : AlphaTerm} (hZ : Z.fv ⊆ {0}) (hH : H.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (listFold Z H) (numeral 0)) Z :=
  (listFold_input_unfold hZ hH 0).trans (branch_zero _ _ (input_fresh hZ (by decide)))

theorem listFold_input_cons {Z H : AlphaTerm} (hZ : Z.fv ⊆ {0}) (hH : H.fv ⊆ {0}) (a d : ℕ) :
    Relation.ReflTransGen Beta (app (listFold Z H) (numeral (Nat.pair a d + 1)))
      (app (app H (numeral a)) (app (listFold Z H) (numeral d))) := by
  apply (listFold_input_unfold hZ hH _).trans
  apply (branch_succ (Nat.pair a d) _ _).trans
  exact beta_steps_app (beta_steps_app_right H (listFieldTerm_cons true a d))
    (beta_steps_app_right (listFold Z H) (listFieldTerm_cons false a d))

theorem listFold_oracle_apply {p : ℕ → ℕ} {Z H : AlphaTerm}
    (hZ : Z.fv ⊆ {0}) (hH : H.fv ⊆ {0})
    (f : List ℕ → AlphaTerm) (h0 : Relation.ReflTransGen (OracleStep p) Z (f []))
    (hs : ∀ a xs, Relation.ReflTransGen (OracleStep p)
      (app (app H (numeral a)) (f xs)) (f (a :: xs))) (xs : List ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (listFold Z H) (numeral (NatListCode.encode xs))) (f xs) := by
  induction xs with
  | nil => exact (beta_steps_oracle (listFold_input_nil hZ hH)).trans h0
  | cons a xs ih =>
    exact (beta_steps_oracle (listFold_input_cons hZ hH a _)).trans
      ((oracle_steps_app_right (app H (numeral a)) ih).trans (hs a xs))

theorem listRecursorTerm_input_start {H Z : AlphaTerm} (hH : H.fv ⊆ {0}) (hZ : Z.fv ⊆ {0}) :
    Relation.ReflTransGen Beta (app (app listRecursorTerm H) Z) (listFold Z H) := by
  have hfH (n : ℕ) (hn : n ≠ 0) := input_fresh hH hn
  have hfZ (n : ℕ) (hn : n ≠ 0) := input_fresh hZ hn
  have h₁ : Beta (app listRecursorTerm H) (lam 31 (listFold (var 31) H)) := by
    convert Beta.contract 30 (lam 31 (listFold (var 31) (var 30))) H using 1
    · rfl
    · simp [subst_lam_fresh, listFold_subst, subst_var, hfH]
  have h₂ : Beta (app (lam 31 (listFold (var 31) H)) Z) (listFold Z H) := by
    convert Beta.contract 31 (listFold (var 31) H) Z using 1
    simp [listFold_subst, subst_var, hfZ, subst_not_free _ _ _ (hfH 31 (by decide))]
  exact .tail (.single (.app_left _ h₁)) h₂


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: List recursion with an input name
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The two beta steps unfolding the fold and the two steps supplying its parameters remain valid: the internal binders cannot capture the free input variable. The empty-list branch returns $Z$. The nonempty branch extracts the head and tail code, giving $H\ChurchNumeral{a}$ applied to the fold on the tail. Induct on the list, lift the tail reduction through application, and then use the assumed reduction for $H$. These operations use precisely the permitted beta/query contexts; no closedness assumption on the intermediate $V_l$ is needed.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The checker in §{sec:lambda-input-certificate-programs} treats an answer table as finite numerical data. We now compare
    those data with the actual input name and implement the bounded test from §{sec:lambda-input-certificates}. The list
    recursor of §{sec:lambda-finite-lists} also works when its handler queries the input.
-/
theorem listRecursorTerm_oracle_apply {p : ℕ → ℕ} {H Z : AlphaTerm}
    (hH : H.fv ⊆ {0}) (hZ : Z.fv ⊆ {0})
    (f : List ℕ → AlphaTerm) (h0 : Relation.ReflTransGen (OracleStep p) Z (f []))
    (hs : ∀ a xs, Relation.ReflTransGen (OracleStep p)
      (app (app H (numeral a)) (f xs)) (f (a :: xs))) (xs : List ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app listRecursorTerm H) Z) (numeral (NatListCode.encode xs))) (f xs) :=
  (beta_steps_oracle (beta_steps_app_left (listRecursorTerm_input_start hH hZ) _)).trans
    (listFold_oracle_apply hZ hH f h0 hs xs)

end PolishSpaceBook.NamedLambda.AlphaTerm
