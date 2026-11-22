module

public import PolishSpaceBook.FirstOrderEqualityMatcher

@[expose] public section

/-! # Alpha representatives with bounded names

This is an existence lemma for a finite-search bound. No computable selection
from alpha-classes is used: an actual bounded search will inspect raw codes.
-/
namespace PolishSpaceBook.NamedLambda.Term
open FirstOrderLambdaEncoding.EqualityMatcher (syntaxNames)

theorem exists_alpha_bounded_names (M : Term) (B : ℕ)
    (hB : ∀ x ∈ M.fv, x < B) :
    ∃ N, M.Alpha N ∧ ∀ x ∈ syntaxNames N, x < B + M.nodes := by
  have bounded : ∀ k (M : Term) B, M.nodes ≤ k → (∀ x ∈ M.fv, x < B) →
      ∃ N, M.Alpha N ∧ ∀ x ∈ syntaxNames N, x < B + M.nodes := by
    intro k
    induction k with
    | zero => intro M B hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M B hk hB
      cases M with
      | var x =>
        refine ⟨.var x, .refl _, ?_⟩
        intro y hy
        simp only [syntaxNames, Finset.mem_singleton] at hy
        subst y
        have hx := hB x (by simp [fv])
        simp only [nodes]; omega
      | app M N =>
        obtain ⟨M', hM, hbM⟩ := ih M B (by simp only [nodes] at hk; omega)
          (fun x hx => hB x (Finset.mem_union_left _ hx))
        obtain ⟨N', hN, hbN⟩ := ih N B (by simp only [nodes] at hk; omega)
          (fun x hx => hB x (Finset.mem_union_right _ hx))
        refine ⟨.app M' N', .app hM hN, ?_⟩
        intro x hx
        simp only [syntaxNames, Finset.mem_union] at hx
        rcases hx with hx | hx
        · have := hbM x hx; simp only [nodes]; omega
        · have := hbN x hx; simp only [nodes]; omega
      | lam x M =>
        have hbody : ∀ y ∈ M.fv.erase x, y < B := hB
        by_cases hx : x = B
        · subst x
          have hf : ∀ y ∈ M.fv, y < B + 1 := by
            intro y hy
            by_cases hyB : y = B
            · omega
            · have := hbody y (Finset.mem_erase.mpr ⟨hyB, hy⟩); omega
          obtain ⟨N, hN, hbN⟩ := ih M (B + 1) (by simpa only [nodes, Nat.add_le_add_iff_right] using hk) hf
          refine ⟨.lam B N, .lam hN B, ?_⟩
          intro y hy
          simp only [syntaxNames, Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · have := M.nodes_pos; simp only [nodes]; omega
          · have := hbN y hy; simp only [nodes]; omega
        · have hz : B ∉ M.fv := by
            intro hz
            have := hbody B (Finset.mem_erase.mpr ⟨Ne.symm hx, hz⟩)
            omega
          have hf : ∀ y ∈ (M.subst x (.var B)).fv, y < B + 1 := by
            intro y hy
            rw [mem_fv_subst] at hy
            rcases hy with ⟨hy, hyx⟩ | ⟨_, hy⟩
            · have := hbody y (Finset.mem_erase.mpr ⟨hyx, hy⟩); omega
            · simp only [fv, Finset.mem_singleton] at hy; omega
          obtain ⟨N, hN, hbN⟩ := ih (M.subst x (.var B)) (B + 1)
            (by simp only [nodes_subst_var]; simp only [nodes] at hk; omega) hf
          refine ⟨.lam B N, (RenameEq.rename M x B hz).trans (.lam B hN), ?_⟩
          intro y hy
          simp only [syntaxNames, Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · have := M.nodes_pos; simp only [nodes]; omega
          · have := hbN y hy; simp only [nodes_subst_var] at this; simp only [nodes]; omega
  exact bounded M.nodes M B le_rfl hB

/-- Replacing variable leaves cannot decrease the number of syntax nodes. -/
theorem nodes_le_subst (M N : Term) (x : ℕ) : M.nodes ≤ (M.subst x N).nodes := by
  have bounded : ∀ k (M N : Term) x, M.nodes ≤ k → M.nodes ≤ (M.subst x N).nodes := by
    intro k
    induction k with
    | zero => intro M N x hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M N x hk
      cases M with
      | var y =>
        by_cases hy : y = x
        · simp only [subst_var, ite_eq_left hy, nodes]
          exact N.nodes_pos
        · simp only [subst_var, ite_eq_right hy, le_refl]
      | app A B =>
        have hA := ih A N x (by simp only [nodes] at hk; omega)
        have hB := ih B N x (by simp only [nodes] at hk; omega)
        simp only [subst_app, nodes]; omega
      | lam y A =>
        rw [subst_lam]
        by_cases hy : y = x
        · rw [ite_eq_left hy]
        · rw [ite_eq_right hy]
          by_cases hf : y ∉ N.fv
          · rw [ite_eq_left hf]
            have hA := ih A N x (by simp only [nodes] at hk; omega)
            simp only [nodes]; omega
          · rw [ite_eq_right hf]
            let z := fresh (A.fv ∪ N.fv ∪ {x})
            have hA := ih (A.subst y (.var z)) N x
              (by simp only [nodes_subst_var]; simp only [nodes] at hk; omega)
            simp only [nodes_subst_var] at hA
            change A.nodes + 1 ≤ ((A.subst y (.var z)).subst x N).nodes + 1
            omega
  exact bounded M.nodes M N x le_rfl

end PolishSpaceBook.NamedLambda.Term
