module

public import PolishSpaceBook.FirstOrderEffectiveQuantifierBounds
public import PolishSpaceBook.FirstOrderCompoundTemplates
public import PolishSpaceBook.LambdaBoundedAlphaNames

@[expose] public section

/-! # A numerical bound for an unannotated equality template

The source determines a fresh distinguished name, a size bound, and a bound on
the free names. Bounded-name alpha normalization supplies a raw representative
within an explicit primitive-recursive numerical search interval.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EqualityBounds
open NamedLambda
open FirstOrderLambdaEncoding (LTerm)
open FirstOrderLambdaEncoding.EqualityMatcher (syntaxNames)
open QuantifierBounds

def freshName (a : ℕ) : ℕ := a + 1
def templateBound (a : ℕ) : ℕ := codeBound (3 * a + 3) (2 * a + 1)

theorem namesLe_of_syntaxNames (M : LTerm) (k : ℕ)
    (h : ∀ x ∈ syntaxNames M, x ≤ k) : NamesLe k M := by
  induction M with
  | var x => exact h x (by simp [syntaxNames])
  | app M N ihM ihN =>
    exact ⟨ihM (fun x hx => h x (Finset.mem_union_left _ hx)),
      ihN (fun x hx => h x (Finset.mem_union_right _ hx))⟩
  | lam x M ih => exact ⟨h x (by simp [syntaxNames]), ih (fun y hy => h y (Finset.mem_insert_of_mem hy))⟩

/-- The unknown distinguished variable can be renamed using freshness of the
observed source, even when the replacement is a compound term. -/
theorem fresh_instances {M N D U V : LTerm} (x : ℕ)
    (hM : (D.subst x U).Alpha M) (hN : (D.subst x V).Alpha N) :
    ((D.subst x (.var (freshName M.code))).subst (freshName M.code) U).Alpha M ∧
    ((D.subst x (.var (freshName M.code))).subst (freshName M.code) V).Alpha N := by
  let z := freshName M.code
  have hz : z ∉ M.fv := by
    intro hz
    have := free_name_le_code M z hz
    dsimp [z, freshName] at this
    omega
  have hf : z ∉ D.bindingTree.fv.erase x := by
    intro hf
    have hh := BindingTree.erase_fv_subset_compound_subst D.bindingTree U.bindingTree x hf
    rw [← Term.bindingTree_subst, Term.bindingTree_fv, hM.fv_eq] at hh
    exact hz hh
  have transport (R : LTerm) :
      ((D.subst x (.var z)).subst z R).Alpha (D.subst x R) := by
    rw [Term.alpha_iff_bindingTree]
    simp only [Term.bindingTree_subst, Term.bindingTree]
    exact BindingTree.subst_fresh_compound D.bindingTree R.bindingTree x z hf
  exact ⟨(transport U).trans hM, (transport V).trans hN⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    For $(=\mathrm E)$ with compound terms, let $a$ be the code of the first displayed instance and put $z=a+1$.
    If an unknown formula and distinguished variable give the two required instances, rename that distinguished free
    name to $z$ in its encoding. Every other free name survives in the first instance, so this renaming is fresh for
    the other free names. The resulting template has at most $2a+1$ nodes and free names at most $a+1$.
    Normalize its bound names without changing its $\alpha$-class, starting with an index above all free names and
    increasing it on descent. At an abstraction, retain the binder if it already has the chosen index; otherwise rename
    it to that index, which is then fresh for the body. This keeps the node count fixed and bounds all
    names by $3a+3$. Hence a suitable raw formula template has code at most
    $\LambdaSyntaxSizeBound{3a+3}{2a+1}$.
-/
theorem bounded_template {M N D U V : LTerm} (x : ℕ)
    (hM : (D.subst x U).Alpha M) (hN : (D.subst x V).Alpha N) :
    ∃ E : LTerm, (D.subst x (.var (freshName M.code))).Alpha E ∧
      E.code ≤ templateBound M.code ∧
      (E.subst (freshName M.code) U).Alpha M ∧
      (E.subst (freshName M.code) V).Alpha N := by
  let z := freshName M.code
  let C := D.subst x (.var z)
  have hfree : ∀ y ∈ C.fv, y < M.code + 2 := by
    intro y hy
    rw [Term.mem_fv_subst] at hy
    rcases hy with ⟨hy, hyx⟩ | ⟨_, hy⟩
    · have hys : y ∈ (D.subst x U).fv := (Term.mem_fv_subst _ _ _ _).mpr (Or.inl ⟨hy, hyx⟩)
      rw [hM.fv_eq] at hys
      have := free_name_le_code M y hys
      omega
    · simp only [Term.fv, Finset.mem_singleton] at hy
      dsimp [z, freshName] at hy
      omega
  obtain ⟨E, hCE, hnames⟩ := Term.exists_alpha_bounded_names C (M.code + 2) hfree
  have hnodes : C.nodes ≤ M.nodes := by
    have hh := Term.nodes_le_subst D U x
    simpa only [C, Term.nodes_subst_var, hM.nodes_eq] using hh
  have hcodeNodes := nodes_le_code M
  have hEnodes : E.nodes ≤ 2 * M.code + 1 := by rw [← hCE.nodes_eq]; omega
  have hEnames : NamesLe (3 * M.code + 3) E := by
    apply namesLe_of_syntaxNames
    intro y hy
    have := hnames y hy
    omega
  obtain ⟨hCU, hCV⟩ := fresh_instances x hM hN
  exact ⟨E, hCE, code_le_bound E _ _ hEnodes hEnames,
    ((hCE.symm.subst (.refl U) z).trans hCU), ((hCE.symm.subst (.refl V) z).trans hCV)⟩

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EqualityBounds
