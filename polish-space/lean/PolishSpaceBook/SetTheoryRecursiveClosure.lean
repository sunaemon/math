module

public import PolishSpaceBook.SetTheoryTransitiveBounds

@[expose] public section

/-! # Identifying internal recursive values with a given external recursion -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma mem_functionGraph_global {D p : ZFSet.{u}} (K : ZFSet.{u} → ZFSet.{u}) :
    p ∈ functionGraph (fun a : D => K a.val) ↔ ∃ a ∈ D, p = ZFSet.pair a (K a) := by
  rw [functionGraph, ZFSet.mem_range]
  exact ⟨fun ⟨a, ha⟩ => ⟨a.val, a.property, ha.symm⟩,
    fun ⟨a, ha, he⟩ => ⟨⟨a, ha⟩, he.symm⟩⟩

lemma graphRange_functionGraph {D : ZFSet.{u}} (K : ZFSet.{u} → ZFSet.{u}) :
    graphRange (functionGraph (fun a : D => K a.val)) = ZFSet.range (fun a : D => K a.val) := by
  apply ZFSet.ext
  intro b
  rw [mem_graphRange, ZFSet.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨c, hc, he⟩ := (mem_functionGraph_global K).mp ha
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨⟨a, hc⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, (mem_functionGraph_global K).mpr ⟨a.val, a.property, rfl⟩⟩

lemma restrict_functionGraph_global {D x : ZFSet.{u}} (K : ZFSet.{u} → ZFSet.{u}) (hx : x ⊆ D) :
    restrictGraph (functionGraph (fun a : D => K a.val)) x = functionGraph (fun a : x => K a.val) := by
  apply ZFSet.ext
  intro p
  rw [mem_restrictGraph, mem_functionGraph_global]
  constructor
  · rintro ⟨a, ha, b, rfl, hab⟩
    obtain ⟨c, hc, he⟩ := (mem_functionGraph_global K).mp hab
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, K a, rfl, (mem_functionGraph_global K).mpr ⟨a, hx ha, rfl⟩⟩

lemma external_function_solution {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (K : ZFSet.{u} → ZFSet.{u})
    (hK : ∀ a, K a = H a (functionGraph (fun b : a => K b.val)))
    {D : ZFSet.{u}} (hD : D.IsTransitive) :
    IsRecursiveSolution H D (functionGraph (fun a : D => K a.val)) := by
  refine ⟨hD, isFunc_doubleUnion (functionGraph_isFunc _), ?_⟩
  intro a ha
  rw [restrict_functionGraph_global K (hD.subset_of_mem ha), ← hK a]
  exact (mem_functionGraph_global K).mpr ⟨a, ha, rfl⟩

/-- An externally given recursive function preserves M once its step is internally defined and closed. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Ambient Replacement makes $\Gamma_{K,D}$ a set for each set $D$.
    When $D$ is transitive, restricting this graph to $a\in D$ gives $\Gamma_{K,a}$, so the assumed equation
    makes it an actual partial solution. For $a\in M$, the preceding corollary supplies an internal partial
    solution assigning a value at $a$. Compare it with the external graph on the same transitive domain.
    Agreement of partial solutions identifies the internal value with $K(a)$, proving that $K(a)\in M$.
    This argument proves membership of the specified recursive value, rather than merely producing some
    unidentified internal solution.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Comparison with an external recursion
-/
theorem external_recursive_value_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → M)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : M,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (hclosed : ∀ a g : M, H a.val g.val ∈ M)
    (K : ZFSet.{u} → ZFSet.{u})
    (hK : ∀ a, K a = H a (functionGraph (fun b : a => K b.val))) (a : M) : K a.val ∈ M := by
  obtain ⟨b, hb, _⟩ := internal_recursive_value_existsUnique hM hinf hpair hunion hpower hsep hrep
    ψ ps H hH hclosed a
  obtain ⟨D, F, hF, haD, hab⟩ := (realize_recursiveValueFormula hM hunion (hsep _) ψ ps H hH a b).mp hb
  have hExt := external_function_solution K hK hF.domain_transitive
  have hpairExt := (mem_functionGraph_global K).mpr ⟨a.val, haD, rfl⟩
  have he := recursive_solutions_agree hF hExt a.val haD haD b.val (K a.val) hab hpairExt
  exact he ▸ b.property

/-- The value formula defines the specified external recursion on model inputs. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    An internal partial solution witnessing the left side agrees with the external graph at $a$, so its value is
    $K(a)$. Conversely, existence of an internal recursive value supplies some $c\in M$ satisfying the left side
    with $c$ in place of $b$. The same comparison gives $c=K(a)=b$, yielding the desired instance of the formula.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: corollary
  title: Defining the external recursive value
-/
theorem realize_recursiveValueFormula_external {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → M)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : M,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (hclosed : ∀ a g : M, H a.val g.val ∈ M)
    (K : ZFSet.{u} → ZFSet.{u})
    (hK : ∀ a, K a = H a (functionGraph (fun b : a => K b.val))) (a b : M) :
    (recursiveValueFormula ψ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) ↔ b.val = K a.val := by
  have hforward (c : M)
      (hc : (recursiveValueFormula ψ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) c)) :
      c.val = K a.val := by
    obtain ⟨D, F, hF, haD, hac⟩ := (realize_recursiveValueFormula hM hunion (hsep _) ψ ps H hH a c).mp hc
    exact recursive_solutions_agree hF (external_function_solution K hK hF.domain_transitive)
      a.val haD haD c.val (K a.val) hac ((mem_functionGraph_global K).mpr ⟨a.val, haD, rfl⟩)
  refine ⟨hforward b, ?_⟩
  intro hb
  obtain ⟨c, hc, _⟩ := internal_recursive_value_existsUnique hM hinf hpair hunion hpower hsep hrep
    ψ ps H hH hclosed a
  have he : c = b := Subtype.ext ((hforward c hc).trans hb.symm)
  exact he ▸ hc

end PolishSpaceBook.SetTheoryModels
