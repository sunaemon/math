module

public import PolishSpaceBook.SetTheoryWordCons
public import PolishSpaceBook.BorelPointGraphs
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # Composition of internal numerical function graphs by reflected Separation -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
open BoundedSetPredicate
universe u

/-- Parameters omega, the input graph, the outer function graph, and the candidate pair. -/
def pointCompositionPredicate : BoundedSetPredicate 4 :=
  .ex 0 (.ex 0 (.ex 0 (.conj (.orderedPair 3 4 6)
    (.conj (.pairMember 1 4 5) (.pairMember 2 5 6)))))

lemma eval_pointCompositionPredicate (x f : ℕ → ℕ) (p : ZFSet.{u}) :
    pointCompositionPredicate.eval ![Ordinal.omega0.toZFSet, pointGraph x, pointGraph f, p] ↔
      p ∈ pointGraph (f ∘ x) := by
  simp [pointCompositionPredicate, eval, Fin.snoc, Fin.castPred, Fin.castLT, exists_mem_omegaOrdinal,
    pointGraph, ZFSet.mem_range, natOrdinal_injective.eq_iff, eq_comm]

/-- A fixed internal numerical function can be applied to every entry of an internal point. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal coordinatewise maps
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separate from $\omega\times\omega$ the pairs $\langle n,k\rangle$ satisfying
    $$\exists j\in\omega\;(\langle n,j\rangle\in g_x\land\langle j,k\rangle\in G_f).$$
    This is a bounded predicate, so the uniform interpretation principle gives an internal set. The first graph
    forces $j=x(n)$ and the second forces $k=f(x(n))$. Thus the separated set is exactly $g_{f\circ x}$.
    In particular, both numerical projections can be applied to an internal sequence of paired entries.
-/
theorem pointGraph_comp_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (x f : ℕ → ℕ) (hx : pointGraph x ∈ M) (hf : pointGraph f ∈ M) :
    pointGraph (f ∘ x) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let ps : Fin 3 → M := ![Ω, ⟨pointGraph x, hx⟩, ⟨pointGraph f, hf⟩]
  have hD := prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property
  apply pointCompositionPredicate.subset_mem hM (hsep _) ps hD (pointGraph_isFunc (f ∘ x)).1
  intro p _
  have he : Fin.snoc (Subtype.val ∘ ps) p =
      ![Ordinal.omega0.toZFSet, pointGraph x, pointGraph f, p] := by funext j; fin_cases j <;> rfl
  rw [he, eval_pointCompositionPredicate]

end PolishSpaceBook.BorelExpression
