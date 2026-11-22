module

public import PolishSpaceBook.BorelNodeCodes
public import PolishSpaceBook.BorelGraphValidity
public import PolishSpaceBook.SetTheoryPredicateGraphs
public import PolishSpaceBook.SetTheoryDefinableSequences

@[expose] public section

/-! # Collecting entire families of Borel label graphs

One bounded label description, with an extra numerical parameter, supplies
both each graph and the whole sequence of graphs. The graph predicate is
constructed once by the shared bounded-predicate infrastructure.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

theorem bounded_labelGraphFamily_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    {k : ℕ} (p : BoundedSetPredicate (k + 3)) (ps : Fin k → M)
    (a b : Fin k) (ha : (ps a).val = finiteSequences) (hb : (ps b).val = Ordinal.omega0.toZFSet)
    (c : ℕ → BorelExpression)
    (hp : ∀ n s y, p.eval (Fin.snoc (Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n))
      (wordGraph s)) y) ↔ y = natOrdinal (c n s)) :
    sequenceGraph (fun n => (c n).labelGraph) ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  have hc (n : ℕ) : (c n).labelGraph ∈ M := by
    apply bounded_labelGraph_mem hM hinf hpair hunion hpower hsep hrep p
      (Fin.snoc ps ⟨natOrdinal n, hn n⟩) (c n)
    intro s y
    simpa only [Fin.comp_snoc] using hp n s y.val
  let values (n : ℕ) : M := ⟨(c n).labelGraph, hc n⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep
    (p.graph a.castSucc b.castSucc) ps values
  intro n L
  have h := eval_graph_iff_eq p a.castSucc b.castSucc
    (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) (c n).labelGraph L.val
    (by simpa only [Fin.snoc_castSucc, Function.comp_apply, ha, hb] using labelGraph_isFunc (c n))
    (by
      intro s hs y hy
      rw [Fin.snoc_castSucc, Function.comp_apply, ha] at hs
      obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hs
      rw [hp, pair_mem_labelGraph])
  simpa only [Fin.comp_snoc] using h.trans
    (show L.val = (c n).labelGraph ↔ L = values n from
      ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩)

end PolishSpaceBook.BorelExpression
