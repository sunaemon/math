module

public import PolishSpaceBook.FirstOrderGraphTotality

@[expose] public section

/-!
# Every recursively constructed term graph has a derivable value

Induct on the actual term. The child witnesses are opened together, then an
operation witness is obtained, and the existential block of the graph is
introduced. All derivations stay in the original language and theory.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- A child graph has no free occurrence of a different child's output name. -/
theorem argumentGraphs_independent {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (B : ℕ) (ht : ∀ i y, y ∈ (ts i).varFinset → y < B) (i j : Fin n) (hij : i ≠ j) :
    B+i.val ∉ (D.termGraph (ts j) (B+j.val) (B+n)).fv := by
  intro hm
  rcases Finset.mem_insert.mp (D.fv_termGraph_subset (ts j) _ _ hm) with he | hm
  · apply hij; exact Fin.ext (by omega)
  · have := ht j _ hm; omega

/-- The old theory proves totality of every nested term graph. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Now induct on the term. For a variable, its own name supplies the value. At a function application, induction
    gives existence of each child value. The child graphs have no free variables other than their own output names
    and original term variables, so the finite witness argument applies. Under these child assumptions, obtain an
    operation value using the first paragraph. Its output name is absent from the child graphs because it does not
    occur in the original term and differs from every child output. Conjoin the child graphs with the operation
    graph, introduce the block of child quantifiers using their own names as witnesses, and introduce the output
    quantifier. Existential elimination discharges the operation witness and then the child witnesses. The final
    conclusion has no free child output, and the original assumptions are sentences, so all eigenvariable conditions
    hold. This proves the first assertion.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Derivable existence of term values
-/
theorem proves_termGraph_exists {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t : (L.sum (functionSymbols ι)).Term ℕ) (x B : ℕ)
    (hx : x < B) (hxt : x ∉ t.varFinset) (ht : ∀ y ∈ t.varFinset, y < B) :
    ProvesFrom T (quant .ex x (D.termGraph t x B)) := by
  induction t generalizing x B with
  | var y =>
    have hxy : y ≠ x := by simpa only [Term.varFinset, Finset.mem_singleton, ne_eq, eq_comm] using hxt
    refine ⟨∅, by simp, Derives.exIntro x _ (.var y) ?_⟩
    simpa only [termGraph, subst_equal, termSubst_var_self, termSubst, Term.subst, ite_eq_right hxy, ite_true]
      using Derives.eqIntro (∅ : Context L) (.var y)
  | @func n f ts ih =>
    let ρ : Fin n → AlphaFormula L := fun i => D.termGraph (ts i) (B+i.val) (B+n)
    let C := D.operationGraph f (fun i : Fin n => .var (B+i.val)) x
    let χ := quant .ex x (D.termGraph (.func f ts) x B)
    have hti (i : Fin n) (y : ℕ) (hy : y ∈ (ts i).varFinset) : y < B :=
      ht y (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hy⟩)
    have hxchild (i : Fin n) : x ∉ (ts i).varFinset := fun hy =>
      hxt (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hy⟩)
    have hs (i : Fin n) : ProvesFrom T (quant .ex (B+i.val) (ρ i)) :=
      ih i _ _ (by have := i.isLt; omega)
        (fun hy => by have := hti i _ hy; omega)
        (fun y hy => by have := hti i y hy; omega)
    have hc := ProvesFrom.conjoin n (fun i => quant .ex (B+i.val) (ρ i)) hs
    have hop := D.proves_operationGraph_exists hT hu f B x hx
    apply ProvesFrom.map₂_sentences hT hc hop
    intro Γ hΓ hcs hop
    have hcross := D.argumentGraphs_independent ts B hti
    have hχ (i : Fin n) : B+i.val ∉ χ.fv := by
      intro hm
      dsimp only [χ] at hm
      rw [fv_quant] at hm
      have hm' := (Finset.mem_erase.mp hm).2
      rcases Finset.mem_insert.mp (D.fv_termGraph_subset (.func f ts) x B hm') with he | hm'
      · omega
      · have := ht _ hm'; omega
    have hxρ : x ∉ (conjoin n ρ).fv := by
      rw [fv_conjoin]
      intro hm
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
      rcases Finset.mem_insert.mp (D.fv_termGraph_subset (ts i) _ _ hi) with he | hi
      · omega
      · exact hxchild i hi
    refine Derives.independent_witnesses n B ρ χ (by intro i; rw [hΓ]; simp) hχ hcross
      (fun i => Derives.conjoin_elim n _ hcs i) ?_
    let Δ := insert (conjoin n ρ) Γ
    have hex : Derives Δ (quant .ex x C) := hop.weaken (Finset.subset_insert _ _)
    have hb : Derives (insert C Δ) χ := by
      apply Derives.exIntro x _ (.var x)
      rw [subst_self]
      apply Derives.existsBlock_intro_self n B
      exact .andIntro (.assumption (by simp [Δ, ρ])) (.hyp Δ C)
    apply Derives.exElim x x C χ hex (by simpa only [subst_self] using hb)
    have hxΓ : x ∉ Δ.fv := by
      simpa only [Δ, Context.fv_insert, hΓ, Finset.union_empty] using hxρ
    have hxχ : x ∉ χ.fv := by
      dsimp only [χ]
      simp only [fv_quant, Finset.notMem_erase, not_false_eq_true]
    simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
      false_and, or_false, not_or]
    exact ⟨hxΓ,hxχ⟩

/-- All argument values can be bound at once, including the empty tuple. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Apply the finite witness argument to the resulting child-value proofs to obtain the second assertion.
    The empty tuple gives the provable empty conjunction.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Derivable existence of term values
-/
theorem proves_argument_values_exists {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ) (B : ℕ)
    (ht : ∀ i y, y ∈ (ts i).varFinset → y < B) :
    ProvesFrom T (existsBlock n B (conjoin n (fun i => D.termGraph (ts i) (B+i.val) (B+n)))) := by
  let ρ : Fin n → AlphaFormula L := fun i => D.termGraph (ts i) (B+i.val) (B+n)
  have hs (i : Fin n) : ProvesFrom T (quant .ex (B+i.val) (ρ i)) :=
    D.proves_termGraph_exists hT hu (ts i) _ _ (by have := i.isLt; omega)
      (fun hm => by have := ht i _ hm; omega)
      (fun y hy => by have := ht i y hy; omega)
  obtain ⟨Γ,hΓ,h⟩ := ProvesFrom.conjoin n (fun i => quant .ex (B+i.val) (ρ i)) hs
  refine ⟨Γ,hΓ,Derives.independent_witness_block n B ρ ?_
    (D.argumentGraphs_independent ts B ht) (fun i => Derives.conjoin_elim n _ h i)⟩
  intro i
  rw [Context.fv_eq_empty_of_sentences hT Γ hΓ]
  simp

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
