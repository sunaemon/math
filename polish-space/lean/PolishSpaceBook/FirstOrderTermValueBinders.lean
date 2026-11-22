module

public import PolishSpaceBook.FirstOrderTermGraphs

@[expose] public section

/-!
# Binding the values of a finite family of terms

Term graphs constrain the witnesses uniquely. The resulting formula evaluates
its continuation at precisely those values and preserves every other parameter.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

def withValues {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (B : ℕ) (ψ : AlphaFormula L) : AlphaFormula L :=
  existsBlock n B (binary .conj (conjoin n (fun i => D.termGraph (ts i) (B+i.val) (B+n))) ψ)

theorem fv_withValues_subset {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (B : ℕ) (ψ : AlphaFormula L) :
    (D.withValues ts B ψ).fv ⊆ (argumentVars ts ∪ ψ.fv) \ temporaryNames n B := by
  rw [withValues, fv_existsBlock, fv_binary, fv_conjoin]
  intro y hy
  obtain ⟨hy,hout⟩ := Finset.mem_sdiff.mp hy
  refine Finset.mem_sdiff.mpr ⟨?_,hout⟩
  rcases Finset.mem_union.mp hy with hy | hy
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hy
    rcases Finset.mem_insert.mp (D.fv_termGraph_subset (ts i) _ _ hi) with he | hi
    · exact False.elim (hout (he ▸ Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
  · exact Finset.mem_union_right _ hy

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The recursive-graph lemma forces the witnesses of an atom to be exactly its argument values. Conversely, these
    values supply witnesses, so the original and translated atoms have the same truth value.
-/
theorem realize_withValues {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (B : ℕ) (ψ : AlphaFormula L) (ht : ∀ i y, y ∈ (ts i).varFinset → y < B) (s : ℕ → M)
    (hu : ∀ k (g : ι k) (s : ℕ → M), ∃! b, (D.graph g).Realize (Function.update s k b))
    (ha : ∀ k (g : ι k) (s : ℕ → M), (D.definingAxiom g).Realize s) :
    (D.withValues ts B ψ).Realize s ↔ ψ.Realize (blockAssignment s B (fun i => (ts i).realize s)) := by
  let s₀ := blockAssignment s B (fun i => (ts i).realize s)
  have hchild (i : Fin n) (s' : ℕ → M) :
      (D.termGraph (ts i) (B+i.val) (B+n)).Realize s' ↔ s' (B+i.val) = (ts i).realize s' :=
    D.realize_termGraph (ts i) _ _ (by have := i.isLt; omega)
      (fun y hy => by have := ht i y hy; omega) s' hu ha
  have hlocal (s' : ℕ → M) (he : ∀ y, y ∉ temporaryNames n B → s' y = s y) (i : Fin n) :
      (ts i).realize s' = (ts i).realize s := by
    apply term_realize_congr
    intro y hy; apply he; rw [mem_temporaryNames_iff]; have := ht i y hy; omega
  rw [withValues, realize_existsBlock]
  constructor
  · rintro ⟨s',he,h⟩
    obtain ⟨hc,hψ⟩ := (realize_conj _ _ _).mp h
    have hc' (i : Fin n) := (hchild i s').mp ((realize_conjoin _ _ _).mp hc i)
    have hs : s' = s₀ := by
      funext y
      by_cases hy : y ∈ temporaryNames n B
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
        rw [hc' ⟨i,Finset.mem_range.mp hi⟩, hlocal s' he]
        exact (blockAssignment_inside s B (fun j => (ts j).realize s) ⟨i,Finset.mem_range.mp hi⟩).symm
      · rw [he y hy]; exact (blockAssignment_outside s B (fun j => (ts j).realize s) y hy).symm
    simpa only [hs] using hψ
  · intro hψ
    have he : ∀ y, y ∉ temporaryNames n B → s₀ y = s y := blockAssignment_outside s B _
    refine ⟨s₀,he,(realize_conj _ _ _).mpr ⟨?_,hψ⟩⟩
    apply (realize_conjoin _ _ _).mpr
    intro i
    apply (hchild i s₀).mpr
    rw [hlocal s₀ he i]
    exact blockAssignment_inside s B _ i

end Semantics
end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
