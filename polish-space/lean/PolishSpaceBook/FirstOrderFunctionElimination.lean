module

public import PolishSpaceBook.FirstOrderTermValueBinders

@[expose] public section

/-!
# Recursive elimination of defined function symbols

Each atom binds the values of all its terms using recursively constructed
old-language graphs. Connectives and quantifiers preserve their constructors.
The translation here acts on named representatives. FirstOrderFunctionClasses
proves compatibility with alpha-equivalence; derivation translation is separate.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

def valueBound {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ) : ℕ :=
  (argumentVars ts).sup id + 1

theorem valueBound_spec {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ) :
    ∀ i y, y ∈ (ts i).varFinset → y < valueBound ts := by
  intro i y hy
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id)
    (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hy⟩))

def equalValues (B : ℕ) : AlphaFormula L := equal (.var B) (.var (B+1))

def relationValues {n : ℕ} (R : L.Relations n) (B : ℕ) : AlphaFormula L :=
  rel R (fun i => .var (B+i.val))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For an atom $R(t_0,\ldots,t_{n-1})$, choose $B$ above all variable indices in its terms and put $z_i=v_{B+i}$.
    Translate it to
    $$\exists z_{n-1}\cdots\exists z_0\,\Bigl(
    \bigwedge_{i<n}\FirstOrderTermGraph{t_i}{z_i}{B+n}\land R(\vec{z})\Bigr).$$
    For an equality, use two witnesses in the same construction and put their equality in the last conjunct.
    Leave falsity unchanged, and translate recursively through connectives and quantifiers while retaining their
    constructors and bound variables.
-/
def eraseFormula : Formula (L.sum (functionSymbols ι)) → AlphaFormula L
  | .falsum => falsum
  | .equal t r => D.withValues ![t,r] (valueBound ![t,r]) (equalValues (valueBound ![t,r]))
  | .rel (Sum.inl R) ts => D.withValues ts (valueBound ts) (relationValues R (valueBound ts))
  | .rel (Sum.inr R) _ => nomatch R
  | .binary c φ ψ => binary c (eraseFormula φ) (eraseFormula ψ)
  | .quant q x φ => quant q x (eraseFormula φ)

theorem fv_equalValues_subset (B : ℕ) : (equalValues (L := L) B).fv ⊆ temporaryNames 2 B := by
  intro y hy
  change y ∈ ({B} ∪ {B+1} : Finset ℕ) at hy
  simp only [Finset.mem_union, Finset.mem_singleton] at hy
  rw [mem_temporaryNames_iff]
  omega

theorem fv_relationValues_subset {n : ℕ} (R : L.Relations n) (B : ℕ) :
    (relationValues R B).fv ⊆ temporaryNames n B := by
  intro y hy
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hy
  have he : y = B+i.val := by simpa using hi
  exact he ▸ Finset.mem_image.mpr ⟨i.val,Finset.mem_range.mpr i.isLt,rfl⟩

theorem fv_withValues_atom {n : ℕ} (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (B : ℕ) (ψ : AlphaFormula L) (hψ : ψ.fv ⊆ temporaryNames n B) :
    (D.withValues ts B ψ).fv ⊆ argumentVars ts := by
  intro y hy
  obtain ⟨hy,hout⟩ := Finset.mem_sdiff.mp (D.fv_withValues_subset ts B ψ hy)
  rcases Finset.mem_union.mp hy with hy | hy
  · exact hy
  · exact False.elim (hout (hψ hy))

/-- Eliminating function terms introduces no new free parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The free-variable
    inclusion follows because all witness variables are bound.
-/
theorem fv_eraseFormula_subset (φ : Formula (L.sum (functionSymbols ι))) :
    (D.eraseFormula φ).fv ⊆ φ.fv := by
  induction φ with
  | falsum => exact Finset.Subset.refl _
  | equal t r =>
    simpa [eraseFormula, argumentVars, Finset.univ_fin2, Formula.fv] using
      D.fv_withValues_atom ![t,r] (valueBound ![t,r]) _ (fv_equalValues_subset _)
  | rel R ts =>
    rcases R with R | R
    · exact D.fv_withValues_atom ts _ _ (fv_relationValues_subset R _)
    · exact nomatch R
  | binary c φ ψ ihφ ihψ =>
    simpa only [eraseFormula, fv_binary, Formula.fv] using Finset.union_subset_union ihφ ihψ
  | quant q x φ ih =>
    simpa only [eraseFormula, fv_quant, Formula.fv] using Finset.erase_subset_erase x ih

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]

/-- Structural recursion preserves the truth of every expanded-language formula. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: Elimination of defined functions
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Structural induction now proves both assertions
    for every formula: connectives combine their subformulas, and quantifiers apply the induction hypothesis under
    each assignment to the bound variable. No new free variable can be captured by an outer quantifier.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The recursive-graph lemma forces the witnesses of an atom to be exactly its argument values. Conversely, these
    values supply witnesses, so the original and translated atoms have the same truth value.
-/
theorem realize_eraseFormula (φ : Formula (L.sum (functionSymbols ι))) (s : ℕ → M)
    (hu : ∀ k (g : ι k) (s : ℕ → M), ∃! b, (D.graph g).Realize (Function.update s k b))
    (ha : ∀ k (g : ι k) (s : ℕ → M), (D.definingAxiom g).Realize s) :
    (D.eraseFormula φ).Realize s ↔ φ.Realize s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t r =>
    rw [eraseFormula, D.realize_withValues _ _ _ (valueBound_spec _) s hu ha]
    let B := valueBound ![t,r]
    have h0 := blockAssignment_inside s B (fun i : Fin 2 => (![t,r] i).realize s) 0
    have h1 := blockAssignment_inside s B (fun i : Fin 2 => (![t,r] i).realize s) 1
    change blockAssignment s B (fun i : Fin 2 => (![t,r] i).realize s) B =
      blockAssignment s B (fun i : Fin 2 => (![t,r] i).realize s) (B+1) ↔ _
    simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at h0 h1
    rw [h0,h1]
    rfl
  | rel R ts =>
    rcases R with R | R
    · rw [eraseFormula, D.realize_withValues _ _ _ (valueBound_spec _) s hu ha]
      change Structure.RelMap (L := L) R (fun i => blockAssignment s (valueBound ts)
        (fun j => (ts j).realize s) (valueBound ts+i.val)) ↔ _
      simp only [blockAssignment_inside]
      exact (iff_of_eq ((inclusion (L := L) (ι := ι)).map_onRelation R _)).symm
    · exact nomatch R
  | binary c φ ψ ihφ ihψ =>
    rw [eraseFormula, realize_binary]
    exact c.eval_congr (ihφ s) (ihψ s)
  | quant q x φ ih =>
    rw [eraseFormula, realize_quant]
    exact q.eval_congr (fun a => ih (Function.update s x a))

end Semantics
end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
