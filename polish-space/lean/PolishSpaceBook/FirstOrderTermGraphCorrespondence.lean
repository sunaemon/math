module

public import PolishSpaceBook.FirstOrderBlockCorrespondence

@[expose] public section

/-!
# Syntactic comparison of recursive term graphs

Input variables retain their correspondence, while witness blocks are paired
by argument position. This permits different fresh starting indices on each side.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

theorem operationGraph_corresponds {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n)
    (ts us : Fin n → L.Term ℕ) (R : ℕ → ℕ → Prop) (x y : ℕ)
    (h : ∀ i, TermRel R (ts i) (us i)) (hxy : R x y) :
    Corresponds R (D.operationGraph f ts x) (D.operationGraph f us y) := by
  rcases f with f | f
  · exact Corresponds.equal (.var hxy) (.func f h)
  · apply simultaneous_corresponds _ _ _ _ (D.freeVars f)
    intro i
    cases i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using TermRel.var hxy
    | cast i => simpa only [Fin.snoc_castSucc] using h i

/-- Fresh recursive graphs preserve comparison even with different witness names. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Induct on the compared terms. Variables give corresponding equalities. At an application, compare each pair of
    child graphs under the updated relation. Their outputs are the paired witnesses, their internal names start at
    $B+n$ and $C+n$, and the original variables remain below those indices. Thus induction applies. For an old
    operation, its value equation compares componentwise. For a new operation, use the comparison of simultaneous
    instances of its defining graph proved above, including the output among the arguments. Combine the child
    graphs by conjunction and close each paired existential quantifier. This yields comparison under the original
    relation. Applying this result to identical terms and outputs with equality as the relation proves independence
    of the fresh starting index up to $\alpha$-equivalence.
-/
theorem termGraph_corresponds (t r : (L.sum (functionSymbols ι)).Term ℕ)
    (R : ℕ → ℕ → Prop) (x y B C : ℕ) (h : TermRel R t r) (hxy : R x y)
    (hx : x < B) (hy : y < C)
    (ht : ∀ a ∈ t.varFinset, a < B) (hr : ∀ b ∈ r.varFinset, b < C) :
    Corresponds R (D.termGraph t x B) (D.termGraph r y C) := by
  induction t generalizing r R x y B C with
  | var a =>
    cases h with
    | var hab => exact Corresponds.equal (.var hxy) (.var hab)
  | @func n f ts ih =>
    cases h
    rename_i us h
    have hts (i : Fin n) (a : ℕ) (ha : a ∈ (ts i).varFinset) : a < B :=
      ht a (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩)
    have hus (i : Fin n) (a : ℕ) (ha : a ∈ (us i).varFinset) : a < C :=
      hr a (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩)
    apply Corresponds.existsBlock
    apply Corresponds.binary .conj
    · apply Corresponds.conjoin
      intro i
      apply ih i (us i) (bindBlock R n B C) (B+i.val) (C+i.val) (B+n) (C+n)
      · exact (h i).congr (fun a ha b hb hab => bindBlock_below n B C a b (hts i a ha) (hus i b hb) hab)
      · exact bindBlock_position R n B C i
      · have := i.isLt; omega
      · have := i.isLt; omega
      · intro a ha; have := hts i a ha; omega
      · intro b hb; have := hus i b hb; omega
    · exact D.operationGraph_corresponds f _ _ _ x y
        (fun i => .var (bindBlock_position R n B C i)) (bindBlock_below n B C x y hx hy hxy)

/-- Bind the same argument positions on both sides before comparing the continuation. -/
theorem withValues_corresponds {n : ℕ}
    (ts us : Fin n → (L.sum (functionSymbols ι)).Term ℕ) (R : ℕ → ℕ → Prop)
    (B C : ℕ) (φ ψ : AlphaFormula L) (h : ∀ i, TermRel R (ts i) (us i))
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) (hu : ∀ i a, a ∈ (us i).varFinset → a < C)
    (hp : Corresponds (bindBlock R n B C) φ ψ) :
    Corresponds R (D.withValues ts B φ) (D.withValues us C ψ) := by
  apply Corresponds.existsBlock
  apply Corresponds.binary .conj _ hp
  apply Corresponds.conjoin
  intro i
  apply D.termGraph_corresponds (ts i) (us i) (bindBlock R n B C)
    (B+i.val) (C+i.val) (B+n) (C+n)
  · exact (h i).congr (fun a ha b hb hab => bindBlock_below n B C a b (ht i a ha) (hu i b hb) hab)
  · exact bindBlock_position R n B C i
  · have := i.isLt; omega
  · have := i.isLt; omega
  · intro a ha; have := ht i a ha; omega
  · intro b hb; have := hu i b hb; omega

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
