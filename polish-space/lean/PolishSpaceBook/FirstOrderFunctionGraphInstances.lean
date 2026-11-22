module

public import PolishSpaceBook.FirstOrderFiniteBinders

@[expose] public section

/-!
# Graph constraints at arbitrary arguments

Old operations use equality with their function term. Defined operations use
their old-language graph, instantiated simultaneously at all inputs and output.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- One operation, after all its arguments have old-language names. -/
def operationGraph {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n)
    (ts : Fin n → L.Term ℕ) (x : ℕ) : AlphaFormula L :=
  match f with
  | Sum.inl g => equal (.var x) (.func g ts)
  | Sum.inr g => (D.graph g).simultaneous (Fin.snoc (α := fun _ => L.Term ℕ) ts (.var x))

theorem fv_operationGraph_subset {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n)
    (ts : Fin n → L.Term ℕ) (x : ℕ) :
    (D.operationGraph f ts x).fv ⊆ insert x (argumentVars ts) := by
  rcases f with f | f
  · change {x} ∪ argumentVars ts ⊆ insert x (argumentVars ts)
    simp
  · have h := fv_simultaneous_subset (D.graph f) (Fin.snoc (α := fun _ => L.Term ℕ) ts (.var x))
    have hf : (D.graph f).fv \ Finset.range (n+1) = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (D.freeVars f)
    rw [hf, Finset.empty_union] at h
    intro y hy
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (h hy)
    cases i using Fin.lastCases with
    | last =>
      have hyx : y = x := by simpa using hi
      exact Finset.mem_insert.mpr (Or.inl hyx)
    | cast i =>
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using hi⟩

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]

/-- A graph constraint determines exactly the value of its operation. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To eliminate a chosen occurrence of $f(\vec{t})$, replace it by a variable fresh for the original formula,
    rename bound variables to avoid capture, and apply this equivalence with the graph at $\vec{t}$. For example,
    one truth-preserving elimination of
    $$
    P(f(x),z)
    $$
    is
    $$
    \exists u\,\bigl(\theta(x,u) \land P(u,z)\bigr),
    $$
    and
    $$
    f(x)=g(z)
    $$
    translates to
    $$
    \exists u\,\exists v\,\bigl(\theta_f(x,u) \land \theta_g(z,v) \land u=v\bigr).
    $$
    Unique existence makes this translation independent of the chosen fresh witnesses, so the expanded notation has the same
    truth conditions as its old-language expansion.
-/
theorem realize_operationGraph {n : ℕ} (f : (L.sum (functionSymbols ι)).Functions n)
    (ts : Fin n → L.Term ℕ) (x : ℕ) (s : ℕ → M)
    (hu : ∀ k (g : ι k) (s : ℕ → M), ∃! b, (D.graph g).Realize (Function.update s k b))
    (ha : ∀ k (g : ι k) (s : ℕ → M), (D.definingAxiom g).Realize s) :
    (D.operationGraph f ts x).Realize s ↔
      s x = Structure.funMap (L := L.sum (functionSymbols ι)) f (fun i => (ts i).realize s) := by
  rcases f with f | f
  · change s x = Structure.funMap (L := L) f (fun i => (ts i).realize s) ↔ _
    rw [← (inclusion (L := L) (ι := ι)).map_onFunction f (fun i => (ts i).realize s)]
    rfl
  · rw [operationGraph, realize_simultaneous]
    let a : ℕ → M := fun i => if h : i < n+1 then (Fin.snoc (α := fun _ => L.Term ℕ) ts (.var x) ⟨i,h⟩).realize s else s i
    change (D.graph f).Realize a ↔ _
    have hg := D.graph_iff_function_value f a (hu n f a) (ha n f) (a n)
    simp only [Function.update_eq_self] at hg
    rw [hg]
    have hav (i : Fin (n+1)) : a i.val = (Fin.snoc (α := fun _ => L.Term ℕ) ts (.var x) i).realize s := by
      simp only [a, dite_eq_left i.isLt]
    have ho : a n = s x := by simpa using hav (Fin.last n)
    have hi (i : Fin n) : a i.val = (ts i).realize s := by simpa using hav i.castSucc
    change a n = Structure.funMap (L := L.sum (functionSymbols ι)) (Sum.inr f) (fun i => a i.val) ↔ _
    simp only [ho, hi]

end Semantics
end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
