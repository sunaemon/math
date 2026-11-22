module

public import PolishSpaceBook.FirstOrderFunctionGraphInstances

@[expose] public section

/-!
# Recursive graphs for nested function terms

At each application, existentially bind one fresh value for each argument.
Child graphs can reuse the next block because their internal binders have
separate scopes. The output and original parameters lie below the current block.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- An old-language graph for a term, with output `x` and fresh names starting at `B`. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    For an old function symbol $f$, let $\FirstOrderOperationGraph{f}{\vec{z}}{y}$ be the equality $y=f(\vec{z})$.
    For a new symbol, let it be $\theta_f(\vec{z},y)$, obtained from its defining graph by simultaneous substitution
    at every input and the output. Define the old-language formula $\FirstOrderTermGraph{t}{y}{B}$ recursively.
    For a variable,
    $$\FirstOrderTermGraph{v_i}{y}{B}\quad:\equiv\quad y=v_i.$$
    For $t=f(t_0,\ldots,t_{n-1})$, put $z_i:=v_{B+i}$ and set
    $$\begin{aligned}
    \FirstOrderTermGraph{t}{y}{B}\quad:\equiv\quad
    \exists z_{n-1}\cdots\exists z_0\,\Bigl(
    &\bigwedge_{i<n}\FirstOrderTermGraph{t_i}{z_i}{B+n}\\
    &{}\land\FirstOrderOperationGraph{f}{\vec{z}}{y}\Bigr).
    \end{aligned}$$
    The conjunction over an empty family is true, and an empty block of quantifiers does nothing.
    Thus the rule includes constants. Each child graph starts its internal names at $B+n$; those names can be reused
    in different child graphs because their quantifiers have separate scopes.
-/
def termGraph : (L.sum (functionSymbols ι)).Term ℕ → ℕ → ℕ → AlphaFormula L
  | .var y, x, _ => equal (.var x) (.var y)
  | .func (l := n) f ts, x, B => existsBlock n B
      (binary .conj (conjoin n (fun i => termGraph (ts i) (B+i.val) (B+n)))
        (D.operationGraph f (fun i => .var (B+i.val)) x))

/-- All temporary argument values are bound inside the graph. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the free-variable assertion, each child contributes only its original variables and its output $z_i$.
    The operation constraint contributes only the argument variables and $y$; the defining graph has no other free
    parameters. Existential quantification removes every $z_i$. Induction therefore gives the displayed inclusion.
-/
theorem fv_termGraph_subset (t : (L.sum (functionSymbols ι)).Term ℕ) (x B : ℕ) :
    (D.termGraph t x B).fv ⊆ insert x t.varFinset := by
  induction t generalizing x B with
  | var y => change ({x} ∪ {y} : Finset ℕ) ⊆ insert x {y}; simp
  | @func n f ts ih =>
    rw [termGraph, fv_existsBlock, fv_binary, fv_conjoin]
    intro y hy
    obtain ⟨hy, hout⟩ := Finset.mem_sdiff.mp hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hy
      rcases Finset.mem_insert.mp (ih i _ _ hi) with he | hi
      · exact False.elim (hout (he ▸ Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · rcases Finset.mem_insert.mp (D.fv_operationGraph_subset f _ x hy) with he | hy
      · exact Finset.mem_insert.mpr (Or.inl he)
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hy
        have he : y = B+i.val := by simpa using hi
        exact False.elim (hout (he ▸ Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩))

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]

/-- The recursively built graph characterizes the term's value with all parameters fixed. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Recursive graphs of terms
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Induct on the term. The variable case is equality. For an application, the induction hypothesis applies to each
    child because its output index is below $B+n$, as are all original variables. A witness assignment changes only
    $z_0,\ldots,z_{n-1}$. Hence it leaves the values of the original terms and of $y$ unchanged. The child graphs
    force each $z_i$ to equal the value of $t_i$ under the original assignment. For an old operation, the remaining
    constraint is its ordinary value equation. For a new operation, its defining axiom and uniqueness identify its
    graph with exactly that value equation. This proves the forward implication. Conversely, assign each $z_i$ the
    value of $t_i$. The child graphs then hold, and the assumed output equation gives the remaining constraint.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The following recursion handles arbitrary nesting of function terms. Enumerate variable names as
    $v_0,v_1,\ldots$. Choose $B$ larger than the index of every variable in a term $t$ and of its output variable $y$.
-/
theorem realize_termGraph (t : (L.sum (functionSymbols ι)).Term ℕ) (x B : ℕ)
    (hx : x < B) (ht : ∀ y ∈ t.varFinset, y < B) (s : ℕ → M)
    (hu : ∀ k (g : ι k) (s : ℕ → M), ∃! b, (D.graph g).Realize (Function.update s k b))
    (ha : ∀ k (g : ι k) (s : ℕ → M), (D.definingAxiom g).Realize s) :
    (D.termGraph t x B).Realize s ↔ s x = t.realize s := by
  induction t generalizing x B s with
  | var y => rfl
  | @func n f ts ih =>
    have hti (i : Fin n) (y : ℕ) (hy : y ∈ (ts i).varFinset) : y < B :=
      ht y (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hy⟩)
    have hout : x ∉ temporaryNames n B := by rw [mem_temporaryNames_iff]; omega
    have hchild (i : Fin n) (s' : ℕ → M) :
        (D.termGraph (ts i) (B+i.val) (B+n)).Realize s' ↔ s' (B+i.val) = (ts i).realize s' :=
      ih i _ _ (by have := i.isLt; omega) (fun y hy => by have := hti i y hy; omega) s'
    have hlocal (s' : ℕ → M) (he : ∀ y, y ∉ temporaryNames n B → s' y = s y) (i : Fin n) :
        (ts i).realize s' = (ts i).realize s := by
      apply term_realize_congr
      intro y hy; apply he; rw [mem_temporaryNames_iff]; have := hti i y hy; omega
    rw [termGraph, realize_existsBlock]
    constructor
    · rintro ⟨s',he,h⟩
      obtain ⟨hc,hf⟩ := (realize_conj _ _ _).mp h
      have hc' (i : Fin n) := (hchild i s').mp ((realize_conjoin _ _ _).mp hc i)
      have hf' := (D.realize_operationGraph f _ x s' hu ha).mp hf
      simpa only [Term.realize_var, hc', hlocal s' he, he x hout, Term.realize_func] using hf'
    · intro h
      let s' := blockAssignment s B (fun i => (ts i).realize s)
      have he : ∀ y, y ∉ temporaryNames n B → s' y = s y := blockAssignment_outside s B _
      refine ⟨s', he, (realize_conj _ _ _).mpr ⟨?_, ?_⟩⟩
      · apply (realize_conjoin _ _ _).mpr
        intro i
        apply (hchild i s').mpr
        rw [hlocal s' he i]
        exact blockAssignment_inside s B _ i
      · apply (D.realize_operationGraph f _ x s' hu ha).mpr
        rw [he x hout]
        simpa only [Term.realize_var, s', blockAssignment_inside, Term.realize_func] using h

end Semantics
end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
