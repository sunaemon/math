module

public import PolishSpaceBook.ComputablePolishSpacesTTE
public import Mathlib.Topology.Order

@[expose] public section

namespace PolishSpaceBook
open Set

/-- Mathlib models the Sierpiński space by propositions with its standard topology. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    **\termdefineas{Sierpinski space}{Sierpi\'nski space} and open sets.** Give $\mathbb S=\{\bot,\top\}$ the topology $\{\varnothing,\{\top\},\mathbb S\}$ and the total representation
    $$
    \delta_{\mathbb S}(p)=\top \iff \exists n\; p(n)\ne 0,
    \qquad
    \delta_{\mathbb S}(p)=\bot \iff \forall n\; p(n)=0.
    $$
    The constant zero and constant one names show surjectivity. For $U\IncludedIn X$, let $\chi_U(x)=\top$ exactly when $x\in U$. Membership in $U$ is semidecidable from names if one closed lambda program, run with a name $p$ and numerical input zero, has a numeral output exactly when $\delta_X(p)\in U$. This requirement applies to every valid name; no behavior is prescribed outside $\DomainOf{\delta_X}$.
-/
def sierpinskiRepresentation : Representation Prop where
  domain := univ
  toFun p := ∃ n, p.val n ≠ 0
  surjective := by
    classical
    intro P
    by_cases h : P
    · refine ⟨⟨fun _ => 1, mem_univ _⟩, propext ?_⟩
      simp [h]
    · refine ⟨⟨fun _ => 0, mem_univ _⟩, propext ?_⟩
      simp [h]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The representation of $\mathbb S$ is continuous: the preimage of $\{\top\}$ is the union, over all coordinates, of the open sets where that coordinate is nonzero. A semidecidable subset therefore has an open preimage in the domain of names. When the representation is a quotient map, the subset itself is open. We call a represented subset effectively open when its characteristic map into $\mathbb S$ is computable. At the topological level, $U$ is open exactly when $\chi_U$ is continuous, since $\{\top\}$ is the only nontrivial open subset of $\mathbb S$.
-/
theorem sierpinskiRepresentation_continuous : sierpinskiRepresentation.IsContinuous := by
  apply continuous_Prop.mpr
  change IsOpen {p : sierpinskiRepresentation.domain | ∃ n, p.val n ≠ 0}
  have he : {p : sierpinskiRepresentation.domain | ∃ n, p.val n ≠ 0} =
      ⋃ n, {p : sierpinskiRepresentation.domain | p.val n ≠ 0} := by
    ext p
    simp
  rw [he]
  exact isOpen_iUnion fun n => isOpen_ne.preimage
    ((continuous_apply n).comp continuous_subtype_val)

end PolishSpaceBook
