module

public import PolishSpaceBook.BorelExpressionCodeComparison
public import PolishSpaceBook.BorelExpressionCompleteness

@[expose] public section

/-! # Open-base expansions, the empty case, and worked Borel codes -/

namespace PolishSpaceBook
open Set TopologicalSpace
namespace BorelExpression

/-- A nonempty open set has a nonempty family of basis sets, which can be
surjectively enumerated even when the family is finite. -/
theorem nonempty_open_eq_iUnion_basis {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hU : IsTopologicalBasis (range U))
    {A : Set X} (hA : IsOpen A) (hne : A.Nonempty) :
    ∃ i : ℕ → ℕ, (⋃ n, U (i n)) = A := by
  classical
  let S : Set ℕ := {n | U n ⊆ A}
  have hn : Nonempty S := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨V, ⟨n, rfl⟩, _, hv⟩ := hU.exists_subset_of_mem_open hx hA
    exact ⟨⟨n, hv⟩⟩
  let e := enumerateChildren S hn
  refine ⟨fun n => (e n).1, ?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, hx⟩
    exact (e n).2 hx
  · intro hx
    obtain ⟨V, ⟨k, rfl⟩, hxk, hk⟩ := hU.exists_subset_of_mem_open hx hA
    obtain ⟨n, he⟩ := enumerateChildren_surjective S hn ⟨k, hk⟩
    exact ⟨n, by simpa only [e, he] using hxk⟩

private theorem basis_union_eq_univ {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hU : IsTopologicalBasis (range U)) : (⋃ n, U n) = univ := by
  rw [← sUnion_range]
  exact hU.sUnion_eq

/-- Empty is coded by complementing the union of the whole basis, never by an empty union node. -/
theorem hasCode_empty_of_basis {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hU : IsTopologicalBasis (range U)) : HasCode U ∅ := by
  let d := BorelCode.compl (BorelCode.union BorelCode.leaf)
  refine ⟨d.expression, d.valid_expression, ?_⟩
  rw [d.denotes_expression U]
  simp only [d, BorelCode.decode, basis_union_eq_univ U hU, compl_univ]

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    For example, let $F\IncludedIn X$ be closed. If $F=X$, use $\BorelUnionCode{\Sequence{\BorelLeafCode{n}}{n\in\omega}}$.
    Otherwise its open complement is nonempty. Enumerate the basis sets it contains, with repetitions if necessary, as
    $$\SetDifference{X}{F}=\bigcup_n U_{i_n}.$$
    Then $\BorelComplementCode{\BorelUnionCode{\Sequence{\BorelLeafCode{i_n}}{n\in\omega}}}$ codes $F$.
    The distinction matters because the union constructor takes a sequence indexed by $\omega$; it has no empty input.
-/
/-- The whole-space closed set uses a union of the entire basis; every other
closed set uses the complement of a nonempty open-base expansion. -/
theorem hasCode_closed_of_basis {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hU : IsTopologicalBasis (range U))
    {F : Set X} (hF : IsClosed F) : HasCode U F := by
  classical
  by_cases h : F = univ
  · subst F
    let d := BorelCode.union BorelCode.leaf
    exact ⟨d.expression, d.valid_expression,
      (d.denotes_expression U).trans (basis_union_eq_univ U hU)⟩
  · obtain ⟨i, hi⟩ := nonempty_open_eq_iUnion_basis U hU hF.isOpen_compl (nonempty_compl.mpr h)
    let d := BorelCode.compl (BorelCode.union (fun n => BorelCode.leaf (i n)))
    refine ⟨d.expression, d.valid_expression, ?_⟩
    rw [d.denotes_expression U]
    simp only [d, BorelCode.decode, hi, compl_compl]

/-- Intersections use the existing complement and union constructors. -/
theorem HasCode.iInter {X : Type*} {U : ℕ → Set X} {A : ℕ → Set X}
    (h : ∀ n, HasCode U (A n)) : HasCode U (⋂ n, A n) := by
  simpa only [compl_iUnion, compl_compl] using (HasCode.iUnion (fun n => (h n).compl)).compl

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    If $A=\bigcap_m\bigcup_n C_{m,n}$ is an $\FsigmaDelta$ set, choose codes $c_{m,n}$ for the closed sets $C_{m,n}$.
    Put
    $$
    \begin{aligned}
    d_m&:=\BorelUnionCode{\Sequence{c_{m,n}}{n\in\omega}},\\
    e&:=\BorelComplementCode{\BorelUnionCode{\Sequence{\BorelComplementCode{d_m}}{m\in\omega}}}.
    \end{aligned}
    $$
    Then $A_{d_m}=\bigcup_n C_{m,n}$ and $A_e=A$, directly by the three evaluation rules.
-/
/-- The worked F-sigma-delta example uses exactly the three layers of the displayed formula. -/
theorem hasCode_iInter_iUnion_closed {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hU : IsTopologicalBasis (range U))
    (C : ℕ → ℕ → Set X) (hC : ∀ m n, IsClosed (C m n)) :
    HasCode U (⋂ m, ⋃ n, C m n) :=
  HasCode.iInter fun m => HasCode.iUnion fun n => hasCode_closed_of_basis U hU (hC m n)

end BorelExpression
end PolishSpaceBook
