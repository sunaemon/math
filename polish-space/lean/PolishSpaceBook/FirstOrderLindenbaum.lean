module

public import PolishSpaceBook.FirstOrderTheoryConsequence
public import Mathlib.Order.Zorn
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-!
# The Lindenbaum extension in the Henkin argument

Finite proof support proves consistency of a nonempty chain's union. Zorn then
provides a maximal consistent extension among sets of sentences. Deductive
closure and deciding every sentence follow from the syntactic deduction lemma.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

namespace AlphaFormula

@[simp] theorem fv_falsum : (falsum : AlphaFormula L).fv = ∅ := rfl

@[simp] theorem fv_binary (c : Connective) (φ ψ : AlphaFormula L) :
    (binary c φ ψ).fv = φ.fv ∪ ψ.fv := by
  induction φ, ψ using Quotient.inductionOn₂ with
  | _ φ ψ => rfl

@[simp] theorem fv_neg (φ : AlphaFormula L) : (neg φ).fv = φ.fv := by simp [neg]

end AlphaFormula

/-- The ambient set for Zorn consists of closed formulas, as in the book. -/
def Sentences (L : Language.{u,v}) : Set (AlphaFormula L) := {φ | φ.fv = ∅}

namespace Consistent

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Let $\mathcal P$ be the set of all consistent theories in the fixed language that extend $S$, ordered by
    inclusion. It is a set because the collection of sentences is a set. For a nonempty chain
    $\mathcal C\IncludedIn\mathcal P$, its union contains $S$. A derivation of falsity from this union would use a
    finite set of axioms, all belonging to one member of the chain, contradicting that member's consistency.
    Thus the union is an upper bound in $\mathcal P$. For the empty chain, take $S$ itself as an upper bound.
    Zorn's lemma gives a maximal element $T^*$.
-/
theorem sUnion {C : Set (Set (AlphaFormula L))} (hc : IsChain (· ⊆ ·) C) (hne : C.Nonempty)
    (hC : ∀ T ∈ C, Consistent T) : Consistent (⋃₀ C) := by
  rintro ⟨Γ, hΓ, hd⟩
  obtain ⟨T, hT, hsub⟩ := hc.directedOn.exists_mem_subset_of_finite_of_subset_sUnion
    hne Γ.finite_toSet hΓ
  exact hC T hT ⟨Γ, hsub, hd⟩

end Consistent

/-- Maximality is among consistent theories in the fixed language. -/
structure MaximallyConsistent (T : Set (AlphaFormula L)) : Prop where
  sentences : T ⊆ Sentences L
  consistent : Consistent T
  maximal : ∀ U, T ⊆ U → U ⊆ Sentences L → Consistent U → U ⊆ T

/-- This constructs the book's extension by the union-of-chains argument. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Lindenbaum extension
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Let $\mathcal P$ be the set of all consistent theories in the fixed language that extend $S$, ordered by
    inclusion. It is a set because the collection of sentences is a set. For a nonempty chain
    $\mathcal C\IncludedIn\mathcal P$, its union contains $S$. A derivation of falsity from this union would use a
    finite set of axioms, all belonging to one member of the chain, contradicting that member's consistency.
    Thus the union is an upper bound in $\mathcal P$. For the empty chain, take $S$ itself as an upper bound.
    Zorn's lemma gives a maximal element $T^*$.
-/
theorem exists_maximallyConsistent {S : Set (AlphaFormula L)}
    (hS : Consistent S) (hclosed : S ⊆ Sentences L) :
    ∃ T, S ⊆ T ∧ MaximallyConsistent T := by
  let P : Set (Set (AlphaFormula L)) := {T | S ⊆ T ∧ T ⊆ Sentences L ∧ Consistent T}
  have hchain : ∀ C ⊆ P, IsChain (· ⊆ ·) C → C.Nonempty → ∃ U ∈ P, ∀ V ∈ C, V ⊆ U := by
    intro C hCP hc hne
    refine ⟨⋃₀ C, ⟨?_, ?_, Consistent.sUnion hc hne (fun U hU => (hCP hU).2.2)⟩,
      fun U hU => Set.subset_sUnion_of_mem hU⟩
    · obtain ⟨U, hU⟩ := hne
      exact (hCP hU).1.trans (Set.subset_sUnion_of_mem hU)
    · intro φ hφ
      obtain ⟨U, hU, hφ⟩ := Set.mem_sUnion.mp hφ
      exact (hCP hU).2.1 hφ
  obtain ⟨T, hST, hT⟩ := zorn_subset_nonempty P hchain S ⟨Set.Subset.rfl, hclosed, hS⟩
  exact ⟨T, hST, hT.prop.2.1, hT.prop.2.2,
    fun U hTU hU hcons => hT.2 ⟨hST.trans hTU, hU, hcons⟩ hTU⟩

namespace MaximallyConsistent

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    If $T^*\vdash\sigma$ for a sentence $\sigma$, the \termuse{first-order deduction and consistency lemma} shows
    that adjoining this sentence preserves consistency; maximality therefore puts $\sigma$ in $T^*$.
    If instead $\sigma\notin T^*$, adjoining it is inconsistent by maximality. Deduction then gives
    $T^*\vdash\neg\sigma$, so deductive closure puts $\neg\sigma$ in $T^*$.
    Finally, the theory cannot contain both a sentence and its negation, since modus ponens would derive falsity.
    \end{proof}
-/
theorem mem_of_proves {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    {φ : AlphaFormula L} (hclosed : φ ∈ Sentences L) (hφ : ProvesFrom T φ) : φ ∈ T := by
  apply hT.maximal (insert φ T) (Set.subset_insert _ _) (Set.insert_subset hclosed hT.sentences)
    (hT.consistent.insert_of_proves hφ)
  exact Set.mem_insert _ _

theorem mem_iff_proves {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    {φ : AlphaFormula L} (hclosed : φ ∈ Sentences L) : φ ∈ T ↔ ProvesFrom T φ :=
  ⟨ProvesFrom.hyp, hT.mem_of_proves hclosed⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    If $T^*\vdash\sigma$ for a sentence $\sigma$, the \termuse{first-order deduction and consistency lemma} shows
    that adjoining this sentence preserves consistency; maximality therefore puts $\sigma$ in $T^*$.
    If instead $\sigma\notin T^*$, adjoining it is inconsistent by maximality. Deduction then gives
    $T^*\vdash\neg\sigma$, so deductive closure puts $\neg\sigma$ in $T^*$.
    Finally, the theory cannot contain both a sentence and its negation, since modus ponens would derive falsity.
    \end{proof}
-/
theorem neg_mem_iff {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    {φ : AlphaFormula L} (hclosed : φ ∈ Sentences L) : neg φ ∈ T ↔ φ ∉ T := by
  constructor
  · intro hn hp
    exact hT.consistent.not_both (ProvesFrom.hyp hp) (ProvesFrom.hyp hn)
  · intro hn
    have hi : ¬Consistent (insert φ T) := by
      intro hcons
      exact hn (hT.maximal _ (Set.subset_insert _ _) (Set.insert_subset hclosed hT.sentences)
        hcons (Set.mem_insert _ _))
    apply hT.mem_of_proves (by simpa [Sentences] using hclosed)
    exact not_consistent_insert_iff.mp hi

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    If $T^*\vdash\sigma$ for a sentence $\sigma$, the \termuse{first-order deduction and consistency lemma} shows
    that adjoining this sentence preserves consistency; maximality therefore puts $\sigma$ in $T^*$.
    If instead $\sigma\notin T^*$, adjoining it is inconsistent by maximality. Deduction then gives
    $T^*\vdash\neg\sigma$, so deductive closure puts $\neg\sigma$ in $T^*$.
    Finally, the theory cannot contain both a sentence and its negation, since modus ponens would derive falsity.
    \end{proof}
-/
theorem decides {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    {φ : AlphaFormula L} (hclosed : φ ∈ Sentences L) : φ ∈ T ∨ neg φ ∈ T := by
  classical
  by_cases hφ : φ ∈ T
  · exact Or.inl hφ
  · exact Or.inr ((hT.neg_mem_iff hclosed).mpr hφ)

theorem falsum_not_mem {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T) :
    falsum ∉ T := fun h => hT.consistent (ProvesFrom.hyp h)

end MaximallyConsistent
end PolishSpaceBook.NamedFirstOrder
