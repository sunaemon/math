module

public import PolishSpaceBook.SetTheoryAbstractRecursiveSolutions

@[expose] public section

/-! # Extending an internal membership-recursive solution by one value -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

/-- Add the next value at a point all of whose members are already in the
transitive domain. Both the enlarged domain and graph are actual model sets. -/
theorem recursiveSolution_extend (hM : M ⊨ fullZFCTheory) {R : M → M → M → Prop}
    {U f a r b : M} (hf : IsRecursiveSolution R U f) (ha : ¬member a U)
    (hsub : ∀ x : M, member x a → member x U) (hr : IsRestriction f a r) (hb : R a r b) :
    ∃ B g : M, (∀ x : M, member x B ↔ member x U ∨ x = a) ∧
      IsRecursiveSolution R B g ∧
      (∀ x y : M, GraphApplication g x y ↔ GraphApplication f x y ∨ (x = a ∧ y = b)) := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hp := hM.realize_of_mem _ ZFCAxiom.pairing
  obtain ⟨s, hs, _⟩ := existsUnique_pair hext hp a a
  obtain ⟨B, hBU, _⟩ := existsUnique_binaryUnion hext hp (hM.realize_of_mem _ ZFCAxiom.union) U s
  have hB (x : M) : member x B ↔ member x U ∨ x = a := by
    rw [hBU x, hs x, or_self]
  obtain ⟨g, hg⟩ := exists_graphInsert hM f a b
  have happ := graphApplication_insert hext hp hg
  have hgraph := isGraphOn_insert hM hf.2.1 ha hB hg
  have htrans : IsTransitiveObject B := by
    intro x hx y hy
    apply (hB y).mpr
    rcases (hB x).mp hx with hx | rfl
    · exact Or.inl (hf.1 x hx y hy)
    · exact Or.inl (hsub y hy)
  have preserve_restriction {x t : M} (ht : IsRestriction f x t) (hax : ¬member a x) :
      IsRestriction g x t := by
    refine ⟨ht.1, ?_⟩
    intro y z
    rw [ht.2 y z, happ y z]
    constructor
    · rintro ⟨hy, hz⟩
      exact ⟨hy, Or.inl hz⟩
    · rintro ⟨hy, hz | ⟨rfl, _⟩⟩
      · exact ⟨hy, hz⟩
      · exact (hax hy).elim
  refine ⟨B, g, hB, ⟨htrans, hgraph, ?_⟩, happ⟩
  intro x hx
  rcases (hB x).mp hx with hxU | hxa
  · obtain ⟨t, c, ht, hxc, hc⟩ := hf.2.2 x hxU
    have hax : ¬member a x := fun hax => ha (hf.1 x hxU a hax)
    exact ⟨t, c, preserve_restriction ht hax, (happ x c).mpr (Or.inl hxc), hc⟩
  · subst x
    have haa : ¬member a a := fun haa => ha (hsub a haa)
    exact ⟨r, b, preserve_restriction hr haa, (happ a b).mpr (Or.inr ⟨rfl, rfl⟩), hb⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
