module

public import PolishSpaceBook.CauchyNamesPolishRepresentations

@[expose] public section

/-! # The identity representation of Baire space -/
namespace PolishSpaceBook

/-- A Baire-space sequence is its own name. -/
def baireIdentityRepresentation : Representation (ℕ → ℕ) where
  domain := Set.univ
  toFun := Subtype.val
  surjective := fun p => ⟨⟨p,Set.mem_univ p⟩,rfl⟩

end PolishSpaceBook
