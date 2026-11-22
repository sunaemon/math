module

public import PolishSpaceBook.ComputablePolishSpacesTTE

@[expose] public section

/-! # Restricted representations, independent of any computation model -/
namespace PolishSpaceBook
open Set
universe u
variable {X : Type u}

def representationRestrictionDomain (δ : Representation X) (A : Set X) : Set (ℕ → ℕ) :=
  {p | ∃ hp : p ∈ δ.domain, δ.toFun ⟨p, hp⟩ ∈ A}

def restrictionOriginalName (δ : Representation X) (A : Set X)
    (p : representationRestrictionDomain δ A) : δ.domain :=
  ⟨p.val, p.property.choose⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    **Subspaces.** If $A\IncludedIn X$, restrict the allowed names to those representing points of $A$ and put
    $$\delta_A:=\restrict{\delta_X}{\delta_X^{-1}(A)},$$
    regarding its values as elements of $A$. Every point still has a name, since the original representation is surjective. This defines the represented subspace without requiring an algorithm to decide which names belong to its domain.
-/
def restrictedRepresentation (δ : Representation X) (A : Set X) : Representation A where
  domain := representationRestrictionDomain δ A
  toFun p := ⟨δ.toFun (restrictionOriginalName δ A p), p.property.choose_spec⟩
  surjective := by
    intro x
    obtain ⟨p, hp⟩ := δ.surjective x.val
    refine ⟨⟨p.val, p.property, hp ▸ x.property⟩, ?_⟩
    exact Subtype.ext hp

end PolishSpaceBook
