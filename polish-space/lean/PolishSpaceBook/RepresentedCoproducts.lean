module

public import PolishSpaceBook.ComputablePolishSpacesTTE

@[expose] public section

/-! # Tagged names and coproduct representations -/
namespace PolishSpaceBook
universe u v
variable {X : Type u} {Y : Type v}

def typeTwoTagName (tag : ℕ) (p : ℕ → ℕ) : ℕ → ℕ
  | 0 => tag
  | n + 1 => p n

def typeTwoTailName (p : ℕ → ℕ) : ℕ → ℕ := fun n => p (n + 1)

@[simp] theorem typeTwoTail_tag (tag : ℕ) (p : ℕ → ℕ) :
    typeTwoTailName (typeTwoTagName tag p) = p := rfl

def coproductNameDomain (δX : Representation X) (δY : Representation Y) : Set (ℕ → ℕ) :=
  {p | (p 0 = 0 ∧ typeTwoTailName p ∈ δX.domain) ∨
    (p 0 = 1 ∧ typeTwoTailName p ∈ δY.domain)}

theorem coproductName_left (δX : Representation X) (δY : Representation Y)
    (p : coproductNameDomain δX δY) (hp : p.val 0 = 0) : typeTwoTailName p.val ∈ δX.domain := by
  rcases p.property with h | h
  · exact h.2
  · omega

theorem coproductName_right (δX : Representation X) (δY : Representation Y)
    (p : coproductNameDomain δX δY) (hp : p.val 0 ≠ 0) :
    p.val 0 = 1 ∧ typeTwoTailName p.val ∈ δY.domain := by
  rcases p.property with h | h
  · exact (hp h.1).elim
  · exact h

def coproductNameValue (δX : Representation X) (δY : Representation Y)
    (p : coproductNameDomain δX δY) : X ⊕ Y :=
  if hp : p.val 0 = 0 then
    Sum.inl (δX.toFun ⟨typeTwoTailName p.val, coproductName_left δX δY p hp⟩)
  else Sum.inr (δY.toFun ⟨typeTwoTailName p.val, (coproductName_right δX δY p hp).2⟩)

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    **Coproducts.** The coproduct $X\disjointUnion Y$ is represented by tagging names:
    $$
    \delta_{X\disjointUnion Y}(0\concat p)=\iota_X(\delta_X(p)),
    \qquad
    \delta_{X\disjointUnion Y}(1\concat q)=\iota_Y(\delta_Y(q)).
    $$
    A valid name has tag zero with a valid name for the left summand as its tail, or tag one with a valid name for the right summand as its tail. No other tags are valid. Surjectivity follows by taking a name in the relevant summand and prefixing its tag.
-/
def typeTwoCoproductRepresentation (δX : Representation X) (δY : Representation Y) :
    Representation (X ⊕ Y) where
  domain := coproductNameDomain δX δY
  toFun := coproductNameValue δX δY
  surjective := by
    intro x
    cases x with
    | inl x =>
      obtain ⟨p, hp⟩ := δX.surjective x
      refine ⟨⟨typeTwoTagName 0 p.val, Or.inl ⟨rfl, p.property⟩⟩, ?_⟩
      simpa [coproductNameValue, typeTwoTagName] using congrArg (Sum.inl (β := Y)) hp
    | inr y =>
      obtain ⟨p, hp⟩ := δY.surjective y
      refine ⟨⟨typeTwoTagName 1 p.val, Or.inr ⟨rfl, p.property⟩⟩, ?_⟩
      simpa [coproductNameValue, typeTwoTagName] using congrArg (Sum.inr (α := X)) hp

end PolishSpaceBook
