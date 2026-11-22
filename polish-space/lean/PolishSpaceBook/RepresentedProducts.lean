module

public import PolishSpaceBook.ComputablePolishSpacesTTE

@[expose] public section

/-! # Pointwise pairing of names and product representations -/
namespace PolishSpaceBook
universe u v
variable {X : Type u} {Y : Type v}

/-- Pointwise pairing is a bijective encoding of two names by one name. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Pair names pointwise:
    $$\NamePair{p}{q}(n):=\NatPair{p(n)}{q(n)}.$$
    Write $\NameProjection{1}{r}$ and $\NameProjection{2}{r}$ for the names obtained by applying the first and second numerical inverse projections at every coordinate of $r$. The numerical inverse identities give
    $$\NameProjection{1}{\NamePair{p}{q}}=p,\qquad
    \NameProjection{2}{\NamePair{p}{q}}=q,\qquad
    \NamePair{\NameProjection{1}{r}}{\NameProjection{2}{r}}=r.$$
    Thus this codes every pair of names by exactly one name.
-/
def typeTwoPairName (p q : ℕ → ℕ) : ℕ → ℕ := fun n => Nat.pair (p n) (q n)
def typeTwoLeftName (p : ℕ → ℕ) : ℕ → ℕ := fun n => (p n).unpair.1
def typeTwoRightName (p : ℕ → ℕ) : ℕ → ℕ := fun n => (p n).unpair.2

@[simp] theorem typeTwoLeft_pair (p q : ℕ → ℕ) : typeTwoLeftName (typeTwoPairName p q) = p := by
  funext n; simp [typeTwoLeftName, typeTwoPairName]
@[simp] theorem typeTwoRight_pair (p q : ℕ → ℕ) : typeTwoRightName (typeTwoPairName p q) = q := by
  funext n; simp [typeTwoRightName, typeTwoPairName]
@[simp] theorem typeTwoPair_projections (p : ℕ → ℕ) :
    typeTwoPairName (typeTwoLeftName p) (typeTwoRightName p) = p := by
  funext n; exact Nat.pair_unpair (p n)

/-- The actual product representation, including its domain and surjectivity. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    **Products.** For represented spaces $\mathbf X=(X,\delta_X)$ and $\mathbf Y=(Y,\delta_Y)$, define the product representation by
    $$\delta_{X\times Y}(r):=
    \bigl(\delta_X(\NameProjection{1}{r}),\delta_Y(\NameProjection{2}{r})\bigr),$$
    with domain
    $$\bigl\{r\in\BaireSpace:\NameProjection{1}{r}\in\DomainOf{\delta_X},\;
    \NameProjection{2}{r}\in\DomainOf{\delta_Y}\bigr\}.$$
    The inverse identities show that its valid names are exactly the pairs of valid component names. In particular,
    $$\delta_{X\times Y}(\NamePair{p}{q})=(\delta_X(p),\delta_Y(q)).$$
    For any point of $X\times Y$, choose names of its two coordinates and pair them. This proves surjectivity, so the construction is indeed a representation.
-/
def typeTwoProductRepresentation (δX : Representation X) (δY : Representation Y) :
    Representation (X × Y) where
  domain := {p | typeTwoLeftName p ∈ δX.domain ∧ typeTwoRightName p ∈ δY.domain}
  toFun p := (δX.toFun ⟨typeTwoLeftName p.val, p.property.1⟩,
    δY.toFun ⟨typeTwoRightName p.val, p.property.2⟩)
  surjective := by
    rintro ⟨x, y⟩
    obtain ⟨p, hp⟩ := δX.surjective x
    obtain ⟨q, hq⟩ := δY.surjective y
    refine ⟨⟨typeTwoPairName p.val q.val, by simp⟩, ?_⟩
    apply Prod.ext
    · simpa using hp
    · simpa using hq

end PolishSpaceBook
