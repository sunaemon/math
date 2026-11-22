module

public import PolishSpaceBook.LambdaMetricPreimages
public import PolishSpaceBook.LambdaComputableNames

@[expose] public section

/-!
# Computable changes of representation

The identity map is realized by a uniform name translator. Bidirectional
translations preserve computable points, computable maps and semidecidable
subsets. Ordinary beta reduction after substitution of a closed numerical term justifies the point case.
-/
namespace PolishSpaceBook
open Set Function NamedLambda NamedLambda.AlphaTerm
universe u v

/-- A finite program translates names without changing the represented point. -/

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A representation $\delta$ of $X$ \termdefineas{computable reducibility of representations}{computably reduces} to
    another representation $\gamma$ of the same set if the identity on $X$ has a computable realizer from $\delta$ to
    $\gamma$. Thus one program converts every valid $\delta$-name into a $\gamma$-name of the same point. The
    representations are \termdefineas{computable equivalence of representations}{computably equivalent} if such translators
    exist in both directions. A point is \termforwardas{computable point in represented space}{computable} relative to a
    representation if it has an ordinary computable name.
-/
def ComputablyReduces {X : Type u} (δ₁ δ₂ : Representation X) : Prop :=
  HasComputableRealizer δ₁ δ₂ id

/-- Both directions have uniform finite-program translators. -/
def ComputablyEquivalent {X : Type u} (δ₁ δ₂ : Representation X) : Prop :=
  ComputablyReduces δ₁ δ₂ ∧ ComputablyReduces δ₂ δ₁

theorem ComputablyReduces.refl {X : Type u} (δ : Representation X) : ComputablyReduces δ δ :=
  hasComputableRealizer_id δ

theorem ComputablyReduces.trans {X : Type u} {δ₁ δ₂ δ₃ : Representation X}
    (h₁₂ : ComputablyReduces δ₁ δ₂) (h₂₃ : ComputablyReduces δ₂ δ₃) :
    ComputablyReduces δ₁ δ₃ := h₂₃.comp h₁₂

theorem ComputablyEquivalent.symm {X : Type u} {δ₁ δ₂ : Representation X}
    (h : ComputablyEquivalent δ₁ δ₂) : ComputablyEquivalent δ₂ δ₁ := ⟨h.2,h.1⟩

theorem ComputablyEquivalent.realizer_iff {X : Type u} {Y : Type v}
    {δX δX' : Representation X} {δY δY' : Representation Y}
    (hX : ComputablyEquivalent δX δX') (hY : ComputablyEquivalent δY δY') (f : X → Y) :
    HasComputableRealizer δX δY f ↔ HasComputableRealizer δX' δY' f := by
  constructor
  · intro hf
    simpa only [Function.comp_id, Function.id_comp] using hY.1.comp (hf.comp hX.2)
  · intro hf
    simpa only [Function.comp_id, Function.id_comp] using hY.2.comp (hf.comp hX.1)

/-- Computability of a point is existence of an ordinary computable name. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    This is the operational form of computable analysis. A real number is computable when it has a computable
    \termuse{Cauchy name}; a function is computable when there is a single lambda realizer which, given any name for an
    input as a function argument, produces a name for the output.
-/
def IsComputablePoint {X : Type u} (δ : Representation X) (x : X) : Prop :=
  ∃ p : δ.domain, (∃ A : AlphaTerm, NumericalComputes A p.val) ∧ δ.toFun p = x

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Let $A$ be a closed numerical lambda term computing an input name $p$, and let $P$ compute a translator $F$.
    Then the closed application $PA$ computes the name $F(p)$. Indeed, substitute $A$ for the free input variable
    in each finite computation of $P$: a query at $i$ becomes the ordinary beta reduction of
    $A\ChurchNumeral{i}$ to $\ChurchNumeral{p(i)}$. The substitution lemma in §{sec:lambda-input-composition}
    justifies this replacement under every term context. Thus computable points are preserved; the reverse translator
    proves the converse. For subsets, apply the computable pullback proposition to the identity in each direction.
    For a map, first translate a name from the new source representation to the old one, then apply the old realizer,
    and finally translate its output to the new target representation. Lambda composition gives one closed realizer
    for these three operations. The reverse translations give the converse.
-/
theorem ComputablyReduces.computablePoint {X : Type u} {δ₁ δ₂ : Representation X}
    (h : ComputablyReduces δ₁ δ₂) {x : X} (hx : IsComputablePoint δ₁ x) :
    IsComputablePoint δ₂ x := by
  obtain ⟨p,⟨A,hA⟩,hpx⟩ := hx
  obtain ⟨F,⟨c,hc⟩,hF⟩ := h
  exact ⟨F p,⟨app c A,hc.numerical_output p hA⟩,(hF p).trans hpx⟩

theorem ComputablyEquivalent.computablePoint_iff {X : Type u} {δ₁ δ₂ : Representation X}
    (h : ComputablyEquivalent δ₁ δ₂) (x : X) :
    IsComputablePoint δ₁ x ↔ IsComputablePoint δ₂ x :=
  ⟨h.1.computablePoint,h.2.computablePoint⟩

theorem ComputablyEquivalent.semidecidable_iff {X : Type u} {δ₁ δ₂ : Representation X}
    (h : ComputablyEquivalent δ₁ δ₂) (U : Set X) :
    SemidecidableFromNames δ₁ U ↔ SemidecidableFromNames δ₂ U := by
  constructor
  · intro hU
    simpa only [Set.preimage_id] using hU.preimage h.2
  · intro hU
    simpa only [Set.preimage_id] using hU.preimage h.1

/-- The three invariance conclusions, for both source and target representations. -/

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Invariance under computable change of representation
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Together with invariance under computable change of representation, the criterion gives an explicit test for
    independence from the dense sequence. It also preserves effectively open sets when both sequences give computable metric
    presentations. If the metric changes as well, one must instead verify computability of the identity in both directions
    between the two presentations. The inverse-image criterion can be used for that purpose. Equality of the induced
    topologies supplies continuity, but does not supply the required uniform enumerations of basic-ball preimages.
-/
theorem ComputablyEquivalent.invariance {X : Type u} {Y : Type v}
    {δX δX' : Representation X} {δY δY' : Representation Y}
    (hX : ComputablyEquivalent δX δX') (hY : ComputablyEquivalent δY δY') :
    (∀ x, IsComputablePoint δX x ↔ IsComputablePoint δX' x) ∧
    (∀ U, SemidecidableFromNames δX U ↔ SemidecidableFromNames δX' U) ∧
    (∀ f : X → Y, HasComputableRealizer δX δY f ↔ HasComputableRealizer δX' δY' f) :=
  ⟨hX.computablePoint_iff, hX.semidecidable_iff, hX.realizer_iff hY⟩

end PolishSpaceBook
