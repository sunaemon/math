module

public import PolishSpaceBook.LambdaHKLCommonRight

@[expose] public section

/-!
# The contradiction inside HKL generic-pair splitting

A relative pair condition in the actual kernel supplies auxiliary-related,
E-inequivalent points meeting every decision and local projection test used
by the common-right construction. Therefore no kernel rectangle makes all
of its generic pairs E-equivalent. The step from one equivalent generic pair
to a rectangle forcing equivalence is supplied by `LambdaBorelTruth`.
The full embedding is assembled in `HKLPolishTransport`.
-/

namespace PolishSpaceBook.LambdaTree
open Set

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Hereditary failure now gives a nonempty analytic pair condition
    $$R=\{(x,y)\in U^2:x\mathrel{\EffectiveClosureER{E}}y\ \land\ x\mathrel{\not E}y\}.$$
    Restrict the family $\mathcal F$ to conditions below $U$. Its members remain dense there.
    The \termuse{generic coordinates of an analytic pair condition} proposition in §{sec:edst-generic-conditions}
    applied to $R$ gives an actual pair in $R$ whose coordinates meet every one of these individual tests.
    This pair contradicts the common-right-point claim.
-/
/-- Choose actual inequivalent auxiliary-related points, with all countably
many genericity tests required by the HKL common-right construction. -/
theorem parameter_hkl_inequivalent_generics (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (A : (parameterAnalyticCatalog ε).Condition)
    (hAH : A.val.val ⊆ equivalenceGapKernel E (invariantSetoid ε E))
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) :
    ∃ x ∈ A.val.val, ∃ y ∈ A.val.val,
      (invariantSetoid ε E).r x y ∧ ¬ E.r x y ∧
      ParameterDecisionGeneric ε x ∧ ParameterDecisionGeneric ε y ∧
      ParameterLeftGeneric ε E x (parameterHKLWitnessTests ε E J) ∧
      ParameterLeftGeneric ε E y (parameterHKLWitnessTests ε E J) := by
  let C := parameterAnalyticCatalog ε
  let F := parameterHKLWitnessTests ε E J
  let T := parameterHKLPointTests ε E F
  have hTc : T.Countable := parameterHKLPointTests_countable E F
    (parameterHKLWitnessTests_countable J hJc)
  have hTd : ∀ D ∈ T, IsCoinitial D := parameterHKLPointTests_dense E hE F
    (parameterHKLWitnessTests_dense hE J hJd)
  let localTest (D : Set C.Condition) : Set (CatalogBelow C A) := {P | P.val ∈ D}
  have hld : ∀ D ∈ localTest '' T, IsCoinitial D := by
    rintro _ ⟨D, hD, rfl⟩ P
    obtain ⟨Q, hQD, hQP⟩ := hTd D hD P.val
    exact ⟨⟨Q, hQP.trans P.property⟩, hQD, hQP⟩
  let R := (({p | (invariantSetoid ε E).r (leftBaire p) (rightBaire p)} ∩
    {p | ¬ E.r (leftBaire p) (rightBaire p)}) ∩ leftBaire ⁻¹' A.val.val) ∩
    rightBaire ⁻¹' A.val.val
  have hR : Projected ε R :=
    (((projected_invariantSetoid ε E hE).inter hneE).inter
      (parameterCondition_projected ε A).leftPreimage).inter
      (parameterCondition_projected ε A).rightPreimage
  have hn : R.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hkl_hereditary ε E hE hneE
      (parameterCondition_projected ε A) A.val.property.2 hAH
    refine ⟨pairBaire x y, ?_⟩
    simpa only [R, mem_inter_iff, mem_ofPred_eq, mem_preimage, leftBaire_pair, rightBaire_pair]
      using And.intro (And.intro (And.intro hxy hne) hx) hy
  let P := parameterCondition ε R hR hn
  have hleft : leftBaire '' P.val.val ⊆ A.val.val := by
    rintro x ⟨p, hp, rfl⟩
    exact hp.1.2
  have hright : rightBaire '' P.val.val ⊆ A.val.val := by
    rintro x ⟨p, hp, rfl⟩
    exact hp.2
  obtain ⟨p, hp, hl, hr⟩ := parameter_pair_generic_coordinates ε P A hleft hright
    (localTest '' T) (hTc.image localTest) hld
  have hgL := parameterHKLPointTests_generic E F (x := leftBaire p) (by
    intro D hD
    obtain ⟨Q, hQ, hpQ⟩ := hl (localTest D) ⟨D, hD, rfl⟩
    exact ⟨Q.val, hQ, hpQ⟩)
  have hgR := parameterHKLPointTests_generic E F (x := rightBaire p) (by
    intro D hD
    obtain ⟨Q, hQ, hpQ⟩ := hr (localTest D) ⟨D, hD, rfl⟩
    exact ⟨Q.val, hQ, hpQ⟩)
  exact ⟨leftBaire p, hp.1.2, rightBaire p, hp.2, hp.1.1.1, hp.1.1.2,
    hgL.1, hgR.1, hgL.2, hgR.2⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Thus no kernel rectangle has only equivalent pairs meeting any prescribed countable
    family of downward-closed dense tests. Apply this to the Borel truth tests above. If a pair in $H\times H$
    meeting them were equivalent, local truth and a common refinement with $H\times H$ would give just such a
    rectangle. This contradiction proves the lemma with that family as $\mathcal J$.
-/
/-- A kernel rectangle cannot have all actual generic pairs E-equivalent.
The contradiction uses the same right point for the two inequivalent left
points, after meeting the required witness tests in the restricted order. -/
theorem parameter_hkl_no_equivalent_generic_rectangle (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (P : ParameterCompatibleRectangle ε E)
    (hPH : P.val.1.val.val ⊆ equivalenceGapKernel E (invariantSetoid ε E))
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D) :
    ¬ (∀ x ∈ P.val.1.val.val, ∀ z ∈ P.val.2.val.val,
      ParameterRectangleGeneric ε E J x z → E.r x z) := by
  intro hall
  obtain ⟨x, hx, y, hy, hxy, hne, hxD, hyD, hxG, hyG⟩ :=
    parameter_hkl_inequivalent_generics ε E hE hneE P.val.1 hPH J hJc hJd
  obtain ⟨z, hz, hxz, hyz⟩ := parameter_hkl_common_right P hE J hJc hJl
    hx hy hxD hyD hxy hxG hyG
  exact hne (E.trans (hall x hx z hz hxz) (E.symm (hall y hy z hz hyz)))

end PolishSpaceBook.LambdaTree
