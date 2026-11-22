module

public import PolishSpaceBook.LambdaCatalogProjections
public import PolishSpaceBook.LambdaHomogeneousHulls

@[expose] public section

/-!
# The common-right contradiction in the Silver splitting proof

Inside the fixed-parameter catalog, a kernel condition contains an
inequivalent pair whose coordinates satisfy the left genericity tests.
The common-right construction rules out any rectangle on which every
product-generic pair is equivalent. This is the contradiction step in the
book. `LambdaCoanalyticTruth` supplies the local-truth step from
one equivalent generic pair to such a rectangle. `LambdaKernelComplexity`
proves relative analyticity of the actual kernel.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set

/-- The contradictory pair is an actual member of the analytic nonrelation,
and both its coordinates meet the tests used by the common-right lemma. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    The Silver-kernel lemma says that
    $$R=\SetDifference{(A\times A)}{E}$$
    is nonempty. It is lightface analytic because $E$ is coanalytic.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Apply the \termuse{generic coordinates of an analytic pair condition} proposition in
    §{sec:edst-generic-conditions} to $R$ and the family $\mathcal F$ of local projection tests just defined.
    Both projections of $R$ lie in $A$, and every member of $\mathcal F$ is dense below $A$, so the proposition
    gives an actual pair $(u,v)\in R$ whose coordinates meet every test in $\mathcal F$.
    The common-right-point argument therefore gives $u\mathrel E v$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    The conclusion concerns generic pairs of actual members of the conditions. It makes no assertion about all pairs
    in their ordinary closures. The distinction between analytic pair conditions and product conditions is essential:
    the contradictory pair in $R$ need only have individually generic coordinates.
-/
theorem parameter_silver_inequivalent_left_generics (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (A B : (parameterAnalyticCatalog ε).Condition)
    (hAH : A.val.val ⊆ silverKernel ε E)
    (J : Set (Set ((parameterAnalyticCatalog ε).Condition × (parameterAnalyticCatalog ε).Condition)))
    (hJc : J.Countable) (hJd : ∀ D ∈ J, IsCoinitial D) :
    ∃ x ∈ A.val.val, ∃ x' ∈ A.val.val, ¬ E.r x x' ∧
      CatalogLeftGeneric (parameterAnalyticCatalog ε) A B x J ∧
      CatalogLeftGeneric (parameterAnalyticCatalog ε) A B x' J := by
  let C := parameterAnalyticCatalog ε
  have hA := parameterCondition_projected ε A
  let R := ({p | ¬ E.r (leftBaire p) (rightBaire p)} ∩ leftBaire ⁻¹' A.val.val) ∩
    rightBaire ⁻¹' A.val.val
  have hR : Projected ε R :=
    (hE.inter hA.leftPreimage).inter hA.rightPreimage
  have hRn : R.Nonempty := by
    have hn := silverKernel_not_homogeneous E hE hA A.val.property.2 hAH
    change ¬ (∀ x ∈ A.val.val, ∀ y ∈ A.val.val, E.r x y) at hn
    push Not at hn
    obtain ⟨x, hx, y, hy, hxy⟩ := hn
    refine ⟨pairBaire x y, ?_⟩
    simpa only [R, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      leftBaire_pair, rightBaire_pair] using And.intro (And.intro hxy hx) hy
  let P := parameterCondition ε R hR hRn
  have hleft : leftBaire '' P.val.val ⊆ A.val.val := by
    rintro x ⟨p, hp, rfl⟩
    exact hp.1.2
  have hright : rightBaire '' P.val.val ⊆ A.val.val := by
    rintro x ⟨p, hp, rfl⟩
    exact hp.2
  let : Countable J := hJc.to_subtype
  let test (p : J × CatalogBelow C B) : Set (CatalogBelow C A) :=
    {Q | Q.val ∈ catalogLeftProjection C A p.2.val p.1.val}
  have hd : ∀ D ∈ Set.range test, IsCoinitial D := by
    rintro _ ⟨⟨D, Q⟩, rfl⟩
    exact catalogLeftProjection_coinitial C A Q.val D.val (hJd D.val D.property)
  obtain ⟨p, hp, hl, hr⟩ := parameter_pair_generic_coordinates ε P A hleft hright
    (Set.range test) (Set.countable_range test) hd
  refine ⟨leftBaire p, hp.1.2, rightBaire p, hp.2, hp.1.1, ?_, ?_⟩
  · intro D hD Q hQB
    obtain ⟨U, hU, hpU⟩ := hl (test (⟨D, hD⟩, ⟨Q, hQB⟩)) ⟨(⟨D, hD⟩, ⟨Q, hQB⟩), rfl⟩
    exact ⟨U.val, hU, hpU⟩
  · intro D hD Q hQB
    obtain ⟨U, hU, hpU⟩ := hr (test (⟨D, hD⟩, ⟨Q, hQB⟩)) ⟨(⟨D, hD⟩, ⟨Q, hQB⟩), rfl⟩
    exact ⟨U.val, hU, hpU⟩

/-- No rectangle with a left condition in the kernel can make all its
product-generic actual pairs equivalent. Only the stated countable dense
family is used; neither coordinate is replaced by an arbitrary singleton. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    But actual membership in $R$ gives $u\mathrel{\not E}v$, a contradiction.
-/
theorem parameter_silver_no_equivalent_generic_rectangle (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (A B : (parameterAnalyticCatalog ε).Condition)
    (hAH : A.val.val ⊆ silverKernel ε E)
    (J : Set (Set ((parameterAnalyticCatalog ε).Condition × (parameterAnalyticCatalog ε).Condition)))
    (hJc : J.Countable) (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D) :
    ¬ (∀ x ∈ A.val.val, ∀ y ∈ B.val.val,
      CatalogProductGeneric (parameterAnalyticCatalog ε) J x y → E.r x y) := by
  intro hall
  obtain ⟨x, hx, x', hx', hne, hgen, hgen'⟩ :=
    parameter_silver_inequivalent_left_generics ε E hE A B hAH J hJc hJd
  obtain ⟨y, hy, hpairs⟩ := silver_common_right_point (parameterAnalyticCatalog ε) A B J hJc hJl
    x x' hgen hgen'
  have hxy := hall x hx y hy (fun D hD => (hpairs D hD).1)
  have hx'y := hall x' hx' y hy (fun D hD => (hpairs D hD).2)
  exact hne (E.trans hxy (E.symm hx'y))

end LambdaTree
end PolishSpaceBook
