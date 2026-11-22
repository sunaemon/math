module

public import PolishSpaceBook.LambdaHKLRefinement

@[expose] public section

/-!
# Relative analytic decision and local projection tests

All tests are families in the fixed-parameter catalog. Decisions about a
relative analytic condition are dense by intersection. Local left projections
of compatible rectangles are dense by mutual saturation restriction. These
are concrete countable genericity tests, not a forcing truth or absoluteness
assumption.
-/

namespace PolishSpaceBook.LambdaTree
open Set

variable {ε : ℕ → ℕ}

def parameterDecisionRequirement (A : (parameterAnalyticCatalog ε).Condition) :
    Set (parameterAnalyticCatalog ε).Condition :=
  {P | P ≤ A ∨ Disjoint P.val.val A.val.val}

theorem parameterDecisionRequirement_dense (A : (parameterAnalyticCatalog ε).Condition) :
    IsCoinitial (parameterDecisionRequirement A) := by
  classical
  intro P
  by_cases h : Disjoint P.val.val A.val.val
  · exact ⟨P, Or.inr h, le_rfl⟩
  · let Q := parameterCondition ε (P.val.val ∩ A.val.val)
      ((parameterCondition_projected ε P).inter (parameterCondition_projected ε A))
      (Set.not_disjoint_iff_nonempty_inter.mp h)
    exact ⟨Q, Or.inl inter_subset_right, inter_subset_left⟩

theorem parameterDecisionRequirement_lower (A : (parameterAnalyticCatalog ε).Condition) :
    IsLowerSet (parameterDecisionRequirement A) := by
  intro P Q hQP hP
  rcases hP with h | h
  · exact Or.inl (hQP.trans h)
  · exact Or.inr (h.mono_left hQP)

def ParameterDecisionGeneric (ε : ℕ → ℕ) (x : FusionReal) : Prop :=
  ∀ A : (parameterAnalyticCatalog ε).Condition,
    ∃ P ∈ parameterDecisionRequirement A, x ∈ P.val.val

/-- If an analytic set misses a decision-generic point, a catalog neighborhood
of that point is disjoint from the set. Empty sets need no decision test. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    A useful consequence is that a $\GHConditions{1}$-generic point $x$ decides every lightface analytic set $A$:
    its filter meets the dense family of conditions contained in $A$ or disjoint from $A$. Thus if $x\notin A$, some
    analytic condition containing $x$ is disjoint from $A$.
-/
theorem ParameterDecisionGeneric.avoiding {x : FusionReal}
    (hx : ParameterDecisionGeneric ε x) {A : Set FusionReal}
    (hA : Projected ε A) (hxn : x ∉ A) :
    ∃ B : (parameterAnalyticCatalog ε).Condition, x ∈ B.val.val ∧ Disjoint A B.val.val := by
  classical
  by_cases hn : A.Nonempty
  · let C := parameterCondition ε A hA hn
    obtain ⟨P, hp, hxP⟩ := hx C
    rcases hp with hp | hp
    · exact False.elim (hxn (hp hxP))
    · exact ⟨P, hxP, hp.symm⟩
  · let C := parameterCondition ε univ (projected_univ ε) (Set.univ_nonempty)
    obtain ⟨P, _, hxP⟩ := hx C
    refine ⟨P, hxP, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hn]
    simp

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    More generally, any two points $x,y$ that decide every lightface analytic set and satisfy
    $x\mathrel{\EffectiveClosureER{E}}y$ agree on all invariant lightface analytic sets.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    If $x\in A$ and $y\notin A$ for such an invariant $A$, the decision test at $y$ gives
    an analytic neighborhood $B$ of $y$ disjoint from $A$. Its saturation is still disjoint from $A$.
    Invariant separation then gives an invariant $\lDelta^1_1$ set distinguishing $x$ from $y$, a contradiction.
-/
/-- Invariant separation makes auxiliary-related decision-generic points
agree on every invariant relative analytic set. -/
theorem parameter_generics_invariant_agree (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    {x y : FusionReal} (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y) {A : Set FusionReal}
    (hA : Projected ε A) (hi : ERInvariant E A) :
    x ∈ A ↔ y ∈ A := by
  have forward {x y : FusionReal} (hy : ParameterDecisionGeneric ε y)
      (hxy : (invariantSetoid ε E).r x y) (hxA : x ∈ A) : y ∈ A := by
    by_contra hyA
    obtain ⟨B, hyB, hAB⟩ := hy.avoiding hA hyA
    have hd : Disjoint A (erSaturation E B.val.val) :=
      (erSaturation_disjoint E hAB.symm hi).symm
    obtain ⟨C, hc, hci, hAC, hCB⟩ := invariant_separation ε E hE hA
      (projected_erSaturation E hE (parameterCondition_projected ε B)) hd
      (erSaturation_invariant E _)
    exact Set.disjoint_left.mp hCB ((hxy C hc hci).mp (hAC hxA))
      (subset_erSaturation E _ hyB)
  exact ⟨forward hy hxy, forward hx ((invariantSetoid ε E).symm hxy)⟩

/-- Local projection conditions include the witness right coordinate. -/
def parameterLeftProjection {E : Setoid FusionReal} (P : ParameterCompatibleRectangle ε E)
    (D : Set (ParameterCompatibleRectangle ε E)) : Set (parameterAnalyticCatalog ε).Condition :=
  {A | ∃ Q ∈ D, Q ≤ P ∧ Q.val.1 = A}

theorem parameterLeftProjection_dense {E : Setoid FusionReal}
    (hE : ProjectedRelation ε E.r)
    (P : ParameterCompatibleRectangle ε E) (D : Set (ParameterCompatibleRectangle ε E))
    (hD : IsCoinitial D) :
    IsCoinitial {A : CatalogBelow (parameterAnalyticCatalog ε) P.val.1 |
      A.val ∈ parameterLeftProjection P D} := by
  intro A
  obtain ⟨Q, hQP, hQA⟩ := P.refine_left hE A.val A.property
  obtain ⟨R, hRD, hRQ⟩ := hD Q
  have hRA : R.val.1 ≤ A.val := by simpa only [hQA] using hRQ.1
  exact ⟨⟨R.val.1, hRA.trans A.property⟩, ⟨R, hRD, hRQ.trans hQP, rfl⟩, hRA⟩

/-- Extend a local dense family to the whole catalog by allowing conditions
disjoint from the local domain. A point in that domain cannot take this case. -/
def parameterLocalTest (A : (parameterAnalyticCatalog ε).Condition)
    (D : Set (CatalogBelow (parameterAnalyticCatalog ε) A)) :
    Set (parameterAnalyticCatalog ε).Condition :=
  {P | Disjoint P.val.val A.val.val ∨ ∃ Q ∈ D, P ≤ Q.val}

theorem parameterLocalTest_dense (A : (parameterAnalyticCatalog ε).Condition)
    (D : Set (CatalogBelow (parameterAnalyticCatalog ε) A)) (hD : IsCoinitial D) :
    IsCoinitial (parameterLocalTest A D) := by
  classical
  intro P
  by_cases h : Disjoint P.val.val A.val.val
  · exact ⟨P, Or.inl h, le_rfl⟩
  · let Q := parameterCondition ε (P.val.val ∩ A.val.val)
      ((parameterCondition_projected ε P).inter (parameterCondition_projected ε A))
      (Set.not_disjoint_iff_nonempty_inter.mp h)
    obtain ⟨R, hRD, hRQ⟩ := hD ⟨Q, inter_subset_right⟩
    exact ⟨R.val, Or.inr ⟨R, hRD, le_rfl⟩,
      fun x hx => (hRQ hx).1⟩

theorem parameterLocalTest_lower (A : (parameterAnalyticCatalog ε).Condition)
    (D : Set (CatalogBelow (parameterAnalyticCatalog ε) A)) :
    IsLowerSet (parameterLocalTest A D) := by
  intro P Q hQP hP
  rcases hP with h | ⟨R, hR, hPR⟩
  · exact Or.inl (h.mono_left hQP)
  · exact Or.inr ⟨R, hR, hQP.trans hPR⟩

def parameterProjectionTest {E : Setoid FusionReal} (P : ParameterCompatibleRectangle ε E)
    (D : Set (ParameterCompatibleRectangle ε E)) : Set (parameterAnalyticCatalog ε).Condition :=
  parameterLocalTest P.val.1 {A | A.val ∈ parameterLeftProjection P D}

def ParameterLeftGeneric (ε : ℕ → ℕ) (E : Setoid FusionReal) (x : FusionReal)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) : Prop :=
  ∀ D ∈ J, ∀ P : ParameterCompatibleRectangle ε E, x ∈ P.val.1.val.val →
    ∃ Q ∈ D, Q ≤ P ∧ x ∈ Q.val.1.val.val

/-- The countable family needed for decisions and all local rectangle tests. -/
def parameterHKLPointTests (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) : Set (Set (parameterAnalyticCatalog ε).Condition) :=
  range parameterDecisionRequirement ∪
    range (fun p : ParameterCompatibleRectangle ε E × J => parameterProjectionTest p.1 p.2.val)

theorem parameterHKLPointTests_countable (E : Setoid FusionReal)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJc : J.Countable) :
    (parameterHKLPointTests ε E J).Countable := by
  let : Countable J := hJc.to_subtype
  exact (countable_range _).union (countable_range _)

theorem parameterHKLPointTests_dense (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJd : ∀ D ∈ J, IsCoinitial D) :
    ∀ D ∈ parameterHKLPointTests ε E J, IsCoinitial D := by
  rintro D (⟨A, rfl⟩ | ⟨⟨P, R⟩, rfl⟩)
  · exact parameterDecisionRequirement_dense A
  · exact parameterLocalTest_dense _ _ (parameterLeftProjection_dense hE P R.val (hJd _ R.property))

theorem parameterHKLPointTests_generic (E : Setoid FusionReal)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) {x : FusionReal}
    (hx : ∀ D ∈ parameterHKLPointTests ε E J, ∃ P ∈ D, x ∈ P.val.val) :
    ParameterDecisionGeneric ε x ∧ ParameterLeftGeneric ε E x J := by
  constructor
  · intro A
    exact hx _ (Or.inl ⟨A, rfl⟩)
  · intro D hD P hxP
    obtain ⟨A, hA, hxA⟩ := hx (parameterProjectionTest P D) (Or.inr ⟨(P, ⟨D, hD⟩), rfl⟩)
    rcases hA with hd | ⟨B, ⟨Q, hQD, hQP, hQB⟩, hAB⟩
    · exact False.elim (Set.disjoint_left.mp hd hxA hxP)
    · exact ⟨Q, hQD, hQP, hQB.symm ▸ hAB hxA⟩

end PolishSpaceBook.LambdaTree
