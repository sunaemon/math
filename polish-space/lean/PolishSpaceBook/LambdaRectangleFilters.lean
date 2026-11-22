module

public import PolishSpaceBook.LambdaGenericFilters

@[expose] public section

/-!
# Generic filters for the relative compatible product

Coordinate witness tests produce an actual unique pair in every rectangle
of an order filter. Coordinate decision tests make the points individually
decision-generic and auxiliary-related. Ordinary order decision tests then
determine the whole rectangle filter from that pair. All these tests are
countable lower dense families; no truth or absoluteness lemma is assumed.
-/

namespace PolishSpaceBook.LambdaTree
open Set

section OrderDecisions
variable {P : Type*} [Preorder P]

def orderDecisionRequirement (a : P) : Set P :=
  {p | p ≤ a ∨ ¬ ∃ r, r ≤ p ∧ r ≤ a}

theorem orderDecisionRequirement_dense (a : P) : IsCoinitial (orderDecisionRequirement a) := by
  classical
  intro p
  by_cases h : ∃ r, r ≤ p ∧ r ≤ a
  · obtain ⟨r, hrp, hra⟩ := h
    exact ⟨r, Or.inl hra, hrp⟩
  · exact ⟨p, Or.inr h, le_rfl⟩

theorem orderDecisionRequirement_lower (a : P) : IsLowerSet (orderDecisionRequirement a) := by
  intro p q hqp hp
  rcases hp with hp | hp
  · exact Or.inl (hqp.trans hp)
  · exact Or.inr (fun ⟨r, hrq, hra⟩ => hp ⟨r, hrq.trans hqp, hra⟩)

end OrderDecisions

variable {ε : ℕ → ℕ} {E : Setoid FusionReal}

def parameterLeftTest (D : Set (parameterAnalyticCatalog ε).Condition) :
    Set (ParameterCompatibleRectangle ε E) := {P | P.val.1 ∈ D}

theorem parameterLeftTest_dense
    (hE : ProjectedRelation ε E.r)
    {D : Set (parameterAnalyticCatalog ε).Condition} (hD : IsCoinitial D) :
    IsCoinitial (parameterLeftTest (E := E) D) := by
  intro P
  obtain ⟨A, hAD, hAP⟩ := hD P.val.1
  obtain ⟨Q, hQP, hQA⟩ := P.refine_left hE A hAP
  have hQD : Q.val.1 ∈ D := hQA.symm ▸ hAD
  exact ⟨Q, hQD, hQP⟩

theorem parameterLeftTest_lower {D : Set (parameterAnalyticCatalog ε).Condition}
    (hD : IsLowerSet D) : IsLowerSet (parameterLeftTest (E := E) D) :=
  fun _ _ h hp => hD h.1 hp

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    its generic pair belongs to every rectangle in the filter.
-/
/-- Coordinate fusion identifies an actual pair in every member of the
rectangle filter, including conditions outside the chosen cofinal sequence. -/
theorem parameter_rectangle_filter_fusion (G : Order.PFilter (ParameterCompatibleRectangle ε E))
    (hL : ∀ D ∈ (parameterAnalyticCatalog ε).requirements, ∃ P ∈ G, P ∈ parameterLeftTest D)
    (hR : ∀ D ∈ (parameterAnalyticCatalog ε).requirements, ∃ P ∈ G, P ∈ parameterRightTest D) :
    ∃! p : FusionReal × FusionReal, ∀ P ∈ G,
      p.1 ∈ P.val.1.val.val ∧ p.2 ∈ P.val.2.val.val := by
  obtain ⟨q, hq, hqG, hcof⟩ := pfilter_countable_cofinal_sequence G
  obtain ⟨x, hx, hxu⟩ := (parameterAnalyticCatalog ε).fusion (fun n => (q n).val.1)
    (fun _ _ h => (hq h).1) (by
      intro D hD
      obtain ⟨P, hPG, hPD⟩ := hL D hD
      obtain ⟨n, hn⟩ := hcof P hPG
      exact ⟨n, ((parameterAnalyticCatalog ε).requirements_dense_lower D hD).2 hn.1 hPD⟩)
  obtain ⟨y, hy, hyu⟩ := (parameterAnalyticCatalog ε).fusion (fun n => (q n).val.2)
    (fun _ _ h => (hq h).2) (by
      intro D hD
      obtain ⟨P, hPG, hPD⟩ := hR D hD
      obtain ⟨n, hn⟩ := hcof P hPG
      exact ⟨n, ((parameterAnalyticCatalog ε).requirements_dense_lower D hD).2 hn.2 hPD⟩)
  refine ⟨(x, y), ?_, ?_⟩
  · intro P hPG
    obtain ⟨n, hn⟩ := hcof P hPG
    exact ⟨hn.1 (hx n), hn.2 (hy n)⟩
  · intro p hp
    exact Prod.ext (hxu p.1 (fun n => (hp (q n) (hqG n)).1))
      (hyu p.2 (fun n => (hp (q n) (hqG n)).2))

/-- Every encountered coordinate test is met by the corresponding actual
point, for any family of tests, not just the decision family. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Consequently coordinate projections of generic filters for this partial order are
    $\GHConditions{1}$-generic, and
-/
theorem parameter_rectangle_filter_coordinate_tests
    (G : Order.PFilter (ParameterCompatibleRectangle ε E)) (x y : FusionReal)
    (hsound : ∀ P ∈ G, x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val)
    (F : Set (Set (parameterAnalyticCatalog ε).Condition))
    (hL : ∀ D ∈ F, ∃ P ∈ G, P ∈ parameterLeftTest D)
    (hR : ∀ D ∈ F, ∃ P ∈ G, P ∈ parameterRightTest D) :
    (∀ D ∈ F, ∃ A ∈ D, x ∈ A.val.val) ∧ (∀ D ∈ F, ∃ B ∈ D, y ∈ B.val.val) := by
  constructor
  · intro D hD
    obtain ⟨P, hPG, hPD⟩ := hL D hD
    exact ⟨P.val.1, hPD, (hsound P hPG).1⟩
  · intro D hD
    obtain ⟨P, hPG, hPD⟩ := hR D hD
    exact ⟨P.val.2, hPD, (hsound P hPG).2⟩

/-- Actual coordinates of the filter meet every encountered coordinate test. -/
theorem parameter_rectangle_filter_coordinate_generics
    (G : Order.PFilter (ParameterCompatibleRectangle ε E)) (x y : FusionReal)
    (hsound : ∀ P ∈ G, x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val)
    (hL : ∀ A : (parameterAnalyticCatalog ε).Condition,
      ∃ P ∈ G, P ∈ parameterLeftTest (parameterDecisionRequirement A))
    (hR : ∀ A : (parameterAnalyticCatalog ε).Condition,
      ∃ P ∈ G, P ∈ parameterRightTest (parameterDecisionRequirement A)) :
    ParameterDecisionGeneric ε x ∧ ParameterDecisionGeneric ε y := by
  constructor
  · intro A
    obtain ⟨P, hPG, hPA⟩ := hL A
    exact ⟨P.val.1, hPA, (hsound P hPG).1⟩
  · intro A
    obtain ⟨P, hPG, hPA⟩ := hR A
    exact ⟨P.val.2, hPA, (hsound P hPG).2⟩

/-- Equal saturations and coordinate decisions make the actual generic pair
indistinguishable by complemented invariant tests. -/
theorem parameter_rectangle_filter_auxiliary_related
    (G : Order.PFilter (ParameterCompatibleRectangle ε E)) (x y : FusionReal)
    (hsound : ∀ P ∈ G, x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val)
    (hL : ∀ A : (parameterAnalyticCatalog ε).Condition,
      ∃ P ∈ G, P ∈ parameterLeftTest (parameterDecisionRequirement A)) :
    (invariantSetoid ε E).r x y := by
  have forward {A : Set FusionReal} (hA : Projected ε A)
      (hi : ERInvariant E A) (hxA : x ∈ A) : y ∈ A := by
    let C := parameterCondition ε A hA ⟨x, hxA⟩
    obtain ⟨P, hPG, hPC⟩ := hL C
    obtain ⟨hxP, hyP⟩ := hsound P hPG
    rcases hPC with hPC | hd
    · have hys := subset_erSaturation E P.val.2.val.val hyP
      rw [← P.property] at hys
      obtain ⟨a, ha, hay⟩ := hys
      exact (hi hay).mp (hPC ha)
    · exact False.elim (Set.disjoint_left.mp hd hxP hxA)
  intro A hA hi
  refine ⟨forward hA.1 hi, ?_⟩
  intro hyA
  by_contra hxA
  have hyAc := forward hA.2 (fun {_ _} h => not_congr (hi h)) hxA
  exact hyAc hyA

/-- Once order decisions are met, the actual pair determines the entire
compatible-product filter. The common-refinement proof rules out the
incompatibility alternative. -/
theorem parameter_rectangle_filter_determined_by_point
    (hE : ProjectedRelation ε E.r)
    (G : Order.PFilter (ParameterCompatibleRectangle ε E)) (x y : FusionReal)
    (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y)
    (hsound : ∀ P ∈ G, x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val)
    (hdec : ∀ A : ParameterCompatibleRectangle ε E, ∃ P ∈ G, P ∈ orderDecisionRequirement A) :
    G = parameterRectanglePointFilter E hE x y hx hy hxy := by
  apply SetLike.ext
  intro A
  change A ∈ G ↔ x ∈ A.val.1.val.val ∧ y ∈ A.val.2.val.val
  refine ⟨hsound A, ?_⟩
  rintro ⟨hxA, hyA⟩
  obtain ⟨P, hPG, hPD⟩ := hdec A
  rcases hPD with hPA | hPA
  · exact Order.PFilter.mem_of_le hPA hPG
  · obtain ⟨hxP, hyP⟩ := hsound P hPG
    obtain ⟨R, hRP, hRA, _, _⟩ := parameter_rectangle_common_refinement E hE hx hy hxy
      P A hxP hyP hxA hyA
    exact False.elim (hPA ⟨R, hRP, hRA⟩)

end PolishSpaceBook.LambdaTree
