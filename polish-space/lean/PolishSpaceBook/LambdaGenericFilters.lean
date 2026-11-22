module

public import PolishSpaceBook.LambdaHKLCommonRight
public import Mathlib.Order.PFilter

@[expose] public section

/-!
# Actual points and order filters in the relative analytic orders

We use mathlib's `Order.PFilter`. Countable filters admit decreasing cofinal
sequences; catalog witness encounters give unique actual points of all their
conditions. Decision tests determine the filter from that point. For the HKL
restricted product, auxiliary-related decision-generic coordinates give a
common compatible refinement of any two rectangles containing them. These
filter facts do not replace forcing semantics or its absoluteness theorem.
-/

namespace PolishSpaceBook.LambdaTree
open Set

/-- A countable order filter has a decreasing cofinal sequence inside it. -/
theorem pfilter_countable_cofinal_sequence {P : Type*} [Preorder P] [Countable P]
    (G : Order.PFilter P) :
    ∃ q : ℕ → P, Antitone q ∧ (∀ n, q n ∈ G) ∧ ∀ p ∈ G, ∃ n, q n ≤ p := by
  let test (p : G) : Set G := {q | q.val ≤ p.val}
  have hd : ∀ D ∈ range test, IsCoinitial D := by
    rintro _ ⟨p, rfl⟩ q
    obtain ⟨r, hr, hrq, hrp⟩ := G.directed q.val q.property p.val p.property
    exact ⟨⟨r, hr⟩, hrp, hrq⟩
  have hl : ∀ D ∈ range test, IsLowerSet D := by
    rintro _ ⟨p, rfl⟩ q r hrq hqp
    exact hrq.trans hqp
  obtain ⟨p, hp⟩ := G.nonempty
  obtain ⟨q, hq, _, hm⟩ := countable_dense_sequence (range test) (countable_range test)
    hd hl (⟨p, hp⟩ : G)
  refine ⟨fun n => (q n).val, hq, fun n => (q n).property, ?_⟩
  intro p hp
  obtain ⟨n, _, hn⟩ := hm (test ⟨p, hp⟩) ⟨⟨p, hp⟩, rfl⟩ 0
  exact ⟨n, hn⟩

/-- Witness encounters in a filter yield actual membership in every
condition, not merely in its closure or in a selected subsequence. -/
theorem catalog_filter_fusion (C : AnalyticConditionCatalog) (G : Order.PFilter C.Condition)
    (hG : ∀ D ∈ C.requirements, ∃ P ∈ G, P ∈ D) :
    ∃! x : FusionReal, ∀ P ∈ G, x ∈ P.val.val := by
  obtain ⟨q, hq, hqG, hcof⟩ := pfilter_countable_cofinal_sequence G
  obtain ⟨x, hx, hxu⟩ := C.fusion q hq (by
    intro D hD
    obtain ⟨P, hPG, hPD⟩ := hG D hD
    obtain ⟨n, hn⟩ := hcof P hPG
    exact ⟨n, (C.requirements_dense_lower D hD).2 hn hPD⟩)
  refine ⟨x, ?_, ?_⟩
  · intro P hPG
    obtain ⟨n, hn⟩ := hcof P hPG
    exact hn (hx n)
  · intro y hy
    exact hxu y (fun n => hy (q n) (hqG n))

variable {ε : ℕ → ℕ}

/-- All relative analytic conditions containing a point form an order filter. -/
def parameterPointFilter (ε : ℕ → ℕ) (x : FusionReal) :
    Order.PFilter (parameterAnalyticCatalog ε).Condition :=
  (Order.IsPFilter.of_def
    (F := {P : (parameterAnalyticCatalog ε).Condition | x ∈ P.val.val})
    ⟨parameterCondition ε univ (projected_univ ε) univ_nonempty, mem_univ x⟩
    (by
      intro P hxP Q hxQ
      let R := parameterCondition ε (P.val.val ∩ Q.val.val)
        ((parameterCondition_projected ε P).inter (parameterCondition_projected ε Q))
        ⟨x, hxP, hxQ⟩
      exact ⟨R, ⟨hxP, hxQ⟩, inter_subset_left, inter_subset_right⟩)
    (by
      intro P Q h hx
      exact h hx)).toPFilter

@[simp] theorem mem_parameterPointFilter (x : FusionReal)
    (P : (parameterAnalyticCatalog ε).Condition) :
    P ∈ parameterPointFilter ε x ↔ x ∈ P.val.val := Iff.rfl

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Also the filter is determined by its point: every analytic
    condition containing that point belongs to the filter.
-/
/-- A filter meeting each analytic decision test is exactly the filter of
conditions containing its actual point. -/
theorem parameter_filter_determined_by_point
    (G : Order.PFilter (parameterAnalyticCatalog ε).Condition) (x : FusionReal)
    (hsound : ∀ P ∈ G, x ∈ P.val.val)
    (hdec : ∀ A : (parameterAnalyticCatalog ε).Condition,
      ∃ P ∈ G, P ∈ parameterDecisionRequirement A) : G = parameterPointFilter ε x := by
  apply SetLike.ext
  intro A
  change A ∈ G ↔ x ∈ A.val.val
  refine ⟨hsound A, ?_⟩
  intro hxA
  obtain ⟨P, hPG, hPD⟩ := hdec A
  rcases hPD with hPA | hd
  · exact Order.PFilter.mem_of_le hPA hPG
  · exact False.elim (Set.disjoint_left.mp hd (hsound P hPG) hxA)

/-- The actual point and its filter determine one another once the filter
meets witness and decision requirements. -/
theorem parameter_filter_unique_point
    (G : Order.PFilter (parameterAnalyticCatalog ε).Condition)
    (hG : ∀ D ∈ (parameterAnalyticCatalog ε).requirements, ∃ P ∈ G, P ∈ D)
    (hdec : ∀ A : (parameterAnalyticCatalog ε).Condition,
      ∃ P ∈ G, P ∈ parameterDecisionRequirement A) :
    ∃! x : FusionReal, G = parameterPointFilter ε x := by
  obtain ⟨x, hx, hu⟩ := catalog_filter_fusion (parameterAnalyticCatalog ε) G hG
  refine ⟨x, parameter_filter_determined_by_point G x hx hdec, ?_⟩
  intro y hy
  exact hu y (fun P hP => (mem_parameterPointFilter y P).mp (hy ▸ hP))

/-- Saturation restrictions of the coordinate intersections give a compatible
common refinement containing both specified decision-generic points. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Now let $A_0\times B_0$ and $A_1\times B_1$ be restricted rectangles containing $(x,y)$, and put
    $$C:=A_0\cap A_1,\qquad D:=B_0\cap B_1.$$
    Both are nonempty analytic conditions. Their saturations are invariant analytic sets, so the preceding
    invariant-agreement argument gives $x\in\ERSaturation{D}{E}$ and $y\in\ERSaturation{C}{E}$. Consequently
    $$(C\cap\ERSaturation{D}{E})\times(D\cap\ERSaturation{C}{E})$$
    is a restricted rectangle containing $(x,y)$ and refining both original rectangles. Its two saturations
    are $\ERSaturation{C}{E}\cap\ERSaturation{D}{E}$.
-/
theorem parameter_rectangle_common_refinement (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    {x y : FusionReal} (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y)
    (P Q : ParameterCompatibleRectangle ε E)
    (hxP : x ∈ P.val.1.val.val) (hyP : y ∈ P.val.2.val.val)
    (hxQ : x ∈ Q.val.1.val.val) (hyQ : y ∈ Q.val.2.val.val) :
    ∃ R : ParameterCompatibleRectangle ε E, R ≤ P ∧ R ≤ Q ∧
      x ∈ R.val.1.val.val ∧ y ∈ R.val.2.val.val := by
  let A := P.val.1.val.val ∩ Q.val.1.val.val
  let B := P.val.2.val.val ∩ Q.val.2.val.val
  have hA : Projected ε A :=
    (parameterCondition_projected ε P.val.1).inter (parameterCondition_projected ε Q.val.1)
  have hB : Projected ε B :=
    (parameterCondition_projected ε P.val.2).inter (parameterCondition_projected ε Q.val.2)
  have hxSat : x ∈ erSaturation E B :=
    (parameter_generics_invariant_agree E hE hx hy hxy
      (projected_erSaturation E hE hB) (erSaturation_invariant E B)).mpr
      (subset_erSaturation E B ⟨hyP, hyQ⟩)
  have hySat : y ∈ erSaturation E A :=
    (parameter_generics_invariant_agree E hE hx hy hxy
      (projected_erSaturation E hE hA) (erSaturation_invariant E A)).mp
      (subset_erSaturation E A ⟨hxP, hxQ⟩)
  let L := parameterCondition ε (A ∩ erSaturation E B)
    (hA.inter (projected_erSaturation E hE hB)) ⟨x, ⟨hxP, hxQ⟩, hxSat⟩
  let R := parameterCondition ε (B ∩ erSaturation E A)
    (hB.inter (projected_erSaturation E hE hA)) ⟨y, ⟨hyP, hyQ⟩, hySat⟩
  have hc : erSaturation E L.val.val = erSaturation E R.val.val := by
    change erSaturation E (A ∩ erSaturation E B) = erSaturation E (B ∩ erSaturation E A)
    rw [erSaturation_inter_saturation, erSaturation_inter_saturation, inter_comm]
  exact ⟨⟨(L, R), hc⟩, ⟨fun _ h => h.1.1, fun _ h => h.1.1⟩,
    ⟨fun _ h => h.1.2, fun _ h => h.1.2⟩, ⟨⟨hxP, hxQ⟩, hxSat⟩, ⟨⟨hyP, hyQ⟩, hySat⟩⟩

/-- The canonical compatible-product filter of two good auxiliary-related
points uses only the original relative conditions. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    This proves directedness. Upward closure follows from
    containment of the pair, and $X\times X$ makes the family nonempty. This constructs the required filter
    directly from pointwise test encounters.
-/
def parameterRectanglePointFilter (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (x y : FusionReal) (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y) : Order.PFilter (ParameterCompatibleRectangle ε E) :=
  (Order.IsPFilter.of_def
    (F := {P : ParameterCompatibleRectangle ε E | x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val})
    (by
      let A := parameterCondition ε univ (projected_univ ε) univ_nonempty
      exact ⟨⟨(A, A), rfl⟩, mem_univ x, mem_univ y⟩)
    (by
      rintro P ⟨hxP, hyP⟩ Q ⟨hxQ, hyQ⟩
      obtain ⟨R, hRP, hRQ, hxR, hyR⟩ :=
        parameter_rectangle_common_refinement E hE hx hy hxy P Q hxP hyP hxQ hyQ
      exact ⟨R, ⟨hxR, hyR⟩, hRP, hRQ⟩)
    (by
      intro P Q h hp
      exact ⟨h.1 hp.1, h.2 hp.2⟩)).toPFilter

@[simp] theorem mem_parameterRectanglePointFilter (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (x y : FusionReal) (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y) (P : ParameterCompatibleRectangle ε E) :
    P ∈ parameterRectanglePointFilter E hE x y hx hy hxy ↔
      x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val := Iff.rfl

end PolishSpaceBook.LambdaTree
