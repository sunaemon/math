module

public import PolishSpaceBook.LambdaRectangleFilters

@[expose] public section

/-!
# Countable tests constructing actual generic filters

Coordinate witness and decision tests, together with order decisions, form
one countable lower dense family. A decreasing sequence generates a genuine
order filter meeting these tests and any additional countable dense family.
The filter is then recovered from its actual pair of points. This supplies
the filter/point infrastructure, but does not construct a set-theoretic generic
extension or prove analytic/coanalytic absoluteness for that extension.
-/

namespace PolishSpaceBook.LambdaTree
open Set

/-- Upward closure of a decreasing sequence, as mathlib's order filter. -/
def pfilterOfAntitone {P : Type*} [Preorder P] (q : ℕ → P) (hq : Antitone q) : Order.PFilter P :=
  (Order.IsPFilter.of_def (F := {p | ∃ n, q n ≤ p})
    ⟨q 0, 0, le_rfl⟩
    (by
      rintro p ⟨n, hn⟩ r ⟨m, hm⟩
      exact ⟨q (max n m), ⟨max n m, le_rfl⟩,
        (hq (le_max_left n m)).trans hn, (hq (le_max_right n m)).trans hm⟩)
    (by
      rintro p r hpr ⟨n, hn⟩
      exact ⟨n, hn.trans hpr⟩)).toPFilter

@[simp] theorem mem_pfilterOfAntitone {P : Type*} [Preorder P]
    (q : ℕ → P) (hq : Antitone q) (p : P) : p ∈ pfilterOfAntitone q hq ↔ ∃ n, q n ≤ p := Iff.rfl

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For each witness requirement on one coordinate, take the rectangles whose corresponding coordinate
    belongs to that requirement. These families are downward-closed. They are dense because a prescribed
    coordinate refinement can be retained exactly while the other coordinate is restricted by its saturation.
    Adjoin these countably many families to $\mathcal J$, and enumerate the result as $\Sequence{D_n}{n\in\omega}$.
    Starting from $P_0$, choose $P_{n+1}\le P_n$ in $D_n$. The upward closure of this decreasing sequence is a
    filter: any two of its members have a common stronger member farther along the sequence.

    Apply analytic-condition fusion separately to the two coordinate sequences. This gives unique points
    $x,y$ belonging to every chosen coordinate condition. Hence $(x,y)$ belongs to every rectangle of the
    filter, including those outside the sequence. Conversely, any pair belonging to every filter member
    belongs to every chosen rectangle, so coordinate uniqueness identifies it with $(x,y)$.
    For each $D_n$, the rectangle $P_{n+1}$ witnesses the required encounter.
    The sequence is chosen using density; its coordinate presentations retain the fixed parameter through
    the intersection and saturation programs already constructed.
    \end{proof}
-/
theorem pfilter_meeting_countable {P : Type*} [Preorder P] (F : Set (Set P))
    (hFc : F.Countable) (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D) (p : P) :
    ∃ G : Order.PFilter P, p ∈ G ∧ ∀ D ∈ F, ∃ q ∈ G, q ∈ D := by
  obtain ⟨q, hq, hq0, hmeet⟩ := countable_dense_sequence F hFc hFd hFl p
  refine ⟨pfilterOfAntitone q hq, ⟨0, hq0⟩, ?_⟩
  intro D hD
  obtain ⟨n, _, hn⟩ := hmeet D hD 0
  exact ⟨q n, ⟨n, le_rfl⟩, hn⟩

def parameterPointFilterTests (ε : ℕ → ℕ) : Set (Set (parameterAnalyticCatalog ε).Condition) :=
  (parameterAnalyticCatalog ε).requirements ∪ range parameterDecisionRequirement

theorem parameterPointFilterTests_countable (ε : ℕ → ℕ) : (parameterPointFilterTests ε).Countable :=
  (parameterAnalyticCatalog ε).requirements_countable.union (countable_range _)

theorem parameterPointFilterTests_dense_lower (ε : ℕ → ℕ) :
    ∀ D ∈ parameterPointFilterTests ε, IsCoinitial D ∧ IsLowerSet D := by
  rintro D (hD | ⟨A, rfl⟩)
  · exact (parameterAnalyticCatalog ε).requirements_dense_lower D hD
  · exact ⟨parameterDecisionRequirement_dense A, parameterDecisionRequirement_lower A⟩

def parameterRectangleFilterTests (ε : ℕ → ℕ) (E : Setoid FusionReal) :
    Set (Set (ParameterCompatibleRectangle ε E)) :=
  (parameterLeftTest '' parameterPointFilterTests ε ∪ parameterRightTest '' parameterPointFilterTests ε) ∪
    range orderDecisionRequirement

theorem parameterRectangleFilterTests_countable (ε : ℕ → ℕ) (E : Setoid FusionReal) :
    (parameterRectangleFilterTests ε E).Countable :=
  (((parameterPointFilterTests_countable ε).image _).union
    ((parameterPointFilterTests_countable ε).image _)).union (countable_range _)

theorem parameterRectangleFilterTests_dense_lower (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r) :
    ∀ D ∈ parameterRectangleFilterTests ε E, IsCoinitial D ∧ IsLowerSet D := by
  rintro D ((⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩) | ⟨P, rfl⟩)
  · have h := parameterPointFilterTests_dense_lower ε A hA
    exact ⟨parameterLeftTest_dense hE h.1, parameterLeftTest_lower h.2⟩
  · have h := parameterPointFilterTests_dense_lower ε A hA
    exact ⟨parameterRightTest_dense hE h.1, parameterRightTest_lower h.2⟩
  · exact ⟨orderDecisionRequirement_dense P, orderDecisionRequirement_lower P⟩

/-- All filter/point correspondences follow from this one explicit countable
family; there is no assumption that a filter has a real already assigned. -/
theorem parameter_rectangle_filter_actual_pair (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (G : Order.PFilter (ParameterCompatibleRectangle ε E))
    (hG : ∀ D ∈ parameterRectangleFilterTests ε E, ∃ P ∈ G, P ∈ D) :
    ∃ x y, ∃ hx : ParameterDecisionGeneric ε x, ∃ hy : ParameterDecisionGeneric ε y,
      ∃ hxy : (invariantSetoid ε E).r x y,
        G = parameterRectanglePointFilter E hE x y hx hy hxy := by
  have hL : ∀ D ∈ parameterPointFilterTests ε, ∃ P ∈ G, P ∈ parameterLeftTest D :=
    fun D hD => hG _ (Or.inl (Or.inl ⟨D, hD, rfl⟩))
  have hR : ∀ D ∈ parameterPointFilterTests ε, ∃ P ∈ G, P ∈ parameterRightTest D :=
    fun D hD => hG _ (Or.inl (Or.inr ⟨D, hD, rfl⟩))
  obtain ⟨p, hp, _⟩ := parameter_rectangle_filter_fusion G
    (fun D hD => hL D (Or.inl hD)) (fun D hD => hR D (Or.inl hD))
  have hLd : ∀ A, ∃ P ∈ G, P ∈ parameterLeftTest (parameterDecisionRequirement A) :=
    fun A => hL _ (Or.inr ⟨A, rfl⟩)
  have hRd : ∀ A, ∃ P ∈ G, P ∈ parameterRightTest (parameterDecisionRequirement A) :=
    fun A => hR _ (Or.inr ⟨A, rfl⟩)
  obtain ⟨hx, hy⟩ := parameter_rectangle_filter_coordinate_generics G p.1 p.2 hp hLd hRd
  have hxy := parameter_rectangle_filter_auxiliary_related G p.1 p.2 hp hLd
  exact ⟨p.1, p.2, hx, hy, hxy, parameter_rectangle_filter_determined_by_point hE G
    p.1 p.2 hx hy hxy hp (fun A => hG _ (Or.inr ⟨A, rfl⟩))⟩

/-- Every starting rectangle admits an actual compatible-product generic
filter and pair for any prescribed countable collection of lower dense tests. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For each witness requirement on one coordinate, take the rectangles whose corresponding coordinate
    belongs to that requirement. These families are downward-closed. They are dense because a prescribed
    coordinate refinement can be retained exactly while the other coordinate is restricted by its saturation.
    Adjoin these countably many families to $\mathcal J$, and enumerate the result as $\Sequence{D_n}{n\in\omega}$.
    Starting from $P_0$, choose $P_{n+1}\le P_n$ in $D_n$. The upward closure of this decreasing sequence is a
    filter: any two of its members have a common stronger member farther along the sequence.

    Apply analytic-condition fusion separately to the two coordinate sequences. This gives unique points
    $x,y$ belonging to every chosen coordinate condition. Hence $(x,y)$ belongs to every rectangle of the
    filter, including those outside the sequence. Conversely, any pair belonging to every filter member
    belongs to every chosen rectangle, so coordinate uniqueness identifies it with $(x,y)$.
    For each $D_n$, the rectangle $P_{n+1}$ witnesses the required encounter.
    The sequence is chosen using density; its coordinate presentations retain the fixed parameter through
    the intersection and saturation programs already constructed.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: proposition
  title: Actual pairs in the restricted product
-/
theorem parameter_rectangle_generic_filter_exists (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (P : ParameterCompatibleRectangle ε E)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D) :
    ∃ (G : Order.PFilter (ParameterCompatibleRectangle ε E)) (x y : FusionReal),
      P ∈ G ∧ (∀ D ∈ J, ∃ Q ∈ G, Q ∈ D) ∧
      x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val ∧
      ∃ hx : ParameterDecisionGeneric ε x, ∃ hy : ParameterDecisionGeneric ε y,
        ∃ hxy : (invariantSetoid ε E).r x y,
          G = parameterRectanglePointFilter E hE x y hx hy hxy := by
  let F := parameterRectangleFilterTests ε E ∪ J
  have hc : F.Countable := (parameterRectangleFilterTests_countable ε E).union hJc
  have hd : ∀ D ∈ F, IsCoinitial D := by
    rintro D (hD | hD)
    · exact (parameterRectangleFilterTests_dense_lower ε E hE D hD).1
    · exact hJd D hD
  have hl : ∀ D ∈ F, IsLowerSet D := by
    rintro D (hD | hD)
    · exact (parameterRectangleFilterTests_dense_lower ε E hE D hD).2
    · exact hJl D hD
  obtain ⟨G, hPG, hG⟩ := pfilter_meeting_countable F hc hd hl P
  obtain ⟨x, y, hx, hy, hxy, heq⟩ := parameter_rectangle_filter_actual_pair ε E hE G
    (fun D hD => hG D (Or.inl hD))
  have hp : x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val := by
    rw [heq] at hPG
    exact hPG
  exact ⟨G, x, y, hPG, fun D hD => hG D (Or.inr hD), hp.1, hp.2, hx, hy, hxy, heq⟩

end PolishSpaceBook.LambdaTree
