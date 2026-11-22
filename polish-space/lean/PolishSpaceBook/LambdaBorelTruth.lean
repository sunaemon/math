module

public import PolishSpaceBook.BorelForcingTruth
public import PolishSpaceBook.LambdaGenericFilterConstruction
public import PolishSpaceBook.LambdaHKLSplitting

@[expose] public section

/-!
# Actual Borel truth in the relative compatible product

Mutual saturation restrictions prove the atomic semantics. Explicit countable
dense tests then give truth for actual pairs. This is a Borel-fragment truth
lemma, not analytic/coanalytic absoluteness for Silver's relation.
-/
namespace PolishSpaceBook.LambdaTree
open Set
variable {ε : ℕ → ℕ} {E : Setoid FusionReal}

/-- Compatible relative neighborhoods retain auxiliary-related generic points. -/
theorem parameter_rectangle_neighborhood
    (hE : ProjectedRelation ε E.r)
    {x y : FusionReal} (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y) {A B : Set FusionReal}
    (hA : Projected ε A)
    (hB : Projected ε B) (hxA : x ∈ A) (hyB : y ∈ B) :
    ∃ P : ParameterCompatibleRectangle ε E,
      x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val ∧ P.val.1.val.val ⊆ A ∧ P.val.2.val.val ⊆ B := by
  have hxSat : x ∈ erSaturation E B :=
    (parameter_generics_invariant_agree E hE hx hy hxy
      (projected_erSaturation E hE hB) (erSaturation_invariant E B)).mpr
      (subset_erSaturation E B hyB)
  have hySat : y ∈ erSaturation E A :=
    (parameter_generics_invariant_agree E hE hx hy hxy
      (projected_erSaturation E hE hA) (erSaturation_invariant E A)).mp
      (subset_erSaturation E A hxA)
  let L := parameterCondition ε (A ∩ erSaturation E B)
    (hA.inter (projected_erSaturation E hE hB)) ⟨x, hxA, hxSat⟩
  let R := parameterCondition ε (B ∩ erSaturation E A)
    (hB.inter (projected_erSaturation E hE hA)) ⟨y, hyB, hySat⟩
  have hc : erSaturation E L.val.val = erSaturation E R.val.val := by
    change erSaturation E (A ∩ erSaturation E B) = erSaturation E (B ∩ erSaturation E A)
    rw [erSaturation_inter_saturation, erSaturation_inter_saturation, inter_comm]
  exact ⟨⟨(L, R), hc⟩, ⟨hxA, hxSat⟩, ⟨hyB, hySat⟩, inter_subset_left, inter_subset_left⟩

def parameterRectangleAtoms (U V : ℕ → Set FusionReal) (n : ℕ) :
    Set (ParameterCompatibleRectangle ε E) :=
  {P | P.val.1.val.val ⊆ U n ∧ P.val.2.val.val ⊆ V n}

theorem parameterRectangleAtoms_lower (U V : ℕ → Set FusionReal) (n : ℕ) :
    IsLowerSet (parameterRectangleAtoms (ε := ε) (E := E) U V n) :=
  fun _ _ hqp hp => ⟨fun _ hx => hp.1 (hqp.1 hx), fun _ hy => hp.2 (hqp.2 hy)⟩

theorem parameter_rectangle_atomic_truth
    (hE : ProjectedRelation ε E.r)
    (U V : ℕ → Set FusionReal)
    (hU : ∀ n, Projected ε (U n))
    (hV : ∀ n, Projected ε (V n))
    (x y : FusionReal) (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y) (n : ℕ) :
    (x, y) ∈ U n ×ˢ V n ↔ ∃ P ∈ parameterRectanglePointFilter E hE x y hx hy hxy,
      P ∈ parameterRectangleAtoms U V n := by
  constructor
  · rintro ⟨hxU, hyV⟩
    obtain ⟨P, hxP, hyP, hPU, hPV⟩ :=
      parameter_rectangle_neighborhood hE hx hy hxy (hU n) (hV n) hxU hyV
    exact ⟨P, ⟨hxP, hyP⟩, hPU, hPV⟩
  · rintro ⟨P, ⟨hxP, hyP⟩, hPU, hPV⟩
    exact ⟨hPU hxP, hPV hyP⟩

/-- The left and right analytic decision tests, viewed as restricted rectangles. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: Coordinate decisions and point filters
-/
def parameterRectangleDecisionTests (ε : ℕ → ℕ) (E : Setoid FusionReal) :
    Set (Set (ParameterCompatibleRectangle ε E)) :=
  range (fun A : (parameterAnalyticCatalog ε).Condition =>
    parameterLeftTest (E := E) (parameterDecisionRequirement A)) ∪
  range (fun A : (parameterAnalyticCatalog ε).Condition =>
    parameterRightTest (E := E) (parameterDecisionRequirement A))

theorem parameterRectangleDecisionTests_countable (ε : ℕ → ℕ) (E : Setoid FusionReal) :
    (parameterRectangleDecisionTests ε E).Countable :=
  (countable_range _).union (countable_range _)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    For density of $\mathcal C_0(S)$, start with $A\times B$. If $A\cap S$ is empty, this rectangle already passes.
    Otherwise retain $A\cap S$ as the left coordinate and replace the right coordinate by
    $B\cap\ERSaturation{A\cap S}{E}$. Equality of the original saturations makes this nonempty and restores
    equality of the two new saturations. The right-coordinate argument is symmetric. Every further shrinking
    preserves either decision, and there are only countably many analytic conditions $S$.
-/
theorem parameterRectangleDecisionTests_dense_lower
    (hE : ProjectedRelation ε E.r) :
    ∀ D ∈ parameterRectangleDecisionTests ε E, IsCoinitial D ∧ IsLowerSet D := by
  rintro D (⟨A, rfl⟩ | ⟨A, rfl⟩)
  · exact ⟨parameterLeftTest_dense hE (parameterDecisionRequirement_dense A),
      parameterLeftTest_lower (parameterDecisionRequirement_lower A)⟩
  · exact ⟨parameterRightTest_dense hE (parameterDecisionRequirement_dense A),
      parameterRightTest_lower (parameterDecisionRequirement_lower A)⟩

/-- Actual encounters imply coordinate genericity and auxiliary relatedness. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Meeting these rectangle tests makes each coordinate meet the analytic decision tests of
    §{sec:edst-generic-conditions}. Let $D$ be an invariant $\lDelta^1_1$ set. A rectangle meeting the left decision
    test for $D$ has its left coordinate contained in $D$ or disjoint from $D$. Equal $E$-saturations and
    invariance of $D$ force the same alternative for its right coordinate. Thus $x\in D$ if and only if $y\in D$;
    the empty-set case is automatic. This proves $x\mathrel{\EffectiveClosureER{E}}y$.
-/
theorem parameter_rectangle_decisions_good {x y : FusionReal}
    (hg : ParameterRectangleGeneric ε E (parameterRectangleDecisionTests ε E) x y) :
    ParameterDecisionGeneric ε x ∧ ParameterDecisionGeneric ε y ∧
      (invariantSetoid ε E).r x y := by
  have hL (A : (parameterAnalyticCatalog ε).Condition) := hg _
    (Or.inl ⟨A, rfl⟩)
  have hR (A : (parameterAnalyticCatalog ε).Condition) := hg _
    (Or.inr ⟨A, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro A
    obtain ⟨P, hPD, hxP, _⟩ := hL A
    exact ⟨P.val.1, hPD, hxP⟩
  · intro A
    obtain ⟨P, hPD, _, hyP⟩ := hR A
    exact ⟨P.val.2, hPD, hyP⟩
  · have forward {A : Set FusionReal}
        (hA : Projected ε A)
        (hi : ERInvariant E A) (hxA : x ∈ A) : y ∈ A := by
      let C := parameterCondition ε A hA ⟨x, hxA⟩
      obtain ⟨P, hPC, hxP, hyP⟩ := hL C
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
    exact (forward hA.2 (fun {_ _} h => not_congr (hi h)) hxA) hyA

/-- The larger witness/order-decision family retains the same pointwise consequences. -/
theorem parameter_rectangle_generic_good {x y : FusionReal}
    (hg : ParameterRectangleGeneric ε E (parameterRectangleFilterTests ε E) x y) :
    ParameterDecisionGeneric ε x ∧ ParameterDecisionGeneric ε y ∧
      (invariantSetoid ε E).r x y := by
  apply parameter_rectangle_decisions_good
  rintro D (⟨A, rfl⟩ | ⟨A, rfl⟩)
  · exact hg _ (Or.inl (Or.inl ⟨parameterDecisionRequirement A, Or.inr ⟨A, rfl⟩, rfl⟩))
  · exact hg _ (Or.inl (Or.inr ⟨parameterDecisionRequirement A, Or.inr ⟨A, rfl⟩, rfl⟩))

/-- Pointwise encounters construct an actual order filter without assuming one. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: Coordinate decisions and point filters
-/
theorem parameter_rectangle_decision_generic_filter
    (hE : ProjectedRelation ε E.r) {x y : FusionReal}
    (hg : ParameterRectangleGeneric ε E (parameterRectangleDecisionTests ε E) x y) :
    ∃ G : Order.PFilter (ParameterCompatibleRectangle ε E),
      ∀ P, P ∈ G ↔ x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val := by
  obtain ⟨hx, hy, hxy⟩ := parameter_rectangle_decisions_good hg
  exact ⟨parameterRectanglePointFilter E hE x y hx hy hxy, fun _ => Iff.rfl⟩

def parameterBorelTests (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (U V : ℕ → Set FusionReal) (c : BorelCode) : Set (Set (ParameterCompatibleRectangle ε E)) :=
  parameterRectangleDecisionTests ε E ∪ c.forcingRequirements (parameterRectangleAtoms U V)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: HKL generic-pair lemma
-/
theorem parameterBorelTests_countable (U V : ℕ → Set FusionReal) (c : BorelCode) :
    (parameterBorelTests ε E U V c).Countable :=
  (parameterRectangleDecisionTests_countable ε E).union (c.forcingRequirements_countable _)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: HKL generic-pair lemma
-/
theorem parameterBorelTests_dense_lower
    (hE : ProjectedRelation ε E.r)
    (U V : ℕ → Set FusionReal) (c : BorelCode) :
    ∀ D ∈ parameterBorelTests ε E U V c, IsCoinitial D ∧ IsLowerSet D := by
  rintro D (hD | hD)
  · exact parameterRectangleDecisionTests_dense_lower hE D hD
  · exact c.forcingRequirements_dense_lower _ (parameterRectangleAtoms_lower U V) D hD

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Include all the families $\mathcal C_i(S)$ from the preceding lemma in the Borel truth tests.
    That lemma constructs the filter of all restricted rectangles containing the actual pair and proves that
    its coordinates decide analytic sets and are $\EffectiveClosureER{E}$-related. Applying the same saturation
    restriction to two basic cylinder neighborhoods gives a condition in this filter contained in their rectangle,
    which proves atomic truth. Induction on the Borel code now proves that an actual generic pair belongs to the decoded
    set exactly when some condition of its filter forces membership. For a complement, its decision test chooses
    the negative alternative exactly when child membership fails. For a union, directedness and its decision test
    turn density below a filter condition into a positive child condition in the filter.
-/
/-- Borel truth for actual pairs, with atomic semantics proved above. -/
theorem parameter_borel_truth
    (hE : ProjectedRelation ε E.r)
    (U V : ℕ → Set FusionReal)
    (hU : ∀ n, Projected ε (U n))
    (hV : ∀ n, Projected ε (V n))
    (c : BorelCode) {x y : FusionReal}
    (hg : ParameterRectangleGeneric ε E (parameterBorelTests ε E U V c) x y) :
    (x, y) ∈ c.decode (fun n => U n ×ˢ V n) ↔
      ∃ P : ParameterCompatibleRectangle ε E, x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val ∧
        P ∈ c.forcing (parameterRectangleAtoms U V) := by
  obtain ⟨hx, hy, hxy⟩ := parameter_rectangle_decisions_good (fun D hD => hg D (Or.inl hD))
  obtain ⟨G, hG⟩ := parameter_rectangle_decision_generic_filter hE (fun D hD => hg D (Or.inl hD))
  have hatom (n : ℕ) : (x, y) ∈ U n ×ˢ V n ↔ ∃ P ∈ G, P ∈ parameterRectangleAtoms U V n := by
    simpa only [hG, mem_parameterRectanglePointFilter] using
      (parameter_rectangle_atomic_truth hE U V hU hV x y hx hy hxy n)
  have ht := c.forcing_truth (fun n => U n ×ˢ V n) (parameterRectangleAtoms U V)
    (parameterRectangleAtoms_lower U V) G (x, y) hatom (by
      intro D hD
      obtain ⟨P, hPD, hxP, hyP⟩ := hg D (Or.inr hD)
      exact ⟨P, (hG P).mpr ⟨hxP, hyP⟩, hPD⟩)
  simpa only [hG, exists_prop, and_assoc] using ht

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Consequently an equivalent
    pair meeting this countable family lies in a rectangle all of whose pairs meeting the same family are equivalent.
-/
/-- A true statement holds for all generic pairs in a smaller rectangle. -/
theorem parameter_borel_local_truth
    (hE : ProjectedRelation ε E.r)
    (U V : ℕ → Set FusionReal)
    (hU : ∀ n, Projected ε (U n))
    (hV : ∀ n, Projected ε (V n))
    (c : BorelCode) {x y : FusionReal}
    (hg : ParameterRectangleGeneric ε E (parameterBorelTests ε E U V c) x y)
    (htrue : (x, y) ∈ c.decode (fun n => U n ×ˢ V n)) :
    ∃ P : ParameterCompatibleRectangle ε E, x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val ∧
      ∀ u ∈ P.val.1.val.val, ∀ v ∈ P.val.2.val.val,
        ParameterRectangleGeneric ε E (parameterBorelTests ε E U V c) u v →
          (u, v) ∈ c.decode (fun n => U n ×ˢ V n) := by
  obtain ⟨P, hxP, hyP, hP⟩ := (parameter_borel_truth hE U V hU hV c hg).mp htrue
  exact ⟨P, hxP, hyP, fun u hu v hv hgen =>
    (parameter_borel_truth hE U V hU hV c hgen).mpr ⟨P, hu, hv, hP⟩⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Thus no kernel rectangle has only equivalent pairs meeting any prescribed countable
    family of downward-closed dense tests. Apply this to the Borel truth tests above. If a pair in $H\times H$
    meeting them were equivalent, local truth and a common refinement with $H\times H$ would give just such a
    rectangle. This contradiction proves the lemma with that family as $\mathcal J$.
-/
/-- The Borel truth lemma closes the contradiction for an actual kernel
rectangle. The code is a representation of E, not a splitting assumption. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: HKL generic-pair lemma
-/
theorem parameter_hkl_generic_inequivalent_of_code
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (U V : ℕ → Set FusionReal)
    (hU : ∀ n, Projected ε (U n))
    (hV : ∀ n, Projected ε (V n))
    (c : BorelCode) (hc : c.decode (fun n => U n ×ˢ V n) = {p | E.r p.1 p.2})
    (P : ParameterCompatibleRectangle ε E)
    (hPH : P.val.1.val.val ⊆ equivalenceGapKernel E (invariantSetoid ε E))
    {x y : FusionReal} (hxP : x ∈ P.val.1.val.val) (hyP : y ∈ P.val.2.val.val)
    (hg : ParameterRectangleGeneric ε E (parameterBorelTests ε E U V c) x y) : ¬ E.r x y := by
  intro heq
  have htrue : (x, y) ∈ c.decode (fun n => U n ×ˢ V n) := by rw [hc]; exact heq
  obtain ⟨Q, hxQ, hyQ, hQ⟩ := parameter_borel_local_truth hE U V hU hV c hg htrue
  obtain ⟨hx, hy, hxy⟩ := parameter_rectangle_decisions_good (fun D hD => hg D (Or.inl hD))
  obtain ⟨R, hRP, hRQ, _, _⟩ := parameter_rectangle_common_refinement E hE hx hy hxy
    P Q hxP hyP hxQ hyQ
  apply parameter_hkl_no_equivalent_generic_rectangle ε E hE hneE R
    (fun _ h => hPH (hRP.1 h)) (parameterBorelTests ε E U V c)
    (parameterBorelTests_countable U V c)
    (fun D hD => (parameterBorelTests_dense_lower hE U V c D hD).1)
    (fun D hD => (parameterBorelTests_dense_lower hE U V c D hD).2)
  intro u hu v hv hgen
  have h := hQ u (hRQ.1 hu) v (hRQ.2 hv) hgen
  rw [hc] at h
  exact h

end PolishSpaceBook.LambdaTree
