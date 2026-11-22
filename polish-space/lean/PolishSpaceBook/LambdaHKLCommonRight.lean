module

public import PolishSpaceBook.LambdaGenericTests
public import PolishSpaceBook.LambdaHKLComponents

@[expose] public section

/-!
# The common-right construction in the relative HKL product

Auxiliary-related decision-generic points stay in the required saturation
restrictions. Alternately meet each rectangular dense family for the two
left points, retaining a common right condition. Catalog witness tests give
an actual common right point. This is the construction inside the HKL
contradiction; it does not assert a forcing truth or absoluteness theorem.
-/

namespace PolishSpaceBook.LambdaTree
open Set
variable {ε : ℕ → ℕ} {E : Setoid FusionReal}

namespace ParameterCompatibleRectangle

/-- Keep a prescribed right condition and a specified left point by taking
the left intersection with its saturation. -/
theorem restrict_right_with_point (P : ParameterCompatibleRectangle ε E)
    (hE : ProjectedRelation ε E.r)
    (B : (parameterAnalyticCatalog ε).Condition) (hB : B ≤ P.val.2)
    {x : FusionReal} (hx : x ∈ P.val.1.val.val) (hxs : x ∈ erSaturation E B.val.val) :
    ∃ Q : ParameterCompatibleRectangle ε E, Q ≤ P ∧ Q.val.2 = B ∧ x ∈ Q.val.1.val.val := by
  let A := parameterCondition ε (P.val.1.val.val ∩ erSaturation E B.val.val)
    ((parameterCondition_projected ε P.val.1).inter
      (projected_erSaturation E hE (parameterCondition_projected ε B))) ⟨x, hx, hxs⟩
  have hc : erSaturation E A.val.val = erSaturation E B.val.val := by
    change erSaturation E (P.val.1.val.val ∩ erSaturation E B.val.val) = _
    rw [erSaturation_inter_saturation, P.property]
    exact inter_eq_right.mpr (erSaturation_mono E hB)
  exact ⟨⟨(A, B), hc⟩, ⟨inter_subset_left, hB⟩, rfl, hx, hxs⟩

end ParameterCompatibleRectangle

/-- Two rectangles with the same right coordinate and prescribed left points. -/
abbrev ParameterCommonState (ε : ℕ → ℕ) (E : Setoid FusionReal) (x y : FusionReal) :=
  {p : ParameterCompatibleRectangle ε E × ParameterCompatibleRectangle ε E //
    x ∈ p.1.val.1.val.val ∧ y ∈ p.2.val.1.val.val ∧ p.1.val.2 = p.2.val.2}

namespace ParameterCommonState
variable {x y : FusionReal}

def requirement (D : Set (ParameterCompatibleRectangle ε E)) : Set (ParameterCommonState ε E x y) :=
  {S | S.val.1 ∈ D ∧ S.val.2 ∈ D}

theorem requirement_lower {D : Set (ParameterCompatibleRectangle ε E)} (hD : IsLowerSet D) :
    IsLowerSet (requirement (x := x) (y := y) D) := by
  intro S T hTS hS
  exact ⟨hD hTS.1 hS.1, hD hTS.2 hS.2⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Similarly choose $C\times D\in J_n$ below $A'\times B$ with
    $y\in C$. Finish the stage with
    $$U_{n+1}=A\cap\ERSaturation{D}{E},\qquad U'_{n+1}=C,\qquad V_{n+1}=D.$$
    The invariant-agreement argument again retains $x$, since $y\in\ERSaturation{D}{E}$.
    Both new rectangles are in $J_n$ and have equal coordinate saturations.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For the next dense family $J_n$, genericity of $x$ gives a refinement $A\times B\in J_n$ below
    $U_n\times V_n$ with $x\in A$. Indeed, left projections of such refinements are dense below $U_n$: any
    nonempty analytic subset of $U_n$ can be paired with its saturation restriction in $V_n$ and then refined into
    $J_n$. Put $A'=U'_n\cap\ERSaturation{A}{E}$. The invariant-agreement argument ensures $y\in A'$.
    For the saturation equality, use $\ERSaturation{U'_n}{E}=\ERSaturation{U_n}{E}$ and $A\IncludedIn U_n$ to obtain
    $$\ERSaturation{A'}{E}=\ERSaturation{U'_n}{E}\cap\ERSaturation{A}{E}
    =\ERSaturation{A}{E}=\ERSaturation{B}{E}.$$
    The last equality holds because $A\times B$ is a restricted rectangle.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Thus $x\mathrel E z$ and
    $y\mathrel E z$, proving the claim.
-/
/-- The book's two alternating selections and two saturation restrictions.
The shared right condition is retained exactly at the end of the step. -/
theorem requirement_dense
    (hE : ProjectedRelation ε E.r)
    (J : Set (Set (ParameterCompatibleRectangle ε E)))
    (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y)
    (hxg : ParameterLeftGeneric ε E x J) (hyg : ParameterLeftGeneric ε E y J)
    {D : Set (ParameterCompatibleRectangle ε E)} (hDJ : D ∈ J) (hDl : IsLowerSet D) :
    IsCoinitial (requirement (x := x) (y := y) D) := by
  intro S
  obtain ⟨Q, hQD, hQS, hxQ⟩ := hxg D hDJ S.val.1 S.property.1
  have hxSat : x ∈ erSaturation E Q.val.2.val.val := by
    rw [← Q.property]
    exact subset_erSaturation E _ hxQ
  have hySat : y ∈ erSaturation E Q.val.2.val.val :=
    (parameter_generics_invariant_agree E hE hx hy hxy
      (projected_erSaturation E hE (parameterCondition_projected ε Q.val.2))
      (erSaturation_invariant E _)).mp hxSat
  have hQB : Q.val.2 ≤ S.val.2.val.2 := by rw [← S.property.2.2]; exact hQS.2
  obtain ⟨P', hPS, hPQ, hyP⟩ := S.val.2.restrict_right_with_point hE Q.val.2 hQB
    S.property.2.1 hySat
  obtain ⟨R, hRD, hRP, hyR⟩ := hyg D hDJ P' hyP
  have hySat' : y ∈ erSaturation E R.val.2.val.val := by
    rw [← R.property]
    exact subset_erSaturation E _ hyR
  have hxSat' : x ∈ erSaturation E R.val.2.val.val :=
    (parameter_generics_invariant_agree E hE hx hy hxy
      (projected_erSaturation E hE (parameterCondition_projected ε R.val.2))
      (erSaturation_invariant E _)).mpr hySat'
  have hRQ : R.val.2 ≤ Q.val.2 := by rw [← hPQ]; exact hRP.2
  obtain ⟨R', hRQ', hright, hxR⟩ := Q.restrict_right_with_point hE R.val.2 hRQ hxQ hxSat'
  exact ⟨⟨(R', R), hxR, hyR, hright⟩, ⟨hDl hRQ' hQD, hRD⟩,
    ⟨hRQ'.trans hQS, hRP.trans hPS⟩⟩

end ParameterCommonState

def parameterRightTest (D : Set (parameterAnalyticCatalog ε).Condition) :
    Set (ParameterCompatibleRectangle ε E) := {P | P.val.2 ∈ D}

theorem parameterRightTest_dense
    (hE : ProjectedRelation ε E.r)
    {D : Set (parameterAnalyticCatalog ε).Condition} (hD : IsCoinitial D) :
    IsCoinitial (parameterRightTest (E := E) D) := by
  intro P
  obtain ⟨A, hAD, hAP⟩ := hD P.val.2
  obtain ⟨Q, hQP, hQA⟩ := P.swap.refine_left hE A hAP
  refine ⟨Q.swap, ?_, ⟨hQP.2, hQP.1⟩⟩
  change Q.val.1 ∈ D
  rwa [hQA]

theorem parameterRightTest_lower {D : Set (parameterAnalyticCatalog ε).Condition}
    (hD : IsLowerSet D) : IsLowerSet (parameterRightTest (E := E) D) :=
  fun _ _ h hP => hD h.2 hP

def parameterHKLWitnessTests (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) :=
  J ∪ parameterRightTest '' (parameterAnalyticCatalog ε).requirements

theorem parameterHKLWitnessTests_countable (J : Set (Set (ParameterCompatibleRectangle ε E)))
    (hJ : J.Countable) : (parameterHKLWitnessTests ε E J).Countable :=
  hJ.union ((parameterAnalyticCatalog ε).requirements_countable.image _)

theorem parameterHKLWitnessTests_dense
    (hE : ProjectedRelation ε E.r)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJ : ∀ D ∈ J, IsCoinitial D) :
    ∀ D ∈ parameterHKLWitnessTests ε E J, IsCoinitial D := by
  rintro D (hD | ⟨R, hR, rfl⟩)
  · exact hJ D hD
  · exact parameterRightTest_dense hE ((parameterAnalyticCatalog ε).requirements_dense_lower R hR).1

theorem parameterHKLWitnessTests_lower
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJ : ∀ D ∈ J, IsLowerSet D) :
    ∀ D ∈ parameterHKLWitnessTests ε E J, IsLowerSet D := by
  rintro D (hD | ⟨R, hR, rfl⟩)
  · exact hJ D hD
  · exact parameterRightTest_lower ((parameterAnalyticCatalog ε).requirements_dense_lower R hR).2

def ParameterRectangleGeneric (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (x y : FusionReal) : Prop :=
  ∀ D ∈ J, ∃ P ∈ D, x ∈ P.val.1.val.val ∧ y ∈ P.val.2.val.val

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Include the analytic-condition witness requirements in this construction.
    Their common right limit $z$ makes both $(x,z)$ and $(y,z)$ generic below $U\times V$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Suppose a rectangle $U\times V$ below $H\times H$ has only equivalent pairs meeting a fixed countable family of
    downward-closed dense tests. We claim that individually generic $x,y\in U$ with
    $x\mathrel{\EffectiveClosureER{E}}y$ must then be $E$-equivalent, with the following individual tests.
    First enlarge the rectangular family by the lifts of the right-coordinate witness requirements from
    analytic-condition fusion. This countable family is still downward closed and dense. For each restricted
    rectangle $P=C\times D_0$ and each member $J$ of this enlarged family, put
    $$\mathcal P(P,J):=\{C'\in\GHConditions{1}:\exists D'\in\GHConditions{1}
     \ (C'\times D'\le P\ \land\ C'\times D'\in J)\}.$$
    This is dense below $C$: retain a prescribed left refinement, restrict the right coordinate by its saturation,
    and refine the resulting rectangle into $J$. Extend it to the whole coordinate order by allowing conditions
    disjoint from $C$ or contained in some member of $\mathcal P(P,J)$. Intersecting with $C$ proves that this
    extension is dense; a point of $C$ meeting it must take the second alternative. These extensions, together
    with all analytic decision tests, form a countable family $\mathcal F$ because the restricted condition
    order and the enlarged rectangular family are countable. Require $x,y$ to meet every member of $\mathcal F$.
    Enumerate the enlarged rectangular tests as
    $\Sequence{J_n}{n\in\omega}$. Construct two sequences of nested rectangles $U_n\times V_n$ and $U'_n\times V_n$, whose
    left conditions contain $x,y$ respectively and whose saturations agree.
-/
/-- The common right limit is an actual member of every chosen right
condition. Both pairs meet all prescribed rectangle tests below the start. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Start both sequences with $U\times V$.
-/
theorem parameter_hkl_common_right (P : ParameterCompatibleRectangle ε E)
    (hE : ProjectedRelation ε E.r)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJc : J.Countable)
    (hJl : ∀ D ∈ J, IsLowerSet D) {x y : FusionReal}
    (hxP : x ∈ P.val.1.val.val) (hyP : y ∈ P.val.1.val.val)
    (hx : ParameterDecisionGeneric ε x) (hy : ParameterDecisionGeneric ε y)
    (hxy : (invariantSetoid ε E).r x y)
    (hxg : ParameterLeftGeneric ε E x (parameterHKLWitnessTests ε E J))
    (hyg : ParameterLeftGeneric ε E y (parameterHKLWitnessTests ε E J)) :
    ∃ z ∈ P.val.2.val.val,
      ParameterRectangleGeneric ε E J x z ∧ ParameterRectangleGeneric ε E J y z := by
  let F := parameterHKLWitnessTests ε E J
  let test := ParameterCommonState.requirement (ε := ε) (E := E) (x := x) (y := y)
  have hc : (test '' F).Countable := (parameterHKLWitnessTests_countable J hJc).image test
  have hd : ∀ D ∈ test '' F, IsCoinitial D := by
    rintro _ ⟨D, hD, rfl⟩
    exact ParameterCommonState.requirement_dense hE F hx hy hxy hxg hyg hD
      (parameterHKLWitnessTests_lower J hJl D hD)
  have hl : ∀ D ∈ test '' F, IsLowerSet D := by
    rintro _ ⟨D, hD, rfl⟩
    exact ParameterCommonState.requirement_lower (parameterHKLWitnessTests_lower J hJl D hD)
  let initial : ParameterCommonState ε E x y := ⟨(P, P), hxP, hyP, rfl⟩
  obtain ⟨S, hS, hS0, hmeet⟩ := countable_dense_sequence (test '' F) hc hd hl initial
  let B n := (S n).val.1.val.2
  have hB : Antitone B := fun i j hij => (hS hij).1.2
  obtain ⟨z, hz, _⟩ := (parameterAnalyticCatalog ε).fusion B hB (by
    intro D hD
    obtain ⟨n, _, hn⟩ := hmeet (test (parameterRightTest D))
      ⟨parameterRightTest D, Or.inr ⟨D, hD, rfl⟩, rfl⟩ 0
    exact ⟨n, hn.1⟩)
  refine ⟨z, hS0.1.2 (hz 0), ?_, ?_⟩
  · intro D hD
    obtain ⟨n, _, hn⟩ := hmeet (test D) ⟨D, Or.inl hD, rfl⟩ 0
    exact ⟨(S n).val.1, hn.1, (S n).property.1, hz n⟩
  · intro D hD
    obtain ⟨n, _, hn⟩ := hmeet (test D) ⟨D, Or.inl hD, rfl⟩ 0
    exact ⟨(S n).val.2, hn.2, (S n).property.2.1, (S n).property.2.2 ▸ hz n⟩

end PolishSpaceBook.LambdaTree
