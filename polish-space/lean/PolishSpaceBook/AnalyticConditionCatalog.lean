module

public import PolishSpaceBook.SilverFusion

@[expose] public section

/-!
# A restricted catalog of analytic conditions

The full boldface analytic-condition order contains every singleton. Its
lower dense sets therefore contain every singleton, so it cannot model the
lightface forcing used in Silver splitting. This module restricts conditions
to an explicit countable catalog with closed presentations and the precise
prefix-refinement closure needed for fusion. It does not claim to construct
the effective catalog or prove correctness of lightface codes.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

/-- A singleton is an atom in the full boldface condition order. It is not
automatically a condition in a restricted effective catalog. -/
def boldfaceSingletonCondition (x : FusionReal) : AnalyticCondition FusionReal :=
  ⟨{x}, isClosed_singleton.measurableSet.analyticSet, Set.singleton_nonempty x⟩

theorem condition_eq_of_le_singleton (x : FusionReal) (P : AnalyticCondition FusionReal)
    (hP : P ≤ boldfaceSingletonCondition x) : P = boldfaceSingletonCondition x := by
  apply Subtype.ext
  exact Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨P.property.2, fun _ hx => hP hx⟩

/-- Every dense family in the full product order contains each singleton
pair. Consequently that order cannot supply Silver's generic-pair splitting. -/
theorem full_product_dense_contains_singletons
    (D : Set (AnalyticCondition FusionReal × AnalyticCondition FusionReal)) (hD : IsCoinitial D)
    (x y : FusionReal) : (boldfaceSingletonCondition x, boldfaceSingletonCondition y) ∈ D := by
  obtain ⟨⟨P, Q⟩, hPQ, hle⟩ := hD (boldfaceSingletonCondition x, boldfaceSingletonCondition y)
  rwa [condition_eq_of_le_singleton x P hle.1, condition_eq_of_le_singleton y Q hle.2] at hPQ

theorem not_silverPairSplitting_full_order (E : Setoid FusionReal) (Ω : Set FusionReal)
    (hΩ : Ω.Nonempty)
    (J : Set (Set (AnalyticCondition FusionReal × AnalyticCondition FusionReal)))
    (hJd : ∀ D ∈ J, IsCoinitial D) : ¬ SilverPairSplitting E Ω J := by
  intro hsplit
  obtain ⟨x, hx⟩ := hΩ
  have hsub : (boldfaceSingletonCondition x).val ⊆ Ω := by
    intro y hy
    exact (Set.mem_singleton_iff.mp hy) ▸ hx
  have hnot := hsplit (fun _ => (boldfaceSingletonCondition x, boldfaceSingletonCondition x))
    (fun _ _ _ => le_rfl) (fun _ => ⟨hsub, hsub⟩)
    (fun D hD => ⟨0, full_product_dense_contains_singletons D (hJd D hD) x x⟩)
    x x (fun _ => rfl) (fun _ => rfl)
  exact hnot (E.refl x)

/-- Only catalogued nonempty analytic sets are forcing conditions. The two
refinement operations are the intersections actually used by witness fusion;
arbitrary analytic refinements and arbitrary singletons are not required. -/
structure AnalyticConditionCatalog where
  conditions : Set (AnalyticCondition FusionReal)
  countable : conditions.Countable
  closed : ℕ → Set (FusionReal × FusionReal)
  isClosed : ∀ i, IsClosed (closed i)
  presentation : ∀ P ∈ conditions, ∃ i, P.val = Prod.fst '' closed i
  witness_refine : ∀ P ∈ conditions, ∀ i n (s t : FusionPrefix n),
    (P.val ∩ witnessProjection (closed i) s t).Nonempty →
    ∃ Q ∈ conditions, Q ≤ P ∧ Q.val ⊆ witnessProjection (closed i) s t
  cylinder_refine : ∀ P ∈ conditions, ∀ n (s : FusionPrefix n),
    (P.val ∩ fusionCylinder s).Nonempty →
    ∃ Q ∈ conditions, Q ≤ P ∧ Q.val ⊆ fusionCylinder s

namespace AnalyticConditionCatalog

abbrev Condition (C : AnalyticConditionCatalog) := {P : AnalyticCondition FusionReal // P ∈ C.conditions}

instance (C : AnalyticConditionCatalog) : Countable C.Condition := C.countable.to_subtype

/-- The same witness tests, interpreted inside the catalog's order. -/
def requirements (C : AnalyticConditionCatalog) : Set (Set C.Condition) :=
  (fun D => Subtype.val ⁻¹' D) '' analyticFusionRequirements C.closed

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Analytic-condition fusion
-/
theorem requirements_countable (C : AnalyticConditionCatalog) : C.requirements.Countable :=
  (analyticFusionRequirements_countable C.closed).image _

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Identify a finite product of Baire spaces with Baire space. For every recursive closed
    $K\IncludedIn X^d\times\BaireSpace$ and finite point and witness prefixes $s,t$, write
    $K_{s,t}=K\cap(\cyl{s}\times\cyl{t})$ and include the dense requirement
    $$
    P\cap\pi_0(K_{s,t})=\emptyset
    \quad\text{or}\quad
    P\IncludedIn\pi_0(K_{s\concat(i),t\concat(j)})\text{ for some }i,j.
-/
theorem witness_coinitial (C : AnalyticConditionCatalog) (i n : ℕ) (s t : FusionPrefix n) :
    IsCoinitial {P : C.Condition | P.val ∈ witnessRequirement (C.closed i) s t} := by
  classical
  intro P
  by_cases hd : Disjoint P.val.val (witnessProjection (C.closed i) s t)
  · exact ⟨P, Or.inl hd, le_rfl⟩
  · obtain ⟨x, hxP, hxs, y, hyt, hxy⟩ := Set.not_disjoint_iff.mp hd
    have hext {u : FusionPrefix n} {z : FusionReal} (hz : z ∈ fusionCylinder u) :
        z ∈ fusionCylinder (Fin.snoc u (z n)) := by
      intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simpa using hz k
    obtain ⟨Q, hQC, hQP, hQ⟩ := C.witness_refine P.val P.property i (n + 1)
      (Fin.snoc s (x n)) (Fin.snoc t (y n)) ⟨x, hxP, hext hxs, y, hext hyt, hxy⟩
    exact ⟨⟨Q, hQC⟩, Or.inr ⟨x n, y n, hQ⟩, hQP⟩

theorem small_coinitial (C : AnalyticConditionCatalog) (n : ℕ) :
    IsCoinitial {P : C.Condition | P.val ∈ smallPrefixRequirement n} := by
  intro P
  obtain ⟨x, hx⟩ := P.val.property.2
  let s : FusionPrefix n := fun i => x i.val
  obtain ⟨Q, hQC, hQP, hQ⟩ := C.cylinder_refine P.val P.property n s ⟨x, hx, fun _ => rfl⟩
  refine ⟨⟨Q, hQC⟩, ?_, hQP⟩
  intro y hy z hz k hk
  exact (hQ hy ⟨k, hk⟩).trans (hQ hz ⟨k, hk⟩).symm

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Analytic-condition fusion
-/
theorem requirements_dense_lower (C : AnalyticConditionCatalog) :
    ∀ D ∈ C.requirements, IsCoinitial D ∧ IsLowerSet D := by
  rintro _ ⟨D, hD, rfl⟩
  refine ⟨?_, fun _ _ hpq hq => (analyticFusionRequirements_dense_lower C.closed C.isClosed D hD).2 hpq hq⟩
  rcases hD with ⟨n, rfl⟩ | ⟨⟨i, n, s, t⟩, rfl⟩
  · exact C.small_coinitial n
  · exact C.witness_coinitial i n s t

/-- The catalog supplies a closed presentation for every chosen condition,
so fusion no longer needs a new presentation hypothesis for a constructed
sequence. Only encounters with the catalog's countable dense family remain. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Analytic-condition fusion
-/
theorem fusion (C : AnalyticConditionCatalog) (P : ℕ → C.Condition) (hP : Antitone P)
    (hmeet : ∀ D ∈ C.requirements, ∃ n, P n ∈ D) :
    ∃! x : FusionReal, ∀ n, x ∈ (P n).val.val := by
  apply analytic_fusion_of_meets_countable_requirements C.closed C.isClosed
    (fun n => (P n).val) (fun i j hij => hP hij)
    (fun n => C.presentation _ (P n).property)
  intro D hD
  exact hmeet (Subtype.val ⁻¹' D) ⟨D, hD, rfl⟩

end AnalyticConditionCatalog

/-- A descending sequence meets every member of a countable lower dense
family cofinally. This is an order-theoretic construction; it does not
identify the catalog with all analytic sets. -/
theorem countable_dense_sequence {P : Type*} [Preorder P]
    (F : Set (Set P)) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D) (p : P) :
    ∃ Q : ℕ → P, Antitone Q ∧ Q 0 ≤ p ∧
      ∀ D ∈ F, ∀ N, ∃ n, N ≤ n ∧ Q n ∈ D := by
  obtain ⟨D, _, hDd, _, hDF⟩ := countable_dense_schedule F hFc hFd hFl
  choose next hnextD hnextle using fun n q => hDd n q
  let Q : ℕ → P := fun n => Nat.rec (next 0 p) (fun n q => next (n + 1) q) n
  have hQ : Antitone Q := antitone_nat_of_succ_le (fun n => hnextle (n + 1) (Q n))
  have hQD n : Q n ∈ D n := by
    cases n with
    | zero => exact hnextD 0 p
    | succ n => exact hnextD (n + 1) (Q n)
  refine ⟨Q, hQ, hnextle 0 p, ?_⟩
  intro A hA N
  obtain ⟨M, hM⟩ := hDF A hA
  exact ⟨max M N, le_max_right _ _, hM _ (le_max_left _ _) (hQD _)⟩

/-- Add witness fusion to any countable lower dense family in the catalog.
The resulting actual point lies in the starting condition and in a chosen
condition from every requested family. -/
theorem catalog_generic_point (C : AnalyticConditionCatalog)
    (F : Set (Set C.Condition)) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D) (p : C.Condition) :
    ∃ x ∈ p.val.val, ∀ D ∈ F, ∃ q ∈ D, x ∈ q.val.val := by
  have hd : ∀ D ∈ F ∪ C.requirements, IsCoinitial D := by
    intro D hD
    rcases hD with hD | hD
    · exact hFd D hD
    · exact (C.requirements_dense_lower D hD).1
  have hl : ∀ D ∈ F ∪ C.requirements, IsLowerSet D := by
    intro D hD
    rcases hD with hD | hD
    · exact hFl D hD
    · exact (C.requirements_dense_lower D hD).2
  obtain ⟨Q, hQ, hQp, hmeet⟩ := countable_dense_sequence (F ∪ C.requirements)
    (hFc.union C.requirements_countable) hd hl p
  obtain ⟨x, hx, _⟩ := C.fusion Q hQ (fun D hD => by
    obtain ⟨n, _, hn⟩ := hmeet D (Or.inr hD) 0
    exact ⟨n, hn⟩)
  refine ⟨x, hQp (hx 0), ?_⟩
  intro D hD
  obtain ⟨n, _, hn⟩ := hmeet D (Or.inl hD) 0
  exact ⟨Q n, hn, hx n⟩

/-- A fixed starting condition defines the local forcing order. -/
abbrev CatalogBelow (C : AnalyticConditionCatalog) (B : C.Condition) := {Q : C.Condition // Q ≤ B}

/-- Local dense families may be met without leaving the initial condition.
Global witness tests restrict to dense tests on this local order. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Add the witness and shrinking requirements from the analytic-condition fusion lemma, restricting them
    to the order below $A$. They remain dense there: refining a condition already below $A$ stays below it.
    The enlarged family is countable. Enumerate its members and recursively refine the preceding condition
    to meet the next member, starting below $A$. The sequence is decreasing; lower closure preserves every
    requirement after it has been met. Witness fusion gives its unique common point $x$, which lies in
    $A$ and in the chosen condition from each original dense set. The refinement choices need not be
    computable. The conclusion is actual membership in the conditions, not just in their closures.
    \end{proof}
-/
theorem catalog_generic_point_below (C : AnalyticConditionCatalog) (B : C.Condition)
    (F : Set (Set (CatalogBelow C B))) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D) :
    ∃ x ∈ B.val.val, ∀ D ∈ F, ∃ q ∈ D, x ∈ q.val.val.val := by
  let W : Set (Set (CatalogBelow C B)) := (fun D => Subtype.val ⁻¹' D) '' C.requirements
  have hWc : W.Countable := C.requirements_countable.image _
  have hWdl : ∀ D ∈ W, IsCoinitial D ∧ IsLowerSet D := by
    rintro _ ⟨D, hD, rfl⟩
    have hdl := C.requirements_dense_lower D hD
    constructor
    · intro p
      obtain ⟨q, hqD, hqp⟩ := hdl.1 p.val
      exact ⟨⟨q, hqp.trans p.property⟩, hqD, hqp⟩
    · intro p q hpq hq
      exact hdl.2 hpq hq
  have hd : ∀ D ∈ F ∪ W, IsCoinitial D := by
    intro D hD
    rcases hD with hD | hD
    · exact hFd D hD
    · exact (hWdl D hD).1
  have hl : ∀ D ∈ F ∪ W, IsLowerSet D := by
    intro D hD
    rcases hD with hD | hD
    · exact hFl D hD
    · exact (hWdl D hD).2
  obtain ⟨Q, hQ, _, hmeet⟩ := countable_dense_sequence (F ∪ W)
    (hFc.union hWc) hd hl (⟨B, le_rfl⟩ : CatalogBelow C B)
  obtain ⟨x, hx, _⟩ := C.fusion (fun n => (Q n).val) (fun i j hij => hQ hij) (by
    intro D hD
    obtain ⟨n, _, hn⟩ := hmeet (Subtype.val ⁻¹' D) (Or.inr ⟨D, hD, rfl⟩) 0
    exact ⟨n, hn⟩)
  refine ⟨x, (Q 0).property (hx 0), ?_⟩
  intro D hD
  obtain ⟨n, _, hn⟩ := hmeet D (Or.inl hD) 0
  exact ⟨Q n, hn, hx n⟩

/-- Left projections of product refinements below a rectangle. -/
def catalogLeftProjection (C : AnalyticConditionCatalog) (A B : C.Condition)
    (D : Set (C.Condition × C.Condition)) : Set C.Condition :=
  {P | P ≤ A ∧ ∃ Q ≤ B, (P, Q) ∈ D}

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For $D\in\mathcal J$ and each nonempty analytic $B'\IncludedIn B$, put
    $$\mathcal L(D,B'):=\{C\in\GHConditions{1}:C\IncludedIn A,\quad
     \exists V\in\GHConditions{1}\ (V\IncludedIn B'\ \land\ C\times V\in D)\}.$$
    This family is dense below $A$: refine any rectangle $C_0\times B'$ into $D$ and take its left coordinate.
    It is downward closed because $D$ is.
-/
/-- Product density gives density of the left projection below the left
condition. All witnesses remain in the restricted catalog. -/
theorem catalogLeftProjection_coinitial (C : AnalyticConditionCatalog) (A B : C.Condition)
    (D : Set (C.Condition × C.Condition)) (hD : IsCoinitial D) :
    IsCoinitial {P : CatalogBelow C A | P.val ∈ catalogLeftProjection C A B D} := by
  intro P
  obtain ⟨⟨U, V⟩, hUV, hle⟩ := hD (P.val, B)
  exact ⟨⟨U, hle.1.trans P.property⟩, ⟨hle.1.trans P.property, V, hle.2, hUV⟩, hle.1⟩

/-- Right conditions that can be paired with a left condition containing x. -/
def catalogAdmissibleRight (C : AnalyticConditionCatalog) (A : C.Condition) (x : FusionReal)
    (D : Set (C.Condition × C.Condition)) : Set C.Condition :=
  {Q | ∃ P ≤ A, x ∈ P.val.val ∧ (P, Q) ∈ D}

theorem catalogAdmissibleRight_lower (C : AnalyticConditionCatalog) (A : C.Condition)
    (x : FusionReal) {D : Set (C.Condition × C.Condition)} (hD : IsLowerSet D) :
    IsLowerSet (catalogAdmissibleRight C A x D) := by
  rintro P Q hPQ ⟨U, hUA, hxU, hUQ⟩
  have h : (U, Q) ∈ D := hD (show (U, Q) ≤ (U, P) from ⟨le_rfl, hPQ⟩) hUQ
  exact ⟨U, hUA, hxU, h⟩

/-- The precise left-point genericity tests needed to obtain local right
 density. Quantification is over catalog conditions, not arbitrary sets. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Here individual genericity means meeting the following specified family of dense tests below $A$.
-/
def CatalogLeftGeneric (C : AnalyticConditionCatalog) (A B : C.Condition) (x : FusionReal)
    (J : Set (Set (C.Condition × C.Condition))) : Prop :=
  ∀ D ∈ J, ∀ Q ≤ B, ∃ P ∈ catalogLeftProjection C A Q D, x ∈ P.val.val

theorem catalogAdmissibleRight_coinitial (C : AnalyticConditionCatalog) (A B : C.Condition)
    (x : FusionReal) (J : Set (Set (C.Condition × C.Condition)))
    (hx : CatalogLeftGeneric C A B x J) {D : Set (C.Condition × C.Condition)} (hD : D ∈ J) :
    IsCoinitial {Q : CatalogBelow C B | Q.val ∈ catalogAdmissibleRight C A x D} := by
  intro Q
  obtain ⟨P, ⟨hPA, R, hRQ, hPR⟩, hxP⟩ := hx D hD Q.val Q.property
  exact ⟨⟨R, hRQ.trans Q.property⟩, ⟨P, hPA, hxP, hPR⟩, hRQ⟩

/-- There are only countably many relevant left-projection tests because
both the product families and the catalog of right conditions are countable. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Let $\mathcal F$ consist of all these families. It is countable,
    since both the analytic condition order and $\mathcal J$ are countable.
-/
theorem catalog_left_generic_exists (C : AnalyticConditionCatalog) (A B : C.Condition)
    (J : Set (Set (C.Condition × C.Condition))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D) :
    ∃ x ∈ A.val.val, CatalogLeftGeneric C A B x J := by
  let : Countable J := hJc.to_subtype
  let test (p : J × CatalogBelow C B) : Set (CatalogBelow C A) :=
    {P | P.val ∈ catalogLeftProjection C A p.2.val p.1.val}
  have hc : (Set.range test).Countable := Set.countable_range test
  have hd : ∀ D ∈ Set.range test, IsCoinitial D := by
    rintro _ ⟨⟨D, Q⟩, rfl⟩
    exact catalogLeftProjection_coinitial C A Q.val D.val (hJd D.val D.property)
  have hl : ∀ D ∈ Set.range test, IsLowerSet D := by
    rintro _ ⟨⟨D, Q⟩, rfl⟩ P R hRP ⟨hPA, U, hUQ, hPU⟩
    exact ⟨R.property, U, hUQ, hJl D.val D.property
      (show (R.val, U) ≤ (P.val, U) from ⟨hRP, le_rfl⟩) hPU⟩
  obtain ⟨x, hxA, hx⟩ := catalog_generic_point_below C A (Set.range test) hc hd hl
  refine ⟨x, hxA, ?_⟩
  intro D hD Q hQB
  obtain ⟨P, hP, hxP⟩ := hx (test (⟨D, hD⟩, ⟨Q, hQB⟩)) ⟨(⟨D, hD⟩, ⟨Q, hQB⟩), rfl⟩
  exact ⟨P.val, hP, hxP⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Alternately meet these two countable lists of
    requirements, including the witness requirements of analytic-condition fusion. The common right limit is the
    required $y$.
-/
/-- Both prescribed left points share an actual right point whose pairs
meet every product family. The left genericity tests and catalog closure
are explicit, and the right point is obtained by witnessed fusion. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Any two individually generic points $x,x'\in A$ have a common point $y\in B$ such that both $(x,y)$ and $(x',y)$
    are product generic.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    To see this explicitly, take a downward-closed dense family $D\in\mathcal J$ of rectangles.
-/
theorem silver_common_right_point (C : AnalyticConditionCatalog) (A B : C.Condition)
    (J : Set (Set (C.Condition × C.Condition))) (hJc : J.Countable)
    (hJl : ∀ D ∈ J, IsLowerSet D) (x x' : FusionReal)
    (hx : CatalogLeftGeneric C A B x J) (hx' : CatalogLeftGeneric C A B x' J) :
    ∃ y ∈ B.val.val, ∀ D ∈ J,
      (∃ P Q, (P, Q) ∈ D ∧ x ∈ P.val.val ∧ y ∈ Q.val.val) ∧
      (∃ P Q, (P, Q) ∈ D ∧ x' ∈ P.val.val ∧ y ∈ Q.val.val) := by
  let L (z : FusionReal) (D : Set (C.Condition × C.Condition)) : Set (CatalogBelow C B) :=
    {Q | Q.val ∈ catalogAdmissibleRight C A z D}
  let F : Set (Set (CatalogBelow C B)) := L x '' J ∪ L x' '' J
  have hFc : F.Countable := (hJc.image (L x)).union (hJc.image (L x'))
  have hFd : ∀ D ∈ F, IsCoinitial D := by
    rintro D (⟨R, hR, rfl⟩ | ⟨R, hR, rfl⟩)
    · exact catalogAdmissibleRight_coinitial C A B x J hx hR
    · exact catalogAdmissibleRight_coinitial C A B x' J hx' hR
  have hFl : ∀ D ∈ F, IsLowerSet D := by
    rintro D (⟨R, hR, rfl⟩ | ⟨R, hR, rfl⟩)
    · exact fun _ _ h hmem => catalogAdmissibleRight_lower C A x (hJl R hR) h hmem
    · exact fun _ _ h hmem => catalogAdmissibleRight_lower C A x' (hJl R hR) h hmem
  obtain ⟨y, hyB, hy⟩ := catalog_generic_point_below C B F hFc hFd hFl
  refine ⟨y, hyB, ?_⟩
  intro D hD
  obtain ⟨Q, ⟨P, _, hxP, hPQ⟩, hyQ⟩ := hy (L x D) (Or.inl ⟨D, hD, rfl⟩)
  obtain ⟨Q', ⟨P', _, hxP', hPQ'⟩, hyQ'⟩ := hy (L x' D) (Or.inr ⟨D, hD, rfl⟩)
  exact ⟨⟨P, Q.val, hPQ, hxP, hyQ⟩, ⟨P', Q'.val, hPQ', hxP', hyQ'⟩⟩

/-- Product genericity as encounters by actual members of catalog conditions. -/
def CatalogProductGeneric (C : AnalyticConditionCatalog)
    (J : Set (Set (C.Condition × C.Condition))) (x y : FusionReal) : Prop :=
  ∀ D ∈ J, ∃ P Q, (P, Q) ∈ D ∧ x ∈ P.val.val ∧ y ∈ Q.val.val

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    If two branches agree through length $n$, their points belong to the same set of
    diameter at most $2^{-n}$; hence $\pi$ is continuous.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    The splitting lemma gives $\pi(a)\mathrel{\not E}\pi(b)$, which also proves injectivity.
-/
/-- The Silver construction in the restricted catalog. Every chosen node
already has a closed witness presentation, so no presentation hypothesis
about the future constructed tree is needed. Generic-pair splitting and
the construction of the effective catalog remain explicit obligations. -/
theorem catalog_silver_fusion (C : AnalyticConditionCatalog) (B : C.Condition)
    (E : Setoid FusionReal) (J : Set (Set (C.Condition × C.Condition)))
    (hJc : J.Countable) (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D)
    (hsplit : ∀ x ∈ B.val.val, ∀ y ∈ B.val.val, CatalogProductGeneric C J x y → ¬ E.r x y) :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      (∀ a, π a ∈ B.val.val) ∧ ∀ a b, a ≠ b → ¬ E.r (π a) (π b) := by
  obtain ⟨d, _, hdd, hdl, hdF⟩ := countable_dense_schedule C.requirements C.requirements_countable
    (fun D hD => (C.requirements_dense_lower D hD).1)
    (fun D hD => (C.requirements_dense_lower D hD).2)
  obtain ⟨j, _, hjd, hjl, hjJ⟩ := countable_dense_schedule J hJc hJd hJl
  obtain ⟨A, hA0, hparent, hAd, hAj⟩ := silver_binary_levels B d hdd hdl j hjd hjl
  have hbranch a : Antitone (fun n => A n (binaryBranchPrefix a n)) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [binaryBranchPrefix_succ]
    exact hparent n _ _
  have hpoint a : ∃! x : FusionReal, ∀ n, x ∈ (A n (binaryBranchPrefix a n)).val.val := by
    apply C.fusion _ (hbranch a)
    intro D hD
    obtain ⟨n, hn⟩ := hdF D hD
    exact ⟨n, hn n le_rfl (hAd n _)⟩
  choose π hπ using fun a => (hpoint a).exists
  have hπB a : π a ∈ B.val.val := hA0 _ (hπ a 0)
  have hc : Continuous π := by
    apply continuous_of_binary_condition_membership (fun n s => (A n s).val) _ π hπ
    intro k
    obtain ⟨n, hn⟩ := hdF (Subtype.val ⁻¹' smallPrefixRequirement (k + 1))
      ⟨smallPrefixRequirement (k + 1), Or.inl ⟨k + 1, rfl⟩, rfl⟩
    exact ⟨n, fun s => hn n le_rfl (hAd n s)⟩
  have hanti a b (hab : a ≠ b) : ¬ E.r (π a) (π b) := by
    apply hsplit _ (hπB a) _ (hπB b)
    have hdiff : ∃ k, a k ≠ b k := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨k, hk⟩ := hdiff
    intro D hD
    obtain ⟨m, hm⟩ := hjJ D hD
    let n := max m (k + 1)
    have hne : binaryBranchPrefix a n ≠ binaryBranchPrefix b n := by
      intro heq
      exact hk (congrFun heq ⟨k, by dsimp [n]; omega⟩)
    exact ⟨A n (binaryBranchPrefix a n), A n (binaryBranchPrefix b n),
      hm n (le_max_left _ _) (hAj n _ _ hne), hπ a n, hπ b n⟩
  have hi : Injective π := by
    intro a b heq
    by_contra hab
    exact hanti a b hab (heq ▸ E.refl (π a))
  exact ⟨π, hc, hi, hπB, hanti⟩

end PolishSpaceBook
