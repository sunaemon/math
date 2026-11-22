module

public import PolishSpaceBook.BorelReducibilitySynthesis
public import PolishSpaceBook.NonarchimedeanRepresentation
public import PolishSpaceBook.AnalyticBorelMaps
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-! # Definitions and orbit projections in the Polish-group chapter

Use the canonical group/action and Polish-space structures. For general Borel
actions the witness relation is Borel, not necessarily closed; refine it only
when invoking the book's Borel-image theorem.
-/
namespace PolishSpaceBook.PolishGroupProse
open Set Topology Filter MeasureTheory

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    A \termdefine{Polish group} is a topological group $G$ whose underlying topological space is Polish.
-/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    For a Polish group a complete compatible metric exists by Polishness,
-/
/-- The canonical structures give exactly a Polish topological group, with
some complete compatible metric, without asserting left invariance of it. -/
theorem polish_group_spec {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] :
    IsTopologicalGroup G ∧ SecondCountableTopology G ∧ IsCompletelyMetrizableByMetric G :=
  ⟨inferInstance, inferInstance,
    (isCompletelyMetrizableByMetric_iff_mathlib G).mpr inferInstance⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    A Polish group is \termdefineas{locally compact group}{locally compact} iff its identity has a compact neighborhood.
-/
/-- In a topological group, one compact neighborhood at the identity suffices. -/
theorem locallyCompact_iff_identity {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    LocallyCompactSpace G ↔ ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 (1 : G) := by
  constructor
  · intro h
    let := h
    exact exists_compact_mem_nhds (1 : G)
  · rintro ⟨K, hK, hmem⟩
    exact hK.locallyCompactSpace_of_mem_nhds_of_group hmem

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    A \termdefine{Borel action} of a Polish group $G$ on a standard Borel space $X$ is a Borel map $\alpha : G \times X \to
    X$ satisfying $\alpha(e, x) = x$ and $\alpha(gh, x) = \alpha(g, \alpha(h, x))$.
-/
/-- The action laws belong to MulAction; joint Borel measurability belongs
to MeasurableSMul, rather than to separate coordinate measurability. -/
theorem borel_action_spec {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace G] [MeasurableSpace X] [MeasurableSMul₂ G X] :
    Measurable (fun p : G × X => p.1 • p.2) ∧
      (∀ x : X, (1 : G) • x = x) ∧
      (∀ g h : G, ∀ x : X, (g * h) • x = g • (h • x)) :=
  ⟨measurable_smul, one_smul G, mul_smul⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The \termdefine{continuous action}
    version requires $\alpha$ to be continuous as a map of topological spaces and requires $X$ to be Polish.
-/
/-- Joint continuity is the continuous-action condition on the Polish space. -/
theorem continuous_action_spec {G X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [ContinuousSMul G X] [PolishSpace X] :
    Continuous (fun p : G × X => p.1 • p.2) ∧ PolishSpace X :=
  ⟨continuous_smul, inferInstance⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The existential quantification over $G$ uses a Polish parameter space, so projection makes $\OrbitER{G}{X}$ analytic
    ($\bSigma^1_1$).
-/
/-- Projection of the Borel witness relation proves analyticity for a Borel
action, including when it is not continuous in the chosen compatible topology. -/
theorem analyticSet_orbitRelation {G X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (hact : Measurable (fun p : G × X => p.1 • p.2)) :
    AnalyticSet {p : X × X | OrbitEquivalent G X p.1 p.2} := by
  let C : Set ((X × X) × G) := {z | z.1.2 = z.2 • z.1.1}
  have hC : MeasurableSet C := measurableSet_eq_fun
    (measurable_snd.comp measurable_fst)
    (hact.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have he : Prod.fst '' C = {p : X × X | OrbitEquivalent G X p.1 p.2} := by
    ext p
    constructor
    · rintro ⟨⟨q, g⟩, hg, rfl⟩
      exact ⟨g, hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨(p, g), hg, rfl⟩
  rw [← he]
  exact analyticSet_borel_image_via_refinement hC measurable_fst

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    An equivalence relation $E$ on a standard Borel space is \termdefine{classifiable by countable structures} if
    $E \BorelReducesTo {\cong_L}$ for some countable language $L$. The relation itself need not be Borel.
-/
/-- Countable-symbol first-order codes are the possible classification targets.
No assumption that the source equivalence relation is Borel is imposed. -/
def ClassifiableByCountableStructures {X : Type*} [MeasurableSpace X]
    (E : X → X → Prop) : Prop :=
  ∃ L : FirstOrder.Language.{0, 0},
    Countable (Σ n, L.Relations n) ∧ Countable (Σ n, L.Functions n) ∧
      ∃ f : X → LogicActions.ModelCode L,
        @Measurable X (LogicActions.ModelCode L) inferInstance (borel _) f ∧
          ∀ x y, E x y ↔ Nonempty (LogicActions.ModelIso L (f x) (f y))

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    A Borel reduction
    $$
    f:X\to\mathrm{Graphs}_\NN
    $$
    from an equivalence relation $E$ on $X$ to graph isomorphism assigns to each object $x$ a countable graph $f(x)$ such
    that
    $$
    x\mathrel E y
    \quad\Longleftrightarrow\quad
    f(x)\cong_{\mathrm{Graph}}f(y).
    $$
    Thus the graph becomes a complete countable invariant for the original object.
-/
/-- The graph assigned by a reduction is a complete invariant up to graph
isomorphism, precisely in the sense of the chapter's reduction definition. -/
theorem graph_reduction_spec {X : Type*} [MeasurableSpace X]
    (E : X → X → Prop) (f : X → CountableGraphActions.GraphCode) :
    @BorelReduces X CountableGraphActions.GraphCode inferInstance (borel _) E
      (fun G H => Nonempty (CountableGraphActions.toGraph G ≃g CountableGraphActions.toGraph H)) f ↔
      (@Measurable X CountableGraphActions.GraphCode inferInstance (borel _) f ∧
        ∀ x y, E x y ↔ Nonempty
          (CountableGraphActions.toGraph (f x) ≃g CountableGraphActions.toGraph (f y))) := Iff.rfl

/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: statement
  excerpt: |
    \begin{corollary*} Every equivalence relation on a standard Borel space that is classifiable by countable structures
-/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    \begin{proof}[Proof from cited results] Let $E$ be such an equivalence relation on $X$. By the definition of
    classification by countable structures, there are a countable language $L$ and a Borel reduction $f$ from $E$ to
    $\cong_L$. Apply the Friedman--Stanley theorem to $L$ to obtain a Borel reduction $g$ from $\cong_L$ to
    $\cong_{\mathrm{Graph}}$. The composite $g\circ f$ is Borel, and for all $x,y\in X$,
    $$
    x\mathrel E y \quad\Longleftrightarrow\quad f(x)\cong_L f(y)
    \quad\Longleftrightarrow\quad g(f(x))\cong_{\mathrm{Graph}}g(f(y)).
    $$
    Hence $g\circ f$ is the required reduction. In Lean, the Friedman--Stanley statement is an explicit hypothesis
    of this derivation.
    \end{proof}
-/
/-- Compose the classifier with the graph coding supplied by the external
Friedman--Stanley statement. Only this consequence is proved here. The argument
works on any measurable source space and does not require E itself to be Borel. -/
theorem graph_universal_of_external_friedman_stanley
    (hfs : ∀ L : FirstOrder.Language.{0, 0},
      Countable (Σ n, L.Relations n) → Countable (Σ n, L.Functions n) →
        @BorelReducible (LogicActions.ModelCode L) CountableGraphActions.GraphCode
          (borel _) (borel _)
          (fun M N => Nonempty (LogicActions.ModelIso L M N))
          (fun G H => Nonempty (CountableGraphActions.toGraph G ≃g CountableGraphActions.toGraph H)))
    {X : Type*} [MeasurableSpace X] {E : X → X → Prop}
    (hE : ClassifiableByCountableStructures E) :
    @BorelReducible X CountableGraphActions.GraphCode inferInstance (borel _) E
      (fun G H => Nonempty (CountableGraphActions.toGraph G ≃g CountableGraphActions.toGraph H)) := by
  obtain ⟨L, hrel, hfun, f, hf, hiff⟩ := hE
  obtain ⟨g, hg⟩ := hfs L hrel hfun
  let : MeasurableSpace (LogicActions.ModelCode L) := borel _
  let : MeasurableSpace CountableGraphActions.GraphCode := borel _
  exact ⟨g ∘ f, hg.comp ⟨hf, hiff⟩⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    A Polish group is \termdefine{non-Archimedean} if it admits a neighborhood base at the identity consisting of *open
    subgroups*.
-/
/-- The canonical nonarchimedean property is the open-subgroup neighborhood condition. -/
theorem nonarchimedean_iff_basis {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    NonarchimedeanGroup G ↔ ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, (H : Set G) ⊆ U := by
  constructor
  · intro h
    let := h
    exact NonarchimedeanGroup.is_nonarchimedean
  · intro h
    exact { is_nonarchimedean := h }

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    If an orbit is meager in its closure, the equivalent conditions of Effros's theorem fail for that orbit.
-/
/-- A nonempty set meager in its closure cannot be G_delta in a Polish space. -/
theorem not_isGdelta_of_meagre_in_closure {X : Type*}
    [TopologicalSpace X] [PolishSpace X] {A : Set X} (hne : A.Nonempty)
    (hM : IsMeagre (Subtype.val ⁻¹' A : Set (closure A))) : ¬ IsGδ A :=
  fun h => not_isMeagre_in_closure_of_isGdelta h hne hM

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The combination of conditions is delicate. Density and meagerness together rule out the Effros regime: by (1) every
    orbit has closure $X$, and by (2) every orbit is meager in $X$, so no orbit is non-meager in its closure.
-/
/-- A dense meager orbit is also meager inside its closure; density alone
therefore cannot satisfy the nonmeager alternative in Effros. -/
theorem dense_meagre_in_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hD : Dense A) (hM : IsMeagre A) :
    IsMeagre (Subtype.val ⁻¹' A : Set (closure A)) := by
  let e : closure A ≃ₜ X :=
    (Homeomorph.setCongr hD.closure_eq).trans (Homeomorph.Set.univ X)
  exact (isMeagre_preimage_homeomorph_iff e A).mpr hM

end PolishSpaceBook.PolishGroupProse
