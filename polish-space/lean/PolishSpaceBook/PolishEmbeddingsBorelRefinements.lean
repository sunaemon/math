module

public import PolishSpaceBook.CauchyNamesPolishRepresentations
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Polish embeddings and Borel-preserving refinements

Formalization targets for
`polish-space/src/polish-space-book/polish-embeddings-borel-refinements.md`.

Formalized here are the Hilbert-cube embedding with G-delta range, permanence
of zero-dimensionality under pullback, sums, and arbitrary joins of
topologies, the non-zero-dimensional part of Kuratowski's refinement theorem,
the one-map and countably-many-map continuity refinements, and iterated
continuity refinement with its application to Borel dynamics.

The Hilbert-cube construction below is mathlib's distance-to-a-dense-sequence
construction. The original refinement API uses mathlib's clopenability and the
fact that comparable Polish topologies have the same Borel sets.
`PolishRefinementSigmaAlgebra.lean` supplies the book's independent sigma-algebra
proof: its open-set split and countable joins check Borel sets directly, using
the closed-diagonal joining lemma proved here. Later callers may use either
of the equivalent refinement APIs.

`ZeroDimensionalPolishRefinement.lean` supplies the graph construction and
zero-dimensional addendum with direct Borel bookkeeping. It depends on this
module for the initial clopen refinement. `ZeroDimensionalClosedPresentation.lean`
constructs the nested shrinking clopen partitions, discards empty pieces, proves
that their tree is pruned, and applies the common clopen-scheme homeomorphism.
Together they prove the continuous Borel isomorphism from a closed Baire
subspace for every Polish space. `StochasticPathControl.lean` applies the
refinement proof of Lusin continuity to path-valued random variables and proves
uniform bounds and the vanishing common modulus on a compact set of large
probability. The combined compatible-topologies API is assembled in the
zero-dimensional refinement modules.
-/

namespace PolishSpaceBook

noncomputable section

universe u v

open Function MeasureTheory Set TopologicalSpace Topology

section HilbertCubeEmbedding

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: theorem
  title: Hilbert-cube embedding
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] The empty space is homeomorphic to the empty $\Gdelta$ subset of $\HilbertCube$, so assume that
    $X$ is nonempty. By the \termuse{bounded complete compatible metric lemma} in §{sec:polish-key-properties}, choose a
    complete compatible metric $d\le 1$. Fix a countable dense $\IndexedFamily{x_n}{n\in\omega} \IncludedIn X$ and define
    $$\iota : X \to \HilbertCube, \qquad \iota(x) \;=\; \Sequence{d(x, x_n)}{n\in\omega}.$$
    Each coordinate is $1$-Lipschitz, so $\iota$ is continuous.

    \emph{Injective.} If $x \ne y$, pick $x_n$ with $d(x_n, x) < d(x,y)/2$. The triangle inequality gives $d(x_n, y) >
    d(x,y)/2$, so $\iota(x)_n \ne \iota(y)_n$.

    \emph{Inverse continuous on $\iota(X)$.} Suppose $\iota(y_k) \to \iota(y)$ in $\HilbertCube$. Given
    $\varepsilon > 0$, pick $x_n$ with $d(x_n, y) < \varepsilon/3$. Coordinatewise convergence gives
    $d(y_k, x_n) \to d(y, x_n) < \varepsilon/3$, so for $k$ large
    $d(y_k, y) \le d(y_k, x_n) + d(x_n, y) < \varepsilon$.

    Thus $\iota$ is a homeomorphism onto $\iota(X)$. The image is Polish, so by \termuse{Alexandrov's theorem} in
    §{sec:alexandrov-theorem} it is $\Gdelta$ in $\HilbertCube$.
-/
/-- Every Polish space embeds into the Hilbert cube with G-delta range.

The map is assembled from mathlib's distance coordinates relative to a dense
sequence; its range is G-delta by the formalized Alexandrov theorem. -/
theorem exists_hilbert_cube_embedding (X : Type u) [TopologicalSpace X]
    [PolishSpace X] :
    ∃ f : X → hilbert_cube, IsEmbedding f ∧ IsGδ (range f) := by
  let := upgradeIsCompletelyMetrizable X
  let firststep :
      X ≃ₜ Metric.PiNatEmbed X (fun _ ↦ unitInterval)
        (Metric.PiNatEmbed.distDenseSeq X) := {
    toFun := Metric.PiNatEmbed.toPiNat
    invFun := Metric.PiNatEmbed.ofPiNat
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := Metric.PiNatEmbed.continuous_toPiNat
      (fun i ↦ Metric.PiNatEmbed.continuous_distDenseSeq i)
    continuous_invFun := Metric.PiNatEmbed.continuous_distDenseSeq_inv }
  let secondstep :
      Metric.PiNatEmbed X (fun _ ↦ unitInterval)
        (Metric.PiNatEmbed.distDenseSeq X) → hilbert_cube :=
    Metric.PiNatEmbed.embed _ _ _
  have hsecond : IsEmbedding secondstep :=
    (Metric.PiNatEmbed.isUniformEmbedding_embed
      Metric.PiNatEmbed.injective_distDenseSeq).isEmbedding
  let f : X → hilbert_cube := secondstep ∘ firststep
  have hf : IsEmbedding f := hsecond.comp firststep.isEmbedding
  refine ⟨f, hf, ?_⟩
  have : PolishSpace (range f) :=
    hf.toHomeomorph.symm.isClosedEmbedding.polishSpace
  exact polish_subspace_isGdelta

end HilbertCubeEmbedding

section ZeroDimensionalPermanence

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    If every $\tau_m$ is zero-dimensional, finite-coordinate clopen boxes form
    a base of the product, and their traces form a clopen base of the diagonal subspace. Thus $\tau_\infty$ is
    zero-dimensional.
-/
/-- An arbitrary join of zero-dimensional topologies is zero-dimensional. -/
theorem isZeroDimensional_iInf
    {X : Type u} {I : Type v} {t : I → TopologicalSpace X}
    (ht : ∀ i, @IsZeroDimensional X (t i)) :
    @IsZeroDimensional X (⨅ i, t i) := by
  let : TopologicalSpace X := ⨅ i, t i
  change IsZeroDimensional X
  have ht' : ∀ i,
      @IsTopologicalBasis X (t i) {s : Set X | @IsClopen X (t i) s} := by
    intro i
    exact ht i
  have hb := IsTopologicalBasis.iInf (t := t)
    (T := fun i ↦ {s : Set X | @IsClopen X (t i) s}) ht'
  refine hb.of_isOpen_of_subset (t := ⨅ i, t i)
    (s' := {s : Set X | @IsClopen X (⨅ i, t i) s})
    (fun _s hs ↦ hs.2) ?_
  rintro S ⟨U, F, hU, rfl⟩
  exact isClopen_biInter_finset fun i hi ↦
    ⟨(hU i hi).1.mono (iInf_le t i), (hU i hi).2.mono (iInf_le t i)⟩

/-- Pulling back a zero-dimensional topology along any map preserves
zero-dimensionality. -/
theorem isZeroDimensional_induced
    {X : Type u} {Y : Type v} [tY : TopologicalSpace Y]
    (hY : IsZeroDimensional Y) (f : X → Y) :
    @IsZeroDimensional X (TopologicalSpace.induced f tY) := by
  let : TopologicalSpace X := TopologicalSpace.induced f tY
  change IsZeroDimensional X
  have hb := hY.induced f
  refine hb.of_isOpen_of_subset (t := TopologicalSpace.induced f tY)
    (s' := {s : Set X | @IsClopen X (TopologicalSpace.induced f tY) s})
    (fun _s hs ↦ hs.2) ?_
  rintro S ⟨U, hU, rfl⟩
  exact hU.preimage continuous_induced_dom

/-- A sum of zero-dimensional spaces is zero-dimensional. -/
theorem isZeroDimensional_sum
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsZeroDimensional X) (hY : IsZeroDimensional Y) :
    IsZeroDimensional (X ⊕ Y) := by
  have hb := hX.sum hY
  refine hb.of_isOpen_of_subset
    (s' := {s : Set (X ⊕ Y) | IsClopen s})
    (fun _s hs ↦ hs.isOpen) ?_
  rintro S (hS | hS)
  · rcases hS with ⟨U, hU, rfl⟩
    exact ⟨Topology.IsClosedEmbedding.inl.isClosedMap U hU.isClosed,
      Topology.IsOpenEmbedding.inl.isOpenMap U hU.isOpen⟩
  · rcases hS with ⟨U, hU, rfl⟩
    exact ⟨Topology.IsClosedEmbedding.inr.isClosedMap U hU.isClosed,
      Topology.IsOpenEmbedding.inr.isOpenMap U hU.isOpen⟩

end ZeroDimensionalPermanence

section PolishRefinements

variable {X : Type u}


/-- Countably many Borel sets become clopen in one finer Polish topology
without changing the Borel sigma-algebra. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: theorem
  title: Kuratowski's refinement theorem
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    *   **Making a Borel subspace open or closed.** If $B\IncludedIn X$ is Borel, include $B$ in the family. Then $B$
        becomes clopen, so it is a Polish subspace in the refined topology. This is the step used in the reduction in the
        proof of the \termforward{Lusin--Suslin theorem} in §{sec:lusin-souslin-proof}.
-/
theorem exists_polish_refinement_clopen
    [t : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (B : ℕ → Set X) (hB : ∀ n, MeasurableSet (B n)) :
    ∃ t' : TopologicalSpace X,
      t' ≤ t ∧ @PolishSpace X t' ∧
        @borel X t' = @borel X t ∧
          ∀ n, @IsClopen X t' (B n) := by
  choose tn htn htn_polish htn_closed htn_open using
    fun n ↦ (hB n).isClopenable
  obtain ⟨t', ht'tn, ht't, ht'_polish⟩ :=
    PolishSpace.exists_polishSpace_forall_le tn htn htn_polish
  refine ⟨t', ht't, ht'_polish, ?_, ?_⟩
  · exact MeasureTheory.borel_eq_borel_of_le (t := t') (t' := t)
      ht'_polish (inferInstance : @PolishSpace X t) ht't
  · intro n
    exact ⟨(htn_closed n).mono (ht'tn n), (htn_open n).mono (ht'tn n)⟩

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: corollary
  title: Borel maps become continuous
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: proof
  excerpt: |
    Apply \termuse{Kuratowski's refinement theorem} to the countable family
    $\{f^{-1}(V_n):n\in\omega\}$, where $\{V_n\}$ is a countable base of $Y$. In the refined topology these preimages are
    clopen, so $f$ has open preimages of basic opens.
-/
/-- A Borel map becomes continuous after a Borel-preserving Polish refinement
of its domain. -/
theorem exists_polish_refinement_continuous
    {Y : Type v}
    [tX : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [tY : TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) :
    ∃ t' : TopologicalSpace X,
      t' ≤ tX ∧ @PolishSpace X t' ∧
        @borel X t' = @borel X tX ∧ @Continuous X Y t' tY f := by
  obtain ⟨V, hV⟩ := exists_seq_basis Y
  obtain ⟨t', hle, hp, hb, hc⟩ := exists_polish_refinement_clopen
    (fun n => f ⁻¹' V n)
    (fun n => (hV.isOpen (mem_range_self n)).measurableSet.preimage hf)
  refine ⟨t', hle, hp, hb, ?_⟩
  apply (@IsTopologicalBasis.continuous_iff X Y t' tY (range V) hV f).mpr
  rintro U ⟨n, rfl⟩
  exact (hc n).isOpen

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    **Several maps at once.** If $f_m:X\to Y_m$ is a countable family of Borel maps into Polish spaces, refine with
    respect to all sets $f_m^{-1}(V^m_k)$, where $\IndexedFamily{V^m_k}{k\in\omega}$ is a base of $Y_m$. Then every $f_m$ is
    continuous in the
    same refined topology.
-/
/-- Countably many Borel maps become continuous in one Borel-preserving Polish
refinement of their common domain. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{compatible Polish topologies theorem}{Compatible Polish topologies}] Let $(X, \mathcal
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    By definition of standard Borel, fix any Polish topology $\tau_0$ on $X$ with
    $\mathcal B(\tau_0) = \mathcal B$. From there, (1) is the zero-dimensional form of
    \termuse{Kuratowski's refinement theorem} applied to $\tau_0$ and $\{B_n\}$. Apply the zero-dimensional part of
    \termuse{closed presentation in Baire space} to that same topology to obtain (2); the $B_n$ remain clopen. Finally, (3)
    is the countable-map variant of \termuse{Borel maps become continuous}.
-/
theorem exists_polish_refinement_continuous_family
    (Y : ℕ → Type v)
    [tX : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [tY : ∀ n, TopologicalSpace (Y n)]
    [pY : ∀ n, PolishSpace (Y n)]
    [mY : ∀ n, MeasurableSpace (Y n)]
    [bY : ∀ n, BorelSpace (Y n)]
    (f : ∀ n, X → Y n) (hf : ∀ n, Measurable (f n)) :
    ∃ t' : TopologicalSpace X,
      t' ≤ tX ∧ @PolishSpace X t' ∧
        @borel X t' = @borel X tX ∧
          ∀ n, @Continuous X (Y n) t' (tY n) (f n) := by
  choose tn htn hfn htn_polish using fun n ↦ (hf n).exists_continuous
  obtain ⟨t', ht'tn, ht't, ht'_polish⟩ :=
    PolishSpace.exists_polishSpace_forall_le tn htn htn_polish
  refine ⟨t', ht't, ht'_polish, ?_, ?_⟩
  · exact MeasureTheory.borel_eq_borel_of_le (t := t') (t' := tX)
      ht'_polish (inferInstance : @PolishSpace X tX) ht't
  · intro n
    apply continuous_iff_le_induced.2
    exact (ht'tn n).trans (continuous_iff_le_induced.1 (hfn n))

end PolishRefinements

section BorelDynamics

variable {X : Type u}

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    Let $\tau_*$ be the topology generated by $\bigcup_n\tau_n$. The joining argument in the proof of
    \termuse{Kuratowski's refinement theorem} identifies it with the topology induced by the diagonal map into
    $\prod_n(X,\tau_n)$. The image is closed because the common Hausdorff topology $\tau$ separates any two unequal
    coordinates, so $\tau_*$ is Polish. Finite-coordinate basic open sets pull back to finite intersections of
    $\tau$-Borel sets, and there are countably many such basic sets. Hence every $\tau_*$-open set is $\tau$-Borel;
    together with $\tau\IncludedIn\tau_*$, this gives $\mathcal B(\tau_*)=\mathcal B(\tau)$.
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    We first record a joining observation. Suppose $\Sequence{\tau_m}{m\in\omega}$ is a countable sequence of Polish
    topologies on $X$ such that each $\tau_m$ refines $\tau$ and $\mathcal B(\tau_m)=\mathcal B(\tau)$. Let $\tau_\infty$ be
    the topology induced by the diagonal map
    $$
    x\longmapsto (x,x,x,\ldots)
    $$
    from $X$ into $\prod_m (X,\tau_m)$. The diagonal image is closed. Indeed, if two coordinates have distinct values, the
    original Hausdorff topology $\tau$ separates them by disjoint open sets, and these sets are open in the corresponding
    $\tau_m$'s. Hence $\tau_\infty$ is Polish by the closed-subspace and countable-product results of
    §{sec:polish-key-properties}. It refines every $\tau_m$. Conversely, its diagonal model has a countable base of
    finite-coordinate boxes. Each such box pulls back to a finite intersection of sets open in some $\tau_m$'s and is
    therefore $\tau$-Borel. Every $\tau_\infty$-open set is a countable union of these basic sets, so
    $\mathcal B(\tau_\infty)=\mathcal B(\tau)$.
-/
/-- The countable join is modeled by the closed diagonal in the product.
The Borel equality is proved directly by measurability of this diagonal. -/
theorem polish_borel_iInf_of_common_refinement
    [t : TopologicalSpace X] [PolishSpace X]
    (ts : ℕ → TopologicalSpace X) (hle : ∀ n, ts n ≤ t)
    (hp : ∀ n, @PolishSpace X (ts n))
    (hb : ∀ n, @borel X (ts n) = @borel X t) :
    @PolishSpace X (⨅ n, ts n) ∧ @borel X (⨅ n, ts n) = @borel X t := by
  let tP : TopologicalSpace (ℕ → X) := @Pi.topologicalSpace ℕ (fun _ ↦ X) ts
  let : ∀ n, @SecondCountableTopology X (ts n) := fun n ↦ (hp n).toSecondCountableTopology
  let : ∀ n, @IsCompletelyMetrizableSpace X (ts n) := fun n ↦ (hp n).toIsCompletelyMetrizableSpace
  let : @PolishSpace (ℕ → X) tP := ⟨⟩
  let d : X → ℕ → X := fun x _ ↦ x
  have hind : induced d inferInstance = ⨅ n, ts n := by
    simp [d, tP, Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def, ← Function.id_def, induced_id]
  have hclosed : IsClosed (range d) := by
    have heq : range d = ⋂ n : ℕ, {z : ℕ → X | z n = z 0} := by
      ext z
      simp only [mem_range, mem_iInter, mem_ofPred_eq]
      constructor
      · rintro ⟨x, rfl⟩ n
        rfl
      · intro hz
        exact ⟨z 0, funext fun n ↦ (hz n).symm⟩
    rw [heq]
    apply isClosed_iInter
    intro n
    have hc (k : ℕ) : @Continuous (ℕ → X) X inferInstance t (fun z ↦ z k) :=
      @Continuous.comp _ _ _ tP (ts k) t _ _
        (continuous_id_iff_le.mpr (hle k)) (@continuous_apply ℕ (fun _ ↦ X) ts k)
    exact isClosed_eq (hc n) (hc 0)
  have hemb : @IsClosedEmbedding X (ℕ → X) (⨅ n, ts n) inferInstance d := by
    let : TopologicalSpace X := ⨅ n, ts n
    exact ⟨⟨⟨hind.symm⟩, fun x y h ↦ congrFun h 0⟩, hclosed⟩
  refine ⟨@IsClosedEmbedding.polishSpace X (ℕ → X) (⨅ n, ts n) tP inferInstance d hemb, ?_⟩
  apply le_antisymm
  · let : MeasurableSpace X := @borel X t
    let : MeasurableSpace (ℕ → X) := MeasurableSpace.pi
    have hsc (n : ℕ) : @SecondCountableTopology X (ts n) := (hp n).toSecondCountableTopology
    let : BorelSpace (ℕ → X) := @Pi.borelSpace ℕ (fun _ ↦ X) _ ts
      (fun _ ↦ @borel X t) hsc (fun n ↦ @BorelSpace.mk X (ts n) (@borel X t) (hb n).symm)
    have hd : Measurable d := Measurable.of_eval (fun _ ↦ measurable_id)
    rw [← hind, borel_comap, ← BorelSpace.measurable_eq]
    exact hd.comap_le
  · exact borel_anti ((iInf_le ts 0).trans (hle 0))


/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    Start with $\tau_0=\tau$. Suppose that a Polish topology $\tau_n$ with the same Borel sets has been constructed.
    Choose a countable base $\{U_{n,k}:k\in\omega\}$ for $\tau_n$. Each $f_m$ is Borel for $\tau_n$, since its Borel
    $\sigma$-algebra agrees with the original one. Apply \termuse{Kuratowski's refinement theorem} to the countable family
    $$
    \{f_m^{-1}(U_{n,k}):m,k\in\omega\}
    $$
    to obtain a Polish topology $\tau_{n+1}\supseteq\tau_n$ with the same Borel sets in which these sets are clopen.
    Then each $f_m:(X,\tau_{n+1})\to(X,\tau_n)$ is continuous.
-/
/-- One stage opens the inverse images of a countable base. -/
theorem exists_polish_refinement_selfmaps_step
    [t : TopologicalSpace X] [PolishSpace X]
    (f : ℕ → X → X) (hf : ∀ m, @Measurable X X (borel X) (borel X) (f m)) :
    ∃ t' : TopologicalSpace X, t' ≤ t ∧ @PolishSpace X t' ∧
      @borel X t' = @borel X t ∧ ∀ m, @Continuous X X t' t (f m) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨U, hU⟩ := exists_seq_basis X
  let B : ℕ → Set X := fun j ↦ f j.unpair.1 ⁻¹' U j.unpair.2
  have hB (j : ℕ) : MeasurableSet (B j) :=
    (hU.isOpen (mem_range_self _)).measurableSet.preimage (hf _)
  obtain ⟨t', hle, hp, hb, hc⟩ := exists_polish_refinement_clopen B hB
  refine ⟨t', hle, hp, hb, fun m ↦ ?_⟩
  apply (@IsTopologicalBasis.continuous_iff X X t' t (range U) hU (f m)).mpr
  rintro V ⟨k, rfl⟩
  simpa [B] using (hc (Nat.pair m k)).isOpen

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: lemma
  title: Iterated continuity refinement
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    For every $U\in\tau_n$, the construction gives $f_m^{-1}(U)\in\tau_{n+1}\IncludedIn\tau_*$. Since the sets in
    $\bigcup_n\tau_n$ generate $\tau_*$ and inverse images commute with unions and finite intersections, each $f_m$
    is continuous from $(X,\tau_*)$ to itself.
-/
/-- Repeated refinement makes all self-maps continuous for the same topology. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    For a map from a space to itself, both the domain and the codomain acquire the new topology. A single application of
    the continuity-refinement corollary only gives continuity into the old codomain topology. We resolve this by refining
    repeatedly, making the inverse images of each stage's open sets open at the next stage.
-/
theorem exists_polish_refinement_continuous_selfmaps
    [t : TopologicalSpace X] [PolishSpace X]
    (f : ℕ → X → X) (hf : ∀ m, @Measurable X X (borel X) (borel X) (f m)) :
    ∃ t' : TopologicalSpace X, t' ≤ t ∧ @PolishSpace X t' ∧
      @borel X t' = @borel X t ∧ ∀ m, @Continuous X X t' t' (f m) := by
  let S := {s : TopologicalSpace X // s ≤ t ∧ @PolishSpace X s ∧ @borel X s = @borel X t}
  have step (s : S) : ∃ s' : S, s'.val ≤ s.val ∧
      ∀ m, @Continuous X X s'.val s.val (f m) := by
    have hfm : ∀ m, @Measurable X X (@borel X s.val) (@borel X s.val) (f m) := by
      have heq : @borel X s.val = @borel X t := s.property.2.2
      rw [heq]
      exact hf
    obtain ⟨s', hle, hp, hb, hc⟩ :=
      @exists_polish_refinement_selfmaps_step X s.val s.property.2.1 f hfm
    exact ⟨⟨s', hle.trans s.property.1, hp, hb.trans s.property.2.2⟩, hle, hc⟩
  choose next hnext using step
  let seq : ℕ → S := Nat.rec ⟨t, le_rfl, inferInstance, rfl⟩ (fun _ s ↦ next s)
  let ts : ℕ → TopologicalSpace X := fun n ↦ (seq n).val
  have hsucc (n m : ℕ) : @Continuous X X (ts (n+1)) (ts n) (f m) :=
    (hnext (seq n)).2 m
  have hp := polish_borel_iInf_of_common_refinement ts
    (fun n ↦ (seq n).property.1) (fun n ↦ (seq n).property.2.1)
    (fun n ↦ (seq n).property.2.2)
  refine ⟨⨅ n, ts n, (iInf_le ts 0).trans (seq 0).property.1, hp.1, hp.2, ?_⟩
  intro m
  apply continuous_iInf_rng.mpr
  intro n
  exact continuous_iInf_dom (i := n+1) (hsucc n m)


/-- A Borel automorphism becomes a homeomorphism without changing its underlying
bijection or the Borel sets. Both directions use the same refined topology. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: example
  title: A measurable dynamical system becomes topological
-/
theorem exists_polish_refinement_homeomorph
    [t : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (T : X ≃ᵐ X) :
    ∃ t' : TopologicalSpace X, t' ≤ t ∧ @PolishSpace X t' ∧
      @borel X t' = @borel X t ∧
      ∃ H : @Homeomorph X X t' t', H.toEquiv = T.toEquiv := by
  let f : ℕ → X → X := fun n ↦ if n = 0 then T else T.symm
  have hf (n : ℕ) : @Measurable X X (borel X) (borel X) (f n) := by
    rw [← BorelSpace.measurable_eq]
    dsimp [f]
    split
    · exact T.measurable
    · exact T.symm.measurable
  obtain ⟨t', hle, hp, hb, hc⟩ := exists_polish_refinement_continuous_selfmaps f hf
  refine ⟨t', hle, hp, hb, ?_⟩
  let : TopologicalSpace X := t'
  exact ⟨{ T.toEquiv with
    continuous_toFun := by simpa [f] using hc 0
    continuous_invFun := by simpa [f] using hc 1 }, rfl⟩

/-- The return-after-`n` condition is closed: it is the preimage of the diagonal
under the map sending `x` to `(T^[n] x, x)`. This is not the exact-period set. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: example
  title: A measurable dynamical system becomes topological
-/
theorem isClosed_periodicPts_of_continuous
    [TopologicalSpace X] [T2Space X] {T : X → X} (hT : Continuous T) (n : ℕ) :
    IsClosed {x | IsPeriodicPt T n x} := by
  exact isClosed_eq (hT.iterate n) continuous_id

/-- Fixed points are the return-after-one-step set. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: example
  title: A measurable dynamical system becomes topological
-/
theorem isClosed_fixedPoints_of_continuous
    [TopologicalSpace X] [T2Space X] {T : X → X} (hT : Continuous T) :
    IsClosed (fixedPoints T) := by
  simpa [IsPeriodicPt, fixedPoints, IsFixedPt] using isClosed_periodicPts_of_continuous hT 1

/-- A limit of points returning after `n` steps still returns after `n` steps. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: example
  title: A measurable dynamical system becomes topological
-/
theorem isPeriodicPt_of_tendsto
    [TopologicalSpace X] [T2Space X] {T : X → X} (hT : Continuous T)
    {n : ℕ} {x : X} {xs : ℕ → X} (hxs : ∀ k, IsPeriodicPt T n (xs k))
    (hx : Filter.Tendsto xs Filter.atTop (𝓝 x)) : IsPeriodicPt T n x := by
  exact (isClosed_periodicPts_of_continuous hT n).mem_of_tendsto hx
    (Filter.Eventually.of_forall hxs)

/-- All finite-period constraints, including fixed points, are closed in the
same Borel-preserving Polish topology that makes the evolution a homeomorphism. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: example
  title: A measurable dynamical system becomes topological
-/
theorem exists_polish_refinement_dynamics
    [t : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (T : X ≃ᵐ X) :
    ∃ t' : TopologicalSpace X, t' ≤ t ∧ @PolishSpace X t' ∧
      @borel X t' = @borel X t ∧
      (∃ H : @Homeomorph X X t' t', H.toEquiv = T.toEquiv) ∧
      ∀ n : ℕ, @IsClosed X t' {x | IsPeriodicPt (T : X → X) n x} := by
  obtain ⟨t', hle, hp, hb, H, hH⟩ := exists_polish_refinement_homeomorph T
  refine ⟨t', hle, hp, hb, ⟨H, hH⟩, ?_⟩
  let : TopologicalSpace X := t'
  let : PolishSpace X := hp
  have hT : Continuous (T : X → X) := by
    have heq : (H : X → X) = T := congrArg Equiv.toFun hH
    rw [← heq]
    exact H.continuous
  exact fun n ↦ isClosed_periodicPts_of_continuous hT n


end BorelDynamics

end

end PolishSpaceBook
