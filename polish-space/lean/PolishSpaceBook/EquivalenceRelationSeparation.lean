module

public import PolishSpaceBook.SeparationUniformizationLusinSuslin
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
# Saturation and separation for the Silver and HKL arguments

This module proves the set-theoretic and boldface analytic infrastructure:
analytic saturation, a Borel homogeneous hull for an analytic homogeneous set,
and invariant Borel separation by the book's alternating separation/saturation
recursion. It also proves equality of saturations along a connected coherent
graph, the full joining-edge projections, the one-edge propagation step,
and disjoint compatible refinements once a distinct related pair is given.
The whole-tree propagation and the existence of that pair in the effective
kernel are still separate obligations. These results do not yet supply
lightface codes or the uniform
effective separation operation. In particular they do not complete the Silver
kernel lemma or the effective invariant separation lemma.
-/

namespace PolishSpaceBook
open Set Function Topology MeasureTheory

variable {X : Type*}

/-- Saturation with the orientation used in the book: a point is related to
some member of the original set. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For an equivalence relation $F$, write
    $$\ERSaturation{A}{F}=\{y:\exists x\in A\ (x\mathrel F y)\}$$
    for the saturation of $A$.
-/
def erSaturation (E : Setoid X) (A : Set X) : Set X := {y | ∃ x ∈ A, E.r x y}

/-- Membership is constant on each equivalence class. -/
def ERInvariant (E : Setoid X) (A : Set X) : Prop :=
  ∀ ⦃x y⦄, E.r x y → (x ∈ A ↔ y ∈ A)

theorem subset_erSaturation (E : Setoid X) (A : Set X) : A ⊆ erSaturation E A :=
  fun x hx => ⟨x, hx, E.refl x⟩

theorem erSaturation_mono (E : Setoid X) {A B : Set X} (h : A ⊆ B) :
    erSaturation E A ⊆ erSaturation E B := by
  rintro y ⟨x, hx, hxy⟩
  exact ⟨x, h hx, hxy⟩

theorem erSaturation_invariant (E : Setoid X) (A : Set X) : ERInvariant E (erSaturation E A) := by
  intro x y hxy
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, E.trans hax hxy⟩
  · rintro ⟨a, ha, hay⟩
    exact ⟨a, ha, E.trans hay (E.symm hxy)⟩

theorem erSaturation_eq_of_invariant (E : Setoid X) {A : Set X} (hA : ERInvariant E A) :
    erSaturation E A = A := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, hxy⟩
    exact (hA hxy).mp hx
  · exact subset_erSaturation E A

theorem erSaturation_disjoint (E : Setoid X) {A B : Set X}
    (hAB : Disjoint A B) (hB : ERInvariant E B) : Disjoint (erSaturation E A) B := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, hxy⟩ hy
  exact Set.disjoint_left.mp hAB hx ((hB hxy).mpr hy)

theorem erSaturation_inter_saturation (E : Setoid X) (A B : Set X) :
    erSaturation E (A ∩ erSaturation E B) = erSaturation E A ∩ erSaturation E B := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxB⟩, hxy⟩
    exact ⟨⟨x, hx, hxy⟩, (erSaturation_invariant E B hxy).mp hxB⟩
  · rintro ⟨⟨x, hx, hxy⟩, hyB⟩
    exact ⟨x, ⟨hx, (erSaturation_invariant E B hxy).mpr hyB⟩, hxy⟩

/-- Full coordinate projections of a relation contained in `E` have equal
saturations. This is the coherence invariant propagated along the HKL tree. -/
theorem erSaturation_projections_eq (E : Setoid X) {R : Set (X × X)}
    (hR : ∀ p ∈ R, E.r p.1 p.2) :
    erSaturation E (Prod.fst '' R) = erSaturation E (Prod.snd '' R) := by
  ext z
  constructor
  · rintro ⟨x, ⟨⟨a, b⟩, hab, rfl⟩, hxz⟩
    exact ⟨b, ⟨(a, b), hab, rfl⟩, E.trans (E.symm (hR (a, b) hab)) hxz⟩
  · rintro ⟨y, ⟨⟨a, b⟩, hab, rfl⟩, hyz⟩
    exact ⟨a, ⟨(a, b), hab, rfl⟩, E.trans (hR (a, b) hab) hyz⟩

/-- Along a connected graph, full projections force every node set to have
one common saturation. No finiteness assumption is needed for this invariant. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Connectedness implies that all node sets have the same $E$-saturation.
-/
theorem erSaturation_eq_of_connected_coherent {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (E : Setoid X) (A : V → Set X)
    (hcoh : ∀ u v, G.Adj u v → ∃ R : Set (X × X),
      Prod.fst '' R = A u ∧ Prod.snd '' R = A v ∧ ∀ p ∈ R, E.r p.1 p.2)
    (u v : V) : erSaturation E (A u) = erSaturation E (A v) := by
  have hedge {u v : V} (huv : G.Adj u v) : erSaturation E (A u) = erSaturation E (A v) := by
    obtain ⟨R, hleft, hright, hR⟩ := hcoh u v huv
    rw [← hleft, ← hright]
    exact erSaturation_projections_eq E hR
  obtain ⟨p⟩ := hG u v
  induction p with
  | nil => rfl
  | cons h p ih => exact (hedge h).trans ih

/-- The full relation used on the joining edge of two components. -/
def fullERBetween (E : Setoid X) (A B : Set X) : Set (X × X) :=
  {p | p.1 ∈ A ∧ p.2 ∈ B ∧ E.r p.1 p.2}

theorem fullERBetween_projections (E : Setoid X) {A B : Set X}
    (hAB : erSaturation E A = erSaturation E B) :
    Prod.fst '' fullERBetween E A B = A ∧ Prod.snd '' fullERBetween E A B = B := by
  constructor
  · ext a
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.1
    · intro ha
      have hs := subset_erSaturation E A ha
      rw [hAB] at hs
      obtain ⟨b, hb, hba⟩ := hs
      exact ⟨(a, b), ⟨ha, hb, E.symm hba⟩, rfl⟩
  · ext b
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.2.1
    · intro hb
      have hs := subset_erSaturation E B hb
      rw [← hAB] at hs
      obtain ⟨a, ha, hab⟩ := hs
      exact ⟨(a, b), ⟨ha, hb, hab⟩, rfl⟩

/-- Restrict an edge at its already processed coordinate. -/
def restrictRelationLeft (R : Set (X × X)) (C : Set X) : Set (X × X) :=
  R ∩ Prod.fst ⁻¹' C

theorem restrictRelationLeft_subset (R : Set (X × X)) (C : Set X) :
    restrictRelationLeft R C ⊆ R := inter_subset_left

theorem restrictRelationLeft_fst {R : Set (X × X)} {C : Set X}
    (hC : C ⊆ Prod.fst '' R) : Prod.fst '' restrictRelationLeft R C = C := by
  ext x
  constructor
  · rintro ⟨p, ⟨_, hpC⟩, rfl⟩
    exact hpC
  · intro hx
    obtain ⟨p, hpR, hpx⟩ := hC hx
    exact ⟨p, ⟨hpR, by simpa only [mem_preimage, hpx] using hx⟩, hpx⟩

theorem restrictRelationLeft_nonempty {R : Set (X × X)} {C : Set X}
    (hC : C ⊆ Prod.fst '' R) (hne : C.Nonempty) : (restrictRelationLeft R C).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p, hp, hpx⟩ := hC hx
  exact ⟨p, ⟨hp, by simpa only [mem_preimage, hpx] using hx⟩⟩

/-- A full equivalence-relation edge stays full under one-sided propagation. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Propagation across a full $E$-edge preserves
    that property: restricting one endpoint and taking the other projection replaces the latter by its intersection
    with the former's saturation.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    During this step keep the new
    joining edge equal to the full $E$-relation between its endpoint sets.
-/
theorem restrict_full_relation_left (E : Setoid X) {A B C : Set X} (hCA : C ⊆ A) :
    restrictRelationLeft {p : X × X | p.1 ∈ A ∧ p.2 ∈ B ∧ E.r p.1 p.2} C =
      {p : X × X | p.1 ∈ C ∧ p.2 ∈ B ∩ erSaturation E C ∧ E.r p.1 p.2} := by
  ext p
  constructor
  · rintro ⟨⟨_, hpB, hpE⟩, hpC⟩
    exact ⟨hpC, ⟨hpB, ⟨p.1, hpC, hpE⟩⟩, hpE⟩
  · rintro ⟨hpC, ⟨hpB, _⟩, hpE⟩
    exact ⟨⟨hCA hpC, hpB, hpE⟩, hpC⟩

section Analytic
variable [TopologicalSpace X] [PolishSpace X]

/-- Binary intersection, obtained from the canonical countable-intersection API. -/
theorem analyticSet_inter {A B : Set X} (hA : AnalyticSet A) (hB : AnalyticSet B) :
    AnalyticSet (A ∩ B) := by
  have h : ∀ b : Bool, AnalyticSet (cond b A B) := by intro b; cases b <;> assumption
  have heq : (⋂ b : Bool, cond b A B) = A ∩ B := by
    ext x
    simp only [mem_iInter, mem_inter_iff]
    constructor
    · intro hx
      exact ⟨hx true, hx false⟩
    · intro hx b
      cases b
      · exact hx.2
      · exact hx.1
  rw [← heq]
  exact AnalyticSet.iInter h

theorem analyticSet_erSaturation (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) {A : Set X} (hA : AnalyticSet A) :
    AnalyticSet (erSaturation E A) := by
  have hp := analyticSet_inter hE (hA.preimage continuous_fst)
  have hi := hp.image_of_continuous continuous_snd
  have heq : Prod.snd '' ({p : X × X | E.r p.1 p.2} ∩ Prod.fst ⁻¹' A) = erSaturation E A := by
    ext y
    constructor
    · rintro ⟨⟨x, z⟩, ⟨hE, hA⟩, rfl⟩
      exact ⟨x, hA, hE⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx⟩, rfl⟩
  rwa [heq] at hi

/-- The local propagation step from finite-tree refinement. The new right
node is the other projection, while the changed left node is kept exactly. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Root the tree at the changed node, and put the prescribed subset there. If $u$ has been processed and $v$
    is its next neighbor away from the root, define
    $$A'_v:=\pi_1(R_{u,v}\cap(A'_u\times X)).$$
    Every point of $A'_u$ has a partner in the old relation, so this set is nonempty. Restricting the edge to
    $A'_u\times A'_v$ preserves exactly these two projections. Continue along the unique paths from the root,
    and finally restrict every old edge to its new endpoints. The unique-path property ensures consistency.
    In particular the chosen root set remains unchanged.

    Now prescribe a nonempty subrelation $P\IncludedIn R_{u,v}$, and put
    $$C:=\pi_0(P),\qquad D:=\pi_1(P).$$
    First propagate $C$ from $u$ as above. Every pair of $P$ survives the restriction of the edge, since its first
    coordinate lies in $C$ and its second lies in the propagated set at $v$. Next propagate $D$ from $v$ in this
    refined system. The new set at $u$ is contained in $C$. Conversely, each point of $C$ has a partner in $D$
    through $P$; the reverse edge retains that pair, so the point survives propagation back to $u$.
    Thus the endpoint sets are exactly $C,D$, and the refined edge still contains $P$. Replace it by $P$ and
    its reverse by the swapped relation. Both projections remain full, and all other edges stay coherent.
    All changes are restrictions, so previously satisfied downward-closed requirements are preserved.
    \end{proof}
-/
theorem analytic_edge_refinement (E : Setoid X) {R : Set (X × X)} {C : Set X}
    (hR : AnalyticSet R) (hRE : ∀ p ∈ R, E.r p.1 p.2)
    (hC : AnalyticSet C) (hsub : C ⊆ Prod.fst '' R) (hne : C.Nonempty) :
    ∃ R' : Set (X × X), R' ⊆ R ∧ AnalyticSet R' ∧ R'.Nonempty ∧
      Prod.fst '' R' = C ∧ AnalyticSet (Prod.snd '' R') ∧
      Prod.snd '' R' ⊆ Prod.snd '' R ∧
      erSaturation E C = erSaturation E (Prod.snd '' R') := by
  let R' := restrictRelationLeft R C
  have hR' : AnalyticSet R' := analyticSet_inter hR (hC.preimage continuous_fst)
  have hf : Prod.fst '' R' = C := restrictRelationLeft_fst hsub
  refine ⟨R', inter_subset_left, hR', restrictRelationLeft_nonempty hsub hne, hf,
    hR'.image_of_continuous continuous_snd, image_mono inter_subset_left, ?_⟩
  rw [← hf]
  exact erSaturation_projections_eq E (fun p hp => hRE p hp.1)

variable [MeasurableSpace X] [BorelSpace X]

/-- Once a distinct related pair is found, disjoint open neighborhoods and
mutual saturation restrictions give compatible analytic refinements. The
existence of that pair inside the effective HKL kernel and the relative
version of this refinement are proved in `LambdaHKLRefinement.lean`. -/
theorem disjoint_analytic_compatible_refinement_of_related_pair (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) {A B : Set X}
    (hA : AnalyticSet A) (hB : AnalyticSet B) {a b : X}
    (ha : a ∈ A) (hb : b ∈ B) (hab : E.r a b) (hne : a ≠ b) :
    ∃ A' B' : Set X, A' ⊆ A ∧ B' ⊆ B ∧ AnalyticSet A' ∧ AnalyticSet B' ∧
      A'.Nonempty ∧ B'.Nonempty ∧ Disjoint A' B' ∧
      erSaturation E A' = erSaturation E B' := by
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hne
  let A₀ := A ∩ U
  let B₀ := B ∩ V
  have hA₀ : AnalyticSet A₀ := analyticSet_inter hA hU.measurableSet.analyticSet
  have hB₀ : AnalyticSet B₀ := analyticSet_inter hB hV.measurableSet.analyticSet
  let A' := A₀ ∩ erSaturation E B₀
  let B' := B₀ ∩ erSaturation E A₀
  refine ⟨A', B', fun _ hx => hx.1.1, fun _ hx => hx.1.1,
    analyticSet_inter hA₀ (analyticSet_erSaturation E hE hB₀),
    analyticSet_inter hB₀ (analyticSet_erSaturation E hE hA₀),
    ⟨a, ⟨ha, haU⟩, b, ⟨hb, hbV⟩, E.symm hab⟩,
    ⟨b, ⟨hb, hbV⟩, a, ⟨ha, haU⟩, hab⟩, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun x hx hy => Set.disjoint_left.mp hUV hx.1.2 hy.1.2)
  · dsimp only [A', B']
    rw [erSaturation_inter_saturation, erSaturation_inter_saturation, inter_comm]

/-- The non-effective homogeneous-hull step in the Silver kernel proof.
The complement of the universal class is an analytic projection; separation
places a Borel set between the original set and that class. -/
theorem borel_homogeneous_hull (E : Setoid X)
    (hE : AnalyticSet {p : X × X | ¬ E.r p.1 p.2}) {A : Set X}
    (hA : AnalyticSet A) (hne : A.Nonempty) (hhom : ∀ x ∈ A, ∀ y ∈ A, E.r x y) :
    ∃ D : Set X, MeasurableSet D ∧ A ⊆ D ∧ ∀ x ∈ D, ∀ y ∈ D, E.r x y := by
  let B : Set X := {y | ∀ x ∈ A, E.r x y}
  have hAc : A ⊆ B := fun y hy x hx => hhom x hx y hy
  have hBc : AnalyticSet Bᶜ := by
    have hp := analyticSet_inter hE (hA.preimage continuous_fst)
    have hi := hp.image_of_continuous continuous_snd
    have heq : Prod.snd '' ({p : X × X | ¬ E.r p.1 p.2} ∩ Prod.fst ⁻¹' A) = Bᶜ := by
      ext y
      simp only [mem_image, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_compl_iff, B]
      constructor
      · rintro ⟨⟨x, z⟩, ⟨hxy, hx⟩, rfl⟩ h
        exact hxy (h x hx)
      · intro h
        push Not at h
        obtain ⟨x, hx, hxy⟩ := h
        exact ⟨(x, y), ⟨hxy, hx⟩, rfl⟩
    rwa [heq] at hi
  obtain ⟨D, hAD, hDB, hD⟩ := lusinSeparation hA hBc
    (Set.disjoint_left.mpr (fun x hx hxc => hxc (hAc hx)))
  have hDB' : D ⊆ B := by simpa using hDB
  refine ⟨D, hD, hAD, ?_⟩
  obtain ⟨a, ha⟩ := hne
  intro x hx y hy
  exact E.trans (E.symm (hDB' hx a ha)) (hDB' hy a ha)

/-- Invariant Borel separation by explicit alternating separation and saturation.
Only the ordinary Borel conclusion is claimed here. The fixed-parameter
lambda codes are supplied separately by `LambdaInvariantSeparation`. -/

theorem borel_invariant_separation (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) {A B : Set X}
    (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : Disjoint A B) (hBinv : ERInvariant E B) :
    ∃ C : Set X, MeasurableSet C ∧ ERInvariant E C ∧ A ⊆ C ∧ Disjoint C B := by
  classical
  let Stage := {S : Set X // AnalyticSet S ∧ Disjoint S B}
  have hsep (S : Stage) : ∃ C : Set X, S.val ⊆ C ∧ C ⊆ Bᶜ ∧ MeasurableSet C :=
    lusinSeparation S.property.1 hB S.property.2
  choose sep hsub havoid hmeas using hsep
  let next : Stage → Stage := fun S => ⟨erSaturation E (sep S),
    analyticSet_erSaturation E hE (hmeas S).analyticSet,
    erSaturation_disjoint E (Set.disjoint_left.mpr (fun x hx hxb => havoid S hx hxb)) hBinv⟩
  let stages : ℕ → Stage := fun n => next^[n] ⟨A, hA, hAB⟩
  have hstep (n : ℕ) : (stages (n + 1)).val = erSaturation E (sep (stages n)) := by
    simp only [stages, Function.iterate_succ_apply', next]
  let C : Set X := ⋃ n : ℕ, sep (stages n)
  refine ⟨C, MeasurableSet.iUnion (fun n => hmeas (stages n)), ?_, ?_, ?_⟩
  · intro x y hxy
    have hforward {x y : X} (hxy : E.r x y) (hx : x ∈ C) : y ∈ C := by
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      apply mem_iUnion.mpr
      refine ⟨n + 1, hsub (stages (n + 1)) ?_⟩
      rw [hstep]
      exact ⟨x, hn, hxy⟩
    exact ⟨hforward hxy, hforward (E.symm hxy)⟩
  · intro x hx
    apply mem_iUnion.mpr
    exact ⟨0, hsub (stages 0) hx⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact havoid (stages n) hn hxB

end Analytic
end PolishSpaceBook
