module

public import PolishSpaceBook.LusinNeighborhoodTrees

@[expose] public section

/-!
# Lusin separation through neighborhood-tree ranks

This realizes the rank proof in the separation chapter. The neighborhood trees
are coded by a Borel map, the existing joint-tree boundedness construction gives
a countable bound, and direct transfinite recursion gives the Borel separator.
The early chapter API remains available independently of the later effective
boundedness development; this module supplies its proof correspondence.
-/

namespace PolishSpaceBook

open Set TopologicalSpace Topology MeasureTheory NamedLambda

namespace RootedPrefixTree

/-- Encoding the nodes leaves the root rank unchanged; invalid codes are isolated. -/
theorem coded_root_rank_eq (T : RootedPrefixTree)
    (hT : WellFounded (strictTreeExtension T.tree)) :
    ((T.codedExtension_wellFounded hT).apply 0).rank = (hT.apply T.root).rank := by
  classical
  let hc := T.codedExtension_wellFounded hT
  let : WellFounded T.codedExtension := hc
  let : WellFounded (strictTreeExtension T.tree) := hT
  let f : ℕ → T.tree := fun n =>
    if h : NatListCode.decode n ∈ T.tree then ⟨NatListCode.decode n, h⟩ else T.root
  have hf : ∀ ⦃b a⦄, T.codedExtension b a → strictTreeExtension T.tree (f b) (f a) := by
    intro b a h
    simpa only [f, dite_eq_left h.1, dite_eq_left h.2.1, strictTreeExtension] using h.2.2
  have hf0 : f 0 = T.root := by
    apply Subtype.ext
    simp [f, NatListCode.decode, T.root_mem, RootedPrefixTree.root]
  apply le_antisymm
  · have h := wellFoundedRank_le_of_relation_preserving f hf 0
    rw [hf0] at h
    exact h
  · let g : T.tree → ℕ := fun s => NatListCode.encode s.val
    have hg : ∀ ⦃b a⦄, strictTreeExtension T.tree b a → T.codedExtension (g b) (g a) := by
      intro b a h
      simpa only [g, codedExtension, NatListCode.decode_encode] using
        (show b.val ∈ T.tree ∧ a.val ∈ T.tree ∧ prefixOf a.val b.val ∧ a.val.length < b.val.length from
          ⟨b.property, a.property, h⟩)
    exact wellFoundedRank_le_of_relation_preserving g hg T.root

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    For $x\in C$, define $\rho(x)$ to be the rank of the root of $T_x$. This rank is countable: every ordinal below a node
    rank occurs as the rank of some node, by induction using the defining supremum of successor ranks, and the tree has
    only countably many nodes.
-/
/-- A well-founded tree has countable root rank because it has countably many nodes. -/
theorem root_rank_countable (T : RootedPrefixTree)
    (hT : WellFounded (strictTreeExtension T.tree)) :
    (hT.apply T.root).rank < Ordinal.omega 1 := by
  let : WellFounded (strictTreeExtension T.tree) := hT
  have hc : (Iio (hT.apply T.root).rank).Countable :=
    (Set.countable_range (WellFounded.rank (strictTreeExtension T.tree))).mono
      (fun β hβ => WellFounded.mem_range_rank_of_le hβ.le)
  have hk := Cardinal.le_aleph0_iff_set_countable.mpr hc
  rw [Cardinal.mk_Iio_ordinal] at hk
  have hcard : (hT.apply T.root).rank.card ≤ Cardinal.aleph0 := by
    have hk' : Cardinal.lift.{1} (hT.apply T.root).rank.card ≤
        Cardinal.lift.{1} (Cardinal.aleph0.{0}) := by
      simpa only [Cardinal.lift_aleph0] using hk
    exact Cardinal.lift_le.mp hk'
  exact Cardinal.lt_omega_iff_card_lt.mpr (Cardinal.lt_aleph_one_iff.mpr hcard)

end RootedPrefixTree

namespace LusinNeighborhood

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def rankLayer (F : Set (X × baire_space)) (α : Ordinal) : Set X :=
  {x | OrdinalRankLayer.Holds (tree F x).codedExtension α 0}

omit [MeasurableSpace X] [BorelSpace X] in
/-- The numerical relation and the word tree give exactly the same rank layers. -/
theorem mem_rankLayer_iff (F : Set (X × baire_space)) (α : Ordinal) (x : X) :
    x ∈ rankLayer F α ↔ ∃ hT : WellFounded (strictTreeExtension (tree F x).tree),
      (hT.apply (tree F x).root).rank ≤ α := by
  constructor
  · rintro ⟨hs, hα⟩
    have hT := (tree F x).wellFounded_of_codedExtension
      ((tree F x).codedExtension_wellFounded_of_root_acc hs)
    refine ⟨hT, ?_⟩
    rw [← RootedPrefixTree.coded_root_rank_eq (tree F x) hT]
    exact hα
  · rintro ⟨hT, hα⟩
    refine ⟨((tree F x).codedExtension_wellFounded hT).apply 0, ?_⟩
    rw [RootedPrefixTree.coded_root_rank_eq (tree F x) hT]
    exact hα

theorem edge_measurable (F : Set (X × baire_space)) (b a : ℕ) :
    MeasurableSet {x | (tree F x).codedExtension b a} := by
  have hb := (node_open F (NatListCode.decode b)).measurableSet
  have ha := (node_open F (NatListCode.decode a)).measurableSet
  by_cases hp : prefixOf (NatListCode.decode a) (NatListCode.decode b) ∧
      (NatListCode.decode a).length < (NatListCode.decode b).length
  · simpa only [RootedPrefixTree.codedExtension, tree, hp.1, hp.2, and_true, Set.ofPred_and] using hb.inter ha
  · have heq : {x | (tree F x).codedExtension b a} = ∅ := by
      ext x
      simp only [RootedPrefixTree.codedExtension, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hp h.2.2
    rw [heq]
    exact MeasurableSet.empty

theorem rankLayer_measurable (F : Set (X × baire_space)) (α : Ordinal)
    (hα : α < Ordinal.omega 1) : MeasurableSet (rankLayer F α) :=
  OrdinalRankLayer.measurableSet (fun x => (tree F x).codedExtension) (edge_measurable F) α hα 0

omit [MeasurableSpace X] [BorelSpace X] in
theorem rankLayer_subset (F : Set (X × baire_space)) (hF : IsClosed F) (α : Ordinal) :
    rankLayer F α ⊆ (Prod.fst '' F)ᶜ := by
  rintro x ⟨hx, _⟩
  apply (wellFounded_iff F hF x).mp
  exact (tree F x).wellFounded_of_codedExtension
    ((tree F x).codedExtension_wellFounded_of_root_acc hx)

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    If $D\IncludedIn C$ is analytic, the Borel-image characterization in §{sec:analytic-sets} makes the set of codes of
    $\{T_x:x\in D\}$ analytic. These trees are well founded, so the
    \termuse{boundedness theorem for well-founded trees}, proved in §{sec:edst-boundedness}, gives a countable ordinal
    $\alpha$ bounding all their root ranks. Thus $D\IncludedIn C_{\le\alpha}$.
-/
/-- The analytic family of codes has a single countable root-rank bound. -/
theorem analytic_subset_rankLayer [PolishSpace X]
    (F : Set (X × baire_space)) (hF : IsClosed F) {D : Set X} (hD : AnalyticSet D)
    (hsub : D ⊆ (Prod.fst '' F)ᶜ) :
    ∃ α < Ordinal.omega 1, D ⊆ rankLayer F α := by
  have ha : AnalyticSet (code F '' D) :=
    analyticSet_image_via_baire_parametrization hD (code_measurable F)
  have hw : ∀ p ∈ code F '' D,
      WellFounded (strictTreeExtension (LambdaTree.treeFromCode p).tree) := by
    rintro p ⟨x, hx, rfl⟩
    rw [treeFromCode_code]
    exact (wellFounded_iff F hF x).mpr (hsub hx)
  let α := LambdaTree.familyRankSup (code F '' D) hw
  refine ⟨α, LambdaTree.analytic_rank_sup_lt ha hw, ?_⟩
  intro x hx
  have htree := (wellFounded_iff F hF x).mpr (hsub hx)
  refine ⟨(tree F x).codedExtension_wellFounded htree |>.apply 0, ?_⟩
  rw [RootedPrefixTree.coded_root_rank_eq (tree F x) htree]
  have hle := Ordinal.le_iSup
    (fun p : code F '' D => ((hw p.val p.property).apply (LambdaTree.treeFromCode p.val).root).rank)
    ⟨code F x, ⟨x, hx, rfl⟩⟩
  have hrank : ∀ (R S : RootedPrefixTree) (e : R = S)
      (hR : WellFounded (strictTreeExtension R.tree))
      (hS : WellFounded (strictTreeExtension S.tree)),
      (hR.apply R.root).rank = (hS.apply S.root).rank := by
    rintro R _ rfl _ _
    rfl
  rw [← hrank _ _ (treeFromCode_code F x) (hw _ ⟨x, hx, rfl⟩) htree]
  exact hle

end LusinNeighborhood

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] Put $C:=\SetDifference{X}{A_1}$. We construct a rank $\rho:C\to\omegaOneOrd$ whose initial segments
    $$C_{\le\alpha}:=\{x\in C:\rho(x)\le\alpha\}$$
    are Borel for countable $\alpha$, and then find one that contains $A_0$.
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Finally, disjointness gives $A_0\IncludedIn C$. Apply this bound to the analytic set $A_0$ and set $B:=C_{\le\alpha}$.
    Then $B$ is Borel, contains $A_0$, and is contained in $C=\SetDifference{X}{A_1}$.
    \end{proof}
-/
/-- The chapter's rank construction of a Borel separator. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Apply the rank construction to the coanalytic set $\SetDifference{X}{A_1}$ and rank boundedness to its analytic subset
    $A_0$. This gives the general-Polish-space version of effective Lusin separation proved in
    §{sec:edst-basis-norms-separation}; no second separation theorem is needed here.
-/
theorem lusinSeparation_via_ranks
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {A₀ A₁ : Set X} (hA₀ : AnalyticSet A₀) (hA₁ : AnalyticSet A₁) (hdisj : Disjoint A₀ A₁) :
    ∃ B : Set X, A₀ ⊆ B ∧ B ⊆ A₁ᶜ ∧ MeasurableSet B := by
  let := metrizableSpaceMetric X
  obtain ⟨F, hF, hproj⟩ := (analyticSet_iff_closed_baire_projection A₁).mp hA₁
  have hsub : A₀ ⊆ (Prod.fst '' F)ᶜ := by
    rw [hproj]
    exact hdisj.le_compl_right
  obtain ⟨α, hα, hA₀⟩ := LusinNeighborhood.analytic_subset_rankLayer F hF hA₀ hsub
  refine ⟨LusinNeighborhood.rankLayer F α, hA₀, ?_, LusinNeighborhood.rankLayer_measurable F α hα⟩
  simpa only [hproj] using LusinNeighborhood.rankLayer_subset F hF α

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    The theorem supplies the separation step in the proof of \termuse{Suslin's theorem} from §{sec:analytic-sets}. If $A$
    is both analytic and coanalytic, then $A$ and $\SetDifference{X}{A}$ are disjoint analytic sets; separating $A$ from
    $\SetDifference{X}{A}$ gives a Borel set squeezed between them, hence exactly $A$.
-/
/-- Applying the constructed separator to a set and its complement proves Suslin's implication. -/
theorem suslin_measurable_via_ranks
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A) (hAc : AnalyticSet Aᶜ) : MeasurableSet A := by
  obtain ⟨B, hAB, hBA, hB⟩ := lusinSeparation_via_ranks hA hAc disjoint_compl_right
  have heq : A = B := hAB.antisymm (by simpa only [compl_compl] using hBA)
  exact heq.symm ▸ hB

end PolishSpaceBook
