module

public import PolishSpaceBook.LambdaEffectiveSeparation
public import PolishSpaceBook.LambdaProjectionOperations
public import PolishSpaceBook.LambdaEffectiveBoundedness

@[expose] public section

/-! # Starred comparisons for ranks of sections

Numerical coordinate projections and the finite map tests present both
analytic comparisons at the original parameter. Reversing and complementing
them gives the coanalytic mates; agreement requires a well-founded right section.
-/
namespace PolishSpaceBook
open Set MeasureTheory NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree

private theorem rootedTree_ext : ∀ T S : RootedPrefixTree, T.tree = S.tree → T = S := by
  rintro ⟨t,ht,hrt⟩ ⟨s,hs,hrs⟩ rfl
  rfl

theorem rootedSection_coordinatePreimage {ε : ℕ → ℕ} (T : PairTree ε)
    {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) (x : ℕ → ℕ) :
    rootedSection (T.coordinatePreimage hF) x = rootedSection T (f ∘ x) := by
  apply rootedTree_ext
  ext t
  simp only [rootedSection,PairTree.coordinatePreimage,Set.mem_ofPred_eq,
    seqPrefix,List.map_ofFn,Function.comp_def]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Fix an $\varepsilon$-recursive pair tree $T$. Retain an empty root in its sections and put
    $$T_x:=\{\emptySeq\}\cup\{t:\Pair{\restrict{x}{\Length{t}}}{t}\in T\},\qquad
    A:=\{x:T_x\text{ is well founded}\}.$$
    Then $A=\SetDifference{\BaireSpace}{\pi_0([T])}$. On $A$ define $\varphi(x):=\rho(T_x)$.
    Let $L(x,y)$ assert that there is a root-preserving map from $T_x$ to $T_y$ preserving strict extension.
    Let $K(x,y)$ assert the existence of a strict-extension-preserving map that sends the root to a nonempty node.
    Define the four relations on the whole ambient space by
    $$\begin{aligned}
    x\leq_\Sigma y&\quad\Longleftrightarrow\quad L(x,y),&
    x\leq_\Pi y&\quad\Longleftrightarrow\quad\neg K(y,x),\\
    x<_\Sigma y&\quad\Longleftrightarrow\quad K(x,y),&
    x<_\Pi y&\quad\Longleftrightarrow\quad\neg L(y,x).
    \end{aligned}$$
-/
def sectionLe {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ) : Prop :=
  TreeComparisonLe (rootedSection T x) (rootedSection T y)

def sectionLt {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ) : Prop :=
  TreeComparisonLt (rootedSection T x) (rootedSection T y)

def sectionLePi {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ) : Prop :=
  ¬ sectionLt T y x

def sectionLtPi {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ) : Prop :=
  ¬ sectionLe T y x

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    For the comparison relations, encode the input pair by $z=\NamePair{x}{y}$ and form two pair trees
    $$\begin{aligned}
    U&:=\{\Pair{s}{t}:\Pair{s_1}{t}\in T\},\\
    V&:=\{\Pair{s}{t}:\Pair{s_2}{t}\in T\},
    \end{aligned}$$
    where $s_1,s_2$ are the coordinatewise numerical projections. Their rooted sections are exactly $T_x,T_y$.
    The list-map and coordinate-preimage programs of §{sec:lambda-kleene-brouwer} decide their membership.
    Apply the finite map tests of §{sec:lambda-comparison-programs}, with either the empty-root or nonempty-root test.
    Their projections are $L$ and $K$, respectively. All programs use the same $\varepsilon$. Swapping the two input
    coordinates is another numerical pairing of projections, so the complements defining the two remaining relations
    are coanalytic at that parameter.
-/
theorem sectionLe_projected {ε : ℕ → ℕ} (T : PairTree ε) :
    ProjectedRelation ε (sectionLe T) := by
  refine ⟨comparisonLeTree (T.coordinatePreimage (projection_computes true))
    (T.coordinatePreimage (projection_computes false)),?_⟩
  rw [pairTreeProjection_comparisonLeTree]
  ext z
  simp only [sectionLe,Set.mem_ofPred_eq,rootedSection_coordinatePreimage]
  rfl

theorem sectionLt_projected {ε : ℕ → ℕ} (T : PairTree ε) :
    ProjectedRelation ε (sectionLt T) := by
  refine ⟨comparisonLtTree (T.coordinatePreimage (projection_computes true))
    (T.coordinatePreimage (projection_computes false)),?_⟩
  rw [pairTreeProjection_comparisonLtTree]
  ext z
  simp only [sectionLt,Set.mem_ofPred_eq,rootedSection_coordinatePreimage]
  rfl

/-- Swapping coordinates is a numerical pairing of the two projections. -/
theorem ProjectedRelation.swap {ε : ℕ → ℕ} {R : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (h : ProjectedRelation ε R) : ProjectedRelation ε (fun x y => R y x) := by
  have h' := h.coordinatePreimage ((projection_computes false).pair (projection_computes true))
  change Projected ε {p | R (leftBaire (pairBaire (rightBaire p) (leftBaire p)))
    (rightBaire (pairBaire (rightBaire p) (leftBaire p)))} at h'
  change Projected ε {p | R (rightBaire p) (leftBaire p)}
  simpa only [leftBaire_pair,rightBaire_pair] using h'

theorem sectionLePi_complement_projected {ε : ℕ → ℕ} (T : PairTree ε) :
    ProjectedRelation ε (fun x y => ¬ sectionLePi T x y) := by
  simpa only [sectionLePi,not_not] using (sectionLt_projected T).swap

theorem sectionLtPi_complement_projected {ε : ℕ → ℕ} (T : PairTree ε) :
    ProjectedRelation ε (fun x y => ¬ sectionLtPi T x y) := by
  simpa only [sectionLtPi,not_not] using (sectionLe_projected T).swap

/-- The root rank on the domain of well-founded sections. -/
noncomputable def sectionRank {ε : ℕ → ℕ} (T : PairTree ε) (x : ℕ → ℕ)
    (hx : WellFounded (strictTreeExtension (rootedSection T x).tree)) : Ordinal :=
  (hx.apply (rootedSection T x).root).rank

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Fix $y\in A$. If $x\in A$, tree-rank comparison identifies $L(x,y)$ with the non-strict rank inequality and
    $K(x,y)$ with the strict inequality. For the latter, the root image has rank strictly below the target root;
    conversely a strict rank inequality supplies a nonempty target node whose rank dominates the source root, after
    which the same comparison construction applies. If $x\notin A$, no extension-preserving map can send its
    ill-founded tree into the well-founded target. A branch in the ill-founded tree supplies both reverse maps,
    by sending a word to the branch prefix of its length, or of its length plus one. Thus both analytic comparisons
    and both coanalytic comparisons are false. This proves the two equivalences for every first argument.
-/
theorem sectionLe_iff_rank {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ)
    (hy : WellFounded (strictTreeExtension (rootedSection T y).tree)) :
    sectionLe T x y ↔ ∃ hx : WellFounded (strictTreeExtension (rootedSection T x).tree),
      sectionRank T x hx ≤ sectionRank T y hy := by
  constructor
  · rintro ⟨f,hr,hmap⟩
    have hx := wellFounded_of_relation_preserving hy f (fun {_ _} h => hmap _ _ h)
    refine ⟨hx,?_⟩
    let : WellFounded (strictTreeExtension (rootedSection T x).tree) := hx
    let : WellFounded (strictTreeExtension (rootedSection T y).tree) := hy
    exact (treeComparisonLe_iff_rank_le _ _).mp ⟨f,hr,hmap⟩
  · rintro ⟨hx,h⟩
    let : WellFounded (strictTreeExtension (rootedSection T x).tree) := hx
    let : WellFounded (strictTreeExtension (rootedSection T y).tree) := hy
    exact (treeComparisonLe_iff_rank_le _ _).mpr h

theorem sectionLt_iff_rank {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ)
    (hy : WellFounded (strictTreeExtension (rootedSection T y).tree)) :
    sectionLt T x y ↔ ∃ hx : WellFounded (strictTreeExtension (rootedSection T x).tree),
      sectionRank T x hx < sectionRank T y hy := by
  constructor
  · rintro ⟨f,hr,hmap⟩
    have hx := wellFounded_of_relation_preserving hy f (fun {_ _} h => hmap _ _ h)
    refine ⟨hx,?_⟩
    let : WellFounded (strictTreeExtension (rootedSection T x).tree) := hx
    let : WellFounded (strictTreeExtension (rootedSection T y).tree) := hy
    exact (treeComparisonLt_iff_rank_lt _ _).mp ⟨f,hr,hmap⟩
  · rintro ⟨hx,h⟩
    let : WellFounded (strictTreeExtension (rootedSection T x).tree) := hx
    let : WellFounded (strictTreeExtension (rootedSection T y).tree) := hy
    exact (treeComparisonLt_iff_rank_lt _ _).mpr h

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Starred comparisons and Borel layers of tree ranks
-/
theorem sectionLe_agreement {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ)
    (hy : WellFounded (strictTreeExtension (rootedSection T y).tree)) :
    sectionLe T x y ↔ sectionLePi T x y :=
  treeComparison_complement (rootedSection T y) (rootedSection T x) (Or.inl hy)

theorem sectionLt_agreement {ε : ℕ → ℕ} (T : PairTree ε) (x y : ℕ → ℕ)
    (hy : WellFounded (strictTreeExtension (rootedSection T y).tree)) :
    sectionLt T x y ↔ sectionLtPi T x y := by
  have h := treeComparison_complement (rootedSection T x) (rootedSection T y) (Or.inr hy)
  exact not_not.symm.trans (not_congr h).symm

/-- One recursive bound for the ranks in a relative analytic subfamily. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Bounded Borel layers of tree ranks
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For the constant-zero parameter the bound is below $\churchKleeneOrd$.
-/
theorem sectionRank_uniform_bound {ε : ℕ → ℕ} (T : PairTree ε) {B : Set (ℕ → ℕ)}
    (hB : Projected ε B)
    (hw : ∀ x ∈ B, WellFounded (strictTreeExtension (rootedSection T x).tree)) :
    ∃ W : LambdaRelative.WellOrderPresentation ε,
      W.orderType < LambdaRelative.recursiveOrdinalBound ε ∧
      ∀ x (hx : x ∈ B), sectionRank T x (hw x hx) < W.orderType := by
  obtain ⟨U,rfl⟩ := hB
  have hd : Disjoint (pairTreeProjection U.tree) (pairTreeProjection T.tree) := by
    apply Set.disjoint_left.mpr
    intro x hx ht
    obtain ⟨p,hp⟩ := (branch_rootedSection_iff T x).mpr ht
    exact (prefixTreeWellFounded_iff _ (rootedSection T x).downward).mpr (hw x hx) ⟨p,hp⟩
  obtain ⟨W,hW,hb⟩ := uniform_section_ordinal_bound U T hd
  refine ⟨W,hW,?_⟩
  intro x hx
  obtain ⟨hs,h⟩ := hb x hx
  exact h



def sectionDomain {ε : ℕ → ℕ} (T : PairTree ε) : Set (ℕ → ℕ) :=
  {x | WellFounded (strictTreeExtension (rootedSection T x).tree)}

theorem sectionDomain_complement {ε : ℕ → ℕ} (T : PairTree ε) :
    (sectionDomain T)ᶜ = pairTreeProjection T.tree := by
  ext x
  change ¬ WellFounded (strictTreeExtension (rootedSection T x).tree) ↔ _
  rw [← branch_rootedSection_iff T x,← prefixTreeWellFounded_iff _ (rootedSection T x).downward]
  exact not_not

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The complement of $A$ is the projection of the recursive pair tree, so $A$ is coanalytic at the original
    parameter. Each node rank is countable. Indeed, well-founded induction shows that every ordinal below a node's
    rank occurs as the rank of another node: in the defining supremum choose a successor whose rank still dominates
    the desired ordinal and apply the induction hypothesis. There are only countably many nodes, so there are only
    countably many ordinals below each rank.
-/
theorem sectionRank_countable {ε : ℕ → ℕ} (T : PairTree ε) (x : ℕ → ℕ)
    (hx : WellFounded (strictTreeExtension (rootedSection T x).tree)) :
    sectionRank T x hx < Ordinal.omega 1 := by
  let : WellFounded (strictTreeExtension (rootedSection T x).tree) := hx
  have hc : (Set.Iio (sectionRank T x hx)).Countable :=
    (Set.countable_range (WellFounded.rank (strictTreeExtension (rootedSection T x).tree))).mono
      (fun β hβ => WellFounded.mem_range_rank_of_le hβ.le)
  have hk := Cardinal.le_aleph0_iff_set_countable.mpr hc
  rw [Cardinal.mk_Iio_ordinal] at hk
  have hcard : (sectionRank T x hx).card ≤ Cardinal.aleph0 := by
    have hk' : Cardinal.lift.{1} (sectionRank T x hx).card ≤
        Cardinal.lift.{1} (Cardinal.aleph0.{0}) := by
      simpa only [Cardinal.lift_aleph0] using hk
    exact Cardinal.lift_le.mp hk'
  exact Cardinal.lt_omega_iff_card_lt.mpr (Cardinal.lt_aleph_one_iff.mpr hcard)

theorem sectionRank_sup_lt {ε : ℕ → ℕ} (T : PairTree ε) {B : Set (ℕ → ℕ)}
    (hB : Projected ε B)
    (hw : ∀ x ∈ B, WellFounded (strictTreeExtension (rootedSection T x).tree)) :
    (⨆ x : B, sectionRank T x.val (hw x.val x.property)) <
      LambdaRelative.recursiveOrdinalBound ε := by
  obtain ⟨W,hW,hb⟩ := sectionRank_uniform_bound T hB hw
  exact (Ordinal.iSup_le (fun x : B => (hb x.val x.property).le)).trans_lt hW

private theorem continuous_pair_right (y : ℕ → ℕ) : Continuous (fun x => pairBaire x y) := by
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := fun k : ℕ => Nat.pair k (y n))).comp
    (continuous_apply n)

private theorem continuous_pair_left (y : ℕ → ℕ) : Continuous (fun x => pairBaire y x) := by
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := fun k : ℕ => Nat.pair (y n) k)).comp
    (continuous_apply n)

theorem sectionLe_measurable {ε : ℕ → ℕ} (T : PairTree ε) (y : ℕ → ℕ)
    (hy : WellFounded (strictTreeExtension (rootedSection T y).tree)) :
    MeasurableSet {x | sectionLe T x y} := by
  have ha := (sectionLe_projected T).analyticSet.preimage (continuous_pair_right y)
  have hb := (sectionLt_projected T).analyticSet.preimage (continuous_pair_left y)
  have he : {x | sectionLe T x y}ᶜ = {x | sectionLt T y x} := by
    ext x
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,sectionLe_agreement T x y hy,sectionLePi,not_not]
  apply AnalyticSet.measurableSet_of_compl
  · simpa only [Set.preimage_ofPred_eq,leftBaire_pair,rightBaire_pair] using ha
  · rw [he]
    simpa only [Set.preimage_ofPred_eq,leftBaire_pair,rightBaire_pair] using hb

def sectionRankLayer {ε : ℕ → ℕ} (T : PairTree ε) (α : Ordinal) : Set (ℕ → ℕ) :=
  {x | ∃ hx : WellFounded (strictTreeExtension (rootedSection T x).tree), sectionRank T x hx ≤ α}

theorem sectionRankLayer_at_rank {ε : ℕ → ℕ} (T : PairTree ε) (y : ℕ → ℕ)
    (hy : WellFounded (strictTreeExtension (rootedSection T y).tree)) :
    sectionRankLayer T (sectionRank T y hy) = {x | sectionLe T x y} := by
  ext x
  exact (sectionLe_iff_rank T x y hy).symm

private theorem countable_ordinal_Iic (α : Ordinal) (hα : α < Ordinal.omega 1) :
    (Set.Iic α).Countable := by
  have hc : α.card ≤ Cardinal.aleph0 :=
    Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp hα)
  have hsucc : (α+1).card ≤ Cardinal.aleph0 := by
    rw [Ordinal.card_add_one]
    exact Cardinal.add_le_aleph0.mpr ⟨hc,by simp⟩
  have hi : (Set.Iio (α+1)).Countable := by
    apply Cardinal.le_aleph0_iff_set_countable.mp
    rw [Cardinal.mk_Iio_ordinal]
    simpa using Cardinal.lift_le.mpr hsucc
  exact hi.mono (fun β hβ => by
    change β < α+1
    simpa only [Order.succ_eq_add_one] using hβ.trans_lt (Order.lt_succ α))

/-- At most countably many attained ranks are needed to cover a countable layer. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    For fixed $y\in A$, the set $\{x:L(x,y)\}$ and its complement $\{x:K(y,x)\}$ are analytic, since fixing a
    coordinate is continuous. \termuse{Suslin's theorem} makes $A_{\le\varphi(y)}$ Borel.
    Now fix $\alpha<\omegaOneOrd$ and let
    $$D:=\{\beta\le\alpha:\exists y\in A\ (\varphi(y)=\beta)\}.$$
    This is a countable set of ordinals. For each $\beta\in D$, choose $y_\beta\in A$ with
    $\varphi(y_\beta)=\beta$. Then
    $$A_{\le\alpha}=\bigcup_{\beta\in D}A_{\le\varphi(y_\beta)}.$$
    For the forward inclusion use the rank of the given point as the index; the reverse inclusion follows from the
    bound on every index. This is a countable union of Borel sets, including the empty union when no rank is attained
    below the bound. The choices prove Borelness and are not asserted to be computable.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Starred comparisons and Borel layers of tree ranks
-/
theorem sectionRankLayer_measurable {ε : ℕ → ℕ} (T : PairTree ε) (α : Ordinal)
    (hα : α < Ordinal.omega 1) : MeasurableSet (sectionRankLayer T α) := by
  classical
  let D : Set Ordinal := {β | β ≤ α ∧ ∃ y hy, sectionRank T y hy = β}
  have hD : D.Countable := (countable_ordinal_Iic α hα).mono (fun _ h => h.1)
  have hm : ∀ β ∈ D, MeasurableSet (sectionRankLayer T β) := by
    rintro β ⟨_,y,hy,rfl⟩
    rw [sectionRankLayer_at_rank]
    exact sectionLe_measurable T y hy
  have he : sectionRankLayer T α = ⋃ β ∈ D, sectionRankLayer T β := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨hx,h⟩
      exact ⟨sectionRank T x hx,⟨h,x,hx,rfl⟩,hx,le_rfl⟩
    · rintro ⟨β,hβ,hx,hxβ⟩
      exact ⟨hx,hxβ.trans hβ.1⟩
  rw [he]
  exact MeasurableSet.biUnion hD hm


/-- Recoding the two existing node sets preserves the rank function itself. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $C=\pi_0([U_C])$ at the same parameter. The projections of $U_C$ and $T$ are disjoint. The joint tree in
    §{sec:edst-boundedness} gives a single $\varepsilon$-recursive well-order whose type strictly bounds every
    root rank of $T_x$ for $x\in C$. Taking the supremum gives the displayed inequality, and the preceding
    proposition supplies the Borel layer. For an arbitrary analytic subset, encode the node sets of its pair-tree
    presentation and of the fixed tree
    in one parameter. This leaves the section trees and their ranks unchanged. The resulting relative ordinal
    bound is countable.
    \end{proof}
-/
theorem analytic_subset_borel_rank_layer {ε : ℕ → ℕ} (T : PairTree ε)
    {B : Set (ℕ → ℕ)} (hB : AnalyticSet B)
    (hw : ∀ x ∈ B, WellFounded (strictTreeExtension (rootedSection T x).tree)) :
    ∃ α < Ordinal.omega 1, MeasurableSet (sectionRankLayer T α) ∧ B ⊆ sectionRankLayer T α := by
  classical
  obtain ⟨δ,U,hU⟩ := (analyticSet_iff_exists_parameter B).mp hB
  let S : ℕ → Set (List ℕ × List ℕ) := fun i => if i = 0 then T.tree else U.tree
  have hs : ∀ i z, z ∈ S i → z.1.length = z.2.length := by
    intro i z h
    by_cases hi : i = 0
    · exact T.synchronized z (by simpa [S,hi] using h)
    · exact U.synchronized z (by simpa [S,hi] using h)
  have hd : ∀ i z, z ∈ S i → ∀ n, (z.1.take n,z.2.take n) ∈ S i := by
    intro i z h n
    by_cases hi : i = 0
    · simpa [S,hi] using T.downward z (by simpa [S,hi] using h) n
    · simpa [S,hi] using U.downward z (by simpa [S,hi] using h) n
  obtain ⟨η,V,hV,_⟩ := pairTrees_in_one_parameter S hs hd
  have hzero : (V 0).tree = T.tree := by simpa [S] using hV 0
  have hone : (V 1).tree = U.tree := by simpa [S] using hV 1
  have he (x : ℕ → ℕ) : rootedSection (V 0) x = rootedSection T x := by
    apply rootedTree_ext
    simp only [rootedSection,hzero]
  have hw' : ∀ x ∈ B, WellFounded (strictTreeExtension (rootedSection (V 0) x).tree) := by
    intro x hx
    rw [he x]
    exact hw x hx
  have hB' : Projected η B := ⟨V 1,by simpa only [hone] using hU⟩
  obtain ⟨W,hW,hb⟩ := sectionRank_uniform_bound (V 0) hB' hw'
  have hc : W.orderType < Ordinal.omega 1 := by
    apply Cardinal.lt_omega_iff_card_lt.mpr
    apply Cardinal.lt_aleph_one_iff.mpr
    exact (Ordinal.card_le_card hW.le).trans (LambdaRelative.recursiveOrdinalBound_countable η)
  refine ⟨W.orderType,hc,sectionRankLayer_measurable T W.orderType hc,?_⟩
  intro x hx
  refine ⟨hw x hx,?_⟩
  have h := (hb x hx).le
  have hrank : ∀ (R S : RootedPrefixTree) (e : R = S)
      (hR : WellFounded (strictTreeExtension R.tree))
      (hS : WellFounded (strictTreeExtension S.tree)),
      (hR.apply R.root).rank = (hS.apply S.root).rank := by
    rintro R _ rfl _ _
    rfl
  change ((hw x hx).apply (rootedSection T x).root).rank ≤ W.orderType
  rw [← hrank _ _ (he x) (hw' x hx) (hw x hx)]
  exact h

end LambdaTree
end PolishSpaceBook
