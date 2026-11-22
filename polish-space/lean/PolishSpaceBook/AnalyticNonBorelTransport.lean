module

public import PolishSpaceBook.AnalyticSetsSuslinSchemes
public import PolishSpaceBook.PerfectSetsStandardBorelCoding

@[expose] public section

/-!
# Transport of analytic non-Borel sets

The closed branch relation proves analyticity of ill-founded trees. Their
non-Borelness is a cited external theorem in the book, so it is an explicit
hypothesis of the final transport theorem, not a new axiom. The local proof
uses the book's Kuratowski isomorphism and refined-topology Borel-image argument.
-/

namespace PolishSpaceBook

open Set TopologicalSpace Topology MeasureTheory

/-- A Borel isomorphism preserves analyticity and non-Borelness. -/
theorem analytic_nonBorel_image
    {Y X : Type*} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : Y ≃ᵐ X) {A : Set Y}
    (hA : AnalyticSet A) (hnot : ¬ MeasurableSet A) :
    AnalyticSet (e '' A) ∧ ¬ MeasurableSet (e '' A) := by
  refine ⟨analyticSet_image_via_baire_parametrization hA e.measurable, ?_⟩
  intro h
  have hpre := h.preimage e.measurable
  exact hnot (by simpa only [e.preimage_image] using hpre)

/-- Suslin's theorem also excludes coanalyticity of this analytic non-Borel image. -/
theorem analytic_nonBorel_not_coanalytic
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {A : Set X}
    (hA : AnalyticSet A) (hnot : ¬ MeasurableSet A) : ¬ CoanalyticSet A := by
  intro hc
  exact hnot (suslin_theorem.mpr ⟨hA, hc⟩)

namespace AnalyticTrees

abbrev Space := {c : EffrosBorel.TreeIndicator // IsSubtree (EffrosBorel.treeOfIndicator c)}

instance : PolishSpace Space := by
  let := metrizableSpaceMetric EffrosBorel.TreeIndicator
  exact EffrosBorel.subtree_indicators_closed.polishSpace

instance : MeasurableSpace Space := borel Space
instance : BorelSpace Space := ⟨rfl⟩

def branchRelation : Set (Space × baire_space) :=
  {z | ∀ n, z.1.val (seqPrefix z.2 n) = true}

def illFounded : Set Space := Prod.fst '' branchRelation

/-- The projection consists exactly of trees with a nonempty body. -/
theorem mem_illFounded (T : Space) :
    T ∈ illFounded ↔ (treeBody (EffrosBorel.treeOfIndicator T.val)).Nonempty := by
  constructor
  · rintro ⟨⟨S, p⟩, hp, rfl⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨(T, p), hp, rfl⟩

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The inclusion of Borel sets into $\bSigma^1_1$ can be strict: there are analytic sets that are not Borel. To
    describe a tree example, let $\mathcal T$ be the space of trees on $\omega$,
    including the empty tree, viewed through their indicator functions as a closed subspace of $2^{\finseq{\omega}}$.
    Each violation of closure under initial segments is detected by two indicator coordinates, so the tree
    condition is closed and $\mathcal T$ is Polish.
    The branch relation is
    $$R:=\{\Pair{T}{p}\in\mathcal T\times\BaireSpace:\forall n\in\omega,\ \restrict{p}{n}\in T\}.$$
    For each finite word $s$, the condition $s\in T$ is clopen, and the cylinder $\cyl{s}$ is clopen. Therefore
    $$
    R=\bigcap_{s\in\finseq{\omega}}
    \left(\{T\in\mathcal T:s\in T\}\times\BaireSpace
    \;\cup\;\mathcal T\times\bigl(\SetDifference{\BaireSpace}{\cyl{s}}\bigr)\right)
    $$
    is closed. Its projection $I:=\{T\in\mathcal T:\TreeBody{T}\ne\emptyset\}$, the set of ill-founded trees, is analytic.
-/
/-- For each word, either it is in the tree or the sequence misses its cylinder. -/
theorem branchRelation_closed : IsClosed branchRelation := by
  have heq : branchRelation = ⋂ s : finseq ℕ,
      ({z : Space × baire_space | z.1.val s = true} ∪
       {z : Space × baire_space | z.2 ∉ cyl s}) := by
    ext z
    simp only [branchRelation, mem_ofPred_eq, mem_iInter, mem_union]
    constructor
    · intro h s
      by_cases hs : z.2 ∈ cyl s
      · exact Or.inl (seqPrefix_eq_of_mem_cyl hs ▸ h s.length)
      · exact Or.inr hs
    · intro h n
      exact (h (seqPrefix z.2 n)).resolve_right (not_not.mpr (mem_cyl_seqPrefix z.2 n))
  rw [heq]
  apply isClosed_iInter
  intro s
  apply IsClosed.union
  · exact (EffrosBorel.indicator_coordinate_clopen s).isClosed.preimage
      (continuous_subtype_val.comp continuous_fst)
  · exact (isClopen_cyl s).isOpen.isClosed_compl.preimage continuous_snd

theorem illFounded_analytic : AnalyticSet illFounded :=
  (analyticSet_iff_closed_baire_projection illFounded).mpr
    ⟨branchRelation, branchRelation_closed, rfl⟩

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    In particular, $\mathcal T$ is uncountable, since every subset of a countable Polish space is a countable union of
    closed singletons and hence Borel. For any uncountable Polish space $X$, \termuse{Kuratowski's isomorphism theorem}
    in §{sec:kuratowski-isomorphism} gives a Borel isomorphism $e:\mathcal T\to X$. The preceding Borel-image argument
    shows that $e(D)$ is analytic. If $e(D)$ were Borel, the identity
    $$e^{-1}(e(D))=D$$
    and measurability of $e$ would make $D$ Borel, a contradiction. Thus $e(D)$ is an analytic non-Borel subset of $X$;
    by \termuse{Suslin's theorem}, it is not coanalytic either.
-/
/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    The transport of this example to every uncountable Polish space is proved in
    §{sec:analytic-nonborel-transfer}, after the general Borel classification. The present tree example already
    shows that analytic projections need not be Borel.
-/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Recall the Polish tree space and its analytic non-Borel set of ill-founded trees from §{sec:analytic-sets}.
    The classification just proved now transports that example to an arbitrary uncountable Polish space.
-/
/-- Non-Borelness of ill-founded trees is the explicitly cited external input. -/
theorem exists_analytic_nonBorel
    (hIF : ¬ MeasurableSet illFounded)
    (X : Type*) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (hX : ¬ Countable X) :
    ∃ A : Set X, AnalyticSet A ∧ ¬ MeasurableSet A := by
  have hT : ¬ Countable Space := by
    intro hc
    let := hc
    exact hIF (Set.to_countable illFounded).measurableSet
  obtain ⟨e⟩ := kuratowskiIsomorphism_exists hT hX
  exact ⟨e '' illFounded, analytic_nonBorel_image e illFounded_analytic hIF⟩

end AnalyticTrees
end PolishSpaceBook
