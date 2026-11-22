module

public import PolishSpaceBook.EffrosBorelCompact

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Pruned-tree realization of the Baire Effros space

The branch construction below identifies pruning with the countable open
no-terminal-node conditions used in the book's first proof.
-/

namespace PolishSpaceBook

open Set TopologicalSpace Topology

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] \emph{Baire-space case.} By §{sec:closed-sets-trees}, the map
    $$
    \begin{aligned}
    \ClosedSets{\BaireSpace}
    &\;\longrightarrow\;2^{\finseq{\omega}},\\
    C
    &\;\mapsto\; T_C := \{s : \cyl{s} \cap C \ne \emptyset\},
    \end{aligned}
    $$
    is a bijection onto the pruned trees, viewed as a subset of $2^{\finseq{\omega}}$. For a subtree $T$, pruning is
    equivalent to the condition
    $$\forall s\in T\;\exists a\in\omega\quad s\concat\langle a\rangle\in T.$$
    Indeed, a branch through a node supplies such an immediate extension. Conversely, starting from any node, choose
    successive immediate extensions. Their union is an infinite sequence through that node; every finite prefix lies in
    $T$ because $T$ is closed under initial segments. The empty tree satisfies the condition and represents the empty set.
-/
/-- Choose successive immediate extensions and take their union. -/
theorem isPruned_iff_has_child {A : Type*} {T : Set (finseq A)} (hT : IsSubtree T) :
    IsPruned T ↔ ∀ s ∈ T, ∃ a : A, s ++ [a] ∈ T := by
  classical
  constructor
  · intro h s hs
    obtain ⟨x, hx, hxs⟩ := h hs
    refine ⟨x s.length, ?_⟩
    simpa [seqPrefix_succ_eq_concat, seqPrefix_eq_of_mem_cyl hxs] using hx (s.length + 1)
  · intro h s hs
    let next (t : T) : T := ⟨t.val ++ [Classical.choose (h t.val t.property)],
      Classical.choose_spec (h t.val t.property)⟩
    let u : ℕ → T := fun n => next^[n] ⟨s, hs⟩
    have hstep (n : ℕ) : (u (n + 1)).val = (u n).val ++
        [Classical.choose (h (u n).val (u n).property)] := by
      exact congrArg Subtype.val (Function.iterate_succ_apply' next n ⟨s, hs⟩)
    have hlen (n : ℕ) : (u n).val.length = s.length + n := by
      induction n with
      | zero => rfl
      | succ n ih => simp [hstep, ih, Nat.add_assoc]
    have hpref {n m : ℕ} (hnm : n ≤ m) : (u n).val <+: (u m).val := by
      induction m, hnm using Nat.le_induction with
      | base => exact List.prefix_rfl
      | succ m hnm ih => exact ih.trans (hstep m ▸ List.prefix_append _ _)
    let x : ℕ → A := fun i => (u (i + 1)).val[i]'(by rw [hlen]; omega)
    have hx (n : ℕ) : x ∈ cyl (u n).val := by
      intro i hi
      change (u (i + 1)).val[i]'(by rw [hlen]; omega) = (u n).val[i]
      by_cases hin : i + 1 ≤ n
      · exact (hpref hin).getElem (by rw [hlen]; omega)
      · exact ((hpref (by omega : n ≤ i + 1)).getElem hi).symm
    refine ⟨x, ?_, hx 0⟩
    intro n
    apply hT (u n).property
    have heq := seqPrefix_eq_of_mem_cyl (hx n)
    rw [← heq]
    exact seqPrefix_prefixOf_of_le x (by rw [hlen]; omega)


namespace EffrosBorel

attribute [local instance] measurableSpace

abbrev TreeIndicator := finseq ℕ → Bool

def treeOfIndicator (c : TreeIndicator) : Set (finseq ℕ) := {s | c s = true}

def prunedIndicators : Set TreeIndicator :=
  {c | IsSubtree (treeOfIndicator c) ∧ IsPruned (treeOfIndicator c)}

theorem indicator_coordinate_clopen (s : finseq ℕ) :
    IsClopen {c : TreeIndicator | c s = true} :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply s)

/-- Prefix closure is a closed condition in the indicator product. -/
theorem subtree_indicators_closed : IsClosed {c : TreeIndicator | IsSubtree (treeOfIndicator c)} := by
  have heq : {c : TreeIndicator | IsSubtree (treeOfIndicator c)} =
      ⋂ s : finseq ℕ, ⋂ t : finseq ℕ, ⋂ (_ : prefixOf s t),
        ({c | c t = true}ᶜ ∪ {c | c s = true}) := by
    ext c
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
    simp only [IsSubtree, treeOfIndicator, mem_ofPred_eq]
    constructor
    · intro h s t hst
      by_cases ht : c t = true
      · exact Or.inr (h ht hst)
      · exact Or.inl ht
    · intro h s t ht hst
      exact (h s t hst).resolve_left (not_not.mpr ht)
  rw [heq]
  exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
    ((indicator_coordinate_clopen t).compl.union (indicator_coordinate_clopen s)).isClosed

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Closure under initial segments is a closed condition on the indicator of $T$: each implication between two fixed
    coordinates is clopen, and there are only countably many pairs of finite words. For each fixed $s$, the displayed
    extension condition is open, since it either excludes $s$ or requires one of its countably many immediate extensions.
    Thus pruned trees form a $\bPi^0_2$ subset of $2^{\finseq{\omega}}$. By \termuse{Alexandrov's theorem} in
    §{sec:alexandrov-theorem}, this is a Polish subspace. Each Effros–Borel generator
    $\{C : C \cap \cyl{s} \ne \emptyset\}$ corresponds under the bijection to the clopen condition $\{T : s \in T\}$.
    These coordinate conditions generate the Borel structure of the indicator product and its subspace. Conversely,
    every open subset of $\BaireSpace$ is a countable union of cylinders, so every open hit is a countable union of
    cylinder hits. Hence the bijection and its inverse are measurable, and $\ClosedSets{\BaireSpace}$ is standard Borel.
-/
/-- Each node has an immediate extension: one open condition for each finite word. -/
theorem pruned_indicators_gdelta : IsGδ prunedIndicators := by
  have heq : prunedIndicators = {c | IsSubtree (treeOfIndicator c)} ∩
      ⋂ s : finseq ℕ, ({c | c s = true}ᶜ ∪ ⋃ a : ℕ, {c | c (s ++ [a]) = true}) := by
    ext c
    simp only [prunedIndicators, mem_ofPred_eq, mem_inter_iff, mem_iInter,
      mem_union, mem_compl_iff, mem_iUnion]
    constructor
    · rintro ⟨hT, hp⟩
      exact ⟨hT, fun s => or_iff_not_imp_left.mpr (fun hs => (isPruned_iff_has_child hT).mp hp s (not_not.mp hs))⟩
    · rintro ⟨hT, hp⟩
      exact ⟨hT, (isPruned_iff_has_child hT).mpr fun s hs => (hp s).resolve_left (not_not.mpr hs)⟩
  rw [heq]
  apply subtree_indicators_closed.isGδ.inter
  apply IsGδ.iInter
  intro s
  exact ((indicator_coordinate_clopen s).compl.isOpen.union
    (isOpen_iUnion fun a => (indicator_coordinate_clopen (s ++ [a])).isOpen)).isGδ

theorem pruned_indicators_polish : PolishSpace prunedIndicators := by
  let := metrizableSpaceMetric TreeIndicator
  exact gdelta_subspace_polish pruned_indicators_gdelta

/-- Closed-set codes as actual zero-one indicators, with the empty tree allowed. -/
noncomputable def closedIndicator (F : Closeds (ℕ → ℕ)) : TreeIndicator :=
  fun s => @decide (s ∈ closedTreeCode (F : Set (ℕ → ℕ))) (Classical.propDecidable _)

@[simp] theorem treeOf_closedIndicator (F : Closeds (ℕ → ℕ)) :
    treeOfIndicator (closedIndicator F) = closedTreeCode (F : Set (ℕ → ℕ)) := by
  ext s
  simp [treeOfIndicator, closedIndicator]

def indicatorBody (c : prunedIndicators) : Closeds (ℕ → ℕ) :=
  ⟨treeBody (treeOfIndicator c.val), isClosed_treeBody _⟩

noncomputable def closedIndicatorEquiv : Closeds (ℕ → ℕ) ≃ prunedIndicators where
  toFun F := ⟨closedIndicator F, by
    change IsSubtree (treeOfIndicator (closedIndicator F)) ∧ IsPruned (treeOfIndicator (closedIndicator F))
    rw [treeOf_closedIndicator]
    exact ⟨closedTreeCode_isSubtree _, closedTreeCode_isPruned _⟩⟩
  invFun := indicatorBody
  left_inv F := by
    apply Closeds.ext
    change treeBody (treeOfIndicator (closedIndicator F)) = _
    rw [treeOf_closedIndicator, treeBody_closedTreeCode_eq_of_closed F.isClosed]
  right_inv c := by
    apply Subtype.ext
    funext s
    apply Bool.eq_iff_iff.mpr
    change (closedIndicator (indicatorBody c) s = true) ↔ c.val s = true
    simp only [closedIndicator, decide_eq_true_eq]
    change s ∈ closedTreeCode (treeBody (treeOfIndicator c.val)) ↔ _
    rw [closedTreeCode_treeBody_eq_of_pruned c.property.2]
    rfl

theorem closedIndicator_measurable : Measurable closedIndicator := by
  apply measurable_pi_iff.mpr
  intro s
  apply measurable_to_bool
  have heq : (fun F => closedIndicator F s) ⁻¹' {true} = hit (cyl s) := by
    ext F
    simp [closedIndicator, closedTreeCode, hit, inter_comm]
  rw [heq]
  exact measurable_hit (isOpen_cyl s)

/-- An arbitrary open hit is the countable union of its basic cylinder hits. -/
theorem indicatorBody_measurable : Measurable indicatorBody := by
  apply measurable_iff_hit.mpr
  intro U hU
  have heq : indicatorBody ⁻¹' hit U =
      ⋃ s : finseq ℕ, ⋃ (_ : cyl s ⊆ U), {c : prunedIndicators | c.val s = true} := by
    ext c
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, hxU⟩
      obtain ⟨s, hxs, hsU⟩ := exists_cyl_subset_of_mem_open hxU hU
      refine ⟨s, hsU, ?_⟩
      change s ∈ treeOfIndicator c.val
      rw [← closedTreeCode_treeBody_eq_of_pruned c.property.2]
      exact ⟨x, hxs, hx⟩
    · rintro ⟨s, hsU, hs⟩
      obtain ⟨x, hx, hxs⟩ := c.property.2 hs
      exact ⟨x, hx, hsU hxs⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro _
  exact ((indicator_coordinate_clopen s).isOpen.preimage continuous_subtype_val).measurableSet

noncomputable def closedIndicatorMeasurableEquiv : Closeds (ℕ → ℕ) ≃ᵐ prunedIndicators where
  toEquiv := closedIndicatorEquiv
  measurable_toFun := closedIndicator_measurable.subtype_mk
  measurable_invFun := indicatorBody_measurable

/-- The Baire-space proof transfers the Polish pruned-tree realization along
its explicit cylinder-hit measurable equivalence. -/
theorem baire_standardBorel_via_pruned_trees : StandardBorelSpace (Closeds (ℕ → ℕ)) := by
  let : PolishSpace prunedIndicators := pruned_indicators_polish
  exact standardBorel_of_measurableEquiv closedIndicatorMeasurableEquiv

end EffrosBorel
end PolishSpaceBook
