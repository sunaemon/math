module

public import PolishSpaceBook.BorelInternalCounterexampleTree
public import PolishSpaceBook.BorelPointComposition
public import PolishSpaceBook.BorelInternalInterpretation
public import PolishSpaceBook.SetTheoryInternalTreeBranches

@[expose] public section

/-! # Internal counterexamples and transfer of closed Borel inclusions

Projecting an internal branch preserves its point graph. Conversely, existence
of an external branch in the internal counterexample tree yields an internal
branch by the already established tree theorem. No new certificate-selection
or rank argument is required.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels NamedLambda
universe u

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

include hM hinf hpair hunion hpower hsep

/-- An internal paired branch yields an internal point outside the coded Borel set. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Given an internal branch $z$, project its entries onto their first coordinates to obtain $x$.
    The lemma gives $g_x\in M$. The branch analysis of §{sec:ranked-closed-inclusions} gives
    $x\in\TreeBody{T}$ and a negative evaluation certificate, hence $x\notin B_c$.
-/
theorem internal_point_of_counterexample_branch (c : BorelExpression) (hc : c.Valid)
    (T : Set (List ℕ)) (z : ℕ → ℕ) (bit : Bool := false)
    (hz : z ∈ treeBody (inclusionTree c T bit))
    (hzM : pointGraph z ∈ M) :
    ∃ x ∈ treeBody T, pointGraph x ∈ M ∧ (if bit then x ∈ c.evaluate hc.2.2.2.2.2 cylinderBasis [] else
      x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis []) := by
  obtain ⟨hx, hcert⟩ := (mem_inclusionTree_body c T z bit).mp hz
  have hproj : pointGraph (fun n => n.unpair.1) ∈ M := by
    simpa only [pointGraph, sequenceGraph, ite_true] using
      naturalProjectionGraph_mem hM hinf hpair hunion hpower hsep true
  refine ⟨fun n => (z n).unpair.1, hx,
    pointGraph_comp_mem hM hinf hpair hunion hpower hsep z (fun n => n.unpair.1) hzM hproj, ?_⟩
  exact (certificateSide_iff c hc _ bit).mp ⟨_, hcert⟩

variable
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)
include hrep hchoice

/-- The counterexample node set and its relation satisfy the earlier internal-branch theorem. -/
theorem no_counterexample_branch_of_no_internal_branch (c : BorelExpression)
    (hcM : c.labelGraph ∈ M) (T : Set (List ℕ)) (hTM : wordTreeSet T ∈ M) (bit : Bool := false)
    (hno : ¬ ∃ z, z ∈ treeBody (inclusionTree c T bit) ∧ pointGraph z ∈ M) :
    ¬ ∃ z, z ∈ treeBody (inclusionTree c T bit) := by
  let W : M := ⟨wordTreeSet (inclusionTree c T bit),
    inclusionTree_mem hM hinf hpair hunion hpower hsep c hcM T hTM bit⟩
  let R : M := ⟨wordExtensionRelation W.val,
    wordExtensionRelation_mem hM hpair hunion hpower hsep W.property⟩
  exact no_external_branch_of_no_internal_branch hM hinf hpair hunion hpower hsep hrep hchoice
    (inclusionTree c T bit) (inclusionTree_isSubtree c T bit) W R rfl rfl hno

/-- Existential correspondence, without asserting a computable or point-preserving certificate choice. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal counterexample branches
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Agreement of the internal and external interpretations at $x$ gives
    $g_x\notin\BorelInterpretation{c}{M}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Conversely, let $x$ satisfy the right-hand side. Agreement at this internal point gives $x\notin B_c$,
    so §{sec:ranked-closed-inclusions} supplies an external branch of $Q$.
    The node set $W_Q$ belongs to $M$ by §{sec:internal-finite-tests}, and the strict-extension relation
    $R_{W_Q}$ belongs to $M$ by §{sec:internal-rank-certificates}. If there were no internal branch,
    the theorem in §{sec:internal-tree-branches} would exclude every external branch, a contradiction.
    Thus an internal branch exists. This argument does not require the resulting branch to project to the
    originally chosen point $x$, and it does not assert computable selection of a certificate.
-/
theorem internal_counterexample_branch_iff (c : BorelExpression) (hc : c.Valid)
    (hcM : c.labelGraph ∈ M) (T : Set (List ℕ)) (hTM : wordTreeSet T ∈ M) :
    (∃ z, z ∈ treeBody (inclusionTree c T) ∧ pointGraph z ∈ M) ↔
      ∃ x ∈ treeBody T, pointGraph x ∈ M ∧
        pointGraph x ∉ internalInterpretation M c hc.2.2.2.2.2 NatListCode.decode [] := by
  constructor
  · rintro ⟨z, hz, hzM⟩
    obtain ⟨x, hx, hxM, hnot⟩ :=
      internal_point_of_counterexample_branch hM hinf hpair hunion hpower hsep c hc T z false hz hzM
    refine ⟨x, hx, hxM, fun hi => ?_⟩
    exact hnot ((pointGraph_mem_internalInterpretation M c _ _ [] x).mp hi).2
  · rintro ⟨x, hx, hxM, hnot⟩
    have hn : x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
      intro he
      exact hnot ((pointGraph_mem_internalInterpretation M c _ _ [] x).mpr ⟨hxM, he⟩)
    by_contra hno
    exact no_counterexample_branch_of_no_internal_branch hM hinf hpair hunion hpower hsep hrep hchoice
      c hcM T hTM false hno ((inclusionTree_has_branch_iff c hc T).mpr ⟨x, hx, hn⟩)

/-- Inclusion on all internal points forces inclusion on every external point, including new ones. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Transfer of closed Borel inclusions
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The theorem excludes internal branches of $Q$. The internal-branch theorem then excludes all external
    branches as well, and the counterexample-tree criterion gives the inclusion. In particular, the inclusion
    holds for new points in a larger transitive model. The proof uses the previously constructed internal rank
    through the internal-branch theorem, rather than assuming that agreement on old points suffices.
-/
theorem closed_inclusion_of_internal_points (c : BorelExpression) (hc : c.Valid)
    (hcM : c.labelGraph ∈ M) (T : Set (List ℕ)) (hTM : wordTreeSet T ∈ M)
    (hsub : ∀ x ∈ treeBody T, pointGraph x ∈ M →
      pointGraph x ∈ internalInterpretation M c hc.2.2.2.2.2 NatListCode.decode []) :
    treeBody T ⊆ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
  have hno : ¬ ∃ z, z ∈ treeBody (inclusionTree c T) ∧ pointGraph z ∈ M := by
    rw [internal_counterexample_branch_iff hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM T hTM]
    rintro ⟨x, hx, hxM, hnot⟩
    exact hnot (hsub x hx hxM)
  have he := no_counterexample_branch_of_no_internal_branch hM hinf hpair hunion hpower hsep hrep hchoice
    c hcM T hTM false hno
  intro x hx
  by_contra hnot
  exact he ((inclusionTree_has_branch_iff c hc T).mpr ⟨x, hx, hnot⟩)

/-- Positive certificates transfer disjointness, using the same tree and branch theorem. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Transfer of closed disjointness
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Use $Q^1(c,T)$, whose tests are $P_i^1$. The parameterized bounded-description and node-set propositions in
    §{sec:appendix-borel-finite-test-infrastructure} put its whole node set in $M$.
    A branch now gives a point in $\TreeBody{T}\cap B_c$,
    and a point in that intersection has a positive evaluation certificate, hence gives an external branch.
    If an external branch existed, the internal-branch theorem would supply an internal branch.
    Its coordinate projection would be an internal point in the intersection, contrary to the hypothesis.
    Thus there is no external branch, and the intersection is empty. This uses the same tree construction and
    rank argument as closed inclusion; it does not require constructing a separate complement code.
-/
theorem closed_disjoint_of_internal_points (c : BorelExpression) (hc : c.Valid)
    (hcM : c.labelGraph ∈ M) (T : Set (List ℕ)) (hTM : wordTreeSet T ∈ M)
    (hdisj : ∀ x ∈ treeBody T, pointGraph x ∈ M →
      x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis []) :
    ∀ x ∈ treeBody T, x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
  have hno : ¬ ∃ z, z ∈ treeBody (inclusionTree c T true) ∧ pointGraph z ∈ M := by
    rintro ⟨z, hz, hzM⟩
    obtain ⟨x, hx, hxM, hmem⟩ :=
      internal_point_of_counterexample_branch hM hinf hpair hunion hpower hsep c hc T z true hz hzM
    exact hdisj x hx hxM hmem
  have hn := no_counterexample_branch_of_no_internal_branch hM hinf hpair hunion hpower hsep hrep hchoice
    c hcM T hTM true hno
  intro x hx hmem
  exact hn ((inclusionTree_side_branch_iff c hc T true).mpr ⟨x, hx, hmem⟩)

end PolishSpaceBook.BorelExpression
