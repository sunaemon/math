module

public import PolishSpaceBook.InternalCohenAvoidance

@[expose] public section

/-! # Ground-model codes for elementary Cohen requirements

The diagonal requirement is bounded separation on the set of binary finite
function graphs. Its parameter is the actual ground-model real's function graph.
-/
noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open CantorTreeMeasure ForcingAtomic
universe u

/-- Avoiding the singleton consisting of x is exactly the diagonal requirement. -/
lemma cohenDiagonalRequirement_eq_avoidance (x : ℕ → Bool) :
    cohenDiagonalRequirement x = cohenAvoidanceSet ({cantorPointGraph x} : ZFSet.{u}) := by
  ext s
  simp only [cohenDiagonalRequirement, Set.mem_ofPred_eq, cohenAvoidanceSet,
    ZFSet.mem_singleton, forall_eq, binaryWordGraph_subset_pointGraph,
    mem_cyl, cohenAgrees_iff_prefixOfSeq]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

include hM hinf hpair hunion hpower hsep

/-- Bounded separation constructs the actual diagonal dense subset inside M. -/
theorem cohenDiagonalRequirement_mem (x : ℕ → Bool) (hx : cantorPointGraph x ∈ M) :
    cohenConditionSet (cohenDiagonalRequirement x) ∈ M := by
  rw [cohenDiagonalRequirement_eq_avoidance]
  exact cohenAvoidanceSet_mem hM hinf hpair hunion hpower hsep _ (singleton_mem hM hpair hx)

local instance cohenRequirementOrder : Preorder (Condition (cohenConditionSet.{u} Set.univ)) := internalCohenOrder

/-- Model genericity applies to D_x because its ground-model membership has been proved. -/
theorem modelGeneric_meets_diagonal
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)))
    (hG : ModelGeneric (cohenConditionSet Set.univ) M G)
    (x : ℕ → Bool) (hx : cantorPointGraph x ∈ M) :
    ∃ s ∈ cohenDiagonalRequirement x, cohenCodedCondition s ∈ G :=
  (modelGeneric_iff_cohenDense M G).mp hG _
    (cohenDiagonalRequirement_mem hM hinf hpair hunion hpower hsep x hx)
    (cohenDiagonalRequirement_dense x)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Choose $s\in G\cap D_x$. The union lemma gives $s\prefixOf c_G$, whereas the definition of $D_x$ gives
    $s\notPrefixOf x$. Hence $c_G\ne x$. For $x\in M\cap\CantorSpace$, the dense set $D_x$ belongs to $M$, so an
    $M$-generic filter meets it.
    \end{proof}
-/
/-- A real agreeing with the filter's finite words differs from every real in M. -/
theorem modelGeneric_cohen_real_new
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)))
    (hG : ModelGeneric (cohenConditionSet Set.univ) M G)
    (c : ℕ → Bool) (hc : ∀ s, cohenCodedCondition s ∈ G → CohenAgrees s c)
    (x : ℕ → Bool) (hx : cantorPointGraph x ∈ M) : c ≠ x := by
  obtain ⟨s, hsD, hsG⟩ := modelGeneric_meets_diagonal hM hinf hpair hunion hpower hsep G hG x hx
  exact cohen_real_ne_of_diagonal (G := {s | cohenCodedCondition s ∈ G})
    hc ⟨s, hsG, hsD⟩

end PolishSpaceBook
