module

public import PolishSpaceBook.ForcingRegularAlgebra
public import PolishSpaceBook.ForcingBooleanValues

@[expose] public section

/-! # The internally computed carrier of the regular-set completion -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic BoundedSetPredicate
universe u

def regularLowerPredicate : BoundedSetPredicate 3 :=
  .all 2 (.all 0 (.disj (.neg (.pairMember 1 4 3)) (.member 4 2)))

def regularSaturatedPredicate : BoundedSetPredicate 3 :=
  .all 0 (.disj (.neg (.all 0 (.disj (.neg (.pairMember 1 4 3))
    (.ex 2 (.pairMember 1 5 4))))) (.member 3 2))

def regularSetPredicate : BoundedSetPredicate 3 :=
  .conj regularLowerPredicate regularSaturatedPredicate

def regularNegPredicate : BoundedSetPredicate 4 :=
  .all 0 (.disj (.neg (.pairMember 1 4 3)) (.neg (.member 4 2)))

def regularDensePredicate : BoundedSetPredicate 4 :=
  .all 0 (.disj (.neg (.pairMember 1 4 3)) (.ex 2 (.pairMember 1 5 4)))

def regularNegCode (P R U : ZFSet.{u}) : ZFSet.{u} :=
  P.sep (fun p => ∀ q ∈ P, pair q p ∈ R → q ∉ U)

def regularDenseCode (P R U : ZFSet.{u}) : ZFSet.{u} :=
  P.sep (fun p => ∀ q ∈ P, pair q p ∈ R → ∃ r ∈ U, pair r q ∈ R)

/-- Only model subsets occur in this carrier. In particular it is not the
external complete Boolean algebra of all regular subsets. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{proof}[Internal construction of the completion]
    Let $P\in M$ be a forcing order whose order relation belongs to $M$ as well. Use the negative operation
    from §{sec:random-forcing-detail} with conditions in $P$:
    $$\ForcingNeg{U}=\{p\in P:\forall q\le p\ (q\notin U)\}.$$
    The regular lower sets are the downward-closed subsets $U$ of $P$ satisfying
    $U=\ForcingNeg{\ForcingNeg{U}}$. Take only those subsets that belong to $M$.
    Their carrier is a set in $M$: apply Separation to the power set of $P$ computed inside $M$.
    All quantifiers in the defining conditions are bounded by $P$, so transitivity makes these conditions
    agree with their external meanings.

    Order this carrier by inclusion. Intersection is meet, $\ForcingNeg{U}$ is complement, and the bottom
    and top are $\varnothing$ and $P$. The double negative is precisely the set of conditions below which
    $U$ is dense. It is an idempotent closure operation on lower sets, and its fixed points form a Boolean
    algebra with these operations. Separation also puts the order, complement, and meet graphs in $M$.

    For a family $\mathcal A\in M$ of regular lower sets, Union and Separation give
    $$\bigvee\mathcal A=\ForcingNeg{\ForcingNeg{\bigcup\mathcal A}}\in M.$$
    Each member of the family is contained in this regularization. Every regular upper bound contains
    the union and therefore also its regularization. This proves the supremum property and hence
    completeness for all families in $M$.
    \end{proof}
-/
def internalRegularCarrier (M P R : ZFSet.{u}) : ZFSet.{u} :=
  (internalPowerSet M P).sep (fun U => regularSetPredicate.eval ![P, R, U])

lemma regularNegCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R U : M) : regularNegCode P.val R.val U.val ∈ M := by
  simpa [regularNegCode, regularNegPredicate, eval, Fin.snoc, Fin.castPred, Fin.castLT, or_iff_not_imp_left] using
    regularNegPredicate.separation_mem hM (hsep _) ![P, R, U] P.property

lemma regularDenseCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R U : M) : regularDenseCode P.val R.val U.val ∈ M := by
  simpa [regularDenseCode, regularDensePredicate, eval, Fin.snoc, Fin.castPred, Fin.castLT, or_iff_not_imp_left] using
    regularDensePredicate.separation_mem hM (hsep _) ![P, R, U] P.property

lemma internalRegularCarrier_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R : M) : internalRegularCarrier M P.val R.val ∈ M :=
  regularSetPredicate.separation_mem hM (hsep _) ![P, R]
    (internalPowerSet_mem hM hpower P.property)

def conditionsOfCode (P U : ZFSet.{u}) : Set (Condition P) := {p | p.val ∈ U}

lemma conditionsOfCode_conditionSet (P : ZFSet.{u}) (U : Set (Condition P)) :
    conditionsOfCode P (conditionSet P U) = U := by
  ext p
  exact mem_conditionSet P U p

lemma conditionSet_conditionsOfCode (P U : ZFSet.{u}) (hU : U ⊆ P) :
    conditionSet P (conditionsOfCode P U) = U := by
  ext x
  simp only [conditionSet, mem_sep, conditionsOfCode, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2.choose_spec, fun h => ⟨hU h, hU h, h⟩⟩

lemma conditionSet_subset (P : ZFSet.{u}) (U : Set (Condition P)) : conditionSet P U ⊆ P :=
  fun _ h => (mem_sep.mp h).1

variable {P R : ZFSet.{u}} [Preorder (Condition P)]
  (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q)
include hR

lemma regularNegCode_correct (U : ZFSet.{u}) :
    conditionsOfCode P (regularNegCode P R U) = forcingNeg (conditionsOfCode P U) := by
  ext p
  simp only [conditionsOfCode, Set.mem_ofPred_eq, regularNegCode, mem_sep]
  constructor
  · rintro ⟨_, h⟩ q hqp hq
    exact h q.val q.property ((hR q p).mpr hqp) hq
  · intro h
    exact ⟨p.property, fun q hq hqp => h ⟨q, hq⟩ ((hR ⟨q, hq⟩ p).mp hqp)⟩

lemma regularDenseCode_correct (U : ZFSet.{u}) (hU : U ⊆ P) :
    conditionsOfCode P (regularDenseCode P R U) = forcingDense (conditionsOfCode P U) := by
  ext p
  simp only [conditionsOfCode, Set.mem_ofPred_eq, regularDenseCode, mem_sep]
  constructor
  · rintro ⟨_, h⟩ q hqp
    obtain ⟨r, hr, hrq⟩ := h q.val q.property ((hR q p).mpr hqp)
    exact ⟨⟨r, hU hr⟩, (hR ⟨r, hU hr⟩ q).mp hrq, hr⟩
  · intro h
    refine ⟨p.property, ?_⟩
    intro q hq hqp
    obtain ⟨r, hrq, hr⟩ := h ⟨q, hq⟩ ((hR ⟨q, hq⟩ p).mp hqp)
    exact ⟨r.val, hr, (hR r ⟨q, hq⟩).mpr hrq⟩

lemma regularSetPredicate_correct (U : ZFSet.{u}) (hU : U ⊆ P) :
    regularSetPredicate.eval ![P, R, U] ↔
      IsLowerSet (conditionsOfCode P U) ∧ forcingDense (conditionsOfCode P U) ⊆ conditionsOfCode P U := by
  simp only [regularSetPredicate, regularLowerPredicate, regularSaturatedPredicate,
    eval, Fin.snoc, Fin.castLT, or_iff_not_imp_left, not_not]
  change ((∀ p ∈ U, ∀ q ∈ P, pair q p ∈ R → q ∈ U) ∧
    (∀ p ∈ P, (∀ q ∈ P, pair q p ∈ R → ∃ r ∈ U, pair r q ∈ R) → p ∈ U)) ↔ _
  constructor
  · rintro ⟨hl, hs⟩
    refine ⟨fun p q hqp hp => hl p.val hp q.val q.property ((hR q p).mpr hqp), ?_⟩
    intro p hp
    apply hs p.val p.property
    intro q hq hqp
    obtain ⟨r, hrq, hr⟩ := hp ⟨q, hq⟩ ((hR ⟨q, hq⟩ p).mp hqp)
    exact ⟨r.val, hr, (hR r ⟨q, hq⟩).mpr hrq⟩
  · rintro ⟨hl, hs⟩
    refine ⟨?_, ?_⟩
    · intro p hp q hq hqp
      exact hl ((hR ⟨q, hq⟩ ⟨p, hU hp⟩).mp hqp) hp
    · intro p hp hd
      apply hs (a := ⟨p, hp⟩)
      intro q hqp
      obtain ⟨r, hr, hrq⟩ := hd q.val q.property ((hR q ⟨p, hp⟩).mpr hqp)
      exact ⟨⟨r, hU hr⟩, (hR ⟨r, hU hr⟩ q).mp hrq, hr⟩

lemma mem_internalRegularCarrier (M U : ZFSet.{u}) :
    U ∈ internalRegularCarrier M P R ↔ U ∈ M ∧ U ⊆ P ∧
      IsLowerSet (conditionsOfCode P U) ∧ forcingDense (conditionsOfCode P U) ⊆ conditionsOfCode P U := by
  rw [internalRegularCarrier, mem_sep, internalPowerSet, mem_sep]
  constructor
  · rintro ⟨⟨hM, hU⟩, hr⟩
    exact ⟨hM, hU, (regularSetPredicate_correct hR U hU).mp hr⟩
  · rintro ⟨hM, hU, hr⟩
    exact ⟨⟨hM, hU⟩, (regularSetPredicate_correct hR U hU).mpr hr⟩

/-- The internal carrier is faithfully interpreted as genuine regular lower
sets of the ambient condition order. -/
def decodeInternalRegular (M : ZFSet.{u}) (U : BooleanElement (internalRegularCarrier M P R)) :
    RegularForcingSet (Condition P) :=
  regularForcingSet (conditionsOfCode P U.val)
    ((mem_internalRegularCarrier hR M U.val).mp U.property).2.2.1
    ((mem_internalRegularCarrier hR M U.val).mp U.property).2.2.2

lemma decodeInternalRegular_injective (M : ZFSet.{u}) :
    Function.Injective (decodeInternalRegular hR M) := by
  intro U V he
  apply BooleanElement.ext
  have hU := ((mem_internalRegularCarrier hR M U.val).mp U.property).2.1
  have hV := ((mem_internalRegularCarrier hR M V.val).mp V.property).2.1
  have hs := congrArg (fun W : RegularForcingSet (Condition P) => (W.val : Set (Condition P))) he
  change conditionsOfCode P U.val = conditionsOfCode P V.val at hs
  rw [← conditionSet_conditionsOfCode P U.val hU, ← conditionSet_conditionsOfCode P V.val hV, hs]

end PolishSpaceBook.SetTheoryModels
