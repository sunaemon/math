module

public import PolishSpaceBook.ForcingInternalRegularCompleteness
public import PolishSpaceBook.SetTheoryPredicateComposition

@[expose] public section

/-! # Internal operation graphs for the regular-set Boolean algebra -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic BoundedSetPredicate
universe u

def regularOrderGraphPredicate : BoundedSetPredicate 2 :=
  .ex 0 (.ex 0 (.conj (.orderedPair 1 2 3) (.subset 2 3)))

def regularComplementGraphPredicate : BoundedSetPredicate 4 :=
  .ex 2 (.ex 2 (.conj (.orderedPair 3 4 5)
    (.all 0 (.iff (.member 6 5)
      (.all 0 (.imply (.pairMember 1 7 6) (.neg (.member 7 4))))))))

def regularMeetGraphPredicate : BoundedSetPredicate 3 :=
  .ex 1 (.ex 1 (.ex 1 (.conj
    (.ex 2 (.ex 6 (.conj (.orderedPair 7 3 4) (.orderedPair 2 7 5))))
    (.all 0 (.iff (.member 6 5) (.conj (.member 6 3) (.member 6 4)))))))

def regularOrderGraph (B : ZFSet.{u}) : ZFSet.{u} :=
  (prod B B).sep (fun p => regularOrderGraphPredicate.eval ![B, p])

def regularComplementGraph (P R B : ZFSet.{u}) : ZFSet.{u} :=
  (prod B B).sep (fun p => regularComplementGraphPredicate.eval ![P, R, B, p])

def regularMeetGraph (P B : ZFSet.{u}) : ZFSet.{u} :=
  (prod (prod B B) B).sep (fun p => regularMeetGraphPredicate.eval ![P, B, p])

lemma regularOrderGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (B : M) : regularOrderGraph B.val ∈ M := by
  have he (p : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![B]) p = ![B.val, p] := by
    funext i; fin_cases i <;> rfl
  simpa only [regularOrderGraph, he] using regularOrderGraphPredicate.separation_mem hM (hsep _) ![B]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) B.property B.property)

lemma regularComplementGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R B : M) : regularComplementGraph P.val R.val B.val ∈ M := by
  have he (p : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![P, R, B]) p = ![P.val, R.val, B.val, p] := by
    funext i; fin_cases i <;> rfl
  simpa only [regularComplementGraph, he] using regularComplementGraphPredicate.separation_mem hM (hsep _) ![P, R, B]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) B.property B.property)

set_option maxHeartbeats 800000 in
lemma regularMeetGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P B : M) : regularMeetGraph P.val B.val ∈ M := by
  have he (p : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![P, B]) p = ![P.val, B.val, p] := by
    funext i; fin_cases i <;> rfl
  simpa only [regularMeetGraph, he] using regularMeetGraphPredicate.separation_mem hM (hsep _) ![P, B]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _)
      (prod_mem_of_separation hM hpair hunion hpower (hsep _) B.property B.property) B.property)

lemma pair_mem_regularOrderGraph {B a b : ZFSet.{u}} (ha : a ∈ B) (hb : b ∈ B) :
    pair a b ∈ regularOrderGraph B ↔ a ⊆ b := by
  simp [regularOrderGraph, regularOrderGraphPredicate, eval, Fin.snoc, Fin.castLT, Fin.castPred,
    pair_inj, ha, hb]

lemma pair_mem_regularComplementGraph {P R B a b : ZFSet.{u}}
    (ha : a ∈ B) (hb : b ∈ B) (hbP : b ⊆ P) :
    pair a b ∈ regularComplementGraph P R B ↔ b = regularNegCode P R a := by
  simp only [regularComplementGraph, mem_sep, pair_mem_prod, ha, hb, true_and,
    regularComplementGraphPredicate, eval, eval_imply, Fin.snoc, Fin.castLT]
  change (∃ x ∈ B, ∃ y ∈ B, pair a b = pair x y ∧
    ∀ p ∈ P, (p ∈ y ↔ ∀ q ∈ P, pair q p ∈ R → q ∉ x)) ↔ _
  constructor
  · rintro ⟨x, _, y, _, hxy, h⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.mp hxy
    ext p
    rw [regularNegCode, mem_sep]
    exact ⟨fun hp => ⟨hbP hp, (h p (hbP hp)).mp hp⟩, fun hp => (h p hp.1).mpr hp.2⟩
  · intro he
    refine ⟨a, ha, b, hb, rfl, ?_⟩
    intro p hp
    rw [he, regularNegCode, mem_sep]
    exact and_iff_right hp

lemma pair_mem_regularMeetGraph {P B a b c : ZFSet.{u}}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (haP : a ⊆ P) (hcP : c ⊆ P) :
    pair (pair a b) c ∈ regularMeetGraph P B ↔ c = a ∩ b := by
  simp only [regularMeetGraph, mem_sep, pair_mem_prod, ha, hb, hc, true_and,
    regularMeetGraphPredicate, eval, Fin.snoc, Fin.castLT]
  change (∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B,
    (∃ s ∈ pair (pair a b) c, ∃ w ∈ s, w = pair x y ∧ pair (pair a b) c = pair w z) ∧
    (∀ p ∈ P, p ∈ z ↔ p ∈ x ∧ p ∈ y)) ↔ _
  constructor
  · rintro ⟨x, _, y, _, z, _, ⟨s, _, w, _, hw, he⟩, h⟩
    rw [hw] at he
    obtain ⟨hab, rfl⟩ := pair_inj.mp he
    obtain ⟨rfl, rfl⟩ := pair_inj.mp hab
    ext p
    rw [mem_inter]
    exact ⟨fun hp => (h p (hcP hp)).mp hp, fun hp => (h p (haP hp.1)).mpr hp⟩
  · intro he
    refine ⟨a, ha, b, hb, c, hc, ⟨{pair a b}, ?_, pair a b, ?_, rfl, rfl⟩, ?_⟩
    · simp [pair]
    · simp
    · intro p _; rw [he, mem_inter]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)

abbrev regularCarrierInModel : M :=
  ⟨internalRegularCarrier M P.val R.val, internalRegularCarrier_mem hM hpower hsep P R⟩

/-- The internally computed regular-set completion supplies all data of the
internal Boolean algebra interface used by the formula-value construction. -/
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
def internalRegularAlgebra :
    letI := internalRegularBooleanAlgebra hM hinf hpair hunion hsep P R hR
    InternalBooleanAlgebra (regularCarrierInModel hM hpower hsep P R) := by
  letI := internalRegularBooleanAlgebra hM hinf hpair hunion hsep P R hR
  let B := regularCarrierInModel hM hpower hsep P R
  refine {
    orderCode := ⟨regularOrderGraph B.val, regularOrderGraph_mem hM hpair hunion hpower hsep B⟩
    complementCode := ⟨regularComplementGraph P.val R.val B.val,
      regularComplementGraph_mem hM hpair hunion hpower hsep P R B⟩
    meetCode := ⟨regularMeetGraph P.val B.val, regularMeetGraph_mem hM hpair hunion hpower hsep P B⟩
    order_iff := ?_
    complement_iff := ?_
    meet_iff := ?_
    complete := internalRegular_complete hM hinf hpair hunion hsep P R hR }
  · intro a b
    exact (pair_mem_regularOrderGraph a.property b.property).trans
      (internalRegular_le_iff hM hinf hpair hunion hsep P R hR a b).symm
  · intro a b
    rw [pair_mem_regularComplementGraph a.property b.property
      ((mem_internalRegularCarrier hR M b.val).mp b.property).2.1,
      ← internalRegular_compl_val hM hinf hpair hunion hsep P R hR a]
    exact ⟨BooleanElement.ext, congrArg BooleanElement.val⟩
  · intro a b c
    rw [pair_mem_regularMeetGraph a.property b.property c.property
      ((mem_internalRegularCarrier hR M a.val).mp a.property).2.1
      ((mem_internalRegularCarrier hR M c.val).mp c.property).2.1,
      ← internalRegular_inf_val hM hinf hpair hunion hsep P R hR a b]
    exact ⟨BooleanElement.ext, congrArg BooleanElement.val⟩

end PolishSpaceBook.SetTheoryModels
