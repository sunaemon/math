module

public import PolishSpaceBook.ForcingGenericTruth
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # Generic decision tests for any internally coded set of conditions -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic BoundedSetPredicate
universe u

/-- Parameters: condition set, order relation, selected conditions, candidate condition. -/
def setDecisionPredicate : BoundedSetPredicate 4 :=
  .disj (.member 3 2) (.all 0 (.disj (.neg (.pairMember 1 4 3)) (.neg (.member 4 2))))

/-- A condition either belongs to S or has no strengthening in S. -/
def setDecision (P R S : ZFSet.{u}) : ZFSet.{u} :=
  P.sep (fun p => p ∈ S ∨ ∀ q ∈ P, pair q p ∈ R → q ∉ S)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal decision tests
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Replace $r\le p$ by $\langle r,p\rangle\in\mathcal O$. The displayed condition is bounded,
    so Separation constructs the decision test. Its density is the general decision lemma of
    §{sec:random-forcing-detail}: either a condition has a strengthening in $S$, or it already
    belongs to the negative alternative. For the family of lower cones, membership says
    $\exists B\in E\ (p\in\InternalMeasureCone{B})$. Substitute the bounded lower-cone test from
    §{sec:internal-random-filter-valuation} and apply Separation on $P$.
    This constructs the whole union without choosing an enumeration of $E$.
-/
lemma setDecision_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R S : M) : setDecision P.val R.val S.val ∈ M := by
  have he : setDecision P.val R.val S.val =
      P.val.sep (fun p => setDecisionPredicate.eval (Fin.snoc (Subtype.val ∘ ![P, R, S]) p)) := by
    ext p
    simp only [setDecision, ZFSet.mem_sep]
    change (_ ∧ (p ∈ S.val ∨ ∀ q ∈ P.val, pair q p ∈ R.val → q ∉ S.val)) ↔
      (_ ∧ (p ∈ S.val ∨ ∀ q ∈ P.val, ¬ pair q p ∈ R.val ∨ q ∉ S.val))
    simp only [Classical.or_iff_not_imp_left, not_not]
  rw [he]
  exact setDecisionPredicate.separation_mem hM (hsep _) ![P, R, S] P.property

lemma mem_setDecision (P R S : ZFSet.{u}) [Preorder (Condition P)]
    (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q) (p : Condition P) :
    p.val ∈ setDecision P R S ↔ p ∈ forcingDecision {q : Condition P | q.val ∈ S} := by
  rw [setDecision, ZFSet.mem_sep, and_iff_right p.property]
  change (p.val ∈ S ∨ ∀ q ∈ P, pair q p.val ∈ R → q ∉ S) ↔
    (p.val ∈ S ∨ ∀ q : Condition P, q ≤ p → q.val ∉ S)
  apply or_congr Iff.rfl
  exact ⟨fun h q hq => h q.val q.property ((hR q p).mpr hq),
    fun h q hq hr => h ⟨q, hq⟩ ((hR ⟨q, hq⟩ p).mp hr)⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal decision tests
-/
lemma modelGeneric_meets_setDecision {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R S : M) [Preorder (Condition P.val)]
    (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    ∃ p ∈ G, p ∈ forcingDecision {q : Condition P.val | q.val ∈ S.val} := by
  have hd : IsCoinitial {p : Condition P.val | p.val ∈ setDecision P.val R.val S.val} := by
    intro p
    obtain ⟨q, hq, hqp⟩ := forcingDecision_dense {q : Condition P.val | q.val ∈ S.val} p
    exact ⟨q, (mem_setDecision P.val R.val S.val hR q).mpr hq, hqp⟩
  obtain ⟨p, hp, hs⟩ := hG _ (setDecision_mem hM hsep P R S)
    (fun _ hp => (ZFSet.mem_sep.mp hp).1) hd
  exact ⟨p, hp, (mem_setDecision P.val R.val S.val hR p).mp hs⟩

end PolishSpaceBook.SetTheoryModels
