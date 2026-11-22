module

public import PolishSpaceBook.ForcingRegularAlgebra
public import PolishSpaceBook.ForcingAtomic

@[expose] public section

/-! # Comparing regular lower sets with an external complete Boolean algebra

Completeness here belongs to the external comparison algebra. The internally
coded regular-set subalgebra does not acquire external completeness.
-/

noncomputable section
namespace PolishSpaceBook
open Set ForcingAtomic
variable {P C : Type*} [Preorder P] [CompleteBooleanAlgebra C]
  (e : P ↪o C) (hne : ∀ p, e p ≠ ⊥) (hd : ∀ c : C, c ≠ ⊥ → ∃ p, e p ≤ c)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To compare this construction with regular opens of Cantor space, send a regular lower set $U$ to
    $$J(U)=\bigvee_{p\in U}\cyl{p},$$
    where the join is computed in the external regular-open algebra, by regularizing the union.
    Then $\cyl{p}\IncludedIn J(U)$ holds exactly when $p\in U$.
    Indeed, if $p\notin U$, regularity supplies $q\le p$ with no extension in $U$.
    Its cylinder is disjoint from every cylinder indexed by $U$, and therefore from their regular-open
    join, contradicting $\cyl{p}\IncludedIn J(U)$. The converse follows from the definition of the join.
    The inverse sends a regular open $V$ to $\{p\in P:\cyl{p}\IncludedIn V\}$; density of cylinders
    makes this set regular and recovers $V$ as its join. Thus the external completions are Boolean
    isomorphic. Restricting to internally coded lower sets gives a faithful Boolean representation,
    and $J(e(p))=\cyl{p}$. Completeness of the internal carrier is still required only for families in $M$.
-/
/-- The external regular-open value is the join of its basic conditions. -/
def regularComparison (U : RegularForcingSet P) : C := sSup (e '' (U.val : Set P))

include hne hd in
 theorem regularComparison_test (U : RegularForcingSet P) (p : P) :
    e p ≤ regularComparison e U ↔ p ∈ (U.val : Set P) := by
  constructor
  · intro hp
    apply regularForcingSet_saturated U
    intro q hqp
    by_contra hn
    have hneg : ∀ r ≤ q, r ∉ (U.val : Set P) := by
      intro r hrq hrU
      exact hn ⟨r, hrq, hrU⟩
    have hu : regularComparison e U ≤ (e q)ᶜ := by
      apply sSup_le
      rintro c ⟨r, hrU, rfl⟩
      apply le_compl_iff_disjoint_left.mpr
      apply disjoint_iff.mpr
      by_contra hmeet
      obtain ⟨s, hs⟩ := hd (e q ⊓ e r) hmeet
      have hsr := e.le_iff_le.mp (hs.trans inf_le_right)
      have hsq := e.le_iff_le.mp (hs.trans inf_le_left)
      exact hneg s hsq (U.val.lower hsr hrU)
    exact hne q (le_compl_self.mp (((e.monotone hqp).trans hp).trans hu))
  · intro hp
    exact le_sSup ⟨p, hp, rfl⟩

include hne hd in
 theorem regularComparison_le_iff (U V : RegularForcingSet P) :
    regularComparison e U ≤ regularComparison e V ↔ U ≤ V := by
  constructor
  · intro h p hp
    exact (regularComparison_test e hne hd V p).mp (((regularComparison_test e hne hd U p).mpr hp).trans h)
  · intro h
    apply sSup_le
    rintro c ⟨p, hp, rfl⟩
    exact (regularComparison_test e hne hd V p).mpr (h hp)

def regularComparisonEmbedding : RegularForcingSet P ↪o C where
  toFun := regularComparison e
  inj' := by
    intro U V h
    exact le_antisymm ((regularComparison_le_iff e hne hd U V).mp h.le)
      ((regularComparison_le_iff e hne hd V U).mp h.ge)
  map_rel_iff' := regularComparison_le_iff e hne hd _ _

include hne hd in
lemma comparison_preimage_saturated (c : C) :
    forcingDense {p : P | e p ≤ c} ⊆ {p : P | e p ≤ c} := by
  intro p hp
  by_contra hpc
  have hn : e p ⊓ cᶜ ≠ ⊥ := by
    intro hz
    apply hpc
    calc
      e p = e p ⊓ c ⊔ e p ⊓ cᶜ := sup_inf_inf_compl.symm
      _ = e p ⊓ c := by rw [hz, sup_bot_eq]
      _ ≤ c := inf_le_right
  obtain ⟨q, hq⟩ := hd _ hn
  obtain ⟨r, hrq, hrc⟩ := hp q (e.le_iff_le.mp (hq.trans inf_le_left))
  exact hne r (le_bot_iff.mp ((le_inf hrc ((e.monotone hrq).trans (hq.trans inf_le_right))).trans_eq (inf_compl_self c)))

def comparisonPreimage (c : C) : RegularForcingSet P :=
  regularForcingSet {p | e p ≤ c} (fun _ _ hqp hp => (e.monotone hqp).trans hp)
    (comparison_preimage_saturated e hne hd c)

include hne hd in
 theorem regularComparison_surjective : Function.Surjective (regularComparison e) := by
  intro c
  refine ⟨comparisonPreimage e hne hd c, le_antisymm ?_ ?_⟩
  · apply sSup_le
    rintro _ ⟨p, hp, rfl⟩
    exact hp
  · by_contra h
    have hn : c ⊓ (regularComparison e (comparisonPreimage e hne hd c))ᶜ ≠ ⊥ := by
      intro hz
      apply h
      calc
        c = c ⊓ regularComparison e (comparisonPreimage e hne hd c) ⊔
          c ⊓ (regularComparison e (comparisonPreimage e hne hd c))ᶜ := sup_inf_inf_compl.symm
        _ = c ⊓ regularComparison e (comparisonPreimage e hne hd c) := by rw [hz, sup_bot_eq]
        _ ≤ regularComparison e (comparisonPreimage e hne hd c) := inf_le_right
    obtain ⟨p, hp⟩ := hd _ hn
    have hpU : p ∈ ((comparisonPreimage e hne hd c).val : Set P) := hp.trans inf_le_left
    have hpv := (regularComparison_test e hne hd (comparisonPreimage e hne hd c) p).mpr hpU
    exact hne p (le_bot_iff.mp ((le_inf hpv (hp.trans inf_le_right)).trans_eq (inf_compl_self _)))

/-- The regular-set completion agrees with any complete Boolean algebra in
which the conditions embed densely as nonzero elements. -/
def regularCompletionIso : RegularForcingSet P ≃o C :=
  OrderIso.ofSurjective (regularComparisonEmbedding e hne hd) (regularComparison_surjective e hne hd)

end PolishSpaceBook
