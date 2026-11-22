module

public import PolishSpaceBook.MeasureAlgebra
public import PolishSpaceBook.BorelForcingTruth

@[expose] public section

/-!
# The Boolean calculation for random forcing

The positive part of the constructed measure algebra is the actual condition
order. Complement and countable union in a Borel code correspond to negative
forcing and density of the union of the children's forcing sets. This module
proves that calculation rather than assuming it. Set-theoretic names and
valuation in generic extensions remain separate infrastructure.
-/

namespace PolishSpaceBook
open MeasureTheory Set
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace MeasureAlgebra

/-- Positive conditions below a Boolean value. -/
def below (a : MeasureAlgebra μ) : Set (Positive μ) := {p | p.val ≤ a}

theorem below_lower (a : MeasureAlgebra μ) : IsLowerSet (below a) := by
  intro p q hqp hp
  exact (show q.val ≤ p.val from hqp).trans hp

/-- Complement means that no stronger positive condition lies below the child. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Positive-condition recursion
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For the first equivalence, $p\le a^c$ excludes a positive common lower bound of $p$ and $a$.
    Conversely, if $p\not\le a^c$, then $p\wedge a\ne0$, and this intersection is such a common lower bound.
    For the second equivalence, suppose $p\le\bigvee_n a_n$ and $0<q\le p$.
    If all $q\wedge a_n$ were zero, distributivity over the countable supremum would give
    $$q=q\wedge\bigvee_n a_n=\bigvee_n(q\wedge a_n)=0,$$
    a contradiction. Thus $r=q\wedge a_n$ is positive for some $n$ and is the required refinement.
    Conversely, if $p\not\le\bigvee_n a_n$, then $q=p\wedge(\bigvee_n a_n)^c$ is positive.
    No positive refinement of $q$ lies below any $a_n$, so the asserted density fails.
    \end{proof}
-/
theorem forcingNeg_below (a : MeasureAlgebra μ) : forcingNeg (below a) = below aᶜ := by
  ext p
  change _ ↔ p.val ≤ aᶜ
  constructor
  · intro h
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff.mpr
    by_contra hn
    let q : Positive μ := ⟨p.val ⊓ a, hn⟩
    exact h q (show p.val ⊓ a ≤ p.val from inf_le_left)
      (show p.val ⊓ a ≤ a from inf_le_right)
  · intro hp q hqp hqa
    apply q.property
    apply le_bot_iff.mp
    have hqc : q.val ≤ aᶜ := le_trans hqp hp
    calc
      q.val ≤ a ⊓ aᶜ := le_inf hqa hqc
      _ = ⊥ := inf_compl_eq_bot

/-- A positive piece of a countable supremum has a positive intersection with
at least one term. -/
theorem exists_positive_intersection [IsFiniteMeasure μ] {ι : Type*}
    (a : ι → MeasureAlgebra μ) (p : Positive μ) (hp : p.val ≤ ⨆ n, a n) :
    ∃ n, p.val ⊓ a n ≠ ⊥ := by
  by_contra! h
  apply p.property
  calc
    p.val = p.val ⊓ ⨆ n, a n := (inf_eq_left.mpr hp).symm
    _ = ⨆ n, p.val ⊓ a n := inf_iSup_eq _ _
    _ = ⊥ := by simp [h]

/-- Countable union is the density of the children's positive forcing sets. -/
theorem forcingDense_iUnion_below [IsFiniteMeasure μ] (a : ℕ → MeasureAlgebra μ) :
    forcingDense (⋃ n, below (a n)) = below (⨆ n, a n) := by
  ext p
  change _ ↔ p.val ≤ ⨆ n, a n
  constructor
  · intro hp
    by_contra hn
    have hi : p.val ⊓ (⨆ n, a n)ᶜ ≠ ⊥ := by
      intro hzero
      apply hn
      have hd := disjoint_iff.mpr hzero
      simpa only [compl_compl] using le_compl_iff_disjoint_right.mpr hd
    let q : Positive μ := ⟨p.val ⊓ (⨆ n, a n)ᶜ, hi⟩
    obtain ⟨r, hrq, hr⟩ := hp q (show p.val ⊓ (⨆ n, a n)ᶜ ≤ p.val from inf_le_left)
    obtain ⟨n, hr⟩ := mem_iUnion.mp hr
    apply r.property
    apply le_bot_iff.mp
    have hrA : r.val ≤ ⨆ n, a n := le_trans hr (le_iSup a n)
    have hrC : r.val ≤ (⨆ n, a n)ᶜ := le_trans hrq inf_le_right
    calc
      r.val ≤ (⨆ n, a n) ⊓ (⨆ n, a n)ᶜ := le_inf hrA hrC
      _ = ⊥ := inf_compl_eq_bot
  · intro hp q hqp
    obtain ⟨n, hn⟩ := exists_positive_intersection a q (le_trans hqp hp)
    exact ⟨⟨q.val ⊓ a n, hn⟩, (show q.val ⊓ a n ≤ q.val from inf_le_left),
      mem_iUnion.mpr ⟨n, (show q.val ⊓ a n ≤ a n from inf_le_right)⟩⟩

end MeasureAlgebra

namespace BorelCode

/-- The Boolean value obtained by interpreting the code in the measure algebra. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    These equivalences give a recursive calculation on Borel codes using just the positive-condition order.
    At a cylinder leaf, assign its equivalence class. At a complement node, take the Boolean complement of the child's
    value;
    at a countable-union node, take the supremum of the children's values.
-/
noncomputable def measureValue [IsFiniteMeasure μ]
    (A : ℕ → MeasureAlgebra μ) : BorelCode → MeasureAlgebra μ
  | .leaf n => A n
  | .compl c => (c.measureValue A)ᶜ
  | .union f => ⨆ n, (f n).measureValue A

/-- The Boolean interpretation is the class of the decoded measurable set. -/
theorem measurable_decode (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (c : BorelCode) :
    MeasurableSet (c.decode U) := by
  induction c with
  | leaf n => exact hU n
  | compl c ih => exact ih.compl
  | union f ih => exact MeasurableSet.iUnion ih

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Boolean values of Borel codes
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induct on the well-founded code. The leaf case is the definition. The complement step follows because taking a complement
    of a representative induces Boolean complementation. At a union node, the class of the countable union is the supremum
    of the children's classes, by the countable-union calculation above. The two assertions about positive conditions follow
    at each step from the positive-condition recursion lemma. This also explains why a condition below a countable supremum
    need not itself lie below one of its terms: the union clause requires such a term only after a further refinement.
    \end{proof}
-/
theorem measureValue_eq_mk_decode [IsFiniteMeasure μ]
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (c : BorelCode) :
    c.measureValue (fun n => MeasureAlgebra.mk (U n) (hU n)) =
      (MeasureAlgebra.mk (c.decode U) (c.measurable_decode U hU) : MeasureAlgebra μ) := by
  induction c with
  | leaf n => rfl
  | compl c ih => simp only [measureValue, decode, ih, MeasureAlgebra.mk_compl]
  | union f ih =>
    simp only [measureValue, decode, ih]
    exact (MeasureAlgebra.mk_iUnion (fun n => (f n).decode U)
      (fun n => (f n).measurable_decode U hU)).symm

/-- The recursive order-forcing calculation has no extra splitting, truth,
or Boolean-completeness assumption. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For a Borel code $c$ with cylinder leaves, write $B_c$ for its interpreted set.
    \begin{mathmeta}
      \define{CodeForcingSet,ForcingNeg,ForcingDecision}
    \end{mathmeta}
    Let $\CodeForcingSet{c}=\{p\in Q_+:p\le[B_c]\}$. The Boolean calculation above identifies its recursion:
    at a complement node, no stronger condition belongs to the child's forcing set; at a union node, the union of the
    children's forcing sets is dense below the condition.
-/
theorem random_forcing_eq_below [IsFiniteMeasure μ]
    (A : ℕ → MeasureAlgebra μ) (c : BorelCode) :
    c.forcing (fun n => MeasureAlgebra.below (A n)) = MeasureAlgebra.below (c.measureValue A) := by
  induction c with
  | leaf n => rfl
  | compl c ih => rw [forcing, measureValue, ih, MeasureAlgebra.forcingNeg_below]
  | union f ih => simp only [forcing, measureValue, ih, MeasureAlgebra.forcingDense_iUnion_below]

/-- A condition forces a decoded set exactly when its difference from that set
is null. This is the Borel-fragment calculation in the actual measure algebra. -/
theorem random_forcing_iff_null_sdiff [IsFiniteMeasure μ]
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (c : BorelCode)
    (B : Set X) (hB : MeasurableSet B) (hpos : μ B ≠ 0) :
    (⟨MeasureAlgebra.mk B hB, fun h => hpos ((MeasureAlgebra.mk_eq_bot B hB).mp h)⟩ :
        MeasureAlgebra.Positive μ) ∈ c.forcing (fun n => MeasureAlgebra.below (MeasureAlgebra.mk (U n) (hU n))) ↔
      μ (B \ c.decode U) = 0 := by
  rw [random_forcing_eq_below, measureValue_eq_mk_decode]
  exact MeasureAlgebra.mk_le_mk_iff_null_sdiff _ _ _ _

end BorelCode
end PolishSpaceBook
