module

public import PolishSpaceBook.ForcingNames
public import PolishSpaceBook.BorelForcingTruth

@[expose] public section

/-!
# The atomic forcing recursion

Membership and equality are defined simultaneously on actual set-theoretic
names. The decreasing measure is the pair of ranks sorted in descending order,
as in the appendix. Ground-model definability is a separate requirement.
-/

noncomputable section
namespace PolishSpaceBook.ForcingAtomic
open ZFSet ForcingNames
universe u

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Each recursive call lies at a strictly smaller rank-pair. The call $q \forces^* \sigma = \pi$ inside the
    $\sigma \in \tau$ clause uses $\mathrm{rank}\pi < \mathrm{rank}\tau$. Decreasing one coordinate of a pair while
    fixing the other strictly decreases the pair sorted in descending order: either its maximum decreases,
    or its maximum stays fixed and its minimum decreases. Thus the new rank-pair is $\prec$-smaller.
    The call $q \forces^* \pi \in \tau$ inside the $\sigma = \tau$ clause uses $\mathrm{rank}\pi < \mathrm{rank}\sigma$,
    with the same lexicographic decrease.
-/
lemma sorted_lt_right {a b c : Ordinal.{u}} (h : c < b) :
    Prod.Lex (· < ·) (· < ·) (max a c, min a c) (max a b, min a b) := by
  by_cases hab : a < b
  · apply Prod.Lex.left
    exact max_lt_iff.mpr ⟨hab.trans_le (le_max_right _ _), h.trans_le (le_max_right _ _)⟩
  · have hba : b ≤ a := le_of_not_gt hab
    rw [max_eq_left hba, max_eq_left (h.le.trans hba), min_eq_right hba,
      min_eq_right (h.le.trans hba)]
    exact Prod.Lex.right _ h

lemma sorted_lt_left {a b c : Ordinal.{u}} (h : c < a) :
    Prod.Lex (· < ·) (· < ·) (max c b, min c b) (max a b, min a b) := by
  simpa only [max_comm, min_comm] using (sorted_lt_right (a := b) h)

/-- Conditions carry their forcing order independently of the ambient subset order. -/
structure Condition (P : ZFSet.{u}) where
  val : ZFSet.{u}
  property : val ∈ P

variable (P : ZFSet.{u}) [Preorder (Condition P)]

def incompatible (p r : Condition P) : Prop := ¬ ∃ q : Condition P, q ≤ p ∧ q ≤ r

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \textbf{Atomic clauses.} Define $p \forces^* \sigma \in \tau$ and $p \forces^* \sigma = \tau$ for $P$-names $\sigma,
    \tau \in M^P$ by recursion on the lexicographic order $\prec$ on the rank-pair
    $$(\sigma,\tau) \;\longmapsto\; \big(\max(\mathrm{rank}\sigma, \mathrm{rank}\tau),\; \min(\mathrm{rank}\sigma,
    \mathrm{rank}\tau)\big).$$
    This order is well-founded because pairs of ordinals are well-ordered lexicographically:

    \begin{itemize}
    \item $p \forces^* \sigma \in \tau$ iff the set
    \end{itemize}
        $$\{q \le p \;:\; \exists \langle \pi,r\rangle \in \tau,\; q \le r \text{ and } q \forces^* \sigma = \pi\}$$
        is dense below $p$.
    \begin{itemize}
    \item $p \forces^* \sigma = \tau$ iff for every $\langle \pi,r\rangle \in \sigma$ the set
    \end{itemize}
        $$\{q \le p : q \perp r \text{ or } q \forces^* \pi \in \tau\}$$
        is dense below $p$, \emph{and} the same condition holds with $\sigma,\tau$ swapped.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    This gives an external well-founded recursion.
-/
def atomic : Bool → ZFSet.{u} → ZFSet.{u} → Set (Condition P)
  | false, σ, τ => forcingDense {q | ∃ (π : ZFSet.{u}) (r : Condition P),
      ∃ (_h : pair π r.val ∈ τ), q ≤ r ∧ q ∈ atomic true σ π}
  | true, σ, τ => {p |
      (∀ π (r : Condition P), pair π r.val ∈ σ → p ∈ forcingDense
        {q | incompatible P q r ∨ q ∈ atomic false π τ}) ∧
      (∀ π (r : Condition P), pair π r.val ∈ τ → p ∈ forcingDense
        {q | incompatible P q r ∨ q ∈ atomic false π σ})}
termination_by _ σ τ => (max σ.rank τ.rank, min σ.rank τ.rank)
decreasing_by
  · exact sorted_lt_right (child_rank_lt ‹pair _ _ ∈ _›)
  · exact sorted_lt_left (child_rank_lt ‹pair _ _ ∈ _›)
  · have h := sorted_lt_right (a := σ.rank) (child_rank_lt ‹pair _ _ ∈ _›)
    rw [max_comm σ.rank π.rank, min_comm σ.rank π.rank] at h
    exact h

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For $\sigma,\tau\in M^P$, put
    $$W(\sigma,\tau):=
    \{q:\exists\langle\pi,r\rangle\in\tau,\;q\le r\text{ and }q\forces^*\sigma=\pi\}.$$
    Then $p\forces^*\sigma\in\tau$ means that $W(\sigma,\tau)$ is dense below $p$.
    The membership test is
    $$W(\sigma,\tau)\;\cup\;
    \{q:\forall s\le q,\;s\notin W(\sigma,\tau)\}.$$

-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    We make the dense tests used in that induction explicit.
-/
def membershipWitness (σ τ : ZFSet.{u}) : Set (Condition P) :=
  {q | ∃ (π : ZFSet.{u}) (r : Condition P), ∃ (_h : pair π r.val ∈ τ), q ≤ r ∧ q ∈ atomic P true σ π}

lemma membership_eq (σ τ : ZFSet.{u}) :
    atomic P false σ τ = forcingDense (membershipWitness P σ τ) := by rw [atomic]; rfl

lemma equality_iff (σ τ : ZFSet.{u}) (p : Condition P) : p ∈ atomic P true σ τ ↔
    (∀ π (r : Condition P), pair π r.val ∈ σ → p ∈ forcingDense
      {q | incompatible P q r ∨ q ∈ atomic P false π τ}) ∧
    (∀ π (r : Condition P), pair π r.val ∈ τ → p ∈ forcingDense
      {q | incompatible P q r ∨ q ∈ atomic P false π σ}) := by rw [atomic]; rfl

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The atomic and density
    clauses inherit denseness from $p$ down to $q$;
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    the universal-style clauses ($\neg, \to, \forall$) inherit by reusing $q
    \le p$ as a stronger universal hypothesis.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For conjunction, density
    of conditions forcing both conjuncts gives density for each separately, and the induction hypothesis applies.
    For negation, a condition forcing the positive formula would have a refinement forcing its negation, a contradiction.
-/
lemma atomic_lower (b : Bool) (σ τ : ZFSet.{u}) : IsLowerSet (atomic P b σ τ) := by
  cases b
  · rw [membership_eq]; exact forcingDense_lower _
  · intro p q hqp hp
    rw [equality_iff] at hp ⊢
    exact ⟨fun π r h => forcingDense_lower _ hqp (hp.1 π r h),
      fun π r h => forcingDense_lower _ hqp (hp.2 π r h)⟩

lemma membershipWitness_lower (σ τ : ZFSet.{u}) : IsLowerSet (membershipWitness P σ τ) := by
  rintro p q hqp ⟨π, r, hπ, hpr, hp⟩
  exact ⟨π, r, hπ, hqp.trans hpr, atomic_lower P true σ π hqp hp⟩

lemma dense_dense {S : Set (Condition P)} {p : Condition P} (h : p ∈ forcingDense (forcingDense S)) :
    p ∈ forcingDense S := by
  intro q hqp
  obtain ⟨r, hrq, hr⟩ := h q hqp
  obtain ⟨s, hsr, hs⟩ := hr r le_rfl
  exact ⟨s, hsr.trans hrq, hs⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For the atomic and density clauses, compose the two dense refinements.
-/
lemma atomic_saturated (b : Bool) (σ τ : ZFSet.{u}) {p : Condition P}
    (h : p ∈ forcingDense (atomic P b σ τ)) : p ∈ atomic P b σ τ := by
  cases b
  · rw [membership_eq] at h ⊢
    exact dense_dense P h
  · rw [equality_iff]
    constructor
    · intro π r hπ q hqp
      obtain ⟨s, hsq, hs⟩ := h q hqp
      obtain ⟨t, hts, ht⟩ := ((equality_iff P σ τ s).mp hs).1 π r hπ s le_rfl
      exact ⟨t, hts.trans hsq, ht⟩
    · intro π r hπ q hqp
      obtain ⟨s, hsq, hs⟩ := h q hqp
      obtain ⟨t, hts, ht⟩ := ((equality_iff P σ τ s).mp hs).2 π r hπ s le_rfl
      exact ⟨t, hts.trans hsq, ht⟩

lemma equality_symm (σ τ : ZFSet.{u}) {p : Condition P} (h : p ∈ atomic P true σ τ) :
    p ∈ atomic P true τ σ := by
  rw [equality_iff] at h ⊢
  exact h.symm

lemma membership_of_witness {σ τ : ZFSet.{u}} {p : Condition P} (h : p ∈ membershipWitness P σ τ) :
    p ∈ atomic P false σ τ := by
  rw [membership_eq]
  exact fun q hqp => ⟨q, le_rfl, membershipWitness_lower P σ τ hqp h⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Equality is symmetric directly from its two clauses. It is also reflexive, by induction on the rank of $\sigma$.
    Fix $\langle\pi,r\rangle\in\sigma$ and $q\le p$. If $q\perp r$, the required alternative already holds.
    Otherwise choose $t\le q,r$. The induction hypothesis gives $t\forces^*\pi=\pi$.
    Every strengthening of $t$ is therefore a witness for the membership clause $\pi\in\sigma$,
    so $t\forces^*\pi\in\sigma$. This verifies the dense requirement for every pair in $\sigma$ and proves
    $p\forces^*\sigma=\sigma$.
-/
/-- Reflexivity is proved through the membership witnesses for each child. -/
theorem equality_refl (σ : ZFSet.{u}) (p : Condition P) : p ∈ atomic P true σ σ := by
  rw [equality_iff]
  suffices h : ∀ π (r : Condition P), pair π r.val ∈ σ → p ∈ forcingDense
      {q | incompatible P q r ∨ q ∈ atomic P false π σ} from ⟨h, h⟩
  intro π r hπ q hqp
  by_cases hqr : incompatible P q r
  · exact ⟨q, le_rfl, Or.inl hqr⟩
  · obtain ⟨t, htq, htr⟩ := not_not.mp hqr
    exact ⟨t, htq, Or.inr (membership_of_witness P ⟨π, r, hπ, htr, equality_refl π t⟩)⟩
termination_by σ.rank
decreasing_by exact child_rank_lt hπ

/-- Below a condition attached to a child, equality forces that child's membership. -/
lemma equality_member {σ τ π : ZFSet.{u}} {p r : Condition P}
    (he : p ∈ atomic P true σ τ) (hπ : pair π r.val ∈ σ) (hpr : p ≤ r) :
    p ∈ atomic P false π τ := by
  apply atomic_saturated P false π τ
  intro q hqp
  obtain ⟨s, hsq, hs⟩ := ((equality_iff P σ τ p).mp he).1 π r hπ q hqp
  rcases hs with hs | hs
  · exact False.elim (hs ⟨s, le_rfl, hsq.trans (hqp.trans hpr)⟩)
  · exact ⟨s, hsq, hs⟩

def equalityDefect (σ τ : ZFSet.{u}) : Set (Condition P) :=
  {q | ∃ (π : ZFSet.{u}) (r : Condition P), pair π r.val ∈ σ ∧ q ≤ r ∧
    q ∈ forcingNeg (atomic P false π τ)}

def equalityTest (σ τ : ZFSet.{u}) : Set (Condition P) :=
  atomic P true σ τ ∪ equalityDefect P σ τ ∪ equalityDefect P τ σ

lemma failed_half_refinement (σ τ : ZFSet.{u}) {p : Condition P}
    (h : ¬ ∀ π (r : Condition P), pair π r.val ∈ σ → p ∈ forcingDense
      {q | incompatible P q r ∨ q ∈ atomic P false π τ}) :
    ∃ q, q ≤ p ∧ q ∈ equalityDefect P σ τ := by
  classical
  simp only [forcingDense, Set.mem_ofPred_eq] at h
  push Not at h
  obtain ⟨π, r, hπ, q, hqp, hq⟩ := h
  obtain ⟨t, htq, htr⟩ := not_not.mp (hq q le_rfl).1
  exact ⟨t, htq.trans hqp, π, r, hπ, htr, fun s hst => (hq s (hst.trans htq)).2⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For equality, define the one-sided defect set and the test
    $$\begin{aligned}
    F(\sigma,\tau):=\{q:{}&\exists\langle\pi,r\rangle\in\sigma,\;q\le r,\\
    &\forall s\le q,\;\neg(s\forces^*\pi\in\tau)\},\\
    D(\sigma,\tau):={}&\{q:q\forces^*\sigma=\tau\}
    \cup F(\sigma,\tau)\cup F(\tau,\sigma).
    \end{aligned}$$
    The set $D(\sigma,\tau)$ is dense. If $p$ fails the equality clause, one half has a pair
    $\langle\pi,r\rangle$ whose dense requirement fails. There is then $q\le p$ such that no $s\le q$ is incompatible
    with $r$ or forces the required membership. In particular $q$ is compatible with $r$.
    Choose $t\le q,r$. No strengthening of $t$ forces that membership, so $t$ lies in the corresponding defect set.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    These tests belong to $M$ by atomic definability.
-/
/-- The equality test either forces equality or records a one-sided membership defect. -/
lemma equalityTest_dense (σ τ : ZFSet.{u}) : IsCoinitial (equalityTest P σ τ) := by
  classical
  intro p
  by_cases hp : p ∈ atomic P true σ τ
  · exact ⟨p, Or.inl (Or.inl hp), le_rfl⟩
  · rw [equality_iff] at hp
    rcases not_and_or.mp hp with h | h
    · obtain ⟨q, hqp, hq⟩ := failed_half_refinement P σ τ h
      exact ⟨q, Or.inl (Or.inr hq), hqp⟩
    · obtain ⟨q, hqp, hq⟩ := failed_half_refinement P τ σ h
      exact ⟨q, Or.inr hq, hqp⟩

lemma equalityDefect_lower (σ τ : ZFSet.{u}) : IsLowerSet (equalityDefect P σ τ) := by
  rintro p q hqp ⟨π, r, hπ, hpr, hp⟩
  exact ⟨π, r, hπ, hqp.trans hpr, forcingNeg_lower _ hqp hp⟩

lemma equalityTest_lower (σ τ : ZFSet.{u}) : IsLowerSet (equalityTest P σ τ) := by
  intro p q hqp hp
  rcases hp with ((hp | hp) | hp)
  · exact Or.inl (Or.inl (atomic_lower P true σ τ hqp hp))
  · exact Or.inl (Or.inr (equalityDefect_lower P σ τ hqp hp))
  · exact Or.inr (equalityDefect_lower P τ σ hqp hp)

end PolishSpaceBook.ForcingAtomic
