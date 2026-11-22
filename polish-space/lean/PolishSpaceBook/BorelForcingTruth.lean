module

public import PolishSpaceBook.BorelExpressionEvaluation
public import Mathlib.Order.PFilter

@[expose] public section

/-!
# Truth for the countable Borel fragment of an order forcing

Negation excludes every stronger positive condition; union means that the
union of its children's forcing sets is dense below the condition. The
countable tree supplies explicit lower dense decision/witness tests. A
filter meeting them satisfies the truth lemma by induction on the code.
Atomic truth is an interface to be proved for the intended point forcing.
This is not analytic/coanalytic absoluteness or a generic-extension model.
-/

namespace PolishSpaceBook
open Set

variable {P : Type*} [Preorder P]

def forcingNeg (S : Set P) : Set P := {p | ∀ q, q ≤ p → q ∉ S}

def forcingDense (S : Set P) : Set P := {p | ∀ q, q ≤ p → ∃ r, r ≤ q ∧ r ∈ S}

def forcingDecision (S : Set P) : Set P := S ∪ forcingNeg S

theorem forcingNeg_lower (S : Set P) : IsLowerSet (forcingNeg S) :=
  fun _ _ hqp hp r hrq => hp r (hrq.trans hqp)

theorem forcingDense_lower (S : Set P) : IsLowerSet (forcingDense S) :=
  fun _ _ hqp hp r hrq => hp r (hrq.trans hqp)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    It is dense: either a condition has a strengthening in $W(\sigma,\tau)$, or it belongs to the second part.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    We make the dense tests used in that induction explicit.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For any set $S\IncludedIn Q_+$ define
    $$\ForcingNeg{S}:=\{p\in Q_+:\forall q\le p\ (q\notin S)\},\qquad
    \ForcingDecision{S}:=S\cup\ForcingNeg{S}.$$
    The quantifier ranges over positive conditions. The decision set is dense: either a condition has a strengthening in
    $S$, or it already belongs to $\ForcingNeg{S}$.
-/
theorem forcingDecision_dense (S : Set P) : IsCoinitial (forcingDecision S) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ q ∈ S
  · obtain ⟨q, hqp, hq⟩ := h
    exact ⟨q, Or.inl hq, hqp⟩
  · exact ⟨p, Or.inr (fun q hqp hq => h ⟨q, hqp, hq⟩), le_rfl⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    If $S$ is closed under strengthening, so is its decision set.
-/
theorem forcingDecision_lower {S : Set P} (hS : IsLowerSet S) : IsLowerSet (forcingDecision S) := by
  intro p q hqp hp
  rcases hp with hp | hp
  · exact Or.inl (hS hqp hp)
  · exact Or.inr (forcingNeg_lower S hqp hp)

theorem lower_iUnion {I : Type*} (S : I → Set P) (hS : ∀ i, IsLowerSet (S i)) :
    IsLowerSet (⋃ i, S i) := by
  intro p q hqp hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨i, hS i hqp hi⟩

/-- Positive and negative forcing conditions cannot coexist in a filter. -/
theorem pfilter_not_pos_neg (G : Order.PFilter P) {S : Set P} (hS : IsLowerSet S)
    {p q : P} (hpG : p ∈ G) (hqG : q ∈ G) (hp : p ∈ S) (hq : q ∈ forcingNeg S) : False := by
  obtain ⟨r, _, hrp, hrq⟩ := G.directed p hpG q hqG
  exact hq r hrq (hS hrp hp)

/-- A filter containing a condition below which S is dense and meeting its
decision test must take the positive alternative. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    If $G$ meets this test and contains a condition below which $W(\sigma,\tau)$ is dense,
    it cannot meet the second part;
    a common strengthening of the two filter conditions would contradict that density. Thus $G$ meets
    $W(\sigma,\tau)$ itself.
-/
theorem pfilter_dense_witness (G : Order.PFilter P) {S : Set P}
    {p : P} (hpG : p ∈ G) (hp : p ∈ forcingDense S)
    (hmeet : ∃ q ∈ G, q ∈ forcingDecision S) : ∃ q ∈ G, q ∈ S := by
  obtain ⟨q, hqG, hq⟩ := hmeet
  rcases hq with hq | hq
  · exact ⟨q, hqG, hq⟩
  · obtain ⟨r, _, hrp, hrq⟩ := G.directed p hpG q hqG
    obtain ⟨s, hsr, hs⟩ := hp r hrp
    exact False.elim (hq s (hsr.trans hrq) hs)

namespace BorelCode

def forcing (A : ℕ → Set P) : BorelCode → Set P
  | .leaf n => A n
  | .compl c => forcingNeg (c.forcing A)
  | .union f => forcingDense (⋃ n, (f n).forcing A)

theorem forcing_lower (A : ℕ → Set P) (hA : ∀ n, IsLowerSet (A n)) (c : BorelCode) :
    IsLowerSet (c.forcing A) := by
  cases c with
  | leaf n => exact hA n
  | compl c => exact forcingNeg_lower _
  | union f => exact forcingDense_lower _

def forcingRequirements (A : ℕ → Set P) : BorelCode → Set (Set P)
  | .leaf _ => ∅
  | .compl c => c.forcingRequirements A ∪ {forcingDecision (c.forcing A)}
  | .union f => (⋃ n, (f n).forcingRequirements A) ∪ {forcingDecision (⋃ n, (f n).forcing A)}

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For each set $S$ of conditions closed under strengthening,
    the decision family
    $$D(S)=S\cup\{P:\forall Q\le P\ (Q\notin S)\}$$
    is downward-closed and dense. At a leaf, $P$ forces membership when it is contained in that cylinder rectangle.
    At a complement node, $P$ forces membership when no stronger condition forces the child. At a union node,
    $P$ forces membership when conditions forcing one of the children are dense below $P$. Include the decision
    family for the child at each complement node and for the union of the children's forcing sets at each union node.
    There are only countably many such tests.
-/
theorem forcingRequirements_countable (A : ℕ → Set P) (c : BorelCode) :
    (c.forcingRequirements A).Countable := by
  induction c with
  | leaf n => exact countable_empty
  | compl c ih => exact ih.union (countable_singleton _)
  | union f ih => exact (countable_iUnion ih).union (countable_singleton _)

theorem forcingRequirements_dense_lower (A : ℕ → Set P) (hA : ∀ n, IsLowerSet (A n))
    (c : BorelCode) : ∀ D ∈ c.forcingRequirements A, IsCoinitial D ∧ IsLowerSet D := by
  induction c with
  | leaf n => simp [forcingRequirements]
  | compl c ih =>
    rintro D (hD | hD)
    · exact ih D hD
    · obtain rfl := mem_singleton_iff.mp hD
      exact ⟨forcingDecision_dense _, forcingDecision_lower (c.forcing_lower A hA)⟩
  | union f ih =>
    rintro D (hD | hD)
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hD
      exact ih n D hn
    · obtain rfl := mem_singleton_iff.mp hD
      exact ⟨forcingDecision_dense _, forcingDecision_lower
        (lower_iUnion _ (fun n => (f n).forcing_lower A hA))⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For this Borel relation we can prove the needed local truth property directly. Fix a well-founded Borel code
    for $E$ whose leaves are basic cylinder rectangles.
-/
/-- Truth and forcing agree for every node of a well-founded Borel code,
once the filter meets the explicit tests and the atoms have actual semantics. -/
theorem forcing_truth {X : Type*} (U : ℕ → Set X) (A : ℕ → Set P)
    (hA : ∀ n, IsLowerSet (A n)) (c : BorelCode) (G : Order.PFilter P) (x : X)
    (hatom : ∀ n, x ∈ U n ↔ ∃ p ∈ G, p ∈ A n)
    (hG : ∀ D ∈ c.forcingRequirements A, ∃ p ∈ G, p ∈ D) :
    x ∈ c.decode U ↔ ∃ p ∈ G, p ∈ c.forcing A := by
  induction c with
  | leaf n => exact hatom n
  | compl c ih =>
    have hchild := ih (fun D hD => hG D (Or.inl hD))
    have hdec := hG _ (Or.inr (mem_singleton _))
    change x ∉ c.decode U ↔ ∃ p ∈ G, p ∈ forcingNeg (c.forcing A)
    constructor
    · intro hn
      obtain ⟨p, hpG, hp⟩ := hdec
      rcases hp with hp | hp
      · exact False.elim (hn (hchild.mpr ⟨p, hpG, hp⟩))
      · exact ⟨p, hpG, hp⟩
    · rintro ⟨p, hpG, hp⟩ hx
      obtain ⟨q, hqG, hq⟩ := hchild.mp hx
      exact pfilter_not_pos_neg G (c.forcing_lower A hA) hqG hpG hq hp
  | union f ih =>
    have hchildren n := ih n (fun D hD => hG D (Or.inl (mem_iUnion.mpr ⟨n, hD⟩)))
    have hdec := hG _ (Or.inr (mem_singleton _))
    change x ∈ ⋃ n, (f n).decode U ↔ ∃ p ∈ G, p ∈ forcingDense (⋃ n, (f n).forcing A)
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨p, hpG, hp⟩ := (hchildren n).mp hn
      refine ⟨p, hpG, ?_⟩
      intro q hqp
      exact ⟨q, le_rfl, mem_iUnion.mpr ⟨n, (f n).forcing_lower A hA hqp hp⟩⟩
    · rintro ⟨p, hpG, hp⟩
      obtain ⟨q, hqG, hq⟩ := pfilter_dense_witness G hpG hp hdec
      obtain ⟨n, hn⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨n, (hchildren n).mpr ⟨q, hqG, hn⟩⟩

/-- A true statement has a condition in the filter which makes it true in
every other filter meeting the same tests and having the specified atoms. -/
theorem forcing_local_truth {X : Type*} (U : ℕ → Set X) (A : ℕ → Set P)
    (hA : ∀ n, IsLowerSet (A n)) (c : BorelCode) (G : Order.PFilter P) (x : X)
    (hatom : ∀ n, x ∈ U n ↔ ∃ p ∈ G, p ∈ A n)
    (hG : ∀ D ∈ c.forcingRequirements A, ∃ p ∈ G, p ∈ D) (hx : x ∈ c.decode U) :
    ∃ p ∈ G, ∀ (H : Order.PFilter P) (y : X), p ∈ H →
      (∀ n, y ∈ U n ↔ ∃ q ∈ H, q ∈ A n) →
      (∀ D ∈ c.forcingRequirements A, ∃ q ∈ H, q ∈ D) → y ∈ c.decode U := by
  obtain ⟨p, hpG, hp⟩ := (c.forcing_truth U A hA G x hatom hG).mp hx
  exact ⟨p, hpG, fun H y hpH hyatom hH =>
    (c.forcing_truth U A hA H y hyatom hH).mpr ⟨p, hpH, hp⟩⟩

end BorelCode
end PolishSpaceBook
