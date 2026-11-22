module

public import PolishSpaceBook.ForcingDenseNameTransport

@[expose] public section

/-! # Matching names through a dense embedding by refining labelled children -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open ZFSet ForcingNames ForcingAtomic
universe u
variable {P Q : ZFSet.{u}} [Preorder (Condition P)] [Preorder (Condition Q)] (e : Condition P ↪o Condition Q)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For recursive forcing, define a matching relation between a $P$-name $\sigma$ and a $Q$-name $\tau$
    by recursion on the rank of the source name. Require both of the following clauses:

    * For $\langle\pi,a\rangle\in\sigma$ and $r\le a$, there are $s\le r$ and
      $\langle\delta,b\rangle\in\tau$ such that $e(s)\le b$ and the child names $\pi,\delta$ match.
    * For $\langle\delta,b\rangle\in\tau$ and $e(r)\le b$, there are $s\le r$ and
      $\langle\pi,a\rangle\in\sigma$ such that $s\le a$ and the child names $\pi,\delta$ match.

    The forward translation matches each name with its image. The reverse translation matches each
    translated name with the original name, since it includes every refining source condition.
-/
/-- Each labelled child can be matched on a dense collection of refinements.
The relation itself is defined by well-founded recursion on the source name. -/
def DenseNameMatch (σ τ : ZFSet.{u}) : Prop :=
  (∀ π (a : Condition P), pair π a.val ∈ σ → ∀ r ≤ a,
    ∃ s ≤ r, ∃ (δ : ZFSet.{u}) (b : Condition Q), pair δ b.val ∈ τ ∧ e s ≤ b ∧ DenseNameMatch π δ) ∧
  (∀ δ (b : Condition Q), pair δ b.val ∈ τ → ∀ r, e r ≤ b →
    ∃ s ≤ r, ∃ (π : ZFSet.{u}) (a : Condition P), ∃ (_h : pair π a.val ∈ σ), s ≤ a ∧ DenseNameMatch π δ)
termination_by σ.rank
decreasing_by all_goals exact child_rank_lt ‹pair _ _ ∈ σ›

lemma DenseNameMatch.forth {σ τ : ZFSet.{u}} (h : DenseNameMatch e σ τ)
    (π : ZFSet.{u}) (a : Condition P) (ha : pair π a.val ∈ σ) (r : Condition P) (hra : r ≤ a) :
    ∃ s ≤ r, ∃ (δ : ZFSet.{u}) (b : Condition Q), pair δ b.val ∈ τ ∧ e s ≤ b ∧ DenseNameMatch e π δ := by
  rw [DenseNameMatch] at h
  exact h.1 π a ha r hra

lemma DenseNameMatch.back {σ τ : ZFSet.{u}} (h : DenseNameMatch e σ τ)
    (δ : ZFSet.{u}) (b : Condition Q) (hb : pair δ b.val ∈ τ) (r : Condition P) (hrb : e r ≤ b) :
    ∃ s ≤ r, ∃ (π : ZFSet.{u}) (a : Condition P), pair π a.val ∈ σ ∧ s ≤ a ∧ DenseNameMatch e π δ := by
  rw [DenseNameMatch] at h
  obtain ⟨s, hsr, π, a, hπ, hsa, hπδ⟩ := h.2 δ b hb r hrb
  exact ⟨s, hsr, π, a, hπ, hsa, hπδ⟩

variable (E S : ZFSet.{u})
  (hE : ∀ p : Condition P, ∀ q : Condition Q, pair p.val q.val ∈ E ↔ e p = q)
  (hS : ∀ p q : Condition Q, pair p.val q.val ∈ S ↔ p ≤ q)

include hE in
 theorem forwardName_match (σ : ZFSet.{u}) : DenseNameMatch e σ (relabelName P Q E σ) := by
  rw [DenseNameMatch]
  constructor
  · intro π a ha r hra
    refine ⟨r, le_rfl, relabelName P Q E π, e a, ?_, e.monotone hra, forwardName_match π⟩
    exact (pair_mem_relabelName P Q E σ _ _).mpr
      ⟨π, a.val, a.property, (e a).property, ha, (hE a (e a)).mpr rfl, rfl⟩
  · intro δ b hb r hrb
    obtain ⟨π, a, haP, hbQ, hπ, hab, rfl⟩ := (pair_mem_relabelName P Q E σ δ b.val).mp hb
    let ac : Condition P := ⟨a, haP⟩
    have hab' := (hE ac b).mp hab
    refine ⟨r, le_rfl, π, ac, hπ, ?_, forwardName_match π⟩
    exact e.le_iff_le.mp (hrb.trans_eq hab'.symm)
termination_by σ.rank
decreasing_by all_goals exact child_rank_lt ‹pair _ _ ∈ σ›

include hE hS in
 theorem inverseName_match (τ : ZFSet.{u}) :
    DenseNameMatch e (relabelName Q P (inverseLabelGraph P Q S E) τ) τ := by
  have hi (q : Condition Q) (p : Condition P) :
      pair q.val p.val ∈ inverseLabelGraph P Q S E ↔ e p ≤ q := by
    simp only [inverseLabelGraph, mem_sep, pair_mem_prod, p.property, q.property, true_and]
    change (∃ b ∈ Q, ∃ a ∈ P, pair q.val p.val = pair b a ∧
      ∃ r ∈ Q, pair a r ∈ E ∧ pair r b ∈ S) ↔ _
    constructor
    · rintro ⟨b, _, a, _, he, r, hr, hpr, hrq⟩
      obtain ⟨rfl, rfl⟩ := pair_inj.mp he
      exact (hE p ⟨r, hr⟩).mp hpr ▸ (hS ⟨r, hr⟩ q).mp hrq
    · intro hpq
      exact ⟨q.val, q.property, p.val, p.property, rfl, (e p).val, (e p).property,
        (hE p (e p)).mpr rfl, (hS (e p) q).mpr hpq⟩
  rw [DenseNameMatch]
  constructor
  · intro π a ha r hra
    obtain ⟨δ, b, hbQ, _, hδ, hba, rfl⟩ := (pair_mem_relabelName Q P _ τ π a.val).mp ha
    let bc : Condition Q := ⟨b, hbQ⟩
    exact ⟨r, le_rfl, δ, bc, hδ, (e.monotone hra).trans ((hi bc a).mp hba), inverseName_match δ⟩
  · intro δ b hb r hrb
    refine ⟨r, le_rfl, relabelName Q P (inverseLabelGraph P Q S E) δ, r, ?_, le_rfl, inverseName_match δ⟩
    exact (pair_mem_relabelName Q P _ τ _ _).mpr
      ⟨δ, b.val, b.property, r.property, hb, (hi b r).mpr hrb, rfl⟩
termination_by τ.rank
decreasing_by all_goals exact child_rank_lt ‹pair _ _ ∈ τ›

end PolishSpaceBook.SetTheoryModels
