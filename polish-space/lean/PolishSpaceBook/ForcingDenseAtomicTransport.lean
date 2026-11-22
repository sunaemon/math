module

public import PolishSpaceBook.ForcingDenseNameRelation

@[expose] public section

/-! # Direct rank induction for atomic forcing under a dense embedding -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open ZFSet ForcingNames ForcingAtomic
universe u
variable {P Q : ZFSet.{u}} [Preorder (Condition P)] [Preorder (Condition Q)]
  (e : Condition P ↪o Condition Q) (hd : ∀ q : Condition Q, ∃ p, e p ≤ q)

include hd in
lemma matched_equality_half_forth {σ τ σ' τ' : ZFSet.{u}} (hσ : DenseNameMatch e σ σ')
    (ih : ∀ π (a : Condition P), pair π a.val ∈ σ → ∀ δ, DenseNameMatch e π δ →
      ∀ p, p ∈ atomic P false π τ ↔ e p ∈ atomic Q false δ τ')
    (p : Condition P) (hp : p ∈ atomic P true σ τ) :
    ∀ δ (b : Condition Q), pair δ b.val ∈ σ' → e p ∈ forcingDense
      {q | incompatible Q q b ∨ q ∈ atomic Q false δ τ'} := by
  intro δ b hb q hqp
  by_cases hqb : incompatible Q q b
  · exact ⟨q, le_rfl, Or.inl hqb⟩
  · obtain ⟨v, hvq, hvb⟩ := not_not.mp hqb
    obtain ⟨r, hrv⟩ := hd v
    obtain ⟨s, hsr, π, a, hπ, hsa, hπδ⟩ := hσ.back e δ b hb r (hrv.trans hvb)
    have hsp : s ≤ p := e.le_iff_le.mp ((e.monotone hsr).trans (hrv.trans (hvq.trans hqp)))
    have hs := equality_member P (atomic_lower P true σ τ hsp hp) hπ hsa
    exact ⟨e s, (e.monotone hsr).trans (hrv.trans hvq), Or.inr ((ih π a hπ δ hπδ s).mp hs)⟩

lemma matched_equality_half_back {σ τ σ' τ' : ZFSet.{u}} (hσ : DenseNameMatch e σ σ')
    (ih : ∀ π (a : Condition P), pair π a.val ∈ σ → ∀ δ, DenseNameMatch e π δ →
      ∀ p, p ∈ atomic P false π τ ↔ e p ∈ atomic Q false δ τ')
    (p : Condition P) (hp : e p ∈ atomic Q true σ' τ') :
    ∀ π (a : Condition P), pair π a.val ∈ σ → p ∈ forcingDense
      {q | incompatible P q a ∨ q ∈ atomic P false π τ} := by
  intro π a hπ r hrp
  by_cases hra : incompatible P r a
  · exact ⟨r, le_rfl, Or.inl hra⟩
  · obtain ⟨s, hsr, hsa⟩ := not_not.mp hra
    obtain ⟨t, hts, δ, b, hδ, htb, hπδ⟩ := hσ.forth e π a hπ s hsa
    have htp : e t ≤ e p := e.monotone (hts.trans (hsr.trans hrp))
    have ht := equality_member Q (atomic_lower Q true σ' τ' htp hp) hδ htb
    exact ⟨t, hts.trans hsr, Or.inr ((ih π a hπ δ hπδ t).mpr ht)⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For matched pairs of name parameters, prove atomic forcing correspondence by induction on the pair
    of source ranks, sorted in decreasing order. In the membership clause, refine a witnessing condition
    into the image and use a matching child; the recursive equality assertion has smaller rank.
    For equality, apply the induction hypothesis to the membership assertions for each child, in both
    directions. Density supplies the image refinements, and downward closure preserves the forced assertions.
-/
include hd in
/-- Both atomic clauses are transported by their defining recursion. The proof
uses dense refinements, never the existence of a generic filter. -/
theorem atomic_dense_transport (b : Bool) (σ τ σ' τ' : ZFSet.{u})
    (hσ : DenseNameMatch e σ σ') (hτ : DenseNameMatch e τ τ') (p : Condition P) :
    p ∈ atomic P b σ τ ↔ e p ∈ atomic Q b σ' τ' := by
  cases b
  · rw [membership_eq, membership_eq]
    constructor
    · intro hp q hqp
      obtain ⟨r, hrq⟩ := hd q
      have hrp : r ≤ p := e.le_iff_le.mp (hrq.trans hqp)
      obtain ⟨s, hsr, π, a, hπ, hsa, hs⟩ := hp r hrp
      obtain ⟨t, hts, δ, c, hδ, htc, hπδ⟩ := hτ.forth e π a hπ s hsa
      have ht := atomic_lower P true σ π hts hs
      exact ⟨e t, (e.monotone (hts.trans hsr)).trans hrq, δ, c, hδ, htc,
        (atomic_dense_transport true σ π σ' δ hσ hπδ t).mp ht⟩
    · intro hp r hrp
      obtain ⟨q, hqr, δ, c, hδ, hqc, hq⟩ := hp (e r) (e.monotone hrp)
      obtain ⟨s, hsq⟩ := hd q
      obtain ⟨t, hts, π, a, hπ, hta, hπδ⟩ := hτ.back e δ c hδ s (hsq.trans hqc)
      have htr : t ≤ r := e.le_iff_le.mp ((e.monotone hts).trans (hsq.trans hqr))
      have ht := atomic_lower Q true σ' δ ((e.monotone hts).trans hsq) hq
      exact ⟨t, htr, π, a, hπ, hta,
        (atomic_dense_transport true σ π σ' δ hσ hπδ t).mpr ht⟩
  · constructor
    · intro hp
      rw [equality_iff]
      constructor
      · exact matched_equality_half_forth e hd hσ
          (fun π a hπ δ hπδ p => atomic_dense_transport false π τ δ τ' hπδ hτ p) p hp
      · exact matched_equality_half_forth e hd hτ
          (fun π a hπ δ hπδ p => atomic_dense_transport false π σ δ σ' hπδ hσ p) p
          (equality_symm P σ τ hp)
    · intro hp
      rw [equality_iff]
      constructor
      · exact matched_equality_half_back e hσ
          (fun π a hπ δ hπδ p => atomic_dense_transport false π τ δ τ' hπδ hτ p) p hp
      · exact matched_equality_half_back e hτ
          (fun π a hπ δ hπδ p => atomic_dense_transport false π σ δ σ' hπδ hσ p) p
          (equality_symm Q σ' τ' hp)
termination_by (max σ.rank τ.rank, min σ.rank τ.rank)
decreasing_by
  · exact sorted_lt_right (child_rank_lt hπ)
  · exact sorted_lt_right (child_rank_lt hπ)
  · exact sorted_lt_left (child_rank_lt hπ)
  · have h := sorted_lt_right (a := σ.rank) (child_rank_lt hπ)
    simpa only [max_comm, min_comm] using h
  · exact sorted_lt_left (child_rank_lt hπ)
  · have h := sorted_lt_right (a := σ.rank) (child_rank_lt hπ)
    simpa only [max_comm, min_comm] using h

end PolishSpaceBook.SetTheoryModels
