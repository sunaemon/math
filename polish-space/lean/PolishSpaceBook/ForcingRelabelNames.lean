module

public import PolishSpaceBook.ForcingNames
public import PolishSpaceBook.ForcingAtomic
public import PolishSpaceBook.PFilterTransport

@[expose] public section

/-! # Recursive relabelling of actual forcing names

A set-coded relation may replace one condition by several conditions. This
includes the inverse dense-embedding translation, which uses every refinement.
-/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open ZFSet ForcingAtomic
universe u

abbrev RelabelChild (P Q E τ : ZFSet.{u}) :=
  {t : ZFSet.sUnion (ZFSet.sUnion τ) × P × Q //
    pair t.1.val t.2.1.val ∈ τ ∧ pair t.2.1.val t.2.2.val ∈ E}

def relabelName (P Q E τ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun t : RelabelChild P Q E τ =>
    pair (relabelName P Q E t.val.1.val) t.val.2.2.val)
termination_by τ.rank
decreasing_by exact child_rank_lt t.property.1

lemma relabelName_eq (P Q E τ : ZFSet.{u}) :
    relabelName P Q E τ = ZFSet.range (fun t : RelabelChild P Q E τ =>
      pair (relabelName P Q E t.val.1.val) t.val.2.2.val) := by rw [relabelName]

lemma mem_relabelName (P Q E τ z : ZFSet.{u}) :
    z ∈ relabelName P Q E τ ↔ ∃ σ p q, p ∈ P ∧ q ∈ Q ∧
      pair σ p ∈ τ ∧ pair p q ∈ E ∧ z = pair (relabelName P Q E σ) q := by
  rw [relabelName_eq, mem_range]
  constructor
  · rintro ⟨t, he⟩
    exact ⟨t.val.1.val, t.val.2.1.val, t.val.2.2.val, t.val.2.1.property,
      t.val.2.2.property, t.property.1, t.property.2, he.symm⟩
  · rintro ⟨σ, p, q, hp, hq, hστ, hpq, he⟩
    exact ⟨⟨⟨⟨σ, child_mem_doubleUnion hστ⟩, ⟨p, hp⟩, ⟨q, hq⟩⟩, hστ, hpq⟩, he.symm⟩

lemma pair_mem_relabelName (P Q E τ σ q : ZFSet.{u}) :
    pair σ q ∈ relabelName P Q E τ ↔ ∃ π p, p ∈ P ∧ q ∈ Q ∧
      pair π p ∈ τ ∧ pair p q ∈ E ∧ σ = relabelName P Q E π := by
  rw [mem_relabelName]
  constructor
  · rintro ⟨π, p, r, hp, hr, hπτ, hpr, he⟩
    obtain ⟨heσ, rfl⟩ := pair_inj.mp he
    exact ⟨π, p, hp, hr, hπτ, hpr, heσ⟩
  · rintro ⟨π, p, hp, hq, hπτ, hpq, rfl⟩
    exact ⟨π, p, q, hp, hq, hπτ, hpq, rfl⟩

lemma relabelName_isName (P Q E τ : ZFSet.{u}) (hτ : IsName P τ) :
    IsName Q (relabelName P Q E τ) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨σ, _, q, _, _, _, _, he⟩ := (mem_relabelName P Q E τ z).mp hz
    exact ⟨relabelName P Q E σ, q, he⟩
  · intro σ q hσ
    obtain ⟨π, p, _, hq, hπτ, _, rfl⟩ := (pair_mem_relabelName P Q E τ σ q).mp hσ
    exact ⟨hq, relabelName_isName P Q E π (hτ.child hπτ)⟩
termination_by τ.rank
decreasing_by exact child_rank_lt hπτ

/-- Valuation commutes with the actual rank recursion whenever the label
relation describes the two filters. No valuation assignment is postulated. -/
theorem valuation_relabelName (P Q E : ZFSet.{u}) (G H : Set ZFSet.{u})
    (hE : ∀ p ∈ P, p ∈ G ↔ ∃ q ∈ Q, q ∈ H ∧ pair p q ∈ E)
    (τ : ZFSet.{u}) (hτ : IsName P τ) :
    valuation H (relabelName P Q E τ) = valuation G τ := by
  ext x
  rw [mem_valuation, mem_valuation]
  constructor
  · rintro ⟨σ, q, hqH, hσ, hx⟩
    obtain ⟨π, p, hp, hq, hπτ, hpq, rfl⟩ := (pair_mem_relabelName P Q E τ σ q).mp hσ
    exact ⟨π, p, (hE p hp).mpr ⟨q, hq, hqH, hpq⟩, hπτ,
      (valuation_relabelName P Q E G H hE π (hτ.child hπτ)).symm.trans hx⟩
  · rintro ⟨σ, p, hpG, hστ, hx⟩
    have hp := hτ.condition hστ
    obtain ⟨q, hq, hqH, hpq⟩ := (hE p hp).mp hpG
    exact ⟨relabelName P Q E σ, q, hqH,
      (pair_mem_relabelName P Q E τ _ q).mpr ⟨σ, p, hp, hq, hστ, hpq, rfl⟩,
      (valuation_relabelName P Q E G H hE σ (hτ.child hστ)).trans hx⟩
termination_by τ.rank
decreasing_by all_goals exact child_rank_lt ‹pair _ _ ∈ τ›

end PolishSpaceBook.ForcingNames
