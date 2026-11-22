module

public import PolishSpaceBook.EffectiveDSTLightfaceHierarchies

@[expose] public section

/-! # Pair-tree geometry independent of a computation model -/
namespace PolishSpaceBook
open Set MeasureTheory

/-- Every finite-prefix test is closed, without requiring computability
or downward closure of the set of permitted pairs. -/
theorem isClosed_pairTreeBody (T : Set (finseq ℕ × finseq ℕ)) :
    IsClosed (pairTreeBody T) := by
  let : TopologicalSpace (finseq ℕ) := ⊥
  let : DiscreteTopology (finseq ℕ) := ⟨rfl⟩
  have hp (n : ℕ) : Continuous (fun p : ℕ → ℕ => seqPrefix p n) :=
    (continuous_of_discreteTopology : Continuous (fun v : Fin n → ℕ => List.ofFn v)).comp
      (continuous_pi (fun i => continuous_apply i.val))
  have heq : pairTreeBody T = ⋂ n : ℕ,
      (fun p : (ℕ → ℕ) × (ℕ → ℕ) => (seqPrefix p.1 n, seqPrefix p.2 n)) ⁻¹' T := by
    ext p
    simp [pairTreeBody]
  rw [heq]
  exact isClosed_iInter fun n => (isClosed_discrete T).preimage
    (((hp n).comp continuous_fst).prodMk ((hp n).comp continuous_snd))

theorem pairTreeProjection_eq_image (T : Set (finseq ℕ × finseq ℕ)) :
    pairTreeProjection T = Prod.fst '' pairTreeBody T := by
  ext p
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨(p, q), hq, rfl⟩
  · rintro ⟨⟨p, q⟩, hq, rfl⟩
    exact ⟨q, hq⟩

theorem analyticSet_pairTreeProjection (T : Set (finseq ℕ × finseq ℕ)) :
    AnalyticSet (pairTreeProjection T) := by
  rw [pairTreeProjection_eq_image]
  exact (isClosed_pairTreeBody T).analyticSet.image_of_continuous continuous_fst

/-- Decode the two independent witness coordinates from one natural-valued
finite word. -/
def leftWitness (t : finseq ℕ) : finseq ℕ := t.map (fun k => k.unpair.1)

def rightWitness (t : finseq ℕ) : finseq ℕ := t.map (fun k => k.unpair.2)

/-- A finite word can meet a cylinder precisely when its defining prefix
and that word are comparable. -/
def prefixCompatible (s t : finseq ℕ) : Prop := prefixOf s t ∨ prefixOf t s

theorem prefixCompatible_take {s t : finseq ℕ} (h : prefixCompatible s t) (n : ℕ) :
    prefixCompatible s (t.take n) := by
  rcases h with h | h
  · exact List.prefix_or_prefix_of_prefix h (List.take_prefix n t)
  · exact Or.inr ((List.take_prefix n t).trans h)

theorem all_prefixCompatible_iff (s : finseq ℕ) (p : ℕ → ℕ) :
    (∀ n, prefixCompatible s (seqPrefix p n)) ↔ p ∈ cyl s := by
  constructor
  · intro h
    rcases h s.length with h | h
    · have heq := h.eq_of_length (seqPrefix_length p s.length).symm
      rw [heq]
      exact mem_cyl_seqPrefix p s.length
    · have heq := h.eq_of_length (seqPrefix_length p s.length)
      rw [← heq]
      exact mem_cyl_seqPrefix p s.length
  · intro hp n
    have heq := seqPrefix_eq_of_mem_cyl hp
    rw [← heq]
    rcases le_total s.length n with h | h
    · exact Or.inl (seqPrefix_prefixOf_of_le p h)
    · exact Or.inr (seqPrefix_prefixOf_of_le p h)

end PolishSpaceBook
