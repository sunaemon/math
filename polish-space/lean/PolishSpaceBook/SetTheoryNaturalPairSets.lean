module

public import PolishSpaceBook.SetTheoryFiniteSequences

@[expose] public section

/-! # Sets of natural-number pairs, with one shared membership calculation -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open ZFSet
universe u

def naturalPairSet (P : ℕ → ℕ → Prop) : ZFSet.{u} :=
  (ZFSet.prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet).sep
    (fun z => ∃ a b : ℕ, z = pair (natOrdinal a) (natOrdinal b) ∧ P a b)

lemma mem_naturalPairSet (P : ℕ → ℕ → Prop) (z : ZFSet.{u}) :
    z ∈ naturalPairSet P ↔ ∃ a b : ℕ, z = pair (natOrdinal a) (natOrdinal b) ∧ P a b := by
  rw [naturalPairSet, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨a, b, rfl, h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨a, rfl⟩,
      mem_omegaOrdinal.mpr ⟨b, rfl⟩⟩, a, b, rfl, h⟩

lemma pair_mem_naturalPairSet (P : ℕ → ℕ → Prop) (a b : ℕ) :
    pair (natOrdinal a) (natOrdinal b) ∈ naturalPairSet.{u} P ↔ P a b := by
  rw [mem_naturalPairSet]
  constructor
  · rintro ⟨m, n, he, h⟩
    obtain ⟨hm, hn⟩ := ZFSet.pair_inj.mp he
    have hm := natOrdinal_injective hm
    have hn := natOrdinal_injective hn
    simpa only [hm, hn] using h
  · intro h
    exact ⟨a, b, rfl, h⟩

lemma naturalPairSet_ext {P Q : ℕ → ℕ → Prop} (h : ∀ a b, P a b ↔ Q a b) :
    naturalPairSet.{u} P = naturalPairSet Q :=
  congrArg naturalPairSet (funext fun a => funext fun b => propext (h a b))

/-- A subset of the natural-pair ambient set is determined by its natural-pair queries. -/
lemma naturalPairSet_characterization (C : ZFSet.{u}) (P : ℕ → ℕ → Prop) :
    (C ⊆ prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet ∧
      ∀ a b, pair (natOrdinal a) (natOrdinal b) ∈ C ↔ P a b) ↔ C = naturalPairSet P := by
  constructor
  · rintro ⟨hsub, hp⟩
    ext z
    rw [mem_naturalPairSet]
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod.mp (hsub hz)
      obtain ⟨a, rfl⟩ := mem_omegaOrdinal.mp hx
      obtain ⟨b, rfl⟩ := mem_omegaOrdinal.mp hy
      exact ⟨a, b, rfl, (hp a b).mp hz⟩
    · rintro ⟨a, b, rfl, h⟩
      exact (hp a b).mpr h
  · rintro rfl
    exact ⟨fun _ h => (ZFSet.mem_sep.mp h).1, pair_mem_naturalPairSet P⟩

end PolishSpaceBook.SetTheoryModels
