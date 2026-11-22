module

public import PolishSpaceBook.SetTheoryDefinableChoice

@[expose] public section

/-! # Recognizing a prescribed subset with a definable fiber -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- The shared fiber formula recognizes an actual subset once point membership is identified. -/
theorem realize_choiceFiber_eq {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (B a r : M)
    (I : ZFSet.{u}) (hI : I ⊆ B.val)
    (heval : ∀ b : M, b.val ∈ B.val →
      (φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) ↔ b.val ∈ I)) :
    (choiceFiberFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps B) a) r) ↔
      r.val = I := by
  rw [realize_choiceFiberFormula]
  constructor
  · intro hr
    ext b
    constructor
    · intro hb
      let bM : M := ⟨b, hM.mem_trans hb r.property⟩
      obtain ⟨hbB, hφ⟩ := (hr bM).mp hb
      exact (heval bM hbB).mp hφ
    · intro hb
      let bM : M := ⟨b, hM.mem_trans (hI hb) B.property⟩
      exact (hr bM).mpr ⟨hI hb, (heval bM (hI hb)).mpr hb⟩
  · intro hr b
    rw [hr]
    exact ⟨fun hb => ⟨hI hb, (heval b (hI hb)).mpr hb⟩,
      fun ⟨hbB, hφ⟩ => (heval b hbB).mp hφ⟩

end PolishSpaceBook.SetTheoryModels
