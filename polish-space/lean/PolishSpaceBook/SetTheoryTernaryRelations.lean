module

public import PolishSpaceBook.SetTheoryWordOperations

@[expose] public section

/-! # Collecting internally recognized ternary relations by Separation -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def ternaryRelationGraph (A B C : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  (ZFSet.prod (ZFSet.prod A B) C).sep (fun p => ∃ x y z, p = pair (pair x y) z ∧ R x y z)

lemma pair_mem_ternaryRelationGraph (A B C x y z : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) :
    pair (pair x y) z ∈ ternaryRelationGraph A B C R ↔ x ∈ A ∧ y ∈ B ∧ z ∈ C ∧ R x y z := by
  simp only [ternaryRelationGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.pair_inj]
  constructor
  · rintro ⟨⟨⟨hx, hy⟩, hz⟩, a, b, c, ⟨⟨rfl, rfl⟩, rfl⟩, hR⟩
    exact ⟨hx, hy, hz, hR⟩
  · rintro ⟨hx, hy, hz, hR⟩
    exact ⟨⟨⟨hx, hy⟩, hz⟩, x, y, z, ⟨⟨rfl, rfl⟩, rfl⟩, hR⟩

/-- A numerical graph is the corresponding ternary relation on finite ordinals. -/
lemma naturalBinaryGraph_eq_ternaryRelationGraph (f : ℕ → ℕ → ℕ)
    (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ i j k : ℕ, R (natOrdinal i) (natOrdinal j) (natOrdinal k) ↔ k = f i j) :
    naturalBinaryGraph f =
      ternaryRelationGraph Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet R := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i, j⟩, rfl⟩ := ZFSet.mem_range.mp hp
    rw [pair_mem_ternaryRelationGraph]
    exact ⟨mem_omegaOrdinal.mpr ⟨i, rfl⟩, mem_omegaOrdinal.mpr ⟨j, rfl⟩,
      mem_omegaOrdinal.mpr ⟨f i j, rfl⟩, (hR i j (f i j)).mpr rfl⟩
  · intro hp
    obtain ⟨xy, hxy, z, hz, rfl⟩ := ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hp).1
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp hxy
    obtain ⟨i, rfl⟩ := mem_omegaOrdinal.mp hx
    obtain ⟨j, rfl⟩ := mem_omegaOrdinal.mp hy
    obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp hz
    have hk := (hR i j k).mp (pair_mem_ternaryRelationGraph _ _ _ _ _ _ _ |>.mp hp).2.2.2
    rw [pair_mem_naturalBinaryGraph, hk]

/-- Three relation parameters, three domains, and the encoded triple. -/
def ternaryRelationGraphFormula (φ : ForcingFormulas.Formula 6) : ForcingFormulas.Formula 7 :=
  boundedExists 3 (boundedExists 4 (boundedExists 5
    ((orderedPairFormula (10 : Fin 11) 7 8 ⊓ orderedPairFormula 6 10 9 ⊓
      reindex φ ![0, 1, 2, 7, 8, 9]).ex)))

lemma realize_ternaryRelationGraphFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (φ : ForcingFormulas.Formula 6) (P Q S A B C p : M) :
    (ternaryRelationGraphFormula φ).Realize Empty.elim ![P, Q, S, A, B, C, p] ↔
      ∃ x : M, x.val ∈ A.val ∧ ∃ y : M, y.val ∈ B.val ∧ ∃ z : M, z.val ∈ C.val ∧
        p.val = pair (pair x.val y.val) z.val ∧ φ.Realize Empty.elim ![P, Q, S, x, y, z] := by
  have hp {n : ℕ} (q x y : Fin n) (xs : Fin n → M) :
      (orderedPairFormula q x y).Realize Empty.elim xs ↔
        (xs q).val = pair (xs x).val (xs y).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) q x y xs
  simp only [ternaryRelationGraphFormula, realize_boundedExists_model, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, hp, realize_reindex]
  have he (x y z r : M) :
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ![P, Q, S, A, B, C, p] x) y) z) r) ∘
        ![(0 : Fin 11), 1, 2, 7, 8, 9] = ![P, Q, S, x, y, z] := by
    funext i; fin_cases i <;> rfl
  simp only [he]
  change (∃ x : M, x.val ∈ A.val ∧ ∃ y : M, y.val ∈ B.val ∧ ∃ z : M, z.val ∈ C.val ∧
    ∃ r : M, (r.val = pair x.val y.val ∧ p.val = pair r.val z.val) ∧
      φ.Realize Empty.elim ![P, Q, S, x, y, z]) ↔ _
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, r, ⟨hr, hp⟩, hφ⟩
    exact ⟨x, hx, y, hy, z, hz, hr ▸ hp, hφ⟩
  · rintro ⟨x, hx, y, hy, z, hz, hp, hφ⟩
    exact ⟨x, hx, y, hy, z, hz,
      ⟨pair x.val y.val, orderedPair_mem hM hpair x.property y.property⟩, ⟨rfl, hp⟩, hφ⟩

/-- Separation constructs the relation as a set, not only its individual triples. -/
theorem ternaryRelationGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence ψ)
    (φ : ForcingFormulas.Formula 6) (P Q S A B C : M)
    (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hφ : ∀ x y z : M, φ.Realize Empty.elim ![P, Q, S, x, y, z] ↔ R x.val y.val z.val) :
    ternaryRelationGraph A.val B.val C.val R ∈ M := by
  let D := ZFSet.prod (ZFSet.prod A.val B.val) C.val
  have hD : D ∈ M := prod_mem_of_separation hM hpair hunion hpower (hsep _)
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) A.property B.property) C.property
  have habs (p : M) : (ternaryRelationGraphFormula φ).Realize Empty.elim ![P, Q, S, A, B, C, p] ↔
      p.val ∈ ternaryRelationGraph A.val B.val C.val R := by
    rw [realize_ternaryRelationGraphFormula hM hpair]
    constructor
    · rintro ⟨x, hx, y, hy, z, hz, hp, hψ⟩
      rw [hp, pair_mem_ternaryRelationGraph]
      exact ⟨hx, hy, hz, (hφ x y z).mp hψ⟩
    · intro hp
      obtain ⟨xy, hxy, z, hz, hpz⟩ := ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hp).1
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp hxy
      rw [hpz] at hp
      have hR := (pair_mem_ternaryRelationGraph _ _ _ _ _ _ _).mp hp
      exact ⟨⟨x, hM.mem_trans hx A.property⟩, hx, ⟨y, hM.mem_trans hy B.property⟩, hy,
        ⟨z, hM.mem_trans hz C.property⟩, hz, hpz, (hφ _ _ _).mpr hR.2.2.2⟩
  have hS := separation_mem_of_absolute hM (ternaryRelationGraphFormula φ) (hsep _)
    ![P, Q, S, A, B, C] hD (fun p => p ∈ ternaryRelationGraph A.val B.val C.val R) (by
      intro p _
      have he : Fin.snoc ![P, Q, S, A, B, C] p = ![P, Q, S, A, B, C, p] := by
        funext i; fin_cases i <;> rfl
      rw [he]
      exact habs p)
  have he : D.sep (fun p => p ∈ ternaryRelationGraph A.val B.val C.val R) =
      ternaryRelationGraph A.val B.val C.val R := by
    ext p
    exact ⟨fun h => (ZFSet.mem_sep.mp h).2, fun h => ZFSet.mem_sep.mpr ⟨(ZFSet.mem_sep.mp h).1, h⟩⟩
  exact he ▸ hS

end PolishSpaceBook.SetTheoryModels
