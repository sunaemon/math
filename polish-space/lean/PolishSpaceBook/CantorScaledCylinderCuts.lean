module

public import PolishSpaceBook.CantorCylinderMeasureCuts
public import PolishSpaceBook.ScaledNonnegativeCuts

@[expose] public section

/-! # Scaled comparisons of cylinder-intersection measures inside a model -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory BoundedSetPredicate
universe u

def scaledCylinderQueryValues (M : ZFSet.{u}) (c d : Code) (m n j : ℕ) : Fin 21 → ZFSet.{u} :=
  Fin.snoc (Fin.snoc (Fin.snoc
    (Fin.append (cylinderMeasureBaseValues M c) (cylinderMeasureBaseValues M d))
    (natOrdinal m)) (natOrdinal n)) (natOrdinal j)

/-- The four final witnesses are the margin numerator, denominator, and their scaled products. -/
def scaledCylinderCutBody : ForcingFormulas.Formula 25 :=
  (BoundedSetPredicate.member (7 : Fin 25) 22).compile ⊓
    ((binaryMemberAt 1 18 21 23).compile ⊓
      ((binaryMemberAt 1 19 22 24).compile ⊓
        ((reindex cylinderMeasureLowerCutFormula ![0,1,2,3,4,5,6,7,8,20,21,22]).not ⊓
          reindex cylinderMeasureLowerCutFormula ![9,10,11,12,13,14,15,16,17,20,23,24])))

def scaledCylinderLtFormula : ForcingFormulas.Formula 21 :=
  boundedExists 0 (boundedExists 0 (boundedExists 0 (boundedExists 0 scaledCylinderCutBody)))

theorem realize_scaledCylinderLtFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M)
    (m n j : ℕ) (hn : 0 < n) (ps : Fin 21 → M)
    (hps : Subtype.val ∘ ps = scaledCylinderQueryValues M c d m n j) :
    scaledCylinderLtFormula.Realize Empty.elim ps ↔
      (m : ℝ) * fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor <
        (n : ℝ) * fairCoinProduct.real (Code.inf d (Code.leaf j)).cantor := by
  have hv (i : Fin 21) : (ps i).val = scaledCylinderQueryValues M c d m n j i := congrFun hps i
  have hΩ : (ps 0).val = Ordinal.omega0.toZFSet := hv 0
  have hzero : (ps 7).val = ∅ := hv 7
  have hmul : (ps 1).val = naturalBinaryGraph (fun a b => a * b) := hv 1
  have hm : (ps 18).val = natOrdinal m := hv 18
  have hnn : (ps 19).val = natOrdinal n := hv 19
  have hj : (ps 20).val = natOrdinal j := hv 20
  have hnat (a : ℕ) : natOrdinal a ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨a,rfl⟩) (hΩ ▸ (ps 0).property)
  let num (a : ℕ) : M := ⟨natOrdinal a, hnat a⟩
  let row (A B U V : M) : Fin 25 → M := Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps A) B) U) V
  have hx (A B U V : M) (a b : ℕ) (hA : A.val = natOrdinal a) (hB : B.val = natOrdinal b) (hb : 0 < b) :
      (reindex cylinderMeasureLowerCutFormula ![0,1,2,3,4,5,6,7,8,20,21,22]).Realize Empty.elim (row A B U V) ↔
        (a : ℝ) / b < fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor := by
    rw [realize_reindex]
    apply realize_cylinderMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc j a b hb
    funext i
    fin_cases i <;> first
      | exact hv 0 | exact hv 1 | exact hv 2 | exact hv 3 | exact hv 4
      | exact hv 5 | exact hv 6 | exact hv 7 | exact hv 8 | exact hv 20 | exact hA | exact hB
  have hy (A B U V : M) (a b : ℕ) (hU : U.val = natOrdinal a) (hV : V.val = natOrdinal b) (hb : 0 < b) :
      (reindex cylinderMeasureLowerCutFormula ![9,10,11,12,13,14,15,16,17,20,23,24]).Realize Empty.elim (row A B U V) ↔
        (a : ℝ) / b < fairCoinProduct.real (Code.inf d (Code.leaf j)).cantor := by
    rw [realize_reindex]
    apply realize_cylinderMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice d hd j a b hb
    funext i
    fin_cases i <;> first
      | exact hv 9 | exact hv 10 | exact hv 11 | exact hv 12 | exact hv 13
      | exact hv 14 | exact hv 15 | exact hv 16 | exact hv 17 | exact hv 20 | exact hU | exact hV
  have hbody (A B U V : M) :
      scaledCylinderCutBody.Realize Empty.elim (row A B U V) ↔
        ∅ ∈ B.val ∧
          pair (pair (natOrdinal m) A.val) U.val ∈ naturalBinaryGraph (fun a b => a * b) ∧
          pair (pair (natOrdinal n) B.val) V.val ∈ naturalBinaryGraph (fun a b => a * b) ∧
          ¬ (reindex cylinderMeasureLowerCutFormula ![0,1,2,3,4,5,6,7,8,20,21,22]).Realize Empty.elim (row A B U V) ∧
            (reindex cylinderMeasureLowerCutFormula ![9,10,11,12,13,14,15,16,17,20,23,24]).Realize Empty.elim (row A B U V) := by
    simp only [scaledCylinderCutBody, BoundedFormula.realize_inf, BoundedFormula.realize_not,
      BoundedSetPredicate.realize_compile hM, eval, eval_binaryMemberAt]
    change ((ps 7).val ∈ B.val ∧
      pair (pair (ps 18).val A.val) U.val ∈ (ps 1).val ∧
        pair (pair (ps 19).val B.val) V.val ∈ (ps 1).val ∧ _ ∧ _) ↔ _
    rw [hzero, hm, hnn, hmul]
  have he : scaledCylinderLtFormula.Realize Empty.elim ps ↔
      ∃ A : M, A.val ∈ Ordinal.omega0.toZFSet ∧ ∃ B : M, B.val ∈ Ordinal.omega0.toZFSet ∧
        ∃ U : M, U.val ∈ Ordinal.omega0.toZFSet ∧ ∃ V : M, V.val ∈ Ordinal.omega0.toZFSet ∧
          scaledCylinderCutBody.Realize Empty.elim (row A B U V) := by
    simp [scaledCylinderLtFormula, realize_boundedExists_model, Fin.snoc, hΩ, row]
  rw [he, scaled_lt_iff_fraction _ _ measureReal_nonneg m n hn]
  constructor
  · rintro ⟨A, hAΩ, B, hBΩ, U, hUΩ, V, hVΩ, h⟩
    obtain ⟨a, hA⟩ := mem_omegaOrdinal.mp hAΩ
    obtain ⟨b, hB⟩ := mem_omegaOrdinal.mp hBΩ
    obtain ⟨u, hU⟩ := mem_omegaOrdinal.mp hUΩ
    obtain ⟨v, hV⟩ := mem_omegaOrdinal.mp hVΩ
    have hA : A.val = natOrdinal a := hA.symm
    have hB : B.val = natOrdinal b := hB.symm
    have hU : U.val = natOrdinal u := hU.symm
    have hV : V.val = natOrdinal v := hV.symm
    obtain ⟨hpos, hma, hnb, hleft, hright⟩ := (hbody A B U V).mp h
    rw [hB, ← natOrdinal_zero, natOrdinal_mem_natOrdinal] at hpos
    have hu : U.val = natOrdinal (m * a) := by simpa only [hA, pair_mem_naturalBinaryGraph] using hma
    have hv' : V.val = natOrdinal (n * b) := by simpa only [hB, pair_mem_naturalBinaryGraph] using hnb
    exact ⟨a, b, hpos, mt (hx A B U V a b hA hB hpos).mpr hleft,
      (hy A B U V (m*a) (n*b) hu hv' (Nat.mul_pos hn hpos)).mp hright⟩
  · rintro ⟨a, b, hb, hleft, hright⟩
    refine ⟨num a, mem_omegaOrdinal.mpr ⟨a,rfl⟩, num b, mem_omegaOrdinal.mpr ⟨b,rfl⟩,
      num (m*a), mem_omegaOrdinal.mpr ⟨m*a,rfl⟩, num (n*b), mem_omegaOrdinal.mpr ⟨n*b,rfl⟩, ?_⟩
    apply (hbody _ _ _ _).mpr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [num, natOrdinal_zero] using (natOrdinal_mem_natOrdinal 0 b).mpr hb
    · exact (pair_mem_naturalBinaryGraph (fun x y => x*y) m a _).mpr rfl
    · exact (pair_mem_naturalBinaryGraph (fun x y => x*y) n b _).mpr rfl
    · exact mt (hx _ _ _ _ a b rfl rfl hb).mp hleft
    · exact (hy _ _ _ _ (m*a) (n*b) rfl rfl (Nat.mul_pos hn hb)).mpr hright

end PolishSpaceBook.CantorTreeMeasure
