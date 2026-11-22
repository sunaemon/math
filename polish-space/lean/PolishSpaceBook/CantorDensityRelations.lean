module

public import PolishSpaceBook.CantorDensityComparisonFormula

@[expose] public section

/-! # Separation constructs the entire internal density-comparison relations -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory BoundedSetPredicate
open NamedLambda
universe u

def densityRelationValues (M : ZFSet.{u}) (c : Code) : Fin 19 → ZFSet.{u} :=
  Fin.snoc (Fin.append (cylinderMeasureBaseValues M c) (cylinderMeasureBaseValues M (Code.leaf 0)))
    (ZFSet.prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet)

/-- Parameters are the common measure data, the natural-pair bound, and the proposed triple. -/
def densityRelationFormula (t : Bool) : ForcingFormulas.Formula 20 :=
  boundedExists 0 (boundedExists 0 (boundedExists 0 (boundedExists 18
    ((BoundedSetPredicate.orderedPair (19 : Fin 24) 20 23).compile ⊓
      ((BoundedSetPredicate.orderedPair (23 : Fin 24) 21 22).compile ⊓
        reindex (densityComparisonFormula t) ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22])))))

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {i : ℕ} (φ : ForcingFormulas.Formula (i + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {i : ℕ} (φ : ForcingFormulas.Formula (i + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence) (c : Code) (hc : c.val.labelGraph ∈ M)

include hM hinf hpair hunion hpower hsep hrep hchoice hc

set_option maxHeartbeats 1000000 in
theorem realize_densityRelationFormula (t : Bool) (ps : Fin 19 → M)
    (hps : Subtype.val ∘ ps = densityRelationValues M c) (z : M) (k N j : ℕ)
    (hz : z.val = pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j))) :
    (densityRelationFormula t).Realize Empty.elim (Fin.snoc ps z) ↔
      N ≤ (NatListCode.decode j).length ∧
        1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) (if t then 1 else 0) := by
  have hv (i : Fin 19) : (ps i).val = densityRelationValues M c i := congrFun hps i
  have hΩ : (ps 0).val = Ordinal.omega0.toZFSet := hv 0
  have hpairs : (ps 18).val = ZFSet.prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet := hv 18
  have hnat (a : ℕ) : natOrdinal a ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨a,rfl⟩) (hΩ ▸ (ps 0).property)
  let num (a : ℕ) : M := ⟨natOrdinal a, hnat a⟩
  let row (K B J I : M) : Fin 24 → M := Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps z) K) B) J) I
  have hquery (K B J I : M) (hK : K.val = natOrdinal k) (hB : B.val = natOrdinal N) (hJ : J.val = natOrdinal j) :
      (reindex (densityComparisonFormula t) ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22]).Realize
        Empty.elim (row K B J I) ↔
      N ≤ (NatListCode.decode j).length ∧
        1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) (if t then 1 else 0) := by
    rw [realize_reindex]
    apply realize_densityComparisonFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc t k N j
    funext i
    fin_cases i
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc] using hv 0
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc] using hv 1
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 2
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 3
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 4
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 5
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 6
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 7
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 8
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 9
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 10
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 11
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 12
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 13
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 14
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 15
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 16
    · simpa [row, densityRelationValues, scaledCylinderQueryValues, Fin.snoc, Fin.castPred, Fin.castLT] using hv 17
    · simpa [row, scaledCylinderQueryValues, Fin.snoc] using hK
    · simpa [row, scaledCylinderQueryValues, Fin.snoc] using hB
    · simpa [row, scaledCylinderQueryValues, Fin.snoc] using hJ
  have he : (densityRelationFormula t).Realize Empty.elim (Fin.snoc ps z) ↔
      ∃ K : M, K.val ∈ Ordinal.omega0.toZFSet ∧ ∃ B : M, B.val ∈ Ordinal.omega0.toZFSet ∧
        ∃ J : M, J.val ∈ Ordinal.omega0.toZFSet ∧
          ∃ I : M, I.val ∈ ZFSet.prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet ∧
            z.val = pair K.val I.val ∧ I.val = pair B.val J.val ∧
              (reindex (densityComparisonFormula t) ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,20,21,22]).Realize
                Empty.elim (row K B J I) := by
    simp [densityRelationFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
      BoundedSetPredicate.realize_compile hM, eval, row, Fin.snoc, Fin.castPred, Fin.castLT, hΩ, hpairs]
  rw [he]
  constructor
  · rintro ⟨K, _, B, _, J, _, I, _, houter, hinner, h⟩
    have hKi := ZFSet.pair_inj.mp (hz.symm.trans houter)
    have hBJ := ZFSet.pair_inj.mp (hKi.2.trans hinner)
    exact (hquery K B J I hKi.1.symm hBJ.1.symm hBJ.2.symm).mp h
  · intro h
    have hI : pair (natOrdinal N) (natOrdinal j) ∈ ZFSet.prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet :=
      ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨N,rfl⟩, mem_omegaOrdinal.mpr ⟨j,rfl⟩⟩
    let I : M := ⟨_, hM.mem_trans hI (hpairs ▸ (ps 18).property)⟩
    exact ⟨num k, mem_omegaOrdinal.mpr ⟨k,rfl⟩, num N, mem_omegaOrdinal.mpr ⟨N,rfl⟩,
      num j, mem_omegaOrdinal.mpr ⟨j,rfl⟩, I, hI, hz, rfl, (hquery _ _ _ _ rfl rfl rfl).mpr h⟩

omit hchoice in
lemma densityRelationValues_mem (i : Fin 19) : densityRelationValues M c i ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hwhole : (Code.leaf 0).val.labelGraph ∈ M := basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep 0
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact prod_mem_of_separation hM hpair hunion hpower (hsep _) hΩ hΩ
  · simp only [densityRelationValues, Fin.snoc_castSucc]
    refine Fin.addCases (m := 9) (n := 9) (fun a => ?_) (fun b => ?_) j
    · simpa only [Fin.append, Fin.addCases_left] using cylinderMeasureBaseValues_mem hM hinf hpair hunion hpower hsep c hc a
    · simpa only [Fin.append, Fin.addCases_right] using cylinderMeasureBaseValues_mem hM hinf hpair hunion hpower hsep (Code.leaf 0) hwhole b

/-- Separation, rather than a per-triple membership assumption, constructs the comparison relation. -/
theorem exists_internal_densityRelation (t : Bool) :
    ∃ D : ZFSet.{u}, D ∈ M ∧ ∀ k N j,
      pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ D ↔
        N ≤ (NatListCode.decode j).length ∧
          1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) (if t then 1 else 0) := by
  let ps : Fin 19 → M := fun i => ⟨densityRelationValues M c i,
    densityRelationValues_mem hM hinf hpair hunion hpower hsep hrep c hc i⟩
  let Q := ZFSet.prod Ordinal.omega0.toZFSet (ZFSet.prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet)
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hP := prod_mem_of_separation hM hpair hunion hpower (hsep _) hΩ hΩ
  have hQ : Q ∈ M := prod_mem_of_separation hM hpair hunion hpower (hsep _) hΩ hP
  let D := Q.sep (fun z => ∃ hz : z ∈ M, (densityRelationFormula t).Realize Empty.elim (Fin.snoc ps ⟨z,hz⟩))
  have hD : D ∈ M := by
    apply separation_mem_of_absolute hM (densityRelationFormula t) (hsep _) ps hQ
    intro z _
    exact ⟨fun h => ⟨z.property, h⟩, fun ⟨_, h⟩ => h⟩
  refine ⟨D, hD, ?_⟩
  intro k N j
  have htriple : pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ Q :=
    ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨k,rfl⟩,
      ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨N,rfl⟩, mem_omegaOrdinal.mpr ⟨j,rfl⟩⟩⟩
  have htripleM := hM.mem_trans htriple hQ
  dsimp only [D]
  rw [ZFSet.mem_sep, and_iff_right htriple]
  constructor
  · rintro ⟨hz, h⟩
    exact (realize_densityRelationFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc t ps rfl
      ⟨_,hz⟩ k N j rfl).mp h
  · intro h
    exact ⟨htripleM, (realize_densityRelationFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc t ps rfl
      ⟨_,htripleM⟩ k N j rfl).mpr h⟩

end PolishSpaceBook.CantorTreeMeasure
