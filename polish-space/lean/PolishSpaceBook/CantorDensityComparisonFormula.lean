module

public import PolishSpaceBook.CantorDensityComparisons

@[expose] public section

/-! # A uniform internal formula for density-deviation triples -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory BoundedSetPredicate
open NamedLambda
universe u

/-- The final two variables are k+1 and one. -/
def densityDeviationPayload (t : Bool) : ForcingFormulas.Formula 23 :=
  if t then
    (reindex scaledCylinderLtFormula ![9,10,11,12,13,14,15,16,17,0,1,2,3,4,5,6,7,8,18,21,20]).not
  else
    reindex cylinderMeasureLowerCutFormula ![9,10,11,12,13,14,15,16,17,20,7,22] ⊓
      (reindex scaledCylinderLtFormula ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,21,22,20]).not

def densityDeviationFormula (t : Bool) : ForcingFormulas.Formula 21 :=
  boundedExists 0 (boundedExists 0
    ((BoundedSetPredicate.successor (21 : Fin 23) 18).compile ⊓
      ((BoundedSetPredicate.successor (22 : Fin 23) 7).compile ⊓ densityDeviationPayload t)))

def densityComparisonFormula (t : Bool) : ForcingFormulas.Formula 21 :=
  reindex wordTailBoundPredicate.compile ![0,3,8,19,20] ⊓ densityDeviationFormula t

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    We construct the entire codes in $M$. Use the standard numbering of finite natural words; nonbinary words
    have empty Cantor traces. For a cylinder trace, put $\nu=\mu(A\cap\cyl{s})$ and $\delta=\mu(\cyl{s})$.
    The density-zero deviation test is
    $$\delta>0\ \land\ \neg\bigl((k+1)\nu<\delta\bigr),$$
    and the density-one test is $\neg\bigl(k\delta<(k+1)\nu\bigr)$. These formulas also handle empty traces if their
    normalized density is set to zero. For nonnegative $x,y$ and $m,n\in\omega$ with $n>0$, rational density gives
    $$mx<ny\quad\Longleftrightarrow\quad
    \exists a,b\in\omega\ \bigl[b>0\land\neg(a/b<x)\land ma/(nb)<y\bigr].$$
    Indeed, a rational margin at or above $x$ proves the reverse direction; in the forward direction choose it
    strictly between $x$ and $ny/m$ when $m>0$, and use any rational above $x$ when $m=0$.
    The lower-cut formula of §{sec:internal-borel-measure-cut} therefore expresses both tests internally. Its
    cylinder parameter is uniform: an internal point graph belongs to a cylinder exactly when it contains the
    corresponding finite-word graph, so bounded Separation constructs the required intersections. Integer
    multiplication and the finite-word length test have their existing internal graph definitions.
-/
set_option maxHeartbeats 2000000 in
theorem realize_densityComparisonFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {i : ℕ} (φ : ForcingFormulas.Formula (i + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {i : ℕ} (φ : ForcingFormulas.Formula (i + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : Code) (hc : c.val.labelGraph ∈ M)
    (t : Bool) (k N j : ℕ) (ps : Fin 21 → M)
    (hps : Subtype.val ∘ ps = scaledCylinderQueryValues M c (Code.leaf 0) k N j) :
    (densityComparisonFormula t).Realize Empty.elim ps ↔
      N ≤ (NatListCode.decode j).length ∧
        1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) (if t then 1 else 0) := by
  have hv (i : Fin 21) : (ps i).val = scaledCylinderQueryValues M c (Code.leaf 0) k N j i := congrFun hps i
  have hΩ : (ps 0).val = Ordinal.omega0.toZFSet := hv 0
  have hK : (ps 18).val = natOrdinal k := hv 18
  have hz : (ps 7).val = ∅ := hv 7
  have hnat (a : ℕ) : natOrdinal a ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨a,rfl⟩) (hΩ ▸ (ps 0).property)
  let num (a : ℕ) : M := ⟨natOrdinal a, hnat a⟩
  have hwhole : (Code.leaf 0).val.labelGraph ∈ M := basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep 0
  let row (K O : M) : Fin 23 → M := Fin.snoc (Fin.snoc ps K) O
  have hlength : (reindex wordTailBoundPredicate.compile ![0,3,8,19,20]).Realize Empty.elim ps ↔
      N ≤ (NatListCode.decode j).length := by
    rw [realize_reindex, wordTailBoundPredicate.realize_compile hM]
    have he : Subtype.val ∘ (ps ∘ ![(0 : Fin 21),3,8,19,20]) =
        ![Ordinal.omega0.toZFSet, finiteSequences, listDecodeGraph, natOrdinal N, natOrdinal j] := by
      funext i
      fin_cases i <;> first | exact hv 0 | exact hv 3 | exact hv 8 | exact hv 19 | exact hv 20
    rw [he, eval_wordTailBoundPredicate]
  have hsuccK (K O : M) :
      (BoundedSetPredicate.successor (21 : Fin 23) 18).compile.Realize Empty.elim (row K O) ↔
        K.val = natOrdinal (k+1) := by
    rw [BoundedSetPredicate.realize_compile hM]
    change K.val = insert (ps 18).val (ps 18).val ↔ _
    rw [hK, natOrdinal_succ]
  have hsuccO (K O : M) :
      (BoundedSetPredicate.successor (22 : Fin 23) 7).compile.Realize Empty.elim (row K O) ↔
        O.val = natOrdinal 1 := by
    rw [BoundedSetPredicate.realize_compile hM]
    change O.val = insert (ps 7).val (ps 7).val ↔ _
    rw [hz, ← natOrdinal_zero, ← natOrdinal_succ]
  have hpayload (K O : M) (hK' : K.val = natOrdinal (k+1)) (hO : O.val = natOrdinal 1) :
      (densityDeviationPayload t).Realize Empty.elim (row K O) ↔
        1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) (if t then 1 else 0) := by
    have hone :
        (reindex scaledCylinderLtFormula ![9,10,11,12,13,14,15,16,17,0,1,2,3,4,5,6,7,8,18,21,20]).Realize
          Empty.elim (row K O) ↔
        (k : ℝ) * fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor <
          (k+1 : ℝ) * fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor := by
      rw [realize_reindex]
      have h := realize_scaledCylinderLtFormula hM hinf hpair hunion hpower hsep hrep hchoice
        (Code.leaf 0) c hwhole hc k (k+1) j (by omega)
        (row K O ∘ ![9,10,11,12,13,14,15,16,17,0,1,2,3,4,5,6,7,8,18,21,20])
      have he : Subtype.val ∘ (row K O ∘ ![(9 : Fin 23),10,11,12,13,14,15,16,17,0,1,2,3,4,5,6,7,8,18,21,20]) =
          scaledCylinderQueryValues M (Code.leaf 0) c k (k+1) j := by
        funext i
        fin_cases i
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 9
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 10
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 11
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 12
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 13
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 14
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 15
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 16
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 17
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 0
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 1
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 2
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 3
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 4
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 5
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 6
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 7
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 8
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 18
        · exact hK'
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 20
      simpa only [Nat.cast_add, Nat.cast_one] using h he
    have hzero :
        (reindex scaledCylinderLtFormula ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,21,22,20]).Realize
          Empty.elim (row K O) ↔
        (k+1 : ℝ) * fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor <
          fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor := by
      rw [realize_reindex]
      have h := realize_scaledCylinderLtFormula hM hinf hpair hunion hpower hsep hrep hchoice
        c (Code.leaf 0) hc hwhole (k+1) 1 j (by omega)
        (row K O ∘ ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,21,22,20])
      have he : Subtype.val ∘ (row K O ∘ ![(0 : Fin 23),1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,21,22,20]) =
          scaledCylinderQueryValues M c (Code.leaf 0) (k+1) 1 j := by
        funext i
        fin_cases i
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.append, Fin.addCases] using hv 0
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.append, Fin.addCases] using hv 1
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 2
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 3
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 4
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 5
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 6
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 7
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 8
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 9
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 10
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 11
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 12
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 13
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 14
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 15
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 16
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 17
        · exact hK'
        · exact hO
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 20
      simpa only [Nat.cast_add, Nat.cast_one, one_mul] using h he
    have hpos :
        (reindex cylinderMeasureLowerCutFormula ![9,10,11,12,13,14,15,16,17,20,7,22]).Realize Empty.elim (row K O) ↔
          0 < fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor := by
      rw [realize_reindex]
      have h := realize_cylinderMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice
        (Code.leaf 0) hwhole j 0 1 (by omega) (row K O ∘ ![9,10,11,12,13,14,15,16,17,20,7,22])
      have he : Subtype.val ∘ (row K O ∘ ![(9 : Fin 23),10,11,12,13,14,15,16,17,20,7,22]) =
          cylinderMeasureQueryValues M (Code.leaf 0) j 0 1 := by
        funext i
        fin_cases i
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 9
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 10
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 11
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 12
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 13
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 14
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 15
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 16
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 17
        · simpa [scaledCylinderQueryValues, cylinderMeasureQueryValues, row, Fin.snoc, Fin.castPred, Fin.castLT, Fin.append, Fin.addCases] using hv 20
        · exact hz.trans natOrdinal_zero.symm
        · exact hO
      simpa only [Nat.cast_zero, Nat.cast_one, zero_div] using h he
    cases t
    · simp only [densityDeviationPayload, Bool.false_eq_true, ↓reduceIte, BoundedFormula.realize_inf,
        BoundedFormula.realize_not, hpos, hzero, density_deviation_zero_iff]
    · simp only [densityDeviationPayload, ↓reduceIte, BoundedFormula.realize_not, hone, density_deviation_one_iff]
  rw [densityComparisonFormula, BoundedFormula.realize_inf, hlength]
  apply and_congr_right
  intro _
  have he : (densityDeviationFormula t).Realize Empty.elim ps ↔
      ∃ K : M, K.val ∈ Ordinal.omega0.toZFSet ∧ ∃ O : M, O.val ∈ Ordinal.omega0.toZFSet ∧
        K.val = natOrdinal (k+1) ∧ O.val = natOrdinal 1 ∧
          (densityDeviationPayload t).Realize Empty.elim (row K O) := by
    have h0 (K : M) : (Fin.snoc ps K : Fin 22 → M) 0 = ps 0 := by simp [Fin.snoc]
    simp only [densityDeviationFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
      h0, hΩ]
    change (∃ K : M, K.val ∈ Ordinal.omega0.toZFSet ∧ ∃ O : M, O.val ∈ Ordinal.omega0.toZFSet ∧
      (BoundedSetPredicate.successor (21 : Fin 23) 18).compile.Realize Empty.elim (row K O) ∧
      (BoundedSetPredicate.successor (22 : Fin 23) 7).compile.Realize Empty.elim (row K O) ∧
      (densityDeviationPayload t).Realize Empty.elim (row K O)) ↔ _
    simp only [hsuccK, hsuccO]
  rw [he]
  constructor
  · rintro ⟨K, _, O, _, hK', hO, h⟩
    exact (hpayload K O hK' hO).mp h
  · intro h
    exact ⟨num (k+1), mem_omegaOrdinal.mpr ⟨k+1,rfl⟩, num 1, mem_omegaOrdinal.mpr ⟨1,rfl⟩,
      rfl, rfl, (hpayload _ _ rfl rfl).mpr h⟩

end PolishSpaceBook.CantorTreeMeasure
