module

public import PolishSpaceBook.NonnegativeRealCutCode

@[expose] public section

/-! # Internal Separation constructs the entire code of a Borel measure value -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory BoundedSetPredicate
universe u

/-- The fixed parameters before the two rational-query integers. -/
def borelMeasureCutBaseValues (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child) :
    Fin 8 → ZFSet.{u} := fun i => borelMeasureCutValues M c hw 0 1 (i.castAdd 2)

lemma borelMeasureCutBaseValues_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (hcM : c.labelGraph ∈ M) :
    ∀ i, borelMeasureCutBaseValues M c hw i ∈ M :=
  fun i => borelMeasureCutValues_mem hM hinf hpair hunion hpower hsep c hw hcM 0 1 (i.castAdd 2)

lemma borelMeasureCut_query_values (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (p : Fin 8 → M) (hp : Subtype.val ∘ p = borelMeasureCutBaseValues M c hw)
    (a b : ℕ) (A B : M) (hA : A.val = natOrdinal a) (hB : B.val = natOrdinal b) :
    Subtype.val ∘ Fin.snoc (Fin.snoc p A) B = borelMeasureCutValues M c hw a b := by
  have hbase : borelMeasureCutBaseValues M c hw =
      fun i : Fin 8 => borelMeasureCutValues M c hw a b (i.castAdd 2) := by
    funext i
    fin_cases i <;> simp only [borelMeasureCutBaseValues, borelMeasureCutValues,
      Fin.castAdd, Fin.castLE, Matrix.cons_val_zero', Matrix.cons_val_succ']
  rw [hbase] at hp
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hB
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · exact hA
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      have hk : k.castSucc.castSucc = k.castAdd 2 := Fin.ext rfl
      rw [hk]
      exact congrFun hp k

/-- Parameters are the common eight sets and a candidate ordered pair.
Both fraction integers are internal bounded witnesses, and the denominator is positive. -/
def borelMeasureCutPairFormula : ForcingFormulas.Formula 9 :=
  boundedExists 0 (boundedExists 0
    ((BoundedSetPredicate.orderedPair (8 : Fin 11) 9 10).compile ⊓
      ((BoundedSetPredicate.member (7 : Fin 11) 10).compile ⊓
        reindex borelMeasureLowerCutFormula ![0, 1, 2, 3, 4, 5, 6, 7, 9, 10])))

lemma realize_borelMeasureCutPairFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (p : Fin 8 → M) (hp : Subtype.val ∘ p = borelMeasureCutBaseValues M c hc.2.2.2.2.2)
    (z : M) (a b : ℕ) (hz : z.val = pair (natOrdinal a) (natOrdinal b)) :
    borelMeasureCutPairFormula.Realize Empty.elim (Fin.snoc p z) ↔
      0 < b ∧ (a : ℝ) / b < fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  have hΩ : (p 0).val = Ordinal.omega0.toZFSet := congrFun hp 0
  have hE : (p 7).val = ∅ := congrFun hp 7
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) (hΩ ▸ (p 0).property)
  let num (n : ℕ) : M := ⟨natOrdinal n, hn n⟩
  have he : borelMeasureCutPairFormula.Realize Empty.elim (Fin.snoc p z) ↔
      ∃ A : M, A.val ∈ (p 0).val ∧ ∃ B : M, B.val ∈ (p 0).val ∧
        z.val = pair A.val B.val ∧ (p 7).val ∈ B.val ∧
        borelMeasureLowerCutFormula.Realize Empty.elim (Fin.snoc (Fin.snoc p A) B) := by
    simp only [borelMeasureCutPairFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
      realize_reindex, BoundedSetPredicate.realize_compile hM, eval]
    have e (A B : M) : Fin.snoc (Fin.snoc (Fin.snoc p z) A) B ∘
        ![(0 : Fin 11), 1, 2, 3, 4, 5, 6, 7, 9, 10] = Fin.snoc (Fin.snoc p A) B := by
      funext i; fin_cases i <;> rfl
    simp only [e]
    rfl
  rw [he]
  constructor
  · rintro ⟨A, _, B, _, hpairEq, hpos, hcut⟩
    have hAB := ZFSet.pair_inj.mp (hz.symm.trans hpairEq)
    have hA : A.val = natOrdinal a := hAB.1.symm
    have hB : B.val = natOrdinal b := hAB.2.symm
    rw [hE, hB, ← natOrdinal_zero] at hpos
    have hb := (natOrdinal_mem_natOrdinal 0 b).mp hpos
    exact ⟨hb, (realize_borelMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice
      c hc hcM a b hb (Fin.snoc (Fin.snoc p A) B)
      (borelMeasureCut_query_values M c hc.2.2.2.2.2 p hp a b A B hA hB)).mp hcut⟩
  · rintro ⟨hb, hcut⟩
    refine ⟨num a, hΩ ▸ mem_omegaOrdinal.mpr ⟨a, rfl⟩,
      num b, hΩ ▸ mem_omegaOrdinal.mpr ⟨b, rfl⟩, hz, ?_, ?_⟩
    · rw [hE, ← natOrdinal_zero]
      exact (natOrdinal_mem_natOrdinal 0 b).mpr hb
    · exact (realize_borelMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice
        c hc hcM a b hb (Fin.snoc (Fin.snoc p (num a)) (num b))
        (borelMeasureCut_query_values M c hc.2.2.2.2.2 p hp a b (num a) (num b) rfl rfl)).mpr hcut

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal real code for Borel measure
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The product $\omega\times\omega$ belongs to $M$. Apply internal Separation on this product with the formula
    $$\begin{aligned}
    P(B,z):\equiv{}&\exists a,b\in\omega\;[\\
    &z=\langle a,b\rangle\land0\in b\land L(B,a,b)].
    \end{aligned}$$
    All parameters of $L$ belong to $M$. The common bounded-interpretation theorem handles the ordered pair
    and the positive-denominator test. The preceding lower-cut theorem handles $L$.
    Thus, for every $a,b\in\omega$,
    $$M\models P(B,\langle a,b\rangle)
    \quad\Longleftrightarrow\quad 0<b\land a/b<\mu(A).$$
    Since every element of the product is such a pair, the separated set is exactly
    $\NonnegativeRealCut{\mu(A)}$. Hence it belongs to $M$.
-/
theorem borel_measure_cutCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M) :
    nonnegativeRealCutCode (fairCoinProduct.real (cantorSet c hc.2.2.2.2.2)) ∈ M := by
  let p (i : Fin 8) : M := ⟨borelMeasureCutBaseValues M c hc.2.2.2.2.2 i,
    borelMeasureCutBaseValues_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM i⟩
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hprod := prod_mem_of_separation hM hpair hunion hpower (hsep _) hΩ hΩ
  unfold nonnegativeRealCutCode
  apply separation_mem_of_absolute hM borelMeasureCutPairFormula (hsep _) p hprod
  intro z hz
  obtain ⟨x, hx, y, hy, he⟩ := ZFSet.mem_prod.mp hz
  obtain ⟨a, rfl⟩ := mem_omegaOrdinal.mp hx
  obtain ⟨b, rfl⟩ := mem_omegaOrdinal.mp hy
  rw [realize_borelMeasureCutPairFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM p rfl z a b he]
  rw [he]
  exact ((mem_nonnegativeRealCutCode _ _).symm.trans (pair_mem_nonnegativeRealCutCode _ a b)).symm

end PolishSpaceBook.CantorTreeMeasure
