module

public import PolishSpaceBook.CantorInternalLowerCut

@[expose] public section

/-! # A first-order formula for the strict rational lower cut of Borel measure -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory BoundedSetPredicate
universe u

/-- Fixed arithmetic, word, point, Borel, empty-set, and query-fraction parameters. -/
def borelMeasureCutValues (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (a b : ℕ) : Fin 10 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
    sequenceGraph (fun n => natOrdinal (2 ^ n)), finiteSequences, internalBaire M,
    internalInterpretation M c hw NamedLambda.NatListCode.decode [], wordTreeSet (binaryLift Set.univ),
    ∅, natOrdinal a, natOrdinal b]

lemma borelMeasureCutValues_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (hcM : c.labelGraph ∈ M) (a b : ℕ) :
    ∀ i, borelMeasureCutValues M c hw a b i ∈ M := by
  have h := nodeApproximationValues_mem hM hinf hpair hunion hpower hsep c hw hcM [] ∅ ∅
    (empty_mem_of_infinity hM hinf) (empty_mem_of_infinity hM hinf) a b
  intro i
  fin_cases i <;> first
    | exact h 0
    | exact h 1
    | exact h 2
    | exact h 4
    | exact h 5
    | exact h 6
    | exact h 7
    | exact h 8
    | exact h 10
    | exact h 11

/-- The last three parameters are the inner tree and the numerator and denominator of a rational margin. -/
def borelMeasureCutWitnessFormula : ForcingFormulas.Formula 13 :=
  reindex innerTreePredicate.compile ![6, 3, 4, 5, 7, 10] ⊓
    ((BoundedSetPredicate.member (7 : Fin 13) 12).compile ⊓
      (reindex rationalLessPredicate.compile ![0, 1, 8, 9, 11, 12] ⊓
        reindex closedMeasureBoundFormula ![0, 1, 2, 10, 11, 12]))

/-- Existential witnesses are sought inside the model; both margin integers are bounded by omega. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For natural numbers $a,b,m,d$, compare fractions by the bounded test
    $$\begin{aligned}
    Q(a,b,m,d):\equiv{}&\exists u,v\in\omega\;[\\
    &\Pair{\Pair{a}{d}}{u}\in G_\times\\
    &{}\land\Pair{\Pair{m}{b}}{v}\in G_\times\land u\in v].
    \end{aligned}$$
    Its meaning is $ad<mb$, hence $a/b<m/d$ when both denominators are positive.
    The common bounded-interpretation theorem supplies this meaning inside $M$ as well.
    Let $H(W,m,d)$ be the closed measure lower-bound formula from §{sec:internal-finite-measure-bounds}, and put
    $$\begin{aligned}
    L(B,a,b):\equiv{}&\exists W\;\exists m,d\in\omega\;[\\
    &J(B,W)\land0\in d\land Q(a,b,m,d)\\
    &{}\land H(W,m,d)].
    \end{aligned}$$
    Here $0\in d$ means that the finite ordinal $d$ is positive. The quantifier on $W$ ranges over $M$
    when the formula is interpreted there. The only new finite test is the cross-product comparison;
    tree recognition, inclusion, and closed measure bounds are reused unchanged.
-/
def borelMeasureLowerCutFormula : ForcingFormulas.Formula 10 :=
  (boundedExists 0 (boundedExists 0 borelMeasureCutWitnessFormula)).ex

lemma realize_borelMeasureCutWitnessFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (a b r d : ℕ) (hb : 0 < b) (p : Fin 10 → M)
    (hp : Subtype.val ∘ p = borelMeasureCutValues M c hc.2.2.2.2.2 a b)
    (W R D : M) (hR : R.val = natOrdinal r) (hD : D.val = natOrdinal d) :
    borelMeasureCutWitnessFormula.Realize Empty.elim
      ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, W, R, D] ↔
      ∃ T : Set (List Bool), IsSubtree T ∧ W.val = wordTreeSet (binaryLift T) ∧
        treeBody T ⊆ cantorSet c hc.2.2.2.2.2 ∧ 0 < d ∧
        (a : ℝ) / b < (r : ℝ) / d ∧ (r : ℝ) / d ≤ fairCoinProduct.real (treeBody T) := by
  have hv (i : Fin 10) : (p i).val = borelMeasureCutValues M c hc.2.2.2.2.2 a b i := congrFun hp i
  let row : Fin 13 → M := ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, W, R, D]
  have e₂ : Subtype.val ∘ (row ∘ ![(0 : Fin 13), 1, 8, 9, 11, 12]) =
      ![(p 0).val, (p 1).val, (p 8).val, (p 9).val, R.val, D.val] := by
    funext i; fin_cases i <;> rfl
  have e₃ : row ∘ ![(0 : Fin 13), 1, 2, 10, 11, 12] = ![p 0, p 1, p 2, W, R, D] := by
    funext i; fin_cases i <;> rfl
  change borelMeasureCutWitnessFormula.Realize Empty.elim row ↔ _
  simp only [borelMeasureCutWitnessFormula, BoundedFormula.realize_inf, realize_reindex,
    innerTreePredicate.realize_compile hM, rationalLessPredicate.realize_compile hM,
    BoundedSetPredicate.realize_compile hM, e₂, e₃]
  change (innerTreePredicate.eval ![(p 6).val, (p 3).val, (p 4).val, (p 5).val, (p 7).val, W.val] ∧
    (p 7).val ∈ D.val ∧
    rationalLessPredicate.eval ![(p 0).val, (p 1).val, (p 8).val, (p 9).val, R.val, D.val] ∧
    closedMeasureBoundFormula.Realize Empty.elim ![p 0, p 1, p 2, W, R, D]) ↔ _
  have eT : ![(p 6).val, (p 3).val, (p 4).val, (p 5).val, (p 7).val, W.val] =
      ![wordTreeSet (binaryLift Set.univ), finiteSequences, internalBaire M,
        internalInterpretation M c hc.2.2.2.2.2 NamedLambda.NatListCode.decode [], ∅, W.val] := by
    funext i; fin_cases i
    · exact hv 6
    · exact hv 3
    · exact hv 4
    · exact hv 5
    · exact hv 7
    · rfl
  have eR : ![(p 0).val, (p 1).val, (p 8).val, (p 9).val, R.val, D.val] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
        natOrdinal a, natOrdinal b, natOrdinal r, natOrdinal d] := by
    funext i; fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 8
    · exact hv 9
    · exact hR
    · exact hD
  have hE : (p 7).val = ∅ := hv 7
  rw [eT, eR, hE, hD]
  rw [eval_innerTreePredicate hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM W,
    eval_rationalLessPredicate, ← natOrdinal_zero, natOrdinal_mem_natOrdinal]
  constructor
  · rintro ⟨⟨T, hT, hW, hTA⟩, hd, hless, hbound⟩
    exact ⟨T, hT, hW, hTA, hd, (rationalLess_iff a b r d hb hd).mp hless,
      (realize_closedMeasureBoundFormula hM hinf hpair hunion hsep T hT r d hd
        (p 0) (p 1) (p 2) W R D (hv 0) (hv 1) (hv 2) hW hR hD).mp hbound⟩
  · rintro ⟨T, hT, hW, hTA, hd, hless, hbound⟩
    exact ⟨⟨T, hT, hW, hTA⟩, hd, (rationalLess_iff a b r d hb hd).mpr hless,
      (realize_closedMeasureBoundFormula hM hinf hpair hunion hsep T hT r d hd
        (p 0) (p 1) (p 2) W R D (hv 0) (hv 1) (hv 2) hW hR hD).mpr hbound⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal rational lower cut of Borel measure
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Suppose the internal formula holds, with witnesses $W,m,d$. The predicate $J$ gives an actual
    downward-closed binary tree $T$ with $W=W_T\in M$ and $\TreeBody{T}\IncludedIn A$.
    The arithmetic test and the closed lower-bound theorem give
    $$\frac ab<\frac md\le\mu(\TreeBody{T})\le\mu(A).$$
    This proves one implication.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Conversely, put $q=a/b$ and suppose $q<\mu(A)$. The internal approximation theorem gives
    $W_T,W_O\in M$ with
    $$\TreeBody{T}\IncludedIn A\IncludedIn U(O),\qquad
    \mu(\SetDifference{U(O)}{\TreeBody{T}})<\mu(A)-q.$$
    Monotonicity and subtraction of the closed inner set yield
    $$\mu(A)-\mu(\TreeBody{T})
    \le\mu(\SetDifference{U(O)}{\TreeBody{T}})<\mu(A)-q,$$
    so $q<\mu(\TreeBody{T})$. Choose a rational $m/d$ strictly between them, with $m,d\in\omega$ and $d>0$;
    this is possible because $q\ge0$. All these finite ordinals belong to $M$.
    The interpretation theorems give $J(B,W_T)$ and $Q(a,b,m,d)$ inside $M$, while the closed measure
    lower-bound theorem gives $H(W_T,m,d)$. These internal witnesses establish $L(B,a,b)$.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus two transitive models containing the same valid code give the same answers to these rational queries.
-/
theorem realize_borelMeasureLowerCutFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (a b : ℕ) (hb : 0 < b) (p : Fin 10 → M)
    (hp : Subtype.val ∘ p = borelMeasureCutValues M c hc.2.2.2.2.2 a b) :
    borelMeasureLowerCutFormula.Realize Empty.elim p ↔
      (a : ℝ) / b < fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  have hv (i : Fin 10) : (p i).val = borelMeasureCutValues M c hc.2.2.2.2.2 a b i := congrFun hp i
  have hΩ : (p 0).val = Ordinal.omega0.toZFSet := hv 0
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans
    (mem_omegaOrdinal.mpr ⟨n, rfl⟩) (hΩ ▸ (p 0).property)
  let num (n : ℕ) : M := ⟨natOrdinal n, hn n⟩
  have he : borelMeasureLowerCutFormula.Realize Empty.elim p ↔
      ∃ W R : M, R.val ∈ (p 0).val ∧ ∃ D : M, D.val ∈ (p 0).val ∧
        borelMeasureCutWitnessFormula.Realize Empty.elim
          ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, W, R, D] := by
    simp only [borelMeasureLowerCutFormula, BoundedFormula.realize_ex, realize_boundedExists_model]
    have he (W R D : M) : Fin.snoc (Fin.snoc (Fin.snoc p W) R) D =
        ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, W, R, D] := by
      funext i; fin_cases i <;> rfl
    simp only [he]
    rfl
  have hcut := internallyApproximable_lower_cut
    (internallyApproximable_cantorSet hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM)
    ((a : ℝ) / b) (by positivity)
  rw [he, hcut]
  constructor
  · rintro ⟨W, R, hr, D, hd, hφ⟩
    obtain ⟨r, hr⟩ := mem_omegaOrdinal.mp (hΩ ▸ hr)
    obtain ⟨d, hd⟩ := mem_omegaOrdinal.mp (hΩ ▸ hd)
    obtain ⟨T, hT, hW, hTA, hd0, hless, hbound⟩ :=
      (realize_borelMeasureCutWitnessFormula hM hinf hpair hunion hpower hsep hrep hchoice
        c hc hcM a b r d hb p hp W R D hr.symm hd.symm).mp hφ
    exact ⟨T, hT, hW ▸ W.property, hTA, r, d, hd0, hless, hbound⟩
  · rintro ⟨T, hT, hTM, hTA, r, d, hd, hless, hbound⟩
    let W : M := ⟨wordTreeSet (binaryLift T), hTM⟩
    refine ⟨W, num r, ?_, num d, ?_, ?_⟩
    · exact hΩ ▸ mem_omegaOrdinal.mpr ⟨r, rfl⟩
    · exact hΩ ▸ mem_omegaOrdinal.mpr ⟨d, rfl⟩
    · exact (realize_borelMeasureCutWitnessFormula hM hinf hpair hunion hpower hsep hrep hchoice
        c hc hcM a b r d hb p hp W (num r) (num d) rfl rfl).mpr
        ⟨T, hT, rfl, hTA, hd, hless, hbound⟩

end PolishSpaceBook.CantorTreeMeasure
