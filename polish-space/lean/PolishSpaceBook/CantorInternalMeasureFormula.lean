module

public import PolishSpaceBook.CantorInternalDyadicBounds
public import PolishSpaceBook.CantorInternalCodeOperations
public import PolishSpaceBook.SetTheoryRankClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # First-order tests for closed measure bounds

Finite levels and finite bijections are quantified inside the model. The
interpretation theorem supplies both directions, rather than assuming a
sequence of correct internal cardinality witnesses.
-/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate BorelExpression
universe u

/-- Parameters omega, node set, level, and proposed level set. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    We can now quantify the finite counts inside a single formula. With $\omega,G_\times,P_2$ retained as
    parameters, put
    $$\begin{aligned}
    L(W,n,A):\equiv{}&A\IncludedIn W\land\forall \sigma\in W\;(\sigma\in A\leftrightarrow \sigma:n\to\omega),\\
    H(W,a,b):\equiv{}&\forall n\in\omega\;\exists k\in\omega\;\exists A\;[\\
    &L(W,n,A)\land\mathrm{Count}(k,A)\land\mathrm{DB}(n,k,a,b)].
    \end{aligned}$$
    For $W=W_T$, the bounded predicate $L$ recognizes exactly $A=W_{T,n}$. The unrestricted quantifiers
    in $H$ range over the model when $H$ is interpreted there.
-/
def finiteLevelPredicate : BoundedSetPredicate 4 :=
  setComprehension 1 3 (.function 2 0 4)

lemma eval_finiteLevelPredicate (T : Set (List ℕ)) (n : ℕ) (A : ZFSet.{u}) :
    finiteLevelPredicate.eval ![Ordinal.omega0.toZFSet, wordTreeSet T, natOrdinal n, A] ↔
      A = finiteWordLevel T n := by
  apply eval_setComprehension_iff_eq
  · intro x hx
    exact (ZFSet.mem_sep.mp hx).1
  · intro x hx
    change x ∈ wordTreeSet T at hx
    change IsFunc (natOrdinal n) Ordinal.omega0.toZFSet x ↔ x ∈ finiteWordLevel T n
    simp only [finiteWordLevel, ZFSet.mem_sep, hx, true_and]

/-- Parameters omega, node set, level, and cardinality. The level set is an internal witness. -/
def levelCardinalityFormula : ForcingFormulas.Formula 4 :=
  (reindex finiteLevelPredicate.compile ![0, 1, 2, 4] ⊓
    reindex finiteCardinalityFormula ![3, 4]).ex

lemma realize_levelCardinalityFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List Bool)) (n k : ℕ) (Ω W N K : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hW : W.val = wordTreeSet (binaryLift T))
    (hN : N.val = natOrdinal n) (hK : K.val = natOrdinal k) :
    levelCardinalityFormula.Realize Empty.elim ![Ω, W, N, K] ↔ k = (level T n).card := by
  have hlevel (A : M) : finiteLevelPredicate.compile.Realize Empty.elim ![Ω, W, N, A] ↔
      A.val = finiteWordLevel (binaryLift T) n := by
    rw [finiteLevelPredicate.realize_compile hM]
    have he : Subtype.val ∘ ![Ω, W, N, A] =
        ![Ordinal.omega0.toZFSet, wordTreeSet (binaryLift T), natOrdinal n, A.val] := by
      funext i; fin_cases i <;> simp [hΩ, hW, hN]
    rw [he, eval_finiteLevelPredicate]
  have he : levelCardinalityFormula.Realize Empty.elim ![Ω, W, N, K] ↔
      ∃ A : M, finiteLevelPredicate.compile.Realize Empty.elim ![Ω, W, N, A] ∧
        finiteCardinalityFormula.Realize Empty.elim ![K, A] := by
    simp only [levelCardinalityFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      realize_reindex]
    have e₁ (Z : M) : Fin.snoc ![Ω, W, N, K] Z ∘ ![(0 : Fin 5), 1, 2, 4] = ![Ω, W, N, Z] := by
      funext i; fin_cases i <;> rfl
    have e₂ (Z : M) : Fin.snoc ![Ω, W, N, K] Z ∘ ![(3 : Fin 5), 4] = ![K, Z] := by
      funext i; fin_cases i <;> rfl
    simp only [e₁, e₂]
  rw [he]
  constructor
  · rintro ⟨A, hA, hc⟩
    exact (binaryLevel_cardinality_absolute hM hinf hpair hunion T n k K A hK
      ((hlevel A).mp hA)).mp hc
  · intro hk
    let A : M := ⟨finiteWordLevel (binaryLift T) n,
      finiteWordLevel_mem hM hinf hsep _ (hW ▸ W.property) n⟩
    exact ⟨A, (hlevel A).mpr rfl,
      (binaryLevel_cardinality_absolute hM hinf hpair hunion T n k K A hK rfl).mpr hk⟩

/-- Parameters omega, multiplication, powers of two, node set, numerator, denominator. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    We can now quantify the finite counts inside a single formula. With $\omega,G_\times,P_2$ retained as
    parameters, put
    $$\begin{aligned}
    L(W,n,A):\equiv{}&A\IncludedIn W\land\forall \sigma\in W\;(\sigma\in A\leftrightarrow \sigma:n\to\omega),\\
    H(W,a,b):\equiv{}&\forall n\in\omega\;\exists k\in\omega\;\exists A\;[\\
    &L(W,n,A)\land\mathrm{Count}(k,A)\land\mathrm{DB}(n,k,a,b)].
    \end{aligned}$$
    For $W=W_T$, the bounded predicate $L$ recognizes exactly $A=W_{T,n}$. The unrestricted quantifiers
    in $H$ range over the model when $H$ is interpreted there.
-/
def closedMeasureBoundFormula : ForcingFormulas.Formula 6 :=
  boundedAll 0 (boundedExists 0
    (reindex levelCardinalityFormula ![0, 3, 6, 7] ⊓
      reindex dyadicBoundPredicate.compile ![0, 1, 2, 7, 4, 5, 6]))

/-- A single internal formula tests a rational lower bound on the full external tree body. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: corollary
  title: Closed measure bounds from internal finite tests
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    If $M\models H(W_T,a,b)$, the internal level set is $W_{T,n}$ and its recognized count is $|T_n|$.
    The preceding proposition therefore gives $a/b\le d_n(T)$ for every actual $n$.
    Conversely, if these inequalities hold, use the internal set $W_{T,n}$, the finite ordinal $|T_n|$,
    and a finite bijection witnessing its cardinality. The earlier lemmas place these witnesses in $M$ and
    verify the corresponding dyadic comparison there. Thus $M\models H(W_T,a,b)$.
    The closed lower-bound criterion of §{sec:coded-measure-bounds} identifies the inequalities with
    $a/b\le\mu(\TreeBody{T})$. No graph collecting all finite counts is assumed: the formula has the
    quantifier order $\forall n\,\exists k\,\exists A$.
-/
theorem realize_closedMeasureBoundFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List Bool)) (hT : IsSubtree T) (a b : ℕ) (hb : 0 < b)
    (Ω Mul Pow W A B : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hMul : Mul.val = naturalBinaryGraph (fun x y => x * y))
    (hPow : Pow.val = sequenceGraph (fun n => natOrdinal (2 ^ n)))
    (hW : W.val = wordTreeSet (binaryLift T)) (hA : A.val = natOrdinal a) (hB : B.val = natOrdinal b) :
    closedMeasureBoundFormula.Realize Empty.elim ![Ω, Mul, Pow, W, A, B] ↔
      (a : ℝ) / b ≤ fairCoinProduct.real (treeBody T) := by
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (hΩ ▸ mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let num (n : ℕ) : M := ⟨natOrdinal n, hn n⟩
  have hd (n k : ℕ) : dyadicBoundPredicate.compile.Realize Empty.elim
      ![Ω, Mul, Pow, num k, A, B, num n] ↔ a * 2 ^ n ≤ k * b := by
    rw [dyadicBoundPredicate.realize_compile hM]
    have he : Subtype.val ∘ ![Ω, Mul, Pow, num k, A, B, num n] = dyadicBoundParams k a b n := by
      funext i; fin_cases i <;> simp [dyadicBoundParams, num, hΩ, hMul, hPow, hA, hB]
    rw [he, eval_dyadicBoundPredicate]
  have he : closedMeasureBoundFormula.Realize Empty.elim ![Ω, Mul, Pow, W, A, B] ↔
      ∀ N : M, N.val ∈ Ω.val → ∃ K : M, K.val ∈ Ω.val ∧
        levelCardinalityFormula.Realize Empty.elim ![Ω, W, N, K] ∧
        dyadicBoundPredicate.compile.Realize Empty.elim ![Ω, Mul, Pow, K, A, B, N] := by
    simp only [closedMeasureBoundFormula, realize_boundedAll, realize_boundedExists_model,
      BoundedFormula.realize_inf, realize_reindex]
    have e₁ (N K : M) : Fin.snoc (Fin.snoc ![Ω, Mul, Pow, W, A, B] N) K ∘
        ![(0 : Fin 8), 3, 6, 7] = ![Ω, W, N, K] := by funext i; fin_cases i <;> rfl
    have e₂ (N K : M) : Fin.snoc (Fin.snoc ![Ω, Mul, Pow, W, A, B] N) K ∘
        ![(0 : Fin 8), 1, 2, 7, 4, 5, 6] = ![Ω, Mul, Pow, K, A, B, N] := by
      funext i; fin_cases i <;> rfl
    simp only [e₁, e₂]
    rfl
  rw [he]
  have hr := closed_lower_bound hT ((a : ℚ) / b)
  simp only [Rat.cast_div, Rat.cast_natCast] at hr
  rw [hr]
  constructor
  · intro h n
    obtain ⟨K, hK, hc, ht⟩ := h (num n) (hΩ ▸ mem_omegaOrdinal.mpr ⟨n, rfl⟩)
    obtain ⟨k, hk⟩ := mem_omegaOrdinal.mp (hΩ ▸ hK)
    have hke : K = num k := Subtype.ext hk.symm
    subst K
    have hc' := (realize_levelCardinalityFormula hM hinf hpair hunion hsep T n k
      Ω W (num n) (num k) hΩ hW rfl rfl).mp hc
    exact (cross_product_le_levelWeight_iff T n a b hb).mp (hc' ▸ (hd n k).mp ht)
  · intro h N hN
    obtain ⟨n, hn'⟩ := mem_omegaOrdinal.mp (hΩ ▸ hN)
    have hne : N = num n := Subtype.ext hn'.symm
    subst N
    refine ⟨num (level T n).card, hΩ ▸ mem_omegaOrdinal.mpr ⟨_, rfl⟩, ?_, ?_⟩
    · exact (realize_levelCardinalityFormula hM hinf hpair hunion hsep T n _
        Ω W (num n) (num _) hΩ hW rfl rfl).mpr rfl
    · exact (hd n _).mpr ((cross_product_le_levelWeight_iff T n a b hb).mpr (h n))


/-- Parameters omega, multiplication, powers, two tree codes, numerator, denominator. -/
def closedUnionBoundFormula : ForcingFormulas.Formula 7 :=
  (binaryUnionFormula (3 : Fin 8) 4 7 ⊓
    reindex closedMeasureBoundFormula ![0, 1, 2, 7, 5, 6]).ex

/-- The union code is an internal witness, not an externally supplied infinite family. -/
theorem realize_closedUnionBoundFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T S : Set (List Bool)) (hT : IsSubtree T) (hS : IsSubtree S) (a b : ℕ) (hb : 0 < b)
    (Ω Mul Pow W V A B : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hMul : Mul.val = naturalBinaryGraph (fun x y => x * y))
    (hPow : Pow.val = sequenceGraph (fun n => natOrdinal (2 ^ n)))
    (hW : W.val = wordTreeSet (binaryLift T)) (hV : V.val = wordTreeSet (binaryLift S))
    (hA : A.val = natOrdinal a) (hB : B.val = natOrdinal b) :
    closedUnionBoundFormula.Realize Empty.elim ![Ω, Mul, Pow, W, V, A, B] ↔
      fairCoinProduct.real (treeBody T ∪ treeBody S)ᶜ ≤ 1 - (a : ℝ) / b := by
  have hu : W.val ∪ V.val = wordTreeSet (binaryLift (T ∪ S)) := by
    simp only [hW, hV, binaryLift, Set.image_union, wordTreeSet_union]
  have he : closedUnionBoundFormula.Realize Empty.elim ![Ω, Mul, Pow, W, V, A, B] ↔
      ∃ Z : M, Z.val = wordTreeSet (binaryLift (T ∪ S)) ∧
        closedMeasureBoundFormula.Realize Empty.elim ![Ω, Mul, Pow, Z, A, B] := by
    simp only [closedUnionBoundFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      realize_binaryUnionFormula hM, realize_reindex]
    have e (Z : M) : Fin.snoc ![Ω, Mul, Pow, W, V, A, B] Z ∘ ![(0 : Fin 8), 1, 2, 7, 5, 6] =
        ![Ω, Mul, Pow, Z, A, B] := by funext i; fin_cases i <;> rfl
    simp only [e]
    change (∃ Z : M, Z.val = W.val ∪ V.val ∧ _) ↔ _
    rw [hu]
  have hc := MeasureTheory.measureReal_add_measureReal_compl (μ := fairCoinProduct)
    (isClosed_treeBody (T ∪ S)).measurableSet
  rw [MeasureTheory.probReal_univ, treeBody_union hT hS] at hc
  rw [he]
  constructor
  · rintro ⟨Z, hZ, hz⟩
    have hr := (realize_closedMeasureBoundFormula hM hinf hpair hunion hsep (T ∪ S)
      (subtree_union hT hS) a b hb Ω Mul Pow Z A B hΩ hMul hPow hZ hA hB).mp hz
    rw [treeBody_union hT hS] at hr
    linarith
  · intro hr
    let Z : M := ⟨wordTreeSet (binaryLift (T ∪ S)),
      treeUnion_mem hM hpair hunion T S (hW ▸ W.property) (hV ▸ V.property)⟩
    refine ⟨Z, rfl, (realize_closedMeasureBoundFormula hM hinf hpair hunion hsep (T ∪ S)
      (subtree_union hT hS) a b hb Ω Mul Pow Z A B hΩ hMul hPow rfl hA hB).mpr ?_⟩
    rw [treeBody_union hT hS]
    linarith

/-- Parameters omega, multiplication, addition, a,b,c,d. Recognize 1-c/d < a/b without division. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Continue to assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, and Separation.
    For two downward-closed binary trees $T,S$ with $W_T,W_S\in M$, put
    $$\mathcal F=\TreeBody{T},\qquad \mathcal K=\TreeBody{S}.$$
    To describe a small error outside $\mathcal F\cup \mathcal K$, retain the internal addition graph $G_+$ as well as
    $\omega,G_\times,P_2$ as parameters and define
    $$\begin{aligned}
    E(W,V,h,d):\equiv{}&\exists a,b\in\omega\;[b>0\land bd<ad+hb\\
    &{}\land\exists Z\;(Z=W\cup V\land H(Z,a,b))].
    \end{aligned}$$
    The arithmetic clause abbreviates a bounded formula: read $bd,ad,hb$ from $G_\times$, read the sum of the
    last two values from $G_+$, and compare the resulting finite ordinals by membership. Likewise, $b>0$
    means that the finite ordinal $b$ is nonempty. The union equality is the ordinary membership-language
    formula. Thus $E$ is a first-order formula with all its arithmetic parameters specified.
-/
def errorMarginPredicate : BoundedSetPredicate 7 :=
  .ex 0 (.ex 0 (.ex 0 (.ex 0
    (.conj (binaryMemberAt 1 4 6 7)
      (.conj (binaryMemberAt 1 3 6 8)
        (.conj (binaryMemberAt 1 5 4 9)
          (.conj (binaryMemberAt 2 8 9 10) (.member 7 10))))))))

lemma eval_errorMarginPredicate (a b c d : ℕ) :
    errorMarginPredicate.eval ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
      naturalBinaryGraph (fun x y => x + y), natOrdinal a, natOrdinal b, natOrdinal c, natOrdinal d] ↔
        b * d < a * d + c * b := by
  simp [errorMarginPredicate, eval, eval_binaryMemberAt, Fin.snoc, exists_mem_omegaOrdinal,
    pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff]
  norm_cast

lemma errorMargin_iff (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    b * d < a * d + c * b ↔ 1 - (c : ℝ) / d < (a : ℝ) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sub_lt_iff_lt_add, div_add_div _ _ (ne_of_gt hb') (ne_of_gt hd'),
    lt_div_iff₀ (mul_pos hb' hd'), one_mul]
  norm_cast
  rw [Nat.mul_comm b c]

/-- The numerical part of an approximation certificate, with its rational margin explicit. -/
def approximationErrorFormula : ForcingFormulas.Formula 10 :=
  reindex errorMarginPredicate.compile ![0, 1, 3, 6, 7, 8, 9] ⊓
    reindex closedUnionBoundFormula ![0, 1, 2, 4, 5, 6, 7]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The union code $Z=W_T\cup W_S=W_{T\cup S}$ belongs to $M$ by
    §{sec:internal-finite-measure-bounds}, and $\TreeBody{T\cup S}=\mathcal F\cup \mathcal K$.
    The criterion for $H$ gives
    $$M\models H(Z,a,b)\quad\Longleftrightarrow\quad
    \mu(\SetDifference{\CantorSpace}{\mathcal F\cup \mathcal K})\le 1-\frac ab.$$
    For positive $b,d$, the finite arithmetic clause is equivalent to
    $$bd<ad+hb\quad\Longleftrightarrow\quad 1-\frac hd<\frac ab.$$
    Together these two inequalities imply the required strict error bound.
-/
/-- Interpret the finite margin and the closed lower cut using the same arithmetic parameters. -/
theorem realize_approximationErrorFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T S : Set (List Bool)) (hT : IsSubtree T) (hS : IsSubtree S)
    (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) (Ω Mul Pow Add W V A B C D : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hMul : Mul.val = naturalBinaryGraph (fun x y => x * y))
    (hPow : Pow.val = sequenceGraph (fun n => natOrdinal (2 ^ n)))
    (hAdd : Add.val = naturalBinaryGraph (fun x y => x + y))
    (hW : W.val = wordTreeSet (binaryLift T)) (hV : V.val = wordTreeSet (binaryLift S))
    (hA : A.val = natOrdinal a) (hB : B.val = natOrdinal b)
    (hC : C.val = natOrdinal c) (hD : D.val = natOrdinal d) :
    approximationErrorFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, W, V, A, B, C, D] ↔
      1 - (c : ℝ) / d < (a : ℝ) / b ∧
        fairCoinProduct.real (treeBody T ∪ treeBody S)ᶜ ≤ 1 - (a : ℝ) / b := by
  have e₁ : ![Ω, Mul, Pow, Add, W, V, A, B, C, D] ∘ ![(0 : Fin 10), 1, 3, 6, 7, 8, 9] =
      ![Ω, Mul, Add, A, B, C, D] := by funext i; fin_cases i <;> rfl
  have e₂ : ![Ω, Mul, Pow, Add, W, V, A, B, C, D] ∘ ![(0 : Fin 10), 1, 2, 4, 5, 6, 7] =
      ![Ω, Mul, Pow, W, V, A, B] := by funext i; fin_cases i <;> rfl
  simp only [approximationErrorFormula, BoundedFormula.realize_inf, realize_reindex, e₁, e₂]
  rw [realize_closedUnionBoundFormula hM hinf hpair hunion hsep T S hT hS a b hb
    Ω Mul Pow W V A B hΩ hMul hPow hW hV hA hB, errorMarginPredicate.realize_compile hM]
  have he : Subtype.val ∘ ![Ω, Mul, Add, A, B, C, D] =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
        naturalBinaryGraph (fun x y => x + y), natOrdinal a, natOrdinal b, natOrdinal c, natOrdinal d] := by
    funext i; fin_cases i <;> simp [hΩ, hMul, hAdd, hA, hB, hC, hD]
  rw [he, eval_errorMarginPredicate, errorMargin_iff a b c d hb hd]


/-- Parameters omega, multiplication, powers, addition, two tree codes, error numerator and denominator. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Continue to assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, and Separation.
    For two downward-closed binary trees $T,S$ with $W_T,W_S\in M$, put
    $$\mathcal F=\TreeBody{T},\qquad \mathcal K=\TreeBody{S}.$$
    To describe a small error outside $\mathcal F\cup \mathcal K$, retain the internal addition graph $G_+$ as well as
    $\omega,G_\times,P_2$ as parameters and define
    $$\begin{aligned}
    E(W,V,h,d):\equiv{}&\exists a,b\in\omega\;[b>0\land bd<ad+hb\\
    &{}\land\exists Z\;(Z=W\cup V\land H(Z,a,b))].
    \end{aligned}$$
    The arithmetic clause abbreviates a bounded formula: read $bd,ad,hb$ from $G_\times$, read the sum of the
    last two values from $G_+$, and compare the resulting finite ordinals by membership. Likewise, $b>0$
    means that the finite ordinal $b$ is nonempty. The union equality is the ordinary membership-language
    formula. Thus $E$ is a first-order formula with all its arithmetic parameters specified.
-/
def smallErrorFormula : ForcingFormulas.Formula 8 :=
  boundedExists 0 (boundedExists 0
    (orderNonemptyFormula 9 ⊓ reindex approximationErrorFormula ![0, 1, 2, 3, 4, 5, 8, 9, 6, 7]))

/-- Rational margins suffice for every error tolerance at most one. -/
lemma lt_iff_rational_margin (r ε : ℝ) (hε : ε ≤ 1) :
    r < ε ↔ ∃ a b : ℕ, 0 < b ∧ 1 - ε < (a : ℝ) / b ∧ r ≤ 1 - (a : ℝ) / b := by
  constructor
  · intro h
    obtain ⟨q, hq, hqr⟩ := exists_rat_btwn (show 1 - ε < 1 - r by linarith)
    have hq0 : 0 ≤ q := by exact_mod_cast (show (0 : ℝ) ≤ q by linarith)
    have he : (q.num.natAbs : ℝ) / q.den = q := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq0)]
      exact (Rat.cast_def q).symm
    exact ⟨q.num.natAbs, q.den, q.den_pos, by simpa only [he] using hq, by rw [he]; linarith⟩
  · rintro ⟨a, b, _, hm, hr⟩
    linarith

/-- Every quantified witness belongs to the model; the resulting strict error is the external one. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal tests for approximation errors
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Conversely, write $r=\mu(\SetDifference{\CantorSpace}{\mathcal F\cup \mathcal K})$ and suppose $r<h/d$.
    Since $h/d\le1$, rational density supplies a nonnegative rational $a/b$ with $b>0$ such that
    $$1-\frac hd<\frac ab<1-r.$$
    Its numerator and denominator are actual natural numbers and hence belong to $M$. The internal union
    code and the criterion for $H$ supply the remaining witnesses. The bounded arithmetic test has the same
    meaning in $M$, so these witnesses establish $M\models E(W_T,W_S,h,d)$.
-/
theorem realize_smallErrorFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T S : Set (List Bool)) (hT : IsSubtree T) (hS : IsSubtree S)
    (c d : ℕ) (hd : 0 < d) (hcd : c ≤ d) (Ω Mul Pow Add W V C D : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (hMul : Mul.val = naturalBinaryGraph (fun x y => x * y))
    (hPow : Pow.val = sequenceGraph (fun n => natOrdinal (2 ^ n)))
    (hAdd : Add.val = naturalBinaryGraph (fun x y => x + y))
    (hW : W.val = wordTreeSet (binaryLift T)) (hV : V.val = wordTreeSet (binaryLift S))
    (hC : C.val = natOrdinal c) (hD : D.val = natOrdinal d) :
    smallErrorFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, W, V, C, D] ↔
      fairCoinProduct.real (treeBody T ∪ treeBody S)ᶜ < (c : ℝ) / d := by
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (hΩ ▸ mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let num (n : ℕ) : M := ⟨natOrdinal n, hn n⟩
  have hp (b : ℕ) : (∃ x, x ∈ (natOrdinal b : ZFSet.{u})) ↔ 0 < b := by
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, _⟩ := mem_natOrdinal.mp hx
      exact Nat.zero_le i |>.trans_lt hi
    · intro hb
      exact ⟨natOrdinal 0, mem_natOrdinal.mpr ⟨0, hb, rfl⟩⟩
  have he : smallErrorFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, W, V, C, D] ↔
      ∃ A : M, A.val ∈ Ω.val ∧ ∃ B : M, B.val ∈ Ω.val ∧ (∃ x, x ∈ B.val) ∧
        approximationErrorFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, W, V, A, B, C, D] := by
    simp only [smallErrorFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
      realize_orderNonemptyFormula hM, realize_reindex]
    have e (A B : M) : Fin.snoc (Fin.snoc ![Ω, Mul, Pow, Add, W, V, C, D] A) B ∘
        ![(0 : Fin 10), 1, 2, 3, 4, 5, 8, 9, 6, 7] = ![Ω, Mul, Pow, Add, W, V, A, B, C, D] := by
      funext i; fin_cases i <;> rfl
    simp only [e]
    rfl
  have hε : (c : ℝ) / d ≤ 1 :=
    (div_le_one (by exact_mod_cast hd)).mpr (by exact_mod_cast hcd)
  rw [he, lt_iff_rational_margin _ _ hε]
  constructor
  · rintro ⟨A, ha, B, hb, hb0, hf⟩
    obtain ⟨a, ha⟩ := mem_omegaOrdinal.mp (hΩ ▸ ha)
    obtain ⟨b, hb⟩ := mem_omegaOrdinal.mp (hΩ ▸ hb)
    have hb' : 0 < b := (hp b).mp (hb ▸ hb0)
    exact ⟨a, b, hb', (realize_approximationErrorFormula hM hinf hpair hunion hsep
      T S hT hS a b c d hb' hd Ω Mul Pow Add W V A B C D hΩ hMul hPow hAdd
      hW hV ha.symm hb.symm hC hD).mp hf⟩
  · rintro ⟨a, b, hb, hm, hr⟩
    refine ⟨num a, hΩ ▸ mem_omegaOrdinal.mpr ⟨a, rfl⟩,
      num b, hΩ ▸ mem_omegaOrdinal.mpr ⟨b, rfl⟩, (hp b).mpr hb, ?_⟩
    exact (realize_approximationErrorFormula hM hinf hpair hunion hsep
      T S hT hS a b c d hb hd Ω Mul Pow Add W V (num a) (num b) C D hΩ hMul hPow hAdd
      hW hV rfl rfl hC hD).mpr ⟨hm, hr⟩

/-- The two-closed-code error is exactly the original open-minus-closed error. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For an inner tree $T$ and an outer open code $O$, take $S=D(O)$ from
    §{sec:internal-finite-measure-bounds}. The exact identity
    $$\SetDifference{\CantorSpace}{\TreeBody{T}\cup\TreeBody{D(O)}}
    =\SetDifference{U(O)}{\TreeBody{T}}$$
    shows that the proposition tests the original approximation error.
-/
lemma complement_treeBody_union_avoidWords (T O : Set (List Bool)) :
    (treeBody T ∪ treeBody (avoidWords O))ᶜ = openFromWords O \ treeBody T := by
  rw [treeBody_avoidWords]
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
  tauto

end PolishSpaceBook.CantorTreeMeasure
