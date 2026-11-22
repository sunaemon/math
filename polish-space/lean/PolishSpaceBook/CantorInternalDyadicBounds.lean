module

public import PolishSpaceBook.CantorInternalLevels
public import PolishSpaceBook.SetTheoryNaturalPowers

@[expose] public section

/-! # Internal dyadic bounds reduced to absolute natural-number comparisons -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Omega, multiplication, powers of two, count, numerator, denominator, level. -/
def dyadicBoundParams (k a b n : ℕ) : Fin 7 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
    sequenceGraph (fun i => natOrdinal (2 ^ i)), natOrdinal k, natOrdinal a, natOrdinal b, natOrdinal n]

/-- Read the power and the two cross products; compare their finite ordinals. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Let $G_\times$ be the internal multiplication graph. For natural numbers $n,k,a,b$, define the bounded test
    $$\begin{aligned}
    \mathrm{DB}(n,k,a,b):\equiv{}&\exists p,u,v\in\omega\;[\langle n,p\rangle\in P_2\\
    &{}\land\langle\langle a,p\rangle,u\rangle\in G_\times\\
    &{}\land\langle\langle k,b\rangle,v\rangle\in G_\times
    \land v\notin u].
    \end{aligned}$$
    The last condition compares finite ordinals and means $u\le v$.
-/
def dyadicBoundPredicate : BoundedSetPredicate 7 :=
  .ex 0 (.ex 0 (.ex 0 (.conj (.pairMember 2 6 7)
    (.conj (binaryMemberAt 1 4 7 8) (.conj (binaryMemberAt 1 3 5 9) (.neg (.member 9 8)))))))

lemma eval_dyadicBoundPredicate (k a b n : ℕ) :
    dyadicBoundPredicate.eval (dyadicBoundParams.{u} k a b n) ↔ a * 2 ^ n ≤ k * b := by
  simp [dyadicBoundPredicate, dyadicBoundParams, eval, eval_binaryMemberAt, Fin.snoc, Fin.castPred, Fin.castLT,
    exists_mem_omegaOrdinal, pair_mem_sequenceGraph, pair_mem_naturalBinaryGraph,
    natOrdinal_injective.eq_iff]
  norm_cast

theorem dyadicBoundParams_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (k a b n : ℕ) : ∀ j, dyadicBoundParams k a b n j ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (i : ℕ) : natOrdinal i ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨i, rfl⟩) hΩ
  have hmul := naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep
  have hpow := naturalTwoPowerGraph_mem hM hinf hpair hunion hpower hsep
  intro j
  fin_cases j <;> simp only [dyadicBoundParams] <;> first | exact hΩ | exact hmul | exact hpow | exact hn _

lemma cross_product_le_levelWeight_iff (T : Set (List Bool)) (n a b : ℕ) (hb : 0 < b) :
    a * 2 ^ n ≤ (level T n).card * b ↔ (a : ℚ) / b ≤ levelWeight T n := by
  have hw : levelWeight T n = ((level T n).card : ℚ) / (2 ^ n) := by
    simp [levelWeight, div_eq_mul_inv]
  rw [hw, div_le_div_iff₀ (by exact_mod_cast hb) (pow_pos (by norm_num) n)]
  norm_cast

/-- The model's count, not an unproved external replacement for it, supplies the numerator. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Absolute dyadic comparisons
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    The count is $k=|T_n|$ by the finite-level proposition. The three graph lookups force
    $p=2^n$, $u=a2^n$, and $v=kb$. The common interpretation theorem therefore reduces the internal test to
    $a2^n\le|T_n|b$. Since $b>0$ and $2^n>0$, multiplying by the positive denominators gives exactly the stated
    rational comparison.
-/
theorem level_dyadicBound_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List Bool)) (n k a b : ℕ) (hb : 0 < b) (K A : M)
    (hK : K.val = natOrdinal k) (hA : A.val = finiteWordLevel (BorelExpression.binaryLift T) n)
    (hcount : finiteCardinalityFormula.Realize Empty.elim ![K, A]) :
    dyadicBoundPredicate.compile.Realize Empty.elim
      (fun j => ⟨dyadicBoundParams k a b n j,
        dyadicBoundParams_mem hM hinf hpair hunion hpower hsep k a b n j⟩ : Fin 7 → M) ↔
      (a : ℚ) / b ≤ levelWeight T n := by
  have hk := (binaryLevel_cardinality_absolute hM hinf hpair hunion T n k K A hK hA).mp hcount
  rw [dyadicBoundPredicate.realize_compile hM]
  change dyadicBoundPredicate.eval (dyadicBoundParams k a b n) ↔ _
  rw [eval_dyadicBoundPredicate, hk, cross_product_le_levelWeight_iff T n a b hb]

/-- Signed rationals reduce to a sign test and the same nonnegative cross product. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    Every nonnegative rational has a representation $a/b$ with $a\in\omega$ and $b>0$.
    For a negative rational $q$, the lower comparison $q\le d_n(T)$ is automatically true, since $d_n(T)\ge0$.
-/
lemma rational_le_levelWeight_iff (T : Set (List Bool)) (n : ℕ) (q : ℚ) :
    q ≤ levelWeight T n ↔ q < 0 ∨
      (0 ≤ q ∧ q.num.natAbs * 2 ^ n ≤ (level T n).card * q.den) := by
  have hw : 0 ≤ levelWeight T n := by unfold levelWeight; positivity
  by_cases hq : q < 0
  · simp only [hq, true_or, iff_true]
    exact (le_of_lt hq).trans hw
  · have hq0 := le_of_not_gt hq
    have hnum : (q.num.natAbs : ℚ) = q.num := by
      calc
        (q.num.natAbs : ℚ) = ((q.num.natAbs : ℤ) : ℚ) := by simp
        _ = (q.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ))
          (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq0))
    have he : (q.num.natAbs : ℚ) / q.den = q := by rw [hnum, Rat.num_div_den]
    simp only [hq, false_or, hq0, true_and]
    rw [cross_product_le_levelWeight_iff T n _ _ q.den_pos, he]

/-- Strict upper queries use the negation of the same signed rational lower test. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Strict upper comparisons $d_n(T)<q$ are obtained by negating $q\le d_n(T)$.
-/
lemma levelWeight_lt_rational_iff (T : Set (List Bool)) (n : ℕ) (q : ℚ) :
    levelWeight T n < q ↔ ¬ (q < 0 ∨
      (0 ≤ q ∧ q.num.natAbs * 2 ^ n ≤ (level T n).card * q.den)) := by
  rw [← not_le, rational_le_levelWeight_iff]

end PolishSpaceBook.CantorTreeMeasure
