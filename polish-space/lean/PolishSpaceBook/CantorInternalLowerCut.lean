module

public import PolishSpaceBook.CantorInternalBorelRegularity

@[expose] public section

/-! # Rational lower cuts with internal closed-tree witnesses -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory BoundedSetPredicate
universe u

lemma lt_iff_nat_fraction_margin (q r : ℝ) (hq : 0 ≤ q) :
    q < r ↔ ∃ a b : ℕ, 0 < b ∧ q < (a : ℝ) / b ∧ (a : ℝ) / b ≤ r := by
  have h := lt_iff_rational_margin (1 - r) (1 - q) (by linarith)
  constructor
  · intro hqr
    obtain ⟨a, b, hb, ha, hr⟩ := h.mp (by linarith)
    exact ⟨a, b, hb, by linarith, by linarith⟩
  · rintro ⟨a, b, hb, ha, hr⟩
    have hh := h.mpr ⟨a, b, hb, by linarith, by linarith⟩
    linarith

/-- Internal two-sided approximation supplies an internal closed witness to each strict lower cut. -/
lemma internallyApproximable_lower_cut {M : ZFSet.{u}} {A : Set (ℕ → Bool)}
    (hA : InternallyApproximable M A) (q : ℝ) (hq : 0 ≤ q) :
    q < fairCoinProduct.real A ↔
      ∃ T : Set (List Bool), IsSubtree T ∧ wordTreeSet (binaryLift T) ∈ M ∧ treeBody T ⊆ A ∧
        ∃ a b : ℕ, 0 < b ∧ q < (a : ℝ) / b ∧ (a : ℝ) / b ≤ fairCoinProduct.real (treeBody T) := by
  constructor
  · intro h
    obtain ⟨T, O, ht, hTM, _, hTA, hAU, hgap⟩ := hA _ (sub_pos.mpr h)
    have hmono := measureReal_mono (μ := fairCoinProduct) hAU
    rw [measureReal_sdiff (hTA.trans hAU) (isClosed_treeBody T).measurableSet] at hgap
    have hqT : q < fairCoinProduct.real (treeBody T) := by linarith
    exact ⟨T, ht, hTM, hTA, (lt_iff_nat_fraction_margin _ _ hq).mp hqT⟩
  · rintro ⟨T, _, _, hTA, a, b, _, hqa, haT⟩
    exact hqa.trans_le (haT.trans (measureReal_mono hTA))

/-- Parameters omega, multiplication, a,b,c,d; compare a/b and c/d by cross-products. -/
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
def rationalLessPredicate : BoundedSetPredicate 6 :=
  .ex 0 (.ex 0 (.conj (binaryMemberAt 1 2 5 6)
    (.conj (binaryMemberAt 1 4 3 7) (.member 6 7))))

lemma eval_rationalLessPredicate (a b c d : ℕ) :
    rationalLessPredicate.eval ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
      natOrdinal a, natOrdinal b, natOrdinal c, natOrdinal d] ↔ a * d < c * b := by
  simp [rationalLessPredicate, eval, eval_binaryMemberAt, Fin.snoc, exists_mem_omegaOrdinal,
    pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff]
  norm_cast

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
lemma rationalLess_iff (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    a * d < c * b ↔ (a : ℝ) / b < (c : ℝ) / d := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hd)]
  norm_cast

/-- Parameters binary words, finite words, points, Borel set, empty set, proposed inner tree. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Keep the transitive-model hypotheses of §{sec:internal-approximation-errors}, and let
    $B=\BorelInterpretation{c}{M}$ and $A=i^{-1}(\BorelValue{c})$ for a valid expression $c$ with internal label graph.
    All the arithmetic and space parameters below are the fixed internal sets already constructed.
    For a proposed inner-tree code, use
    $$J(B,W):\equiv\mathrm{Tree}(W)\land\mathrm{Inc}(B,W,\emptyset).$$
    The empty tree has no branches, so the second inclusion condition is automatic. By the shared
    interpretation and inclusion theorems, $M\models J(B,W)$ holds exactly when $W=W_T$ for a downward-closed
    binary tree $T$ with $\TreeBody{T}\IncludedIn A$.
-/
def innerTreePredicate : BoundedSetPredicate 6 :=
  .conj (binaryTreePredicate.rename ![0, 5])
    (approximationInclusionPredicate.rename ![1, 2, 3, 5, 4])

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Keep the transitive-model hypotheses of §{sec:internal-approximation-errors}, and let
    $B=\BorelInterpretation{c}{M}$ and $A=i^{-1}(\BorelValue{c})$ for a valid expression $c$ with internal label graph.
    All the arithmetic and space parameters below are the fixed internal sets already constructed.
    For a proposed inner-tree code, use
    $$J(B,W):\equiv\mathrm{Tree}(W)\land\mathrm{Inc}(B,W,\emptyset).$$
    The empty tree has no branches, so the second inclusion condition is automatic. By the shared
    interpretation and inclusion theorems, $M\models J(B,W)$ holds exactly when $W=W_T$ for a downward-closed
    binary tree $T$ with $\TreeBody{T}\IncludedIn A$.
-/
lemma eval_innerTreePredicate {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (W : M) : innerTreePredicate.eval ![wordTreeSet (binaryLift Set.univ), finiteSequences,
      internalBaire M, internalInterpretation M c hc.2.2.2.2.2 NamedLambda.NatListCode.decode [], ∅, W.val] ↔
        ∃ T : Set (List Bool), IsSubtree T ∧ W.val = wordTreeSet (binaryLift T) ∧
          treeBody T ⊆ cantorSet c hc.2.2.2.2.2 := by
  have he : wordTreeSet (binaryLift (∅ : Set (List Bool))) = (∅ : ZFSet.{u}) := by
    ext x; simp [mem_wordTreeSet, binaryLift]
  simp only [innerTreePredicate, eval, eval_rename]
  change (binaryTreePredicate.eval ![wordTreeSet (binaryLift Set.univ), W.val] ∧
    approximationInclusionPredicate.eval ![finiteSequences, internalBaire M,
      internalInterpretation M c hc.2.2.2.2.2 NamedLambda.NatListCode.decode [], W.val, ∅]) ↔ _
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨T, hT, hW⟩ := (binaryTreePredicate_iff W.val).mp ht
    refine ⟨T, hT, hW, ?_⟩
    rw [hW, ← he] at hi
    exact ((approximationInclusion_absolute hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
      T ∅ (hW ▸ W.property) (he ▸ empty_mem_of_infinity hM hinf)).mp hi).1
  · rintro ⟨T, hT, hW, hi⟩
    refine ⟨(binaryTreePredicate_iff W.val).mpr ⟨T, hT, hW⟩, ?_⟩
    rw [hW, ← he]
    exact (approximationInclusion_absolute hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
      T ∅ (hW ▸ W.property) (he ▸ empty_mem_of_infinity hM hinf)).mpr
      ⟨hi, by simp [treeBody]⟩

end PolishSpaceBook.CantorTreeMeasure
