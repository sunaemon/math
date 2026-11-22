module

public import PolishSpaceBook.NonnegativeRealCutRationalFamilies
public import PolishSpaceBook.NonnegativeRealCutInternalInfimum
public import PolishSpaceBook.NonnegativeRealCutInternalAddition
public import PolishSpaceBook.CantorInternalClopenFamilies

@[expose] public section

/-! # Internal finite-level value codes and their rounded limit -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open ZFSet SetTheoryModels FirstOrder Language ForcingFormulas MeasureTheory BorelExpression
universe u

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $T\IncludedIn\finseq{2}$, write $k_n=|T_n|$ and define
    $$\TreeLevelMeasureCode{T}{n}:=\NonnegativeRealCut{k_n/2^n}.$$
    The finite-level calculation in §{sec:coded-measure-bounds} gives
    $$\frac{k_n}{2^n}=\mu(C_n(T)).$$
    This counts all words in $T_n$, including dead ends.
-/
lemma levelWeight_as_fraction (T : Set (List Bool)) (n : ℕ) :
    (levelWeight T n : ℝ) = ((level T n).card : ℝ) / (2 ^ n : ℕ) := by
  simp [levelWeight, div_eq_mul_inv]

/-- The finite cylinder count determines a dyadic rational, whose entire cut is used as its code. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $T\IncludedIn\finseq{2}$, write $k_n=|T_n|$ and define
    $$\TreeLevelMeasureCode{T}{n}:=\NonnegativeRealCut{k_n/2^n}.$$
    The finite-level calculation in §{sec:coded-measure-bounds} gives
    $$\frac{k_n}{2^n}=\mu(C_n(T)).$$
    This counts all words in $T_n$, including dead ends.
-/
def levelMeasureCode (T : Set (List Bool)) (n : ℕ) : ZFSet.{u} :=
  nonnegativeRealCutCode (levelWeight T n : ℝ)

lemma levelMeasureCode_eq (T : Set (List Bool)) (n : ℕ) :
    levelMeasureCode.{u} T n = nonnegativeRealCutCode (fairCoinProduct.real (levelSet T n)) := by
  rw [levelMeasureCode, levelWeight_eq_measureReal]

lemma levelMeasureCode_valid (T : Set (List Bool)) (n : ℕ) :
    ValidNonnegativeRealCutCode (levelMeasureCode.{u} T n) := nonnegativeRealCutCode_valid _

lemma decode_levelMeasureCode (T : Set (List Bool)) (n : ℕ) :
    decodeNonnegativeRealCut (levelMeasureCode.{u} T n) = fairCoinProduct.real (levelSet T n) := by
  rw [levelMeasureCode_eq, decode_nonnegativeRealCutCode measureReal_nonneg]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal sequence of finite-level measure values
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The entire count sequence $\Sequence{k_n}{n\in\omega}$ belongs to $M$ by §{sec:internal-borel-measure-cut}.
    The entire sequence $\Sequence{2^n}{n\in\omega}$ belongs to $M$ by §{sec:internal-natural-arithmetic}.
    Apply the preceding proposition to these sequences. Validity and the decoded values follow from
    §{sec:internal-borel-measure-cut} and the finite-level measure calculation.
-/
theorem levelMeasureCode_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) :
    sequenceGraph (levelMeasureCode T) ∈ M := by
  have h := fractionCutCode_sequence_mem hM hinf hpair hunion hpower hsep hrep
    (fun n => (level T n).card) (fun n => 2 ^ n) (fun n => by positivity)
    (levelCardinality_sequence_mem hM hinf hpair hunion hsep hrep T hT)
    (naturalTwoPowerGraph_mem hM hinf hpair hunion hpower hsep)
  change sequenceGraph (fun n => nonnegativeRealCutCode (levelWeight T n : ℝ)) ∈ M
  simpa only [levelWeight_as_fraction] using h

lemma level_union (T S : Set (List Bool)) (n : ℕ) :
    level (T ∪ S) n = level T n ∪ level S n := by
  classical
  ext s
  simp [level]

lemma levelWeight_union {T S : Set (List Bool)} {n : ℕ}
    (h : Disjoint (level T n) (level S n)) :
    levelWeight (T ∪ S) n = levelWeight T n + levelWeight S n := by
  simp only [levelWeight, level_union, Finset.card_union_of_disjoint h, Nat.cast_add, add_mul]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Finite additivity of level value codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The finite level of the union is $T_n\cup S_n$. Since these finite sets are disjoint, their cardinalities
    add. Dividing by $2^n$ gives addition of the level weights. The addition theorem in
    §{sec:internal-real-cut-addition} converts this numerical equality into the stated code equality.
-/
theorem levelMeasureCode_union {T S : Set (List Bool)} {n : ℕ}
    (h : Disjoint (level T n) (level S n)) :
    levelMeasureCode.{u} (T ∪ S) n = sumCutCode (levelMeasureCode T n) (levelMeasureCode S n) := by
  rw [levelMeasureCode, levelWeight_union h, Rat.cast_add]
  exact (sumCutCode_eq _ _ (levelWeight_nonneg T n) (levelWeight_nonneg S n)).symm

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Closed measure from the internal level-value sequence
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The entire graph $G_Q$ is internal, so §{sec:internal-real-cut-addition} constructs its rounded infimum
    inside $M$ and identifies the decoded value with $\inf_n k_n/2^n$.
    By §{sec:coded-measure-bounds}, the level weights converge to $\mu(\TreeBody{T})$, and each is at least
    that value. Their infimum is therefore exactly that value. The encoding and decoding identities from
    §{sec:internal-real-cut-addition} give the two remaining equalities.
-/
theorem roundedInf_levelMeasureCode {T : Set (List Bool)} (hT : IsSubtree T) :
    roundedInfCutCode (levelMeasureCode.{u} T) =
      nonnegativeRealCutCode (fairCoinProduct.real (treeBody T)) := by
  unfold levelMeasureCode
  rw [roundedInfCutCode_eq _ (levelWeight_nonneg T), levelWeight_ciInf hT]

theorem decode_roundedInf_levelMeasureCode {T : Set (List Bool)} (hT : IsSubtree T) :
    decodeNonnegativeRealCut (roundedInfCutCode (levelMeasureCode.{u} T)) =
      fairCoinProduct.real (treeBody T) := by
  rw [roundedInf_levelMeasureCode hT, decode_nonnegativeRealCutCode measureReal_nonneg]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Closed measure from the internal level-value sequence
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This constructs the closed-measure code from the entire internal level-value sequence.
-/
theorem roundedInf_levelMeasureCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) :
    roundedInfCutCode (levelMeasureCode T) ∈ M :=
  roundedInfCutCode_mem hM hinf hpair hunion hpower hsep _
    (levelMeasureCode_sequence_mem hM hinf hpair hunion hpower hsep hrep T hT)

end PolishSpaceBook.CantorTreeMeasure
