module

public import PolishSpaceBook.CantorScaledCylinderCuts
public import PolishSpaceBook.RandomDensityException
public import PolishSpaceBook.SetTheoryWordOperations

@[expose] public section

/-! # Rational-cut descriptions of the two density-deviation tests -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory BoundedSetPredicate
open NamedLambda
universe u

lemma cantor_leaf_zero : (Code.leaf 0).cantor = Set.univ := by
  rw [Code.cantor_leaf]
  simp [NatListCode.decode]

lemma density_ratio_eq (c : Code) (j : ℕ) :
    cylinderDensity c.cantor (NatListCode.decode j) =
      fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor /
        fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor := by
  rw [Code.cantor_inf, Code.cantor_inf, cantor_leaf_zero, Set.univ_inter, Code.cantor_leaf]
  rfl

lemma density_numerator_le_denominator (c : Code) (j : ℕ) :
    fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor ≤
      fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor := by
  rw [Code.cantor_inf, Code.cantor_inf, cantor_leaf_zero, Set.univ_inter]
  exact measureReal_mono Set.inter_subset_right

theorem density_deviation_zero_iff (c : Code) (k j : ℕ) :
    1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) 0 ↔
      0 < fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor ∧
        ¬ ((k + 1 : ℝ) * fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor <
          fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor) := by
  rw [density_ratio_eq]
  exact reciprocal_le_density_dist_zero _ _ measureReal_nonneg measureReal_nonneg
    (density_numerator_le_denominator c j) k

theorem density_deviation_one_iff (c : Code) (k j : ℕ) :
    1 / (k + 1 : ℝ) ≤ dist (cylinderDensity c.cantor (NatListCode.decode j)) 1 ↔
      ¬ ((k : ℝ) * fairCoinProduct.real (Code.inf (Code.leaf 0) (Code.leaf j)).cantor <
        (k + 1 : ℝ) * fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor) := by
  rw [density_ratio_eq]
  exact reciprocal_le_density_dist_one _ _ measureReal_nonneg measureReal_nonneg
    (density_numerator_le_denominator c j) k

/-- Parameters omega, finite words, decoder, tail bound, cylinder index. -/
def wordTailBoundPredicate : BoundedSetPredicate 5 :=
  .ex 1 (.ex 0 (.conj (.pairMember 2 4 5) (.conj (.function 6 0 5) (.subset 3 6))))

lemma eval_wordTailBoundPredicate (N j : ℕ) :
    wordTailBoundPredicate.eval (![Ordinal.omega0.toZFSet, finiteSequences, listDecodeGraph,
      natOrdinal N, natOrdinal j] : Fin 5 → ZFSet.{u}) ↔ N ≤ (NatListCode.decode j).length := by
  change (∃ w ∈ finiteSequences, ∃ n ∈ Ordinal.omega0.toZFSet,
    pair (natOrdinal j) w ∈ listDecodeGraph ∧ IsFunc n Ordinal.omega0.toZFSet w ∧ natOrdinal N ⊆ n) ↔ _
  simp only [exists_mem_finiteSequences, exists_mem_omegaOrdinal, pair_mem_listDecodeGraph,
    wordLength_iff]
  have he (m : ℕ) : natOrdinal N ⊆ (natOrdinal m : ZFSet.{u}) ↔ N ≤ m := by
    change (N : Ordinal).toZFSet ⊆ (m : Ordinal).toZFSet ↔ _
    rw [Ordinal.toZFSet_subset_toZFSet_iff]
    exact_mod_cast Iff.rfl
  simp [he]

end PolishSpaceBook.CantorTreeMeasure
