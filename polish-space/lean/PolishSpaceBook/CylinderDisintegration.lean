module

public import PolishSpaceBook.DyadicMeasureAlgebra
public import PolishSpaceBook.DisintegrationFibers
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-!
# Conditional fair-coin measures on prefix fibers

Normalize the restriction to a cylinder, verify the finite disintegration
identity, and calculate the tail law on cylinders before extending it to Borel sets.
-/

noncomputable section
namespace PolishSpaceBook.CylinderDisintegration
open Set MeasureTheory MeasurableSpace Function
open scoped ENNReal
open DyadicMeasureAlgebra

/-- Delete the first `n` bits. -/
def tailMap (n : ℕ) (x : cantor_space) : cantor_space := fun k => x (n + k)

lemma tailMap_measurable (n : ℕ) : Measurable (tailMap n) :=
  Measurable.of_eval fun k => measurable_pi_apply (n + k)

lemma normalizing_factor (n : ℕ) : (2 : ℝ≥0∞) ^ n * (1 / 2 : ℝ≥0∞) ^ n = 1 := by
  rw [← mul_pow]
  norm_num [ENNReal.mul_inv_cancel]

/-- The normalized restriction to one prefix fiber. -/
def conditional {n : ℕ} (s : Word n) : Measure cantor_space :=
  (2 : ℝ≥0∞) ^ n • fairCoinProduct.restrict (cell s)

lemma conditional_apply {n : ℕ} (s : Word n) {A : Set cantor_space}
    (hA : MeasurableSet A) :
    conditional s A = (2 : ℝ≥0∞) ^ n * fairCoinProduct (A ∩ cell s) := by
  rw [conditional, Measure.smul_apply, Measure.restrict_apply hA]
  rfl

instance {n : ℕ} (s : Word n) : IsProbabilityMeasure (conditional s) where
  measure_univ := by
    rw [conditional_apply s MeasurableSet.univ, univ_inter, cell_mass, normalizing_factor]

lemma conditional_fiber {n : ℕ} (s : Word n) : conditional s (cell s) = 1 := by
  rw [conditional_apply s (show MeasurableSet (cell s) from levelEvent_measurable _), inter_self, cell_mass, normalizing_factor]

/-- The probability-valued kernel is measurable because the base is finite. -/
def kernel (n : ℕ) (s : Word n) : ProbabilityMeasure cantor_space := ⟨conditional s, inferInstance⟩

lemma kernel_measurable (n : ℕ) : Measurable (kernel n) := measurable_of_countable _

lemma prefix_mass {n : ℕ} (s : Word n) :
    (fairCoinProduct.map (prefixMap n)) {s} = (1 / 2 : ℝ≥0∞) ^ n := by
  rw [Measure.map_apply (prefixMap_measurable n) (measurableSet_singleton s)]
  exact cell_mass s

lemma cells_disjoint (n : ℕ) : Pairwise (Disjoint on (@cell n)) := by
  intro s t hst
  apply disjoint_left.mpr
  intro x hs ht
  exact hst (hs.symm.trans ht)

lemma cells_cover (n : ℕ) : (⋃ s : Word n, cell s) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨prefixMap n x, rfl⟩

lemma disintegration_sum (n : ℕ) {A : Set cantor_space} (hA : MeasurableSet A) :
    ∑ s : Word n, (1 / 2 : ℝ≥0∞) ^ n * conditional s A = fairCoinProduct A := by
  have hn : (1 / 2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ n = 1 := by
    rw [mul_comm, normalizing_factor]
  simp_rw [conditional_apply _ hA, ← mul_assoc, hn, one_mul]
  have hd : Pairwise (Disjoint on fun s : Word n => A ∩ cell s) := by
    intro s t hst
    exact (cells_disjoint n hst).mono inter_subset_right inter_subset_right
  have h := measure_iUnion (μ := fairCoinProduct) hd
    (fun s => hA.inter (levelEvent_measurable {s}))
  simpa only [← inter_iUnion, cells_cover, inter_univ, tsum_fintype] using h.symm

lemma disintegration_integral (n : ℕ) {A : Set cantor_space} (hA : MeasurableSet A) :
    ∫⁻ s, (kernel n s : Measure cantor_space) A ∂fairCoinProduct.map (prefixMap n) =
      fairCoinProduct A := by
  rw [lintegral_fintype]
  simp_rw [prefix_mass, mul_comm]
  exact disintegration_sum n hA

/-- The full conditional identity, on every subset of the finite observation space. -/
theorem conditional_identity (n : ℕ) {A : Set cantor_space} (hA : MeasurableSet A)
    (D : Set (Word n)) :
    ∫⁻ s in D, (kernel n s : Measure cantor_space) A ∂fairCoinProduct.map (prefixMap n) =
      fairCoinProduct (A ∩ prefixMap n ⁻¹' D) := by
  exact DisintegrationFibers.identity_of_fiber fairCoinProduct (prefixMap n) (kernel n)
    (prefixMap_measurable n) (Filter.Eventually.of_forall (conditional_fiber ·))
    (fun _ hB => disintegration_integral n hB) A D hA (Set.toFinite D).measurableSet

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The cylinder $\cyl{s}$ has measure $2^{-n}$, so the normalized restriction $\lambda_s$ is a probability measure
    concentrated on that cylinder. The map $s\mapsto\lambda_s$ is measurable because its domain is finite.
    Since the length-$n$ cylinders form a disjoint partition,
    $$\sum_{s\in\funcspace{n}{2}}2^{-n}\lambda_s(A)
    =\sum_{s\in\funcspace{n}{2}}\lambda(A\cap\cyl{s})=\lambda(A).$$
    The fiber concentration and this identity give the full conditional identity by the argument in
    §{sec:disintegration}; on the finite base its integral is the displayed weighted sum.
-/
/-- The conditional identity is the weighted sum over the selected prefix cells. -/
lemma conditional_sum (n : ℕ) {A : Set cantor_space} (hA : MeasurableSet A)
    (D : Finset (Word n)) :
    ∑ s ∈ D, (1 / 2 : ℝ≥0∞) ^ n * conditional s A =
      fairCoinProduct (A ∩ prefixMap n ⁻¹' (D : Set (Word n))) := by
  rw [← conditional_identity n hA (D : Set (Word n)), lintegral_finset]
  apply Finset.sum_congr rfl
  intro s _
  rw [prefix_mass, mul_comm]
  rfl

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Finally, uniqueness in the disintegration theorem holds outside a $\nu_n$-null set. Each singleton has positive
    $\nu_n$-measure, so that null set is empty: the conditional probability is determined at every prefix.
-/
/-- Uniqueness holds at every prefix, since each prefix has positive mass. -/
theorem kernel_unique (n : ℕ) (q : Word n → ProbabilityMeasure cantor_space)
    (hfiber : ∀ᵐ s ∂fairCoinProduct.map (prefixMap n), (q s : Measure cantor_space) (cell s) = 1)
    (hint : ∀ A, MeasurableSet A →
      ∫⁻ s, (q s : Measure cantor_space) A ∂fairCoinProduct.map (prefixMap n) = fairCoinProduct A) :
    kernel n = q := by
  have h := DisintegrationFibers.ae_unique fairCoinProduct (prefixMap n) (kernel n)
    (kernel_measurable n) (prefixMap_measurable n) q (measurable_of_countable _)
    (Filter.Eventually.of_forall (conditional_fiber ·)) hfiber
    (fun _ hA => disintegration_integral n hA) hint
  funext s
  apply (ae_iff_of_countable.mp h) s
  rw [prefix_mass]
  exact (ENNReal.pow_pos (by norm_num) n).ne'

lemma cylinders_pi : IsPiSystem {U : Set cantor_space | ∃ s : List Bool, U = cyl s} := by
  rintro U ⟨s, rfl⟩ V ⟨t, rfl⟩ ⟨x, hxs, hxt⟩
  have nest {s t : List Bool} (hs : x ∈ cyl s) (ht : x ∈ cyl t) (hle : s.length ≤ t.length) :
      cyl t ⊆ cyl s := by
    intro y hy i hi
    exact (hy i (lt_of_lt_of_le hi hle)).trans
      ((ht i (lt_of_lt_of_le hi hle)).symm.trans (hs i hi))
  rcases le_total s.length t.length with h | h
  · exact ⟨t, inter_eq_right.mpr (nest hxs hxt h)⟩
  · exact ⟨s, inter_eq_left.mpr (nest hxt hxs h)⟩

/-- Two finite Borel measures agreeing on all prefix cylinders agree everywhere. -/
lemma measure_ext_cyl {μ ν : Measure cantor_space} [IsFiniteMeasure μ]
    (h : ∀ t : List Bool, μ (cyl t) = ν (cyl t)) : μ = ν := by
  refine Measure.ext_of_generateFrom_of_iUnion (μ := μ) (ν := ν)
    {U : Set cantor_space | ∃ s : List Bool, U = cyl s} (fun _ => univ) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [@BorelSpace.measurable_eq cantor_space _ _ _]
    exact isTopologicalBasis_cyl.borel_eq_generateFrom
  · exact cylinders_pi
  · exact iUnion_const univ
  · intro _
    exact ⟨[], cyl_nil.symm⟩
  · intro _
    exact measure_ne_top _ _
  · rintro _ ⟨t, rfl⟩
    exact h t

lemma tail_cylinder_inter {n : ℕ} (s : Word n) (t : List Bool) :
    tailMap n ⁻¹' cyl t ∩ cell s = cyl (concat (List.ofFn s) t) := by
  ext x
  rw [mem_cyl_concat_iff, ← cell_eq_cyl]
  simp only [mem_inter_iff, mem_preimage, List.length_ofFn]
  exact and_comm

lemma conditional_tail_cylinder {n : ℕ} (s : Word n) (t : List Bool) :
    (conditional s).map (tailMap n) (cyl t) = fairCoinProduct (cyl t) := by
  rw [Measure.map_apply (tailMap_measurable n) (isOpen_cyl t).measurableSet,
    conditional_apply s ((tailMap_measurable n) (isOpen_cyl t).measurableSet),
    tail_cylinder_inter, fairCoinProduct_cyl, fairCoinProduct_cyl]
  simp only [concat, List.length_append, List.length_ofFn, pow_add]
  rw [← mul_assoc, normalizing_factor, one_mul]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    To identify the tail law, take a finite binary word $t$. Directly from the definition of a cylinder,
    $$\cyl{s}\cap\SequenceTailMap{n}^{-1}(\cyl{t})=\cyl{s\concat t}.$$
    Consequently
    $$\begin{aligned}
    \lambda_s(\SequenceTailMap{n}^{-1}(\cyl{t}))
    &=2^n\lambda(\cyl{s\concat t})\\
    &=2^n2^{-(n+|t|)}=2^{-|t|}=\lambda(\cyl{t}).
    \end{aligned}$$
    Two cylinders with nonempty intersection are nested, so the cylinders together with $\emptyset$ form a
    $\pi$-system. They generate the
    Borel sets and include the whole space. Uniqueness of finite measures on a generating $\pi$-system therefore
    extends the equality to every Borel set.
-/
/-- Removing the fixed prefix restores exactly the fair-coin product measure. -/
theorem conditional_tail {n : ℕ} (s : Word n) :
    (conditional s).map (tailMap n) = fairCoinProduct :=
  measure_ext_cyl (conditional_tail_cylinder s)

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: proposition
  title: Conditional measures on cylinders
-/
/-- The concrete disintegration of fair-coin measure along its prefix projection. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The finite cylinder partitions give an explicit instance of disintegration.
-/
theorem prefix_disintegration (n : ℕ) :
    Measurable (kernel n) ∧
      (∀ s : Word n, (kernel n s : Measure cantor_space) (cell s) = 1) ∧
      (∀ A : Set cantor_space, MeasurableSet A → ∀ D : Set (Word n),
        ∫⁻ s in D, (kernel n s : Measure cantor_space) A ∂fairCoinProduct.map (prefixMap n) =
          fairCoinProduct (A ∩ prefixMap n ⁻¹' D)) ∧
      ∀ s : Word n, (kernel n s : Measure cantor_space).map (tailMap n) = fairCoinProduct :=
  ⟨kernel_measurable n, conditional_fiber, fun _ hA D => conditional_identity n hA D,
    conditional_tail⟩

end PolishSpaceBook.CylinderDisintegration
