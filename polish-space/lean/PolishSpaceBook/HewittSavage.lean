module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import PolishSpaceBook.BorelMeasuresPolishSpaces

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The finite-block proof of Hewitt--Savage

The two copies of a finite-coordinate approximation are separated by the
explicit block permutation used in the book. No ergodicity hypothesis is
assumed.
-/

namespace PolishSpaceBook

noncomputable section
open MeasureTheory ProbabilityTheory MeasurableSpace Set Function Filter Topology
open scoped symmDiff ENNReal

/-- The permutation exchanging two adjacent blocks of length `N`. -/
def swapBlocksFun (N n : ℕ) : ℕ :=
  if n < N then n + N else if n < 2 * N then n - N else n

lemma swapBlocksFun_involutive (N : ℕ) : Involutive (swapBlocksFun N) := by
  intro n
  unfold swapBlocksFun
  split_ifs <;> omega

def swapBlocks (N : ℕ) : Equiv.Perm ℕ :=
  ⟨swapBlocksFun N, swapBlocksFun N, swapBlocksFun_involutive N, swapBlocksFun_involutive N⟩

lemma swapBlocks_apply_small (N n : ℕ) (h : n < N) :
    swapBlocks N n = n + N := by simp [swapBlocks, swapBlocksFun, h]

lemma swapBlocks_apply_large (N n : ℕ) (h : 2 * N ≤ n) :
    swapBlocks N n = n := by
  simp [swapBlocks, swapBlocksFun, show ¬ n < N by omega, show ¬ n < 2 * N by omega]

lemma swapBlocks_finite_support (N : ℕ) :
    {n | swapBlocks N n ≠ n}.Finite := by
  apply (Finset.range (2 * N)).finite_toSet.subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hn (swapBlocks_apply_large N n (by omega))

variable {X : Type*} [MeasurableSpace X]

/-- Finite measurable cylinders form the generating algebra. -/
lemma measurableCylinders_isSetRing : IsSetRing (measurableCylinders (fun _ : ℕ => X)) where
  empty_mem := empty_mem_measurableCylinders _
  union_mem := by
    intro s t hs ht
    exact union_mem_measurableCylinders hs ht
  sdiff_mem := by
    intro s t hs ht
    exact sdiff_mem_measurableCylinders hs ht

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: lemma
  title: Approximation by a generating algebra
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $\mathcal R$ be the class of sets in $\mathcal F$ with the approximation property.
    It contains $\mathcal A$. Taking complements preserves the symmetric difference, so $\mathcal R$ is closed
    under complements.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $E_n\in\mathcal R$ be pairwise disjoint and fix $\varepsilon>0$.
    Choose numbers $\delta_n>0$ with $\sum_n\delta_n<\varepsilon/2$, and choose $B_n\in\mathcal A$ such that
    $$\mu(\SymmetricDifference{E_n}{B_n})<\delta_n.$$
    Continuity from above for the decreasing tails gives $N$ with
    $$\mu\!\left(\bigcup_{n\ge N}E_n\right)<\varepsilon/2.$$
    Put $B:=\bigcup_{n<N}B_n\in\mathcal A$. The symmetric difference between $B$ and $\bigcup_nE_n$ is contained
    in the union of the first $N$ approximation errors and the remaining tail. Hence
    $$\begin{aligned}
    \mu\!\left(\SymmetricDifference{B}{\bigcup_nE_n}\right)
    &\le\sum_{n<N}\mu(\SymmetricDifference{B_n}{E_n})
      +\mu\!\left(\bigcup_{n\ge N}E_n\right)\\
    &<\varepsilon/2+\varepsilon/2=\varepsilon.
    \end{aligned}$$
    Thus $\mathcal R$ is a Dynkin system containing the algebra $\mathcal A$, which is a $\pi$-system.
    The \termuseas{Dynkin pi-lambda theorem}{Dynkin $\pi$--$\lambda$ theorem} gives
    $\mathcal F=\sigma(\mathcal A)\IncludedIn\mathcal R$.
-/
/-- The generating-algebra approximation lemma, with the book's closure
argument. The disjoint-union induction and measure-continuity lemmas are
standard measure infrastructure; the approximating sets are constructed here. -/
theorem generating_algebra_approximation {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {C : Set (Set Ω)}
    (hC : IsSetRing C) (huniv : univ ∈ C) (hgen : m = generateFrom C)
    {A : Set Ω} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B ∈ C, μ (B ∆ A) < ε := by
  classical
  apply DynkinPiLambda.induction_on_inter
    (C := fun A => ∀ ε : ℝ≥0∞, 0 < ε → ∃ B ∈ C, μ (B ∆ A) < ε)
    hgen hC.isSetSemiring.isPiSystem ?_ ?_ ?_ ?_ A hA ε hε
  · intro ε hε
    exact ⟨∅, hC.empty_mem, by simpa using hε⟩
  · intro A hAC ε hε
    exact ⟨A, hAC, by simpa using hε⟩
  · intro A _ ih ε hε
    obtain ⟨B, hBC, herr⟩ := ih ε hε
    refine ⟨Bᶜ, ?_, ?_⟩
    · have heq : univ \ B = Bᶜ := by
        ext x
        exact ⟨fun h => h.2, fun h => ⟨mem_univ x, h⟩⟩
      rw [← heq]
      exact hC.sdiff_mem huniv hBC
    · simpa only [compl_symmDiff_compl] using herr
  · intro A hdis hmeas ih ε hε
    obtain ⟨δ, hδpos, hδsum⟩ :=
      ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos hε.ne').ne' ℕ
    choose B hBC herr using fun i => ih i (δ i) (hδpos i)
    have htail : Tendsto (fun n => μ (⋃ i ∈ Ici n, A i)) atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i => (hmeas i).nullMeasurableSet) hdis
    obtain ⟨n, hn⟩ := ((tendsto_order.mp htail).2 (ε / 2)
      (ENNReal.half_pos hε.ne')).exists
    refine ⟨⋃ i ∈ Finset.range n, B i, hC.biUnion_mem _ (fun i _ => hBC i), ?_⟩
    have hsub : (⋃ i ∈ Finset.range n, B i) ∆ (⋃ i, A i) ⊆
        (⋃ i ∈ Finset.range n, B i ∆ A i) ∪ ⋃ i ∈ Ici n, A i := by
      intro x hx
      simp only [Finset.mem_range, mem_symmDiff, mem_iUnion, exists_prop,
        not_exists, not_and, mem_Ici, mem_union] at hx ⊢
      grind
    calc
      μ ((⋃ i ∈ Finset.range n, B i) ∆ (⋃ i, A i))
        ≤ μ ((⋃ i ∈ Finset.range n, B i ∆ A i) ∪ ⋃ i ∈ Ici n, A i) := measure_mono hsub
      _ ≤ μ (⋃ i ∈ Finset.range n, B i ∆ A i) + μ (⋃ i ∈ Ici n, A i) := measure_union_le _ _
      _ ≤ (∑ i ∈ Finset.range n, μ (B i ∆ A i)) + μ (⋃ i ∈ Ici n, A i) :=
        add_le_add (measure_biUnion_finset_le (μ := μ) (Finset.range n) (fun i => B i ∆ A i)) le_rfl
      _ ≤ (∑ i ∈ Finset.range n, δ i) + μ (⋃ i ∈ Ici n, A i) := by
        exact add_le_add (Finset.sum_le_sum (fun i _ => (herr i).le)) le_rfl
      _ ≤ (∑' i, δ i) + μ (⋃ i ∈ Ici n, A i) :=
        add_le_add (ENNReal.sum_le_tsum (Finset.range n)) le_rfl
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hδsum hn
      _ = ε := ENNReal.add_halves ε

/-- Approximation in measure by a single finite-coordinate event. -/
theorem finite_coordinate_approximation (μ : Measure (ℕ → X)) [IsFiniteMeasure μ]
    {A : Set (ℕ → X)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (I : Finset ℕ) (S : Set (I → X)), MeasurableSet S ∧
      μ (A ∆ cylinder I S) < ε := by
  obtain ⟨B, hB, hdist⟩ := generating_algebra_approximation μ
    measurableCylinders_isSetRing (univ_mem_measurableCylinders _)
    (generateFrom_measurableCylinders (α := fun _ : ℕ => X)).symm hA hε
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hB
  exact ⟨I, S, hS, by simpa [symmDiff_comm] using hdist⟩

/-- Reindexing the iid product by a permutation preserves its measure. -/
theorem iid_permutation_measurePreserving (ν : Measure X) [IsProbabilityMeasure ν]
    (σ : Equiv.Perm ℕ) :
    MeasurePreserving (fun x : ℕ → X => x ∘ σ)
      (Measure.infinitePi (fun _ : ℕ => ν)) (Measure.infinitePi (fun _ : ℕ => ν)) := by
  exact ⟨by fun_prop, Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν) σ.injective⟩

/-- A cylinder and its permuted copy depend on disjoint coordinates. -/
theorem iid_cylinder_independent_copy (ν : Measure X) [IsProbabilityMeasure ν]
    (I : Finset ℕ) (S : Set (I → X)) (hS : MeasurableSet S)
    (σ : Equiv.Perm ℕ) (hdis : Disjoint I (I.image σ)) :
    let μ := Measure.infinitePi (fun _ : ℕ => ν)
    let B : Set (ℕ → X) := cylinder I S
    μ (B ∩ (fun x : ℕ → X => x ∘ σ) ⁻¹' B) = μ B * μ B := by
  classical
  dsimp only
  let J := I.image σ
  let r : (J → X) → (I → X) := fun x i => x ⟨σ i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  have hr : Measurable r := by fun_prop
  have hind := (iIndepFun_infinitePi (P := fun _ : ℕ => ν)
    (X := fun _ (x : X) => x) (by fun_prop)).indepFun_finset I J hdis (by fun_prop)
  have h := hind.measure_inter_preimage_eq_mul S (r ⁻¹' S) hS (hS.preimage hr)
  change _ = _ * (Measure.infinitePi (fun _ : ℕ => ν))
    ((fun x : ℕ → X => x ∘ σ) ⁻¹' cylinder I S) at h
  rw [(iid_permutation_measurePreserving ν σ).measure_preimage (MeasurableSet.cylinder I hS).nullMeasurableSet] at h
  exact h

/-- The real-valued form of the symmetric-difference error bound. -/
lemma measureReal_abs_sub_le_symmDiff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real A - μ.real B| ≤ μ.real (A ∆ B) := by
  have h₁ := MeasuredSets.real_sub_real_le_dist (μ := μ) ⟨A, hA⟩ ⟨B, hB⟩
  have h₂ := MeasuredSets.real_sub_real_le_dist (μ := μ) ⟨B, hB⟩ ⟨A, hA⟩
  change μ.real A - μ.real B ≤ μ.real (A ∆ B) at h₁
  change μ.real B - μ.real A ≤ μ.real (B ∆ A) at h₂
  rw [symmDiff_comm B A] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Combine the two approximations using $A = A \cap A$ and
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    with $S=T=A$, $S'=B$, and $T'=\sigma^*(B)$:
    $$
    \begin{aligned}
    |\mu(A) - \mu(B \cap \sigma^*(B))|
    &= |\mu(A \cap A) - \mu(B \cap \sigma^*(B))|\\
    &\le \mu(A \triangle B) + \mu(A \triangle \sigma^*(B))\\
    &< 2\varepsilon.
    \end{aligned}
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Also $|\mu(A) - \mu(B)| < \varepsilon$, hence $|\mu(A)^2 - \mu(B)^2| < 2\varepsilon$ since both are in $[0, 1]$.
    Therefore
    $$|\mu(A) - \mu(A)^2| \;\le\; |\mu(A) - \mu(B)^2| + |\mu(B)^2 - \mu(A)^2| \;<\; 2\varepsilon + 2\varepsilon =
    4\varepsilon.$$
    Letting $\varepsilon \to 0$ gives $\mu(A) = \mu(A)^2$, so $\mu(A) \in \{0, 1\}$.
-/
/-- Two independent approximations force the measure of the event to equal
its square. This is the error estimate in the finite-block argument. -/
theorem zero_one_of_independent_approximations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : MeasurableSet A)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ B C : Set Ω,
      MeasurableSet B ∧ MeasurableSet C ∧
      μ.real (A ∆ B) < ε ∧ μ.real (A ∆ C) < ε ∧
      μ (B ∩ C) = μ B * μ B) : μ A = 0 ∨ μ A = 1 := by
  have ha0 : 0 ≤ μ.real A := measureReal_nonneg
  have ha1 : μ.real A ≤ 1 := measureReal_le_one
  have heq : μ.real A = μ.real A ^ 2 := by
    apply eq_of_abs_sub_nonpos
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨B, C, hB, hC, hAB, hAC, hind⟩ := happrox (ε / 4) (by positivity)
    have hb0 : 0 ≤ μ.real B := measureReal_nonneg
    have hb1 : μ.real B ≤ 1 := measureReal_le_one
    have hab := measureReal_abs_sub_le_symmDiff μ hA hB
    have hab' : |μ.real A - μ.real B| < ε / 4 := hab.trans_lt hAB
    have hi : μ.real (A ∆ (B ∩ C)) < ε / 2 := by
      have hsub : A ∆ (B ∩ C) ⊆ (A ∆ B) ∪ (A ∆ C) := by
        simpa only [inter_self] using inter_symmDiff_subset_union_symmDiff A A B C
      have := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
      linarith
    have hreal : μ.real (B ∩ C) = μ.real B ^ 2 := by
      simp only [measureReal_def, hind, ENNReal.toReal_mul, pow_two]
    have hi' := (measureReal_abs_sub_le_symmDiff μ hA (hB.inter hC)).trans_lt hi
    rw [hreal] at hi'
    have hsquare : |μ.real A ^ 2 - μ.real B ^ 2| < ε / 2 := by
      rw [sq_sub_sq, abs_mul]
      have hsum : |μ.real A + μ.real B| ≤ 2 := by
        rw [abs_of_nonneg (by positivity)]; linarith
      nlinarith [abs_nonneg (μ.real A - μ.real B), abs_nonneg (μ.real A + μ.real B)]
    have htri := abs_sub_le (μ.real A) (μ.real B ^ 2) (μ.real A ^ 2)
    rw [abs_sub_comm (μ.real B ^ 2) (μ.real A ^ 2)] at htri
    linarith
  have hroot : μ.real A = 0 ∨ μ.real A = 1 := by
    have : μ.real A * (μ.real A - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hroot with h | h
  · left
    exact (ENNReal.toReal_eq_zero_iff (μ A)).mp h |>.resolve_right (measure_ne_top μ A)
  · right
    exact (ENNReal.toReal_eq_one_iff (μ A)).mp h

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Hewitt--Savage 0-1 law
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Apply the generating-algebra approximation lemma to $\mathcal A_\infty$. For every
    $\varepsilon > 0$ there exist $N$ and $B \in \mathcal A_N$ with $\mu(A \triangle B) < \varepsilon$.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $\sigma$ be the permutation of $\omega$ swapping the blocks $\{0, 1, \ldots, N-1\}$ and $\{N, N+1, \ldots, 2N-1\}$
    and fixing all other coordinates. Define the Borel automorphism $\sigma^* : \seqPower{X_0}{\omega} \to
    \seqPower{X_0}{\omega}$ by $\sigma^*(x)_n = x_{\sigma(n)}$. Since $\mu$ is i.i.d., $\sigma^*$ is measure-preserving.
    Since $A$ is permutation-invariant, $\sigma^*(A) = A$.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Apply $\sigma^*$ to the approximation:
    $$\mu(A \triangle \sigma^*(B)) = \mu(\sigma^*(A) \triangle \sigma^*(B)) = \mu(\sigma^*(A \triangle B)) = \mu(A \triangle
    B) < \varepsilon.$$
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Now $B \in \mathcal A_N$ depends on coordinates $0, \ldots, N-1$, while $\sigma^*(B)$ depends on coordinates $N, \ldots,
    2N-1$. These two coordinate blocks are independent under the i.i.d. product, so
    $$\mu(B \cap \sigma^*(B)) = \mu(B)\mu(\sigma^*(B)) = \mu(B)^2.$$
-/
/-- Hewitt--Savage, proved by the book's adjacent-block exchange and
symmetric-difference estimates. The proof works for any measurable base. -/
theorem hewitt_savage_zero_one (ν : Measure X) [IsProbabilityMeasure ν]
    {A : Set (ℕ → X)} (hA : MeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm ℕ, {n | σ n ≠ n}.Finite →
      ∀ x : ℕ → X, x ∘ σ ∈ A ↔ x ∈ A) :
    (Measure.infinitePi (fun _ : ℕ => ν)) A = 0 ∨
      (Measure.infinitePi (fun _ : ℕ => ν)) A = 1 := by
  classical
  let μ := Measure.infinitePi (fun _ : ℕ => ν)
  apply zero_one_of_independent_approximations μ hA
  intro ε hε
  obtain ⟨I, S, hS, happ⟩ := finite_coordinate_approximation μ hA (ENNReal.ofReal_pos.mpr hε)
  let N := I.sup id + 1
  let σ := swapBlocks N
  let T : (ℕ → X) → (ℕ → X) := fun x => x ∘ σ
  let B : Set (ℕ → X) := cylinder I S
  have hB : MeasurableSet B := MeasurableSet.cylinder I hS
  have hT : MeasurePreserving T μ μ := iid_permutation_measurePreserving ν σ
  have hTA : T ⁻¹' A = A := by
    ext x
    exact hinv σ (swapBlocks_finite_support N) x
  have hdist : μ.real (A ∆ B) < ε := ENNReal.toReal_lt_of_lt_ofReal happ
  have hcopy : μ.real (A ∆ (T ⁻¹' B)) < ε := by
    rw [← hTA, ← preimage_symmDiff, hT.measureReal_preimage (hA.symmDiff hB).nullMeasurableSet]
    exact hdist
  have hbound : ∀ i ∈ I, i < N := by
    intro i hi
    have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
    dsimp [N]
    omega
  have hdis : Disjoint I (I.image σ) := by
    apply Finset.disjoint_left.mpr
    intro j hj hjs
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hjs
    have hiN := hbound i hi
    have hjN := hbound j hj
    have hσ : σ i = i + N := swapBlocks_apply_small N i hiN
    omega
  exact ⟨B, T ⁻¹' B, hB, hB.preimage hT.measurable, hdist, hcopy,
    iid_cylinder_independent_copy ν I S hS σ hdis⟩

end
end PolishSpaceBook
