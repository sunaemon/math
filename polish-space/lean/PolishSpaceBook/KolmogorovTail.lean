module

public import PolishSpaceBook.DynkinPiLambda
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Order.LiminfLimsup

@[expose] public section

/-!
# The prefix-algebra proof of Kolmogorov's zero-one law

Prefix events form a generating pi-system. Independence from every prefix is
extended by the pi-lambda argument, then applied to the tail event itself.
The final specialization uses the actual coordinates of an infinite product.
-/

noncomputable section

namespace PolishSpaceBook.KolmogorovTail

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Function
open scoped ENNReal

variable {Ω : Type*}

/-- Events observable in the first `N` coordinates. -/
abbrev prefixSigma (s : ℕ → MeasurableSpace Ω) (N : ℕ) : MeasurableSpace Ω := ⨆ n < N, s n

/-- Events observable from coordinate `N` onward. -/
abbrev tailFrom (s : ℕ → MeasurableSpace Ω) (N : ℕ) : MeasurableSpace Ω := ⨆ n ≥ N, s n

/-- The book's tail sigma-algebra. -/
abbrev tail (s : ℕ → MeasurableSpace Ω) : MeasurableSpace Ω := ⨅ N, tailFrom s N

lemma tail_eq_limsup (s : ℕ → MeasurableSpace Ω) : tail s = limsup s atTop :=
  limsup_eq_iInf_iSup_of_nat.symm

lemma prefix_mono (s : ℕ → MeasurableSpace Ω) : Monotone (prefixSigma s) := by
  intro N M hNM
  exact iSup₂_le fun n hn => le_iSup_of_le n (le_iSup_of_le (lt_of_lt_of_le hn hNM) le_rfl)

lemma prefix_le_iSup (s : ℕ → MeasurableSpace Ω) (N : ℕ) : prefixSigma s N ≤ ⨆ n, s n :=
  iSup₂_le fun n _ => le_iSup s n

lemma tail_le_iSup (s : ℕ → MeasurableSpace Ω) : tail s ≤ ⨆ n, s n :=
  (iInf_le _ 0).trans (iSup₂_le fun n _ => le_iSup s n)

/-- The union of the increasing prefix sigma-algebras, regarded as sets of events. -/
def prefixEvents (s : ℕ → MeasurableSpace Ω) : Set (Set Ω) :=
  {B | ∃ N, MeasurableSet[prefixSigma s N] B}

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The prefix $\sigma$-algebras increase with $N$. If $B\in\mathcal A_N$ and $C\in\mathcal A_M$, then
    $B\cap C\in\mathcal A_{\max\{N,M\}}$, and $B^c\in\mathcal A_N$. Thus $\mathcal A_\infty$ is an algebra,
    in particular a $\pi$-system. It generates the full Borel $\sigma$-algebra of $X$, since it contains every
    coordinate \termuse{cylinder} and is contained in the product $\sigma$-algebra.
-/
lemma prefixEvents_pi (s : ℕ → MeasurableSpace Ω) : IsPiSystem (prefixEvents s) := by
  rintro B ⟨N, hB⟩ C ⟨M, hC⟩ _
  exact ⟨max N M, ((prefix_mono s (le_max_left N M)) B hB).inter
    ((prefix_mono s (le_max_right N M)) C hC)⟩

lemma prefixEvents_generate (s : ℕ → MeasurableSpace Ω) :
    (⨆ n, s n) = generateFrom (prefixEvents s) := by
  apply le_antisymm
  · refine iSup_le fun n B hB => measurableSet_generateFrom ?_
    have hn : s n ≤ prefixSigma s (n + 1) :=
      le_iSup_of_le n (le_iSup_of_le (Nat.lt_succ_self n) le_rfl)
    exact ⟨n + 1, hn B hB⟩
  · apply generateFrom_le
    rintro B ⟨N, hB⟩
    exact prefix_le_iSup s N B hB

section Independent

variable [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (s : ℕ → MeasurableSpace Ω) (hle : ∀ n, s n ≤ m) (hind : iIndep s μ)

include hle hind

omit [IsProbabilityMeasure μ] in
lemma prefix_tail_indep (N : ℕ) : Indep (prefixSigma s N) (tailFrom s N) μ := by
  have hd : Disjoint (Iio N) (Ici N) := disjoint_left.mpr fun n hn hn' => Nat.not_lt_of_ge hn' hn
  exact indep_iSup_of_disjoint hle hind hd

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Now put
    $$\mathcal D := \{B \in \mathrm{Borel}(X) : \mu(A \cap B) = \mu(A)\mu(B)\}.$$
    This class contains $X$. If $B\in\mathcal D$, then
    $$
    \begin{aligned}
    \mu(A\cap B^c)
    &=\mu(A)-\mu(A\cap B)\\
    &=\mu(A)(1-\mu(B))\\
    &=\mu(A)\mu(B^c),
    \end{aligned}
    $$
    so $B^c\in\mathcal D$.

    If $B_n\in\mathcal D$ are pairwise disjoint, countable additivity gives
    $$
    \begin{aligned}
    \mu\Bigl(A\cap\bigcup_n B_n\Bigr)
    &=\sum_n\mu(A\cap B_n)\\
    &=\mu(A)\sum_n\mu(B_n)\\
    &=\mu(A)\mu\Bigl(\bigcup_n B_n\Bigr).
    \end{aligned}
    $$
    Hence $\bigcup_n B_n\in\mathcal D$, and $\mathcal D$ is a Dynkin system containing $\mathcal A_\infty$.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For each $N$, write $\mathcal A_N := \sigma(\pi_0, \ldots, \pi_{N-1})$ for the prefix
    $\sigma$-algebra and $\mathcal B_N := \sigma(\pi_n : n \ge N)$ for the tail-from-$N$ $\sigma$-algebra. Independence of
    coordinates under the product measure gives
    $$\mu(B \cap C) = \mu(B)\mu(C) \qquad (B \in \mathcal A_N,\, C \in \mathcal B_N).$$
    Let $A \in \mathcal T$. Then $A \in \mathcal B_N$ for every $N$, so for every $B \in \mathcal A_\infty := \bigcup_N
    \mathcal A_N$,
    \begin{equation*}
    \mu(A \cap B) = \mu(A)\mu(B). \tag{$\dagger$}
    \end{equation*}
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    By \termuseas{Dynkin pi-lambda theorem}{Dynkin's $\pi$-$\lambda$ theorem},
    $\mathcal D \supseteq \sigma(\mathcal A_\infty) = \mathrm{Borel}(X)$. Setting $B := A$ in $(\dagger)$ yields
    $\mu(A) = \mu(A)^2$, so $\mu(A) \in \{0, 1\}$.
-/
/-- Extend independence from the prefix algebra to the generated sigma-algebra
by the complement and disjoint-union steps of the pi-lambda argument. -/
theorem tail_independent_of_generated {A : Set Ω} (hA : MeasurableSet[tail s] A)
    {B : Set Ω} (hB : MeasurableSet[⨆ n, s n] B) : μ (A ∩ B) = μ A * μ B := by
  have hfull : (⨆ n, s n) ≤ m := iSup_le hle
  have hAm : MeasurableSet A := hfull A (tail_le_iSup s A hA)
  apply DynkinPiLambda.induction_on_inter (m := ⨆ n, s n)
    (C := fun B => μ (A ∩ B) = μ A * μ B)
    (prefixEvents_generate s) (prefixEvents_pi s) ?_ ?_ ?_ ?_ B hB
  · simp
  · rintro B ⟨N, hBN⟩
    have htail : tail s ≤ tailFrom s N := iInf_le _ N
    have hAN : MeasurableSet[tailFrom s N] A := htail A hA
    have h := (prefix_tail_indep μ s hle hind N).indepSet_of_measurableSet hBN hAN
    simpa only [inter_comm, mul_comm] using h.measure_inter_eq_mul
  · intro B hB ih
    have hBm := hfull B hB
    have hd : A ∩ Bᶜ = A \ (A ∩ B) := by ext x; simp
    rw [hd, measure_sdiff inter_subset_left (hAm.inter hBm).nullMeasurableSet (measure_ne_top _ _),
      ih, measure_compl hBm (measure_ne_top _ _), measure_univ,
      ENNReal.mul_sub (fun _ _ => measure_ne_top μ A), mul_one]
  · intro B hdis hB ih
    have hBm n := hfull (B n) (hB n)
    have hd : Pairwise (Disjoint on fun n => A ∩ B n) := by
      intro i j hij
      exact (hdis hij).mono inter_subset_right inter_subset_right
    rw [inter_iUnion, measure_iUnion hd (fun n => hAm.inter (hBm n))]
    simp_rw [ih]
    rw [ENNReal.tsum_mul_left, measure_iUnion hdis hBm]

/-- The tail event is independent of itself, so its probability is idempotent. -/
theorem zero_one {A : Set Ω} (hA : MeasurableSet[tail s] A) : μ A = 0 ∨ μ A = 1 := by
  have h := tail_independent_of_generated μ s hle hind hA (tail_le_iSup s A hA)
  rw [inter_self] at h
  by_cases h0 : μ A = 0
  · exact Or.inl h0
  · right
    have heq : μ A * 1 = μ A * μ A := by simpa using h
    exact ((ENNReal.mul_right_inj h0 (measure_ne_top μ A)).mp heq).symm

end Independent

section Product

variable {X : ℕ → Type*} [mX : ∀ n, MeasurableSpace (X n)]

/-- The sigma-algebra observed by one coordinate of the product. -/
abbrev coordinateSigma (n : ℕ) : MeasurableSpace (∀ n, X n) :=
  (mX n).comap (fun x => x n)

lemma coordinateSigma_generate :
    (⨆ n, coordinateSigma (X := X) n) = (inferInstance : MeasurableSpace (∀ n, X n)) := rfl

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Kolmogorov 0-1 law
-/
/-- Kolmogorov's law for the actual coordinate tail sigma-algebra of a product
probability measure, proved through the book's prefix-algebra argument. -/
theorem product_zero_one (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)]
    {A : Set (∀ n, X n)} (hA : MeasurableSet[tail (coordinateSigma (X := X))] A) :
    Measure.infinitePi ν A = 0 ∨ Measure.infinitePi ν A = 1 := by
  have hle : ∀ n, coordinateSigma (X := X) n ≤ (inferInstance : MeasurableSpace (∀ n, X n)) :=
    fun n => (measurable_pi_apply n).comap_le
  have hind := (iIndepFun_infinitePi (P := ν)
    (X := fun _ x => x) (fun _ => measurable_id)).iIndep
  exact zero_one (Measure.infinitePi ν) (coordinateSigma (X := X)) hle hind hA

end Product

end PolishSpaceBook.KolmogorovTail
