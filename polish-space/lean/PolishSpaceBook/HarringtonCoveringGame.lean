module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Mathlib.MeasureTheory.Measure.RegularityCompacts

@[expose] public section

/-!
# The covering estimate in Harrington's game

A response strategy is indexed by the finite bit history supplied by I.
Its own earlier responses are determined by that history. Taking every possible
response gives an open cover, with the budget paid once for each bit history.
The theorem excluding a winning strategy for I is an external input.
-/
noncomputable section
namespace PolishSpaceBook.HarringtonCoveringGame
open Set MeasureTheory TopologicalSpace Filter Topology
open scoped ENNReal Classical

abbrev Cantor := ℕ → Bool

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Fix a finite Borel measure $\mu$ on $\CantorSpace$. We use the
    \termdefine{Harrington covering game} from [@Moschovakis2009, 6A.17]. For $B\IncludedIn\CantorSpace$ and
    $\varepsilon>0$, I plays bits, forming $x$, and II replies at round $n$ with a clopen set $G_n$ satisfying
    $$\mu(G_n)\le\varepsilon 2^{-2n-2}.$$
    Clopen sets are coded by integers. Player I wins precisely when
    $$x\in\SetDifference{B}{\bigcup_n G_n}.$$
    The empty clopen set is always a legal response.

    For a fixed strategy $\sigma$ of II, let $G_\sigma(s)$ be its response after I has played the nonempty
    binary string $s$. Earlier responses of II are determined by $s$, so this notation retains the whole relevant
    history. The strategy is winning exactly when
    $$\forall x\in B\ \exists n\in\omega\quad x\in G_\sigma(\restrict{x}{n+1}).$$
-/
/-- Compactness and a countable basis allow integer codes for the clopen moves. -/
instance clopensCountable : Countable (Clopens Cantor) :=
  Clopens.countable_iff_secondCountable.mpr inferInstance

/-- A strategy for II, including the legality of every response. -/
structure Strategy (μ : Measure Cantor) (ε : ℝ≥0∞) where
  response : ∀ n, (Fin (n + 1) → Bool) → Clopens Cantor
  budget : ∀ n h, μ (response n h) ≤ ε * (2⁻¹ : ℝ≥0∞) ^ (2 * n + 2)

/-- Empty responses ensure that legal second-player strategies exist at every budget. -/
def emptyStrategy (μ : Measure Cantor) (ε : ℝ≥0∞) : Strategy μ ε where
  response := fun _ _ => ⊥
  budget := by intros; simp

/-- Against every point of the payoff, some prescribed response catches it. -/
def Winning {μ : Measure Cantor} {ε : ℝ≥0∞} (σ : Strategy μ ε) (B : Set Cantor) : Prop :=
  ∀ x ∈ B, ∃ n, x ∈ σ.response n (fun i => x i)

/-- The union includes all possible histories, not just one play. -/
def cover {μ : Measure Cantor} {ε : ℝ≥0∞} (σ : Strategy μ ε) : Set Cantor :=
  ⋃ n, ⋃ h, (σ.response n h : Set Cantor)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Take the union over all possible bit histories:
    $$U_\sigma:=\bigcup_{n\in\omega}\ \bigcup_{s\in 2^{n+1}}G_\sigma(s).$$
    It is open because the responses are clopen. If $x\in B$, the winning condition gives
    $x\in G_\sigma(\restrict{x}{n+1})$ for some $n$, hence $x\in U_\sigma$. At round $n$ there are
    $2^{n+1}$ histories. Countable subadditivity and the response bounds give
    $$
    \begin{aligned}
    \mu(U_\sigma)
    &\le\sum_{n\in\omega}\ \sum_{s\in 2^{n+1}}\mu(G_\sigma(s))\\
    &\le\sum_{n\in\omega}2^{n+1}\varepsilon 2^{-2n-2}\\
    &=\varepsilon\sum_{n\in\omega}2^{-n-1}=\varepsilon.
    \end{aligned}
    $$
    Thus $\mu^*(B)\le\varepsilon$. Applying this to every positive budget proves the last assertion.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-strategy estimate
-/
lemma cover_isOpen {μ : Measure Cantor} {ε : ℝ≥0∞} (σ : Strategy μ ε) :
    IsOpen (cover σ) :=
  isOpen_iUnion (fun n => isOpen_iUnion (fun h => (σ.response n h).isOpen))

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-strategy estimate
-/
lemma subset_cover {μ : Measure Cantor} {ε : ℝ≥0∞} {σ : Strategy μ ε}
    {B : Set Cantor} (hσ : Winning σ B) : B ⊆ cover σ := by
  intro x hx
  obtain ⟨n, hn⟩ := hσ x hx
  exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨fun i => x i, hn⟩⟩

lemma history_budget (ε : ℝ≥0∞) (n : ℕ) :
    (2 : ℝ≥0∞) ^ (n + 1) * (ε * (2⁻¹ : ℝ≥0∞) ^ (2 * n + 2)) =
      ε * (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
  have hn : 2 * n + 2 = (n + 1) + (n + 1) := by omega
  rw [hn, pow_add (2⁻¹ : ℝ≥0∞)]
  calc
    _ = ε * (((2 : ℝ≥0∞) ^ (n + 1) * (2⁻¹ : ℝ≥0∞) ^ (n + 1)) *
      (2⁻¹ : ℝ≥0∞) ^ (n + 1)) := by ac_rfl
    _ = _ := by rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]; simp

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-strategy estimate
-/
lemma measure_cover_le {μ : Measure Cantor} {ε : ℝ≥0∞} (σ : Strategy μ ε) :
    μ (cover σ) ≤ ε := by
  calc
    μ (cover σ) ≤ ∑' n, μ (⋃ h, (σ.response n h : Set Cantor)) := measure_iUnion_le _
    _ ≤ ∑' n, ∑ h, μ (σ.response n h) :=
      ENNReal.tsum_le_tsum (fun n => measure_iUnion_fintype_le μ _)
    _ ≤ ∑' n, (2 : ℝ≥0∞) ^ (n + 1) * (ε * (2⁻¹ : ℝ≥0∞) ^ (2 * n + 2)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa using Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => σ.budget n h)
    _ = ε := by
      simp_rw [history_budget]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      norm_num only [ENNReal.one_sub_inv_two, inv_inv]
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

lemma measure_le_of_winning {μ : Measure Cantor} {ε : ℝ≥0∞}
    {σ : Strategy μ ε} {B : Set Cantor} (hσ : Winning σ B) : μ B ≤ ε :=
  (measure_mono (subset_cover hσ)).trans (measure_cover_le σ)

/-- Arbitrarily small positive finite budgets force outer measure zero. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Covering-strategy estimate
-/
theorem measure_zero_of_winning {μ : Measure Cantor} {B : Set Cantor}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ε < ∞ → ∃ σ : Strategy μ ε, Winning σ B) : μ B = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_forall_gt
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ := exists_between hε
  obtain ⟨σ, hσ⟩ := h δ hδ0 (hδε.trans_le le_top)
  exact (measure_le_of_winning hσ).trans_lt hδε

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Outer regularity gives open sets $U_n\supseteq A$ with
    $$\mu(U_n)\le\mu^*(A)+2^{-n}.$$
    Put $H:=\bigcap_n U_n$. This is a Borel set containing $A$, and
    $$\mu^*(A)\le\mu(H)\le\mu^*(A)+2^{-n}\qquad(n\in\omega).$$
    Letting $n\to\infty$ gives $\mu(H)=\mu^*(A)$.

    Set $B:=\SetDifference{H}{A}$. If $C\IncludedIn B$ is Borel, then $A\IncludedIn\SetDifference{H}{C}$ and
    $$
    \begin{aligned}
    \mu(H)&=\mu(\SetDifference{H}{C})+\mu(C),\\
    \mu(H)&=\mu^*(A)\le\mu(\SetDifference{H}{C}).
    \end{aligned}
    $$
    Finiteness of $\mu(H)$ forces $\mu(C)=0$. The hypothesis now supplies winning strategies for II on $B$,
    and the covering-strategy estimate gives $\mu^*(B)=0$. The set $B$ is therefore measurable in the completion.
    Since $A=\SetDifference{H}{B}$ and $H$ is Borel, $A$ is measurable in the completion as well.
    \end{proof}
-/
section Hull
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Choose open supersets with errors tending to zero, then intersect them. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Borel hull criterion
-/
theorem exists_open_intersection_hull [TopologicalSpace X] [BorelSpace X] [μ.OuterRegular] (A : Set X) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n) ∧ A ⊆ U n) ∧ μ (⋂ n, U n) = μ A := by
  have he : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n ≠ 0 :=
    fun n => pow_ne_zero n (by norm_num)
  choose U hAU hU hμU using fun n => A.exists_isOpen_le_add μ (he n)
  refine ⟨U, fun n => ⟨hU n, hAU n⟩, le_antisymm ?_ ?_⟩
  · have ht : Tendsto (fun n : ℕ => μ A + (2⁻¹ : ℝ≥0∞) ^ n) atTop (𝓝 (μ A)) := by
      simpa using tendsto_const_nhds.add
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ℝ≥0∞) < 1))
    exact ge_of_tendsto ht (Eventually.of_forall fun n =>
      (measure_mono (iInter_subset U n)).trans (hμU n))
  · exact measure_mono (subset_iInter hAU)

/-- Removing a positive measurable subset of the hull defect would lower its measure. -/
lemma hull_defect_inner_zero [IsFiniteMeasure μ] {A H C : Set X} (hAH : A ⊆ H)
    (hH : μ H = μ A) (hC : MeasurableSet C) (hCH : C ⊆ H \ A) : μ C = 0 := by
  have hCH' : C ⊆ H := fun x hx => (hCH hx).1
  have hAC : A ⊆ H \ C := fun x hx => ⟨hAH hx, fun hc => (hCH hc).2 hx⟩
  have hadd : μ (H \ C) + μ C = μ H := by
    simpa only [inter_eq_right.mpr hCH'] using measure_sdiff_add_inter H hC
  have hle : μ (H \ C) + μ C ≤ μ (H \ C) + 0 := by
    rw [hadd, hH, add_zero]
    exact measure_mono hAC
  exact le_antisymm ((ENNReal.add_le_add_iff_left (measure_ne_top μ _)).mp hle) bot_le

/-- A null defect from a measurable hull gives measurability in the completion. -/
lemma nullMeasurable_of_hull_defect {A H : Set X} (hAH : A ⊆ H)
    (hH : MeasurableSet H) (hnull : μ (H \ A) = 0) : NullMeasurableSet A μ := by
  have h := hH.nullMeasurableSet.diff (NullMeasurableSet.of_null hnull)
  simpa only [sdiff_sdiff_cancel_left hAH] using h

end Hull

/-- Apply the external game input only to the defect of the Borel hull. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Borel hull criterion
-/
theorem nullMeasurable_of_defect_strategies (μ : Measure Cantor) [IsFiniteMeasure μ]
    (A : Set Cantor)
    (hgame : ∀ H : Set Cantor, MeasurableSet H → A ⊆ H →
      (∀ C : Set Cantor, MeasurableSet C → C ⊆ H \ A → μ C = 0) →
      ∀ ε : ℝ≥0∞, 0 < ε → ε < ∞ →
        ∃ σ : Strategy μ ε, Winning σ (H \ A)) : NullMeasurableSet A μ := by
  obtain ⟨U, hU, hμU⟩ := exists_open_intersection_hull μ A
  have hAH : A ⊆ ⋂ n, U n := subset_iInter (fun n => (hU n).2)
  have hH : MeasurableSet (⋂ n, U n) := MeasurableSet.iInter (fun n => (hU n).1.measurableSet)
  apply nullMeasurable_of_hull_defect μ hAH hH
  apply measure_zero_of_winning
  exact hgame _ hH hAH (fun C hC hCH => hull_defect_inner_zero μ hAH hμU hC hCH)

end PolishSpaceBook.HarringtonCoveringGame
