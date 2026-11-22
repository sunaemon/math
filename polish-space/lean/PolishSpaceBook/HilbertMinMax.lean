module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Norm-continuous Hilbert space min–max coordinates

These min–max numbers use the closed unit ball, so their values are
nonnegative and remain defined for zero-dimensional orthogonal complements.
The `n`th coordinate discards subspaces of dimension at most `n`.
They are defined in arbitrary real or complex Hilbert spaces and are
1-Lipschitz in operator norm. Applying the same construction to `-A` supplies
the negative coordinates.

Identifying these coordinates with the ordered, multiplicity-counted positive
eigenvalues of a compact self-adjoint operator is a separate spectral theorem;
it is not assumed or claimed here.
-/

noncomputable section

open Set MeasureTheory

namespace PolishSpaceBook.HilbertMinMax

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Unit vectors of norm at most one in a specified subspace, including zero. -/
abbrev UnitBall (K : Submodule 𝕜 H) := {x : K // ‖x‖ ≤ 1}

instance (K : Submodule 𝕜 H) : Nonempty (UnitBall K) :=
  ⟨⟨0, by simp⟩⟩

private theorem rayleigh_abs_le (A : H →L[𝕜] H) {x : H} (hx : ‖x‖ ≤ 1) :
    |RCLike.re (inner 𝕜 x (A x))| ≤ ‖A‖ := by
  calc
    |RCLike.re (inner 𝕜 x (A x))| ≤ ‖inner 𝕜 x (A x)‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖A‖ * 1) := mul_le_mul hx
      ((A.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))
      (norm_nonneg _) zero_le_one
    _ = ‖A‖ := by ring

private theorem rayleigh_sub_abs_le (A B : H →L[𝕜] H) {x : H} (hx : ‖x‖ ≤ 1) :
    |RCLike.re (inner 𝕜 x (A x)) - RCLike.re (inner 𝕜 x (B x))| ≤ ‖A - B‖ := by
  simpa only [sub_apply, inner_sub_right, map_sub] using
    rayleigh_abs_le (A - B) hx

/-- Maximum positive Rayleigh value over the closed unit ball of a subspace. -/
def rayleighSup (A : H →L[𝕜] H) (K : Submodule 𝕜 H) : ℝ :=
  ⨆ x : UnitBall K, RCLike.re (inner 𝕜 (x.1 : H) (A (x.1 : H)))

private theorem rayleigh_bddAbove (A : H →L[𝕜] H) (K : Submodule 𝕜 H) :
    BddAbove (range (fun x : UnitBall K => RCLike.re (inner 𝕜 (x.1 : H) (A x.1)))) := by
  refine ⟨‖A‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact le_trans (le_abs_self _) (rayleigh_abs_le A x.2)

theorem rayleighSup_nonneg (A : H →L[𝕜] H) (K : Submodule 𝕜 H) :
    0 ≤ rayleighSup A K := by
  unfold rayleighSup
  simpa only [ZeroMemClass.coe_zero, map_zero, inner_zero_left, RCLike.zero_re] using
    le_ciSup (rayleigh_bddAbove A K) (⟨0, by simp⟩ : UnitBall K)

theorem rayleighSup_le_norm (A : H →L[𝕜] H) (K : Submodule 𝕜 H) :
    rayleighSup A K ≤ ‖A‖ := by
  exact ciSup_le (fun x => (le_abs_self _).trans (rayleigh_abs_le A x.2))

theorem rayleighSup_le_add_norm (A B : H →L[𝕜] H) (K : Submodule 𝕜 H) :
    rayleighSup A K ≤ rayleighSup B K + ‖A - B‖ := by
  apply ciSup_le
  intro x
  have h₁ := (abs_le.mp (rayleigh_sub_abs_le A B (x := (x.1 : H)) x.2)).2
  have h₂ := le_ciSup (rayleigh_bddAbove B K) x
  change RCLike.re (inner 𝕜 (x.1 : H) (B x.1)) ≤ rayleighSup B K at h₂
  linarith

/-- The finite-dimensional spaces discarded in the `n`th min–max problem. -/
abbrev Discard (n : ℕ) :=
  {K : Submodule 𝕜 H // FiniteDimensional 𝕜 K ∧ Module.finrank 𝕜 K ≤ n}

instance (n : ℕ) : Nonempty (Discard (𝕜 := 𝕜) (H := H) n) :=
  ⟨⟨⊥, inferInstance, by simp⟩⟩

/-- The nonnegative `n`th min–max number. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{OrthogonalComplement,MinMaxValue}
    \end{mathmeta}
    Work with this norm topology. Write $\OrthogonalComplement{F}$ for the orthogonal complement of a subspace $F$.
    The nonnegative min--max values are
    $$\MinMaxValue{A}{n}:=
    \inf_{\dim F\le n}\ \sup_{\substack{x\in\OrthogonalComplement{F}\\\|x\|\le1}}
    \operatorname{Re}\langle x,Ax\rangle,$$
    where $F$ ranges over finite-dimensional subspaces of $H$.
-/
def minMax (A : H →L[𝕜] H) (n : ℕ) : ℝ :=
  ⨅ K : Discard (𝕜 := 𝕜) (H := H) n, rayleighSup A K.1ᗮ

private theorem minMax_bddBelow (A : H →L[𝕜] H) (n : ℕ) :
    BddBelow (range (fun K : Discard (𝕜 := 𝕜) (H := H) n => rayleighSup A K.1ᗮ)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨K, rfl⟩
  exact rayleighSup_nonneg A K.1ᗮ

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Including $x=0$ makes these values nonnegative,
    even if $H$ is zero-dimensional.
-/
theorem minMax_nonneg (A : H →L[𝕜] H) (n : ℕ) : 0 ≤ minMax A n :=
  le_ciInf (fun K => rayleighSup_nonneg A K.1ᗮ)

theorem minMax_le_rayleighSup (A : H →L[𝕜] H) (n : ℕ)
    (K : Discard (𝕜 := 𝕜) (H := H) n) : minMax A n ≤ rayleighSup A K.1ᗮ :=
  ciInf_le (minMax_bddBelow A n) K

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The values decrease with $n$.
-/
theorem minMax_antitone (A : H →L[𝕜] H) : Antitone (minMax A) := by
  intro n m hnm
  apply le_ciInf
  intro K
  exact minMax_le_rayleighSup A m ⟨K.1, K.2.1, K.2.2.trans hnm⟩

theorem minMax_le_norm (A : H →L[𝕜] H) (n : ℕ) : minMax A n ≤ ‖A‖ := by
  let K : Discard (𝕜 := 𝕜) (H := H) n := ⟨⊥, inferInstance, by simp⟩
  exact (minMax_le_rayleighSup A n K).trans (rayleighSup_le_norm A K.1ᗮ)

theorem rayleighSup_bot (A : H →L[𝕜] H) : rayleighSup A (⊥ : Submodule 𝕜 H) = 0 := by
  apply le_antisymm _ (rayleighSup_nonneg A ⊥)
  apply ciSup_le
  intro x
  have hx : (x.1 : H) = 0 := congrArg
    (fun y : (⊥ : Submodule 𝕜 H) => (y : H)) (Subsingleton.elim x.1 0)
  simp [hx]

/-- Finite-dimensional spaces have zero padding without any nontriviality assumption. -/
theorem minMax_eq_zero_of_finrank_le [FiniteDimensional 𝕜 H]
    (A : H →L[𝕜] H) {n : ℕ} (hn : Module.finrank 𝕜 H ≤ n) :
    minMax A n = 0 := by
  apply le_antisymm _ (minMax_nonneg A n)
  let K : Discard (𝕜 := 𝕜) (H := H) n :=
    ⟨⊤, inferInstance, by simpa using hn⟩
  have h := minMax_le_rayleighSup A n K
  simpa only [K, Submodule.top_orthogonal_eq_bot, rayleighSup_bot] using h

theorem minMax_zero (n : ℕ) : minMax (0 : H →L[𝕜] H) n = 0 := by
  exact le_antisymm (by simpa using minMax_le_norm (0 : H →L[𝕜] H) n)
    (minMax_nonneg 0 n)

theorem minMax_le_add_norm (A B : H →L[𝕜] H) (n : ℕ) :
    minMax A n ≤ minMax B n + ‖A - B‖ := by
  suffices minMax A n - ‖A - B‖ ≤ minMax B n by linarith
  apply le_ciInf
  intro K
  have h₁ := minMax_le_rayleighSup A n K
  have h₂ := rayleighSup_le_add_norm A B K.1ᗮ
  linarith

/-- Dimension-free norm stability of each min–max coordinate. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    For unit-ball vectors, the quadratic forms of $A$ and $B$ differ by at most
    $\|A-B\|$. Taking suprema and infima preserves this bound, so
    $$|\MinMaxValue{A}{n}-\MinMaxValue{B}{n}|\le\|A-B\|.$$
-/
theorem minMax_lipschitz (n : ℕ) :
    LipschitzWith 1 (fun A : H →L[𝕜] H => minMax A n) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply abs_le.mpr
  have h₁ := minMax_le_add_norm A B n
  have h₂ := minMax_le_add_norm B A n
  rw [norm_sub_rev B A] at h₂
  constructor <;> linarith

theorem continuous_minMax (n : ℕ) :
    Continuous (fun A : H →L[𝕜] H => minMax A n) :=
  (minMax_lipschitz n).continuous

/-- Both signed min–max lists vary continuously in the product topology. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Both coordinate lists are therefore continuous for the norm topology.
-/
theorem continuous_signed_minMax :
    Continuous (fun A : H →L[𝕜] H => (minMax A, minMax (-A))) := by
  exact (continuous_pi (fun n => continuous_minMax n)).prodMk
    (continuous_pi (fun n => (continuous_minMax n).comp continuous_neg))

end PolishSpaceBook.HilbertMinMax
