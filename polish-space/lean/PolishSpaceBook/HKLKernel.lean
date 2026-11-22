module

public import PolishSpaceBook.SilverKernel

@[expose] public section

/-!
# The ordinary Borel part of the HKL kernel

A countable sequence of invariant Borel tests gives the auxiliary equivalence
relation and its Cantor-valued complete invariant. Nonsmoothness forces a
nonempty analytic kernel, invariant under the auxiliary relation. The tests
are supplied explicitly. `LambdaInvariantKernel` supplies the actual family
of complemented invariant tests, and `LambdaInvariantClosure` proves the GH
closure identity. `LambdaKernelComplexity` constructs the relative analytic
code and discharges the corresponding hereditary-failure hypothesis.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

variable {X : Type*}

/-- Indistinguishability by the chosen countable family of invariant tests. -/
def invariantTestSetoid (W : ℕ → Set X) : Setoid X where
  r x y := ∀ n, x ∈ W n ↔ y ∈ W n
  iseqv := ⟨fun _ _ => Iff.rfl, fun h n => (h n).symm,
    fun hxy hyz n => (hxy n).trans (hyz n)⟩

theorem relation_le_invariantTestSetoid (E : Setoid X) (W : ℕ → Set X)
    (hW : ∀ n, ERInvariant E (W n)) {x y : X} (hxy : E.r x y) :
    (invariantTestSetoid W).r x y := fun n => hW n hxy

/-- The indicator sequence used in the book. -/
noncomputable def invariantTestCode (W : ℕ → Set X) (x : X) : ℕ → Bool := by
  classical
  exact fun n => if x ∈ W n then true else false

theorem invariantTestCode_complete (W : ℕ → Set X) :
    CompleteInvariant (invariantTestSetoid W).r (invariantTestCode W) := by
  classical
  intro x y
  constructor
  · intro h
    funext n
    simp only [invariantTestCode, h n]
  · intro h n
    have hn := congrFun h n
    by_cases hx : x ∈ W n <;> by_cases hy : y ∈ W n <;> simp_all [invariantTestCode]

variable [MeasurableSpace X]

theorem invariantTestCode_measurable (W : ℕ → Set X) (hW : ∀ n, MeasurableSet (W n)) :
    Measurable (invariantTestCode W) := by
  classical
  apply Measurable.of_eval
  intro n
  exact Measurable.ite (hW n) measurable_const measurable_const

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    If $E=\EffectiveClosureER{E}$, enumerate the invariant $\lDelta^1_1$ sets as $\Sequence{B_n}{n\in\omega}$. The Borel map
    $x\mapsto\Sequence{\mathbf 1_{B_n}(x)}{n\in\omega}$ reduces $E$ to equality on Cantor space, so $E$ is smooth. The
    enumeration need not
    be effective: the conclusion here is ordinary Borel smoothness.
-/
theorem smooth_of_invariant_tests_complete (E : Setoid X) (W : ℕ → Set X)
    (hW : ∀ n, MeasurableSet (W n))
    (hcomplete : ∀ x y, E.r x y ↔ (invariantTestSetoid W).r x y) : Smooth E.r := by
  apply smooth_of_standardBorel_completeInvariant (invariantTestCode_measurable W hW)
  exact fun x y => (hcomplete x y).trans (invariantTestCode_complete W x y)

/-- Points in an auxiliary class containing more than one E-class. -/
def equivalenceGapKernel (E F : Setoid X) : Set X := {x | ∃ y, F.r x y ∧ ¬ E.r x y}

omit [MeasurableSpace X] in
theorem equivalenceGapKernel_invariant (E F : Setoid X) : ERInvariant F (equivalenceGapKernel E F) := by
  have hforward {x z : X} (hxz : F.r x z) (hx : x ∈ equivalenceGapKernel E F) :
      z ∈ equivalenceGapKernel E F := by
    obtain ⟨y, hxy, hne⟩ := hx
    by_cases hExz : E.r x z
    · exact ⟨y, F.trans (F.symm hxz) hxy, fun hzy => hne (E.trans hExz hzy)⟩
    · exact ⟨x, F.symm hxz, fun hzx => hExz (E.symm hzx)⟩
  intro x z hxz
  exact ⟨hforward hxz, hforward (F.symm hxz)⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For a nonsmooth $E$, therefore, the
    \termdefine{ergodic kernel}
    $$H=\{x:\exists y\ (x\mathrel{\EffectiveClosureER{E}}y\ \land\ x\mathrel{\not E}y)\}$$
    is nonempty.
-/
theorem hkl_gap_kernel_nonempty (E : Setoid X) (W : ℕ → Set X)
    (hW : ∀ n, MeasurableSet (W n)) (hWi : ∀ n, ERInvariant E (W n))
    (hns : ¬ Smooth E.r) : (equivalenceGapKernel E (invariantTestSetoid W)).Nonempty := by
  classical
  by_contra h
  apply hns
  apply smooth_of_invariant_tests_complete E W hW
  intro x y
  refine ⟨relation_le_invariantTestSetoid E W hWi, ?_⟩
  intro hxy
  by_contra hne
  exact h ⟨x, y, hxy, hne⟩

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X] in
theorem invariantTestSetoid_measurable (W : ℕ → Set X) (hW : ∀ n, MeasurableSet (W n)) :
    MeasurableSet {p : X × X | (invariantTestSetoid W).r p.1 p.2} := by
  have heq : {p : X × X | (invariantTestSetoid W).r p.1 p.2} =
      {p : X × X | invariantTestCode W p.1 = invariantTestCode W p.2} := by
    ext p
    exact invariantTestCode_complete W p.1 p.2
  rw [heq]
  exact measurableSet_eq_fun ((invariantTestCode_measurable W hW).comp measurable_fst)
    ((invariantTestCode_measurable W hW).comp measurable_snd)

/-- Projection of the Borel relation F minus E gives an analytic kernel. -/
theorem hkl_gap_kernel_analytic (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2})
    (W : ℕ → Set X) (hW : ∀ n, MeasurableSet (W n)) :
    AnalyticSet (equivalenceGapKernel E (invariantTestSetoid W)) := by
  have hR := ((invariantTestSetoid_measurable W hW).diff hE).analyticSet
  have heq : Prod.fst '' ({p : X × X | (invariantTestSetoid W).r p.1 p.2} \
      {p : X × X | E.r p.1 p.2}) = equivalenceGapKernel E (invariantTestSetoid W) := by
    ext x
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hxy, hne⟩, rfl⟩
      exact ⟨y, hxy, hne⟩
    · rintro ⟨y, hxy, hne⟩
      exact ⟨(x, y), ⟨hxy, hne⟩, rfl⟩
  rw [← heq]
  exact hR.image_of_continuous continuous_fst

/-- The ordinary Borel hypotheses supply the kernel's analyticity,
nonemptiness, and both invariances. Hereditary failure on the lightface
subsets is handled in `LambdaInvariantClosure` once the actual auxiliary
relation has a relative analytic code. -/
theorem hkl_borel_kernel (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2})
    (W : ℕ → Set X) (hW : ∀ n, MeasurableSet (W n)) (hWi : ∀ n, ERInvariant E (W n))
    (hns : ¬ Smooth E.r) :
    AnalyticSet (equivalenceGapKernel E (invariantTestSetoid W)) ∧
      (equivalenceGapKernel E (invariantTestSetoid W)).Nonempty ∧
      ERInvariant (invariantTestSetoid W) (equivalenceGapKernel E (invariantTestSetoid W)) ∧
      ERInvariant E (equivalenceGapKernel E (invariantTestSetoid W)) := by
  have hi := equivalenceGapKernel_invariant E (invariantTestSetoid W)
  exact ⟨hkl_gap_kernel_analytic E hE W hW, hkl_gap_kernel_nonempty E W hW hWi hns,
    hi, fun {_ _} h => hi (relation_le_invariantTestSetoid E W hWi h)⟩

end PolishSpaceBook
