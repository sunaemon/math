module

public import PolishSpaceBook.HausdorffBoundary
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

/-!
# Hausdorff representation by alternating open sets

Interleave two open sets for each removed boundary layer. The negative side
enters at an even stage and the positive side at the next odd stage. Ordinal
quotient and remainder implement the lexicographic two-point blocks.
-/

noncomputable section
namespace PolishSpaceBook.HausdorffDifference
open Set Order Topology
universe u
variable {X : Type u} [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Now form an increasing open approximation with two steps at stage $\xi$. Write $\alpha=2\cdot\theta$ for the
    ordinal sum of $\theta$ many two-point blocks. Every $\eta<\alpha$ has a unique expression $\eta=2\cdot\xi+i$
    with $\xi<\theta$ and $i\in\{0,1\}$. Define
    $$
    \begin{aligned}
    V_{2\cdot\xi}&=R_\xi\cup H_\xi,\\
    V_{2\cdot\xi+1}&=R_\xi\cup H_\xi\cup G_\xi=R_{\xi+1}.
    \end{aligned}
    $$
-/
/-- Two successive entries for each layer of the boundary recursion. -/
def approximation (A : Set X) (η : Ordinal.{u}) : Set X :=
  if parity η = 0 then
    (boundaryStage A (η / 2))ᶜ ∪ negativeExit A (boundaryStage A (η / 2))
  else (boundaryStage A (η / 2 + 1))ᶜ

lemma div_two_even (ξ : Ordinal) : (2 * ξ) / 2 = ξ :=
  Ordinal.mul_div_cancel ξ (by norm_num)

lemma div_two_odd (ξ : Ordinal) : (2 * ξ + 1) / 2 = ξ := by
  rw [Ordinal.mul_add_div ξ (by norm_num), Ordinal.div_eq_zero_of_lt one_lt_two, add_zero]

lemma approximation_even (A : Set X) (ξ : Ordinal.{u}) :
    approximation A (2 * ξ) =
      (boundaryStage A ξ)ᶜ ∪ negativeExit A (boundaryStage A ξ) := by
  simp [approximation]

lemma approximation_odd (A : Set X) (ξ : Ordinal.{u}) :
    approximation A (2 * ξ + 1) = (boundaryStage A (ξ + 1))ᶜ := by
  simp [approximation, div_two_odd]

lemma approximation_open (A : Set X) (η : Ordinal.{u}) : IsOpen (approximation A η) := by
  unfold approximation
  split_ifs
  · exact (boundaryStage_closed A _).isOpen_compl.union (negativeExit_open _ _)
  · exact (boundaryStage_closed A _).isOpen_compl

lemma approximation_lower (A : Set X) (η : Ordinal.{u}) :
    (boundaryStage A (η / 2))ᶜ ⊆ approximation A η := by
  unfold approximation
  split_ifs
  · exact subset_union_left
  · exact compl_subset_compl.mpr (boundaryStage_antitone A (lt_add_one _).le)

lemma approximation_upper (A : Set X) (η : Ordinal.{u}) :
    approximation A η ⊆ (boundaryStage A (η / 2 + 1))ᶜ := by
  unfold approximation
  split_ifs
  · intro x hx hd
    rw [boundaryStage_succ] at hd
    rcases hx with hx | hx
    · exact hx (boundaryDerivative_subset A (boundaryStage_closed A _) hd)
    · exact hx hd.1
  · exact Subset.rfl

lemma ordinal_two_decomposition (η : Ordinal) :
    η = 2 * (η / 2) + parity η := (Ordinal.div_add_mod η 2).symm

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Each set is open. For $\xi<\zeta<\theta$,
    $$
    \begin{aligned}
    R_\xi&\IncludedIn V_{2\cdot\xi}\IncludedIn V_{2\cdot\xi+1}=R_{\xi+1},\\
    R_{\xi+1}&\IncludedIn R_\zeta\IncludedIn V_{2\cdot\zeta},
    \end{aligned}
    $$
    so the entire sequence is increasing.
-/
lemma approximation_mono (A : Set X) : Monotone (approximation A) := by
  intro η ζ hle
  have hdiv := Ordinal.div_le_left hle 2
  rcases hdiv.eq_or_lt with he | hlt
  · have hη := ordinal_two_decomposition η
    have hζ := ordinal_two_decomposition ζ
    rcases parity_cases η with hp | hp <;> rcases parity_cases ζ with hq | hq
    · simp only [hp, hq, add_zero] at hη hζ
      have : η = ζ := hη.trans ((congrArg (2 * ·) he).trans hζ.symm)
      rw [this]
    · simp only [hp, hq, add_zero] at hη hζ
      rw [hη, hζ, ← he, approximation_odd]
      intro x hx
      have hu := approximation_upper A (2 * (η / 2)) hx
      rw [div_two_even] at hu
      exact hu
    · simp only [hp, hq, add_zero] at hη hζ
      have hbad : 2 * (η / 2) + 1 ≤ 2 * (η / 2) := calc
        2 * (η / 2) + 1 = η := hη.symm
        _ ≤ ζ := hle
        _ = 2 * (η / 2) := hζ.trans (congrArg (2 * ·) he.symm)
      exact (not_le_of_gt (lt_add_one _) hbad).elim
    · simp only [hp, hq] at hη hζ
      have : η = ζ := hη.trans ((congrArg (fun q => 2 * q + 1) he).trans hζ.symm)
      rw [this]
  · exact (approximation_upper A η).trans
      ((compl_subset_compl.mpr (boundaryStage_antitone A (add_one_le_of_lt hlt))).trans
        (approximation_lower A ζ))

/-- A point surviving to a layer cannot enter any earlier two-point block. -/
lemma not_mem_approximation_before {A : Set X} {ξ η : Ordinal.{u}} {x : X}
    (hx : x ∈ boundaryStage A ξ) (hη : η < 2 * ξ) : x ∉ approximation A η := by
  have hq : η / 2 < ξ := (Ordinal.lt_mul_iff_div_lt (by norm_num)).mp hη
  exact fun hm => approximation_upper A η hm
    (boundaryStage_antitone A (add_one_le_of_lt hq) hx)

lemma positive_layer_not_even {A : Set X} {ξ : Ordinal.{u}} {x : X}
    (hxA : x ∈ A) (hxF : x ∈ boundaryStage A ξ) : x ∉ approximation A (2 * ξ) := by
  rw [approximation_even]
  rintro (hx | hx)
  · exact hx hxF
  · exact hx (subset_closure ⟨hxA, hxF⟩)

/-- The first-entry piece at an odd stage is exactly the positive side of its layer. -/
lemma odd_piece (A : Set X) (ξ : Ordinal.{u}) :
    piece (approximation A) (2 * ξ + 1) =
      A ∩ (boundaryStage A ξ \ boundaryStage A (ξ + 1)) := by
  classical
  ext x
  rw [mem_piece]
  constructor
  · rintro ⟨hx, hbefore⟩
    rw [approximation_odd] at hx
    have hneven := hbefore (2 * ξ) (lt_add_one _)
    have hxF : x ∈ boundaryStage A ξ := by
      by_contra hn
      exact hneven (by rw [approximation_even]; exact Or.inl hn)
    have hxA : x ∈ A := by
      by_contra hn
      have hneg : x ∈ negativeExit A (boundaryStage A ξ) := by
        apply ((Set.ext_iff.mp (negativeExit_inter A (boundaryStage A ξ)) x).mpr ?_).1
        exact ⟨⟨hxF, by rwa [← boundaryStage_succ]⟩, hn⟩
      exact hneven (by rw [approximation_even]; exact Or.inr hneg)
    exact ⟨hxA, hxF, hx⟩
  · rintro ⟨hxA, hxF, hxnext⟩
    refine ⟨by rwa [approximation_odd], fun η hη => ?_⟩
    rcases (lt_add_one_iff.mp hη).lt_or_eq with hlt | rfl
    · exact not_mem_approximation_before hxF hlt
    · exact positive_layer_not_even hxA hxF

/-- The negative side enters at the even step, before the positive side. -/
lemma negative_layer_first {A : Set X} {ξ : Ordinal.{u}} {x : X}
    (hx : x ∈ (boundaryStage A ξ \ boundaryStage A (ξ + 1)) \ A) :
    x ∈ piece (approximation A) (2 * ξ) := by
  apply (mem_piece _ _ _).mpr
  refine ⟨?_, fun η hη => not_mem_approximation_before hx.1.1 hη⟩
  rw [approximation_even]
  apply Or.inr
  apply ((Set.ext_iff.mp (negativeExit_inter A (boundaryStage A ξ)) x).mpr ?_).1
  exact ⟨⟨hx.1.1, by simpa only [boundaryStage_succ] using hx.1.2⟩, hx.2⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    If $x\in P_\xi$, then $x\notin R_\xi$ and $x\in R_{\xi+1}$. Every earlier block lies in $R_\xi$, so $x$ has
    not entered before stage $2\cdot\xi$. The identities for $G_\xi,H_\xi$ show that $x\in\SetDifference{P_\xi}{A}$
    first enters at $2\cdot\xi$, while $x\in A\cap P_\xi$ first enters at $2\cdot\xi+1$.
    These two indices have even and odd parity, respectively, and $\alpha=2\cdot\theta$ is even.
    Since the layers partition $X$, selecting the odd first-entry stages gives exactly $A$:
    $$
    A=D_\alpha((V_\eta)_{\eta<\alpha}).
    $$
-/
/-- Empty final derivative ensures that the interleaving represents every point. -/
theorem approximation_represents {A : Set X} {θ : Ordinal.{u}}
    (hθ : boundaryStage A θ = ∅) : A = differenceSet (2 * θ) (approximation A) := by
  classical
  ext x
  constructor
  · intro hxA
    obtain ⟨ξ, hξ, hxF, hxnext⟩ := boundaryStage_exists_removal A θ
      (show x ∉ boundaryStage A θ by simp [hθ])
    apply (mem_chosen _ _ _ _).mpr
    refine ⟨2 * ξ + 1, Ordinal.lt_mul_iff.mpr ⟨ξ, hξ, 1, one_lt_two, rfl⟩,
      by simp, ?_⟩
    rw [odd_piece]
    exact ⟨hxA, hxF, hxnext⟩
  · intro hx
    obtain ⟨η, _, hp, hxη⟩ := (mem_chosen _ _ _ _).mp hx
    have hp1 : parity η = 1 := (parity_cases η).resolve_left (by simpa using hp)
    have he : η = 2 * (η / 2) + 1 := by simpa only [hp1] using ordinal_two_decomposition η
    rw [he, odd_piece] at hxη
    exact hxη.1

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    The ordinal $\alpha$ is countable because it consists of countably many two-point blocks. The case $\theta=0$
    is included: then $X=F_0=F_\theta=\emptyset$, and both $A$ and $D_0$ are empty.
-/
lemma two_mul_countable {θ : Ordinal} (hθ : θ < Ordinal.omega 1) :
    2 * θ < Ordinal.omega 1 := by
  apply Ordinal.isPrincipal_mul_omega 1
  · exact (Ordinal.natCast_lt_omega0 2).trans_le (Ordinal.omega0_le_omega 1)
  · exact hθ

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Thus $A\in\mathsf D_\alpha(\bSigma^0_1)(X)$ for some countable $\alpha$. Together with the proposition, this proves the
    theorem.
    \end{proof}
-/
/-- Hausdorff's representation theorem, using the closed boundary recursion. -/
theorem hausdorff_representation [PolishSpace X] {A : Set X}
    (hA : A ∈ borelDelta (2 : Ordinal)) :
    ∃ α : Ordinal.{u}, α < Ordinal.omega 1 ∧ InLevel α A := by
  obtain ⟨θ, hθ, he⟩ := boundaryStage_countable_empty hA
  exact ⟨2 * θ, two_mul_countable hθ, approximation A,
    fun η _ => approximation_open A η, fun _ _ _ _ h => approximation_mono A h,
    approximation_represents he⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: theorem
  title: Hausdorff
-/
theorem hausdorff_iff [PolishSpace X] {A : Set X} :
    A ∈ borelDelta (2 : Ordinal) ↔ ∃ α : Ordinal.{u}, α < Ordinal.omega 1 ∧ InLevel α A := by
  refine ⟨hausdorff_representation, ?_⟩
  rintro ⟨α, hα, hA⟩
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact level_subset_delta2 hα hA

end PolishSpaceBook.HausdorffDifference
