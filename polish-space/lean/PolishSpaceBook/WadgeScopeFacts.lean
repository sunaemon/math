module

public import PolishSpaceBook.MartinMonk
public import PolishSpaceBook.BorelStructure
public import Mathlib.Order.Antisymmetrization
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

noncomputable section
namespace PolishSpaceBook
open Set Function MeasureTheory
universe u v

section Pointclasses
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The witnessing continuous map preserves the very same additive level. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *Compatibility with Borel classes.* If $A \le_W B$ via continuous $f$, then $A$ has Borel rank no greater than that
    of $B$, since
    continuous preimages of $\bSigma^0_\alpha$ sets remain $\bSigma^0_\alpha$. So each Borel pointclass $\bSigma^0_\alpha,
    \bPi^0_\alpha, \bDelta^0_\alpha$ is **closed under $\le_W$** — Wadge reductions never escape upward in the Borel
    hierarchy, and each of these pointclasses is downward closed in the Wadge ordering.
-/
theorem WadgeReducible.borelSigma {A : Set X} {B : Set Y}
    (h : WadgeReducible A B) (α : Ordinal) (hB : B ∈ borelSigma α) :
    A ∈ borelSigma α := by
  obtain ⟨f, hf, rfl⟩ := h
  exact borelSigma_preimage f hf α hB

/-- Multiplicative levels are preserved as well. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *Compatibility with Borel classes.* If $A \le_W B$ via continuous $f$, then $A$ has Borel rank no greater than that
    of $B$, since
    continuous preimages of $\bSigma^0_\alpha$ sets remain $\bSigma^0_\alpha$. So each Borel pointclass $\bSigma^0_\alpha,
    \bPi^0_\alpha, \bDelta^0_\alpha$ is **closed under $\le_W$** — Wadge reductions never escape upward in the Borel
    hierarchy, and each of these pointclasses is downward closed in the Wadge ordering.
-/
theorem WadgeReducible.borelPi {A : Set X} {B : Set Y}
    (h : WadgeReducible A B) (α : Ordinal) (hB : B ∈ borelPi α) :
    A ∈ borelPi α := by
  obtain ⟨f, hf, rfl⟩ := h
  exact borelPi_preimage f hf α hB

/-- The ambiguous level is the intersection of the preceding two levels. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *Compatibility with Borel classes.* If $A \le_W B$ via continuous $f$, then $A$ has Borel rank no greater than that
    of $B$, since
    continuous preimages of $\bSigma^0_\alpha$ sets remain $\bSigma^0_\alpha$. So each Borel pointclass $\bSigma^0_\alpha,
    \bPi^0_\alpha, \bDelta^0_\alpha$ is **closed under $\le_W$** — Wadge reductions never escape upward in the Borel
    hierarchy, and each of these pointclasses is downward closed in the Wadge ordering.
-/
theorem WadgeReducible.borelDelta {A : Set X} {B : Set Y}
    (h : WadgeReducible A B) (α : Ordinal) (hB : B ∈ borelDelta α) :
    A ∈ borelDelta α := by
  exact ⟨h.borelSigma α hB.1, h.borelPi α hB.2⟩

/-- A fixed target's lower cone is closed under continuous preimages.
This is distinct from `WadgeClass`, which names an equivalence class. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Wadge classes are closed pointclasses.** The collection of $A$ with $A \le_W B$ for fixed $B$ is closed under
        continuous preimages, making each Wadge class a Wadge-closed pointclass. This is the right setting for
        game-theoretic determinacy: $\Gamma$-determinacy is a property of the Wadge class $\Gamma$, not of any particular
        generating set.
-/
theorem wadge_lowerCone_continuous_preimage {A : Set X} {B : Set Y}
    (h : WadgeReducible A B) {Z : Type*} [TopologicalSpace Z]
    (g : Z → X) (hg : Continuous g) : WadgeReducible (g ⁻¹' A) B :=
  (show WadgeReducible (g ⁻¹' A) A from ⟨g, hg, rfl⟩).trans h

end Pointclasses

namespace BorelWadgeRank
abbrev Baire := ℕ → ℕ

/-- Borel payoffs, equipped below with coarse reducibility rather than inclusion. -/
structure Payoff where
  val : Set Baire
  borel : MeasurableSet val

instance : Preorder Payoff where
  le A B := CoarseWadgeReducible A.val B.val
  le_refl A := Or.inl (WadgeReducible.refl A.val)
  le_trans _ _ _ hAB hBC := hAB.trans hBC

/-- Mutual coarse reducibility identifies a degree with its complemented degree. -/
abbrev Degree := Antisymmetrization Payoff (· ≤ ·)

def degree (A : Payoff) : Degree := toAntisymmetrization (· ≤ ·) A

def compl (A : Payoff) : Payoff := ⟨A.valᶜ, A.borel.compl⟩

def empty : Payoff := ⟨∅, MeasurableSet.empty⟩

def full : Payoff := ⟨univ, MeasurableSet.univ⟩

/-- Wadge's lemma makes the quotient order total. -/
theorem degree_total (a b : Degree) : a ≤ b ∨ b ≤ a := by
  induction a using Antisymmetrization.ind with
  | _ A =>
    induction b using Antisymmetrization.ind with
    | _ B =>
      rcases WadgeGame.borel_semilinear A.borel B.borel with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- Martin--Monk supplies well-foundedness on representatives; quotienting
mutual reducibility preserves it. Totality then gives the actual well-order. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The preceding partial order and the Martin--Monk theorem make the Borel coarse degrees a well-order.
-/
theorem degreeWellOrder : IsWellOrder Degree (· < ·) where
  trichotomous a b hab hba := by
    rcases degree_total a b with h | h
    · by_contra heq
      exact hab (lt_of_le_of_ne h heq)
    · by_contra heq
      exact hba (lt_of_le_of_ne h (Ne.symm heq))
  wf := by
    apply wellFounded_antisymmetrization_iff.mpr
    have hw := MartinMonk.martin_monk.onFun
      (f := fun A : Payoff => (⟨A.val, A.borel⟩ : {A : Set Baire // MeasurableSet A}))
    exact hw

/-- Zero-based rank is the order type of the strict initial segment of the
coarse degree, rather than a successor or a difference-hierarchy index. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We use the zero-based convention: the Wadge rank $|A|_W$ is the order type of the strict initial segment
    below $A^\ast$.
-/
def rank (A : Payoff) : Ordinal :=
  let := degreeWellOrder
  Ordinal.typein (· < ·) (degree A)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We use the zero-based convention: the Wadge rank $|A|_W$ is the order type of the strict initial segment
    below $A^\ast$.
-/
theorem rank_eq_initialSegment_type (A : Payoff) :
    rank A = (letI := degreeWellOrder
      Ordinal.type (Subrel (α := Degree) (· < ·) (· < degree A))) := by
  let := degreeWellOrder
  exact (Ordinal.type_subrel (· < ·) (degree A)).symm

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus $|A|_W=0$ for the empty/full pair, complements have the same rank, and
    $A^\ast<_W^\ast B^\ast$ exactly when $|A|_W<|B|_W$.
-/
theorem strict_iff_rank_lt (A B : Payoff) :
    MartinMonk.StrictCoarse A.val B.val ↔ rank A < rank B := by
  let := degreeWellOrder
  exact (Ordinal.typein_lt_typein (α := Degree) (· < ·) (a := degree A) (b := degree B)).symm

theorem degree_compl (A : Payoff) : degree (compl A) = degree A := by
  apply (toAntisymmetrization_eq (· ≤ ·) _ _).mpr
  constructor
  · exact Or.inr (WadgeReducible.refl A.valᶜ)
  · exact Or.inr (by simpa [compl] using WadgeReducible.refl A.val)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus $|A|_W=0$ for the empty/full pair, complements have the same rank, and
    $A^\ast<_W^\ast B^\ast$ exactly when $|A|_W<|B|_W$.
-/
theorem rank_compl (A : Payoff) :
    rank (compl A) = rank A := by
  unfold rank
  rw [degree_compl]

lemma empty_le (A : Payoff) : empty ≤ A := by
  classical
  let x : Baire := fun _ => 0
  by_cases hx : x ∈ A.val
  · exact Or.inr ⟨fun _ => x, continuous_const, by ext y; simp [empty, hx]⟩
  · exact Or.inl ⟨fun _ => x, continuous_const, by ext y; simp [empty, hx]⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus $|A|_W=0$ for the empty/full pair, complements have the same rank, and
    $A^\ast<_W^\ast B^\ast$ exactly when $|A|_W<|B|_W$.
-/
theorem rank_empty : rank empty = 0 := by
  let := degreeWellOrder
  change Ordinal.typein (· < ·) (degree empty) = 0
  rw [← Ordinal.type_subrel]
  let : IsEmpty {b : Degree // b < degree empty} := ⟨by
    intro ⟨b, hb⟩
    have hle : degree empty ≤ b := by
      induction b using Antisymmetrization.ind with
      | _ A => exact empty_le A
    exact (not_lt_of_ge hle) hb⟩
  exact Ordinal.type_eq_zero_of_empty _

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus $|A|_W=0$ for the empty/full pair, complements have the same rank, and
    $A^\ast<_W^\ast B^\ast$ exactly when $|A|_W<|B|_W$.
-/
theorem rank_full : rank full = 0 := by
  have h : full = compl empty := by simp [full, compl, empty]
  rw [h, rank_compl, rank_empty]

end BorelWadgeRank
end PolishSpaceBook
