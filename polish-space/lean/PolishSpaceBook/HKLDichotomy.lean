module

public import PolishSpaceBook.HKLPolishTransport
public import PolishSpaceBook.E0Nonsmooth

@[expose] public section

/-!
# The complete HKL and Glimm--Effros dichotomies

The fusion theorem supplies the embedding alternative; the finite-block
Hewitt--Savage argument rules it out for a smooth relation.
-/

namespace PolishSpaceBook
open MeasureTheory MeasurableSpace Set Function

/-- The HKL embedding alternative holds exactly for nonsmooth Borel
relations on a Polish space. All auxiliary hypotheses are discharged. -/
theorem hkl_dichotomy_polish (X : Type) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) :
    ¬ Smooth E.r ↔ ∃ π : (ℕ → Bool) → X, Continuous π ∧ Injective π ∧
      ∀ a b, E0 a b ↔ E.r (π a) (π b) := by
  constructor
  · exact hkl_embedding_polish X E hE
  · rintro ⟨π, hc, _, hr⟩ hs
    exact smooth_excludes_e0_reduction e0_not_smooth hs ⟨π, hc.measurable, hr⟩

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    For the converse, assume $E$ is not smooth, and choose a Polish topology presenting the underlying
    standard Borel space. The
    \termforwardas{Harrington--Kechris--Louveau embedding}{Harrington--Kechris--Louveau embedding theorem}, whose proof is
    given in §{sec:edst-gh-hkl}, gives a continuous injection
    $$\pi:\CantorSpace\to X$$
    such that
    $$a \mathrel{\EventualEqualityER} b
    \quad\Longleftrightarrow\quad
    \pi(a)\mathrel E\pi(b).$$
    This $\pi$ is a Borel reduction from $\EventualEqualityER$ to $E$. Hence nonsmoothness implies
    $\EventualEqualityER\BorelReducesTo E$, completing the dichotomy.
-/
/-- The reduction formulation does not require a chosen Polish topology. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    It is the minimal nonsmooth benchmark for
    Borel equivalence relations: every Borel equivalence relation is either smooth or has $\EventualEqualityER$
    Borel-reducing to it.
-/
theorem hkl_reducible_iff_nonsmooth (X : Type) [MeasurableSpace X]
    [StandardBorelSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) :
    BorelReducible E0 E.r ↔ ¬ Smooth E.r := by
  constructor
  · intro hr hs
    exact smooth_excludes_e0_reduction e0_not_smooth hs hr
  · intro hns
    let := upgradeStandardBorel X
    obtain ⟨π, hc, _, hr⟩ := hkl_embedding_polish X E hE hns
    exact ⟨π, hc.measurable, hr⟩

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: statement
  kind: theorem
  title: Harrington–Kechris–Louveau
-/
/-- Exactly one of smoothness and the existence of a Borel reduction of E0
holds, for every Borel equivalence relation on a standard Borel space. -/
theorem glimm_effros_dichotomy (X : Type) [MeasurableSpace X]
    [StandardBorelSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) :
    (Smooth E.r ∨ BorelReducible E0 E.r) ∧
      ¬ (Smooth E.r ∧ BorelReducible E0 E.r) := by
  classical
  constructor
  · by_cases hs : Smooth E.r
    · exact Or.inl hs
    · exact Or.inr ((hkl_reducible_iff_nonsmooth X E hE).mpr hs)
  · rintro ⟨hs, hr⟩
    exact smooth_excludes_e0_reduction e0_not_smooth hs hr

end PolishSpaceBook
