module

public import PolishSpaceBook.LambdaProjectiveBase
public import PolishSpaceBook.LambdaAnalyticCatalog

@[expose] public section

/-! # Relativization at every positive finite projective level

The base is the closed-projection characterization of analytic sets, with
its fixed-parameter pair-tree equivalence. Higher levels commute with
existential real projection. Combining two parameters uses the actual
lambda accessors; no computable selection of a parameter or witness is
asserted.
-/
noncomputable section
namespace PolishSpaceBook
open Set MeasureTheory NamedLambda NamedLambda.AlphaTerm

local instance projectiveRelativeWords : Encodable (List ℕ) := NatListCode.encodable

namespace LambdaRelative
universe u

/-- Change a fixed parameter by total lambda computation. Finite acceptance
certificates supply an exact semidecider, including the nonacceptance direction. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefineas{boldface class}{boldface classes} are recovered by **\termforward{relativization}**. Fix a real
    $a \in \BaireSpace$
    and allow all algorithms and recursive predicates in the preceding definitions to use $a$ as an input function.
    Concretely, a relative computation may ask for the value $a(n)$ at any natural number $n$ during its finite computation.
    Thus $a$ acts as a fixed infinite table of background information.
-/
theorem SemidecidablePredicate.changeParameter {α : Type u} [Encodable α]
    {ε δ : ℕ → ℕ} {Q : AlphaTerm} {R : α → Prop}
    (hR : SemidecidablePredicate ε R) (hQ : Computes δ Q ε) : SemidecidablePredicate δ R := by
  obtain ⟨P, hP, hR⟩ := hR
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
  have ha : Computes ε (acceptanceTestProgram e)
      (fun z : ℕ => if acceptanceTest ε e z then 1 else 0) :=
    ⟨(acceptanceTestProgram_computes e).1, (acceptanceTestProgram_computes e).2 ε⟩
  have ht := open_computes_changeParameter ha hQ
  refine ⟨relativeSearchProgram _, relativeSearchProgram_closed ht.1, fun a => ?_⟩
  rw [relativeSearchProgram_runs_iff ht]
  have hh : R a ↔ ∃ k, acceptanceTest ε e (Nat.pair (Encodable.encode a) k) = true := by
    rw [hR a, ← he]
    simpa only [acceptanceTest, Term.oracleOutputCandidate, Nat.unpair_pair] using
      (oracle_outputTest_exists_iff ε e (Encodable.encode a) 1).symm
  simpa using hh
end LambdaRelative

theorem relativelyEffectivelyOpen_changeParameter {ε δ : ℕ → ℕ} {Q : AlphaTerm}
    {A : Set (ℕ → ℕ)} (hA : RelativelyEffectivelyOpen ε A)
    (hQ : LambdaRelative.Computes δ Q ε) : RelativelyEffectivelyOpen δ A := by
  obtain ⟨W, hW, hA⟩ := hA
  exact ⟨W, hW.changeParameter hQ, hA⟩

theorem relativelyEffectivelyClosed_changeParameter {ε δ : ℕ → ℕ} {Q : AlphaTerm}
    {A : Set (ℕ → ℕ)} (hA : RelativelyEffectivelyClosed ε A)
    (hQ : LambdaRelative.Computes δ Q ε) : RelativelyEffectivelyClosed δ A :=
  relativelyEffectivelyOpen_changeParameter hA hQ

namespace LambdaFinite

/-- A single computed accessor works through every finite real quantifier. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefineas{boldface class}{boldface classes} are recovered by **\termforward{relativization}**. Fix a real
    $a \in \BaireSpace$
    and allow all algorithms and recursive predicates in the preceding definitions to use $a$ as an input function.
    Concretely, a relative computation may ask for the value $a(n)$ at any natural number $n$ during its finite computation.
    Thus $a$ acts as a fixed infinite table of background information.
-/
theorem projectiveSigma_changeParameter {ε δ : ℕ → ℕ} {Q : AlphaTerm}
    {n : ℕ} {A : Set (ℕ → ℕ)} (hA : ProjectiveSigma ε n A)
    (hQ : LambdaRelative.Computes δ Q ε) : ProjectiveSigma δ n A := by
  induction n generalizing A with
  | zero =>
    obtain ⟨C, hC, hA⟩ := hA
    exact ⟨C, relativelyEffectivelyClosed_changeParameter hC hQ, hA⟩
  | succ n ih =>
    obtain ⟨B, hB, hA⟩ := hA
    exact ⟨B, ih hB, hA⟩

/-- Canonical finite projective recursion on the fixed Baire-product code.
As in the lightface API, internal n denotes positive level n + 1. -/
def BoldProjectiveSigma : ℕ → Set (ℕ → ℕ) → Prop
  | 0, A => AnalyticSet A
  | n + 1, A => ∃ B : Set (ℕ → ℕ), BoldProjectiveSigma n B ∧
      A = {p | ∃ q : ℕ → ℕ, pairBaire p q ∉ B}

def BoldProjectivePi (n : ℕ) (A : Set (ℕ → ℕ)) : Prop := BoldProjectiveSigma n Aᶜ

def BoldProjectiveDelta (n : ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  BoldProjectiveSigma n A ∧ BoldProjectivePi n A

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The resulting relativized classes are denoted $\lSigma^k_n(a)$, $\lPi^k_n(a)$, and $\lDelta^k_n(a)$. Then
    $$\bSigma^k_n \;=\; \bigcup_{a \in \BaireSpace} \lSigma^k_n(a).$$
    The slogan is *boldface = lightface relativized to all real parameters*.
-/
theorem boldProjectiveSigma_iff_exists_parameter (n : ℕ) (A : Set (ℕ → ℕ)) :
    BoldProjectiveSigma n A ↔ ∃ ε, ProjectiveSigma ε n A := by
  induction n generalizing A with
  | zero =>
    exact (LambdaTree.analyticSet_iff_exists_parameter A).trans
      (exists_congr fun ε => (projectiveSigma_zero_iff_projected ε A).symm)
  | succ n ih =>
    constructor
    · rintro ⟨B, hB, hA⟩
      obtain ⟨ε, hB⟩ := (ih B).mp hB
      exact ⟨ε, B, hB, hA⟩
    · rintro ⟨ε, B, hB, hA⟩
      exact ⟨B, (ih B).mpr ⟨ε, hB⟩, hA⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The resulting relativized classes are denoted $\lSigma^k_n(a)$, $\lPi^k_n(a)$, and $\lDelta^k_n(a)$. Then
    $$\bSigma^k_n \;=\; \bigcup_{a \in \BaireSpace} \lSigma^k_n(a).$$
    The slogan is *boldface = lightface relativized to all real parameters*.
-/
theorem boldProjectivePi_iff_exists_parameter (n : ℕ) (A : Set (ℕ → ℕ)) :
    BoldProjectivePi n A ↔ ∃ ε, ProjectivePi ε n A :=
  boldProjectiveSigma_iff_exists_parameter n Aᶜ

/-- The ambiguous class uses one paired original parameter for both sides;
the projections are total closed lambda computations of its two components. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The resulting relativized classes are denoted $\lSigma^k_n(a)$, $\lPi^k_n(a)$, and $\lDelta^k_n(a)$. Then
    $$\bSigma^k_n \;=\; \bigcup_{a \in \BaireSpace} \lSigma^k_n(a).$$
    The slogan is *boldface = lightface relativized to all real parameters*.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This slogan should be read literally. A boldface open set may require a noncomputable list of cylinders. Treat that list
    as a real parameter $a$, give the program input-function access to $a$, and the same set becomes lightface relative to
    $a$. The topological hierarchy is therefore the union of all its computable versions relative to all possible real
    parameters.
-/
theorem boldProjectiveDelta_iff_exists_parameter (n : ℕ) (A : Set (ℕ → ℕ)) :
    BoldProjectiveDelta n A ↔ ∃ ε, ProjectiveDelta ε n A := by
  constructor
  · rintro ⟨hS, hP⟩
    obtain ⟨ε, hS⟩ := (boldProjectiveSigma_iff_exists_parameter n A).mp hS
    obtain ⟨η, hP⟩ := (boldProjectivePi_iff_exists_parameter n A).mp hP
    refine ⟨LambdaTree.sectionParameter ε η, ?_, ?_⟩
    · exact projectiveSigma_changeParameter hS (LambdaTree.parameterProjection_computes true ε η)
    · exact projectiveSigma_changeParameter hP (LambdaTree.parameterProjection_computes false ε η)
  · rintro ⟨ε, hS, hP⟩
    exact ⟨(boldProjectiveSigma_iff_exists_parameter n A).mpr ⟨ε, hS⟩,
      (boldProjectivePi_iff_exists_parameter n A).mpr ⟨ε, hP⟩⟩

end LambdaFinite
end PolishSpaceBook
