module

public import PolishSpaceBook.LambdaHaltingLanguage
public import PolishSpaceBook.LambdaRealizerAbstraction
public import Mathlib.Topology.Instances.Nat

@[expose] public section

/-! # Halting on the fixed numerical input zero

The reduction constructs indices of delayed applications using the already
proved lambda syntax compiler. It does not identify fixed-input halting with
diagonal halting or choose outputs of programs.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm LambdaHaltingLanguage

/-- Programs returning a numeral when their numerical input is zero. -/
/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    For example, consider the natural-number codes of programs that return a natural number on input 0.
    Finite computations witnessing an output let us computably enumerate the members, although no program decides
    membership in every case. In the discrete topology on the natural numbers, however, every subset is open and
    closed, including this one. Its computational difficulty is therefore not a high level of the ordinary Borel
    hierarchy. The effective hierarchy distinguishes the existence of a computable enumeration from computable
    decidability. The same set thus makes visible the difference between topological and effective complexity.
-/
def zeroInputHalting : Set ℕ := {e | ∃ m, App e 0 m}

/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    For example, consider the natural-number codes of programs that return a natural number on input 0.
    Finite computations witnessing an output let us computably enumerate the members, although no program decides
    membership in every case. In the discrete topology on the natural numbers, however, every subset is open and
    closed, including this one. Its computational difficulty is therefore not a high level of the ordinary Borel
    hierarchy. The effective hierarchy distinguishes the existence of a computable enumeration from computable
    decidability. The same set thus makes visible the difference between topological and effective complexity.
-/
theorem zeroInputHalting_enumerable : LambdaEnumerable zeroInputHalting := by
  have hc := zeroWordProgram_computes.comp
    (numericalIdentity_computes.pair (numericalConstant_computes 0))
  have he : (fun e => zeroWordCode (Nat.pair e 0)) ⁻¹' haltingLanguage = zeroInputHalting := by
    ext e
    exact code_mem_haltingLanguage e 0
  exact he ▸ haltingLanguage_enumerable.preimage hc

/-- The code transformation is total; the delayed computation may diverge. -/
/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    For example, consider the natural-number codes of programs that return a natural number on input 0.
    Finite computations witnessing an output let us computably enumerate the members, although no program decides
    membership in every case. In the discrete topology on the natural numbers, however, every subset is open and
    closed, including this one. Its computational difficulty is therefore not a high level of the ordinary Borel
    hierarchy. The effective hierarchy distinguishes the existence of a computable enumeration from computable
    decidability. The same set thus makes visible the difference between topological and effective complexity.
-/
theorem exists_diagonal_to_zeroInput_compiler :
    ∃ C f, NumericalComputes C f ∧
      ∀ e, f e ∈ zeroInputHalting ↔ diagonalHalts e := by
  obtain ⟨B, hB⟩ := realizerAbstraction_computable.2.2
  have hc := hB.comp (numericalIdentity_computes.pair numericalIdentity_computes)
  refine ⟨numericalCompose B (pairNumerical numericalIdentity numericalIdentity),
    (fun e => realizerAbstraction.body e e), ?_, ?_⟩
  · simpa only [Nat.unpair_pair, id_eq] using hc
  · intro e
    change (∃ m, App (realizerAbstraction.body e e) 0 m) ↔ ∃ m, App e e m
    simp only [realizerAbstraction_body_iff]

/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    For example, consider the natural-number codes of programs that return a natural number on input 0.
    Finite computations witnessing an output let us computably enumerate the members, although no program decides
    membership in every case. In the discrete topology on the natural numbers, however, every subset is open and
    closed, including this one. Its computational difficulty is therefore not a high level of the ordinary Borel
    hierarchy. The effective hierarchy distinguishes the existence of a computable enumeration from computable
    decidability. The same set thus makes visible the difference between topological and effective complexity.
-/
theorem zeroInputHalting_not_decidable : ¬ LambdaDecidable zeroInputHalting := by
  classical
  rintro ⟨D, hD⟩
  obtain ⟨C, f, hC, hf⟩ := exists_diagonal_to_zeroInput_compiler
  have hd := hD.comp hC
  have h := reverseZero_computes.comp hd
  apply diagonalHalts_not_decidable
  refine ⟨_, ⟨h.1, fun e => ?_⟩⟩
  have he := h.2 e
  dsimp only at he
  rw [hf e] at he
  by_cases hh : diagonalHalts e <;>
    simpa only [hh, ite_true, ite_false, Nat.one_ne_zero, ↓reduceIte] using he

/-- Computational undecidability is compatible with topological clopenness. -/
/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    For example, consider the natural-number codes of programs that return a natural number on input 0.
    Finite computations witnessing an output let us computably enumerate the members, although no program decides
    membership in every case. In the discrete topology on the natural numbers, however, every subset is open and
    closed, including this one. Its computational difficulty is therefore not a high level of the ordinary Borel
    hierarchy. The effective hierarchy distinguishes the existence of a computable enumeration from computable
    decidability. The same set thus makes visible the difference between topological and effective complexity.
-/
theorem zeroInputHalting_isClopen : IsClopen zeroInputHalting := isClopen_discrete _

end PolishSpaceBook.LambdaIndexPCA
