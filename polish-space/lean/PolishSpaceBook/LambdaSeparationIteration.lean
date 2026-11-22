module

public import PolishSpaceBook.LambdaComplementedCodes
public import PolishSpaceBook.LambdaUniformFamilies
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree

/-- The state is a pair of analytic input indices. Recursive updates are
computed from the preceding state, not selected independently at each stage. -/
def separatorStates (f : ℕ → ℕ) (seed : ℕ) : ℕ → ℕ
  | 0 => seed
  | n + 1 => f (separatorStates f seed n)

def separatorIterationProgram (F : AlphaTerm) : AlphaTerm :=
  numericalRecursion numericalIdentity
    (numericalCompose F
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))

theorem separatorIterationProgram_computes {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) : NumericalComputes (separatorIterationProgram F)
      (fun z => separatorStates f z.unpair.1 z.unpair.2) := by
  have h := numericalRecursion_computes numericalIdentity_computes
    (hF.comp ((projection_computes false).comp (projection_computes false)))
  simp only [id_eq, Bool.false_eq_true, ite_false, Nat.unpair_pair] at h
  convert h using 1 <;> try rfl
  funext z
  induction z.unpair.2 with
  | zero => rfl
  | succ n ih => simpa only [separatorStates, primitiveRec] using congrArg f ih

theorem separatorStates_computable {f : ℕ → ℕ}
    (hf : ∃ F, NumericalComputes F f) (seed : ℕ) :
    ∃ S, NumericalComputes S (separatorStates f seed) := by
  obtain ⟨F, hF⟩ := hf
  have h := (separatorIterationProgram_computes hF).comp
    ((numericalConstant_computes seed).pair numericalIdentity_computes)
  exact ⟨_, by simpa only [Nat.unpair_pair, id_eq] using h⟩

theorem separatorStates_valid {ε : ℕ → ℕ} {f : ℕ → ℕ} {seed : ℕ}
    (hseed : ValidComplementedIndex ε seed)
    (hstep : ∀ z, ValidComplementedIndex ε z → ValidComplementedIndex ε (f z)) (n : ℕ) :
    ValidComplementedIndex ε (separatorStates f seed n) := by
  induction n with
  | zero => exact hseed
  | succ n ih => exact hstep _ ih

/-- The common numerical iteration feeds the fixed positive and negative
separation compilers, yielding two jointly decidable tree families. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Iterating these index transformations recursively therefore produces uniformly $\lDelta^1_1$ separators.
-/
theorem recursive_uniform_separators (ε : ℕ → ℕ) (f : ℕ → ℕ)
    (hf : ∃ F, NumericalComputes F f) (seed : ℕ)
    (hseed : ValidComplementedIndex ε seed)
    (hstep : ∀ z, ValidComplementedIndex ε z → ValidComplementedIndex ε (f z)) :
    ∃ D D' : ℕ → Set (ℕ → ℕ), UniformProjected ε D ∧ UniformProjected ε D' ∧
      ∀ n, indexedProjection ε (separatorStates f seed n).unpair.1 ⊆ D n ∧
        D n ⊆ (indexedProjection ε (separatorStates f seed n).unpair.2)ᶜ ∧
        D n = (D' n)ᶜ := by
  obtain ⟨C⟩ := exists_complementedCodes ε
  obtain ⟨S, hS⟩ := separatorStates_computable hf seed
  obtain ⟨P, hP⟩ := C.positive_computable
  obtain ⟨N, hN⟩ := C.negative_computable
  have hp := indexedTree_reindex_decidable ε (hP.comp hS)
  have hn := indexedTree_reindex_decidable ε (hN.comp hS)
  refine ⟨fun n => C.positiveSet (separatorStates f seed n),
    fun n => C.negativeSet (separatorStates f seed n), ?_, ?_, ?_⟩
  · exact ⟨fun n => indexedTree ε (C.positive (separatorStates f seed n)), hp, fun _ => rfl⟩
  · exact ⟨fun n => indexedTree ε (C.negative (separatorStates f seed n)), hn, fun _ => rfl⟩
  · intro n
    have h := C.separates (separatorStates f seed n).unpair.1
      (separatorStates f seed n).unpair.2 (separatorStates_valid hseed hstep n)
    simpa only [Nat.pair_unpair, ComplementedCodes.positiveSet,
      ComplementedCodes.negativeSet] using h

end LambdaTree
end PolishSpaceBook
