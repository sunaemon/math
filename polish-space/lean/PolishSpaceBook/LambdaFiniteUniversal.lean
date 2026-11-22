module

public import PolishSpaceBook.LambdaFinitePointclasses
public import PolishSpaceBook.LambdaUniformInterpreter

@[expose] public section

/-! # Uniform effective universal sets at every positive finite Borel level

The same parameter is supplied to the matrix and universal interpreter.
Natural-number contexts carry the universal index before the quantifiers;
actual numerical lambda translations extract and replace that index.
-/
noncomputable section
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaFinite

/-- Recover the initial context after n appended numerical quantifiers. -/
def contextRoot : ℕ → ℕ → ℕ
  | 0, z => z
  | n + 1, z => contextRoot n z.unpair.1

def contextRootProgram : ℕ → AlphaTerm
  | 0 => numericalIdentity
  | n + 1 => numericalCompose (contextRootProgram n) (numericalProjectionTerm true)

theorem contextRootProgram_computes (n : ℕ) :
    NumericalComputes (contextRootProgram n) (contextRoot n) := by
  induction n with
  | zero => exact numericalIdentity_computes
  | succ n ih =>
    simpa only [contextRootProgram, contextRoot, ite_true] using ih.comp (projection_computes true)

theorem contextRoot_succ_right (n : ℕ) (z : ℕ) :
    contextRoot (n + 1) z = (contextRoot n z).unpair.1 := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => exact ih z.unpair.1

/-- A root-dependent matrix has a single fixed index throughout each
quantifier block. Only its numerical context is extended. -/
theorem alternating_root (n : ℕ) (R : ℕ → ℕ → (ℕ → ℕ) → Prop)
    (h f : ℕ → ℕ) (z : ℕ) (p : ℕ → ℕ) :
    alternating n (fun a => R (h (contextRoot n a)) (mapContext n f a)) z p ↔
      alternating n (R (h z)) (f z) p := by
  induction n generalizing h f z with
  | zero => rfl
  | succ n ih =>
    change (∃ k, ¬ alternating n
      (fun a => R (h (contextRoot (n + 1) a)) (mapContext (n + 1) f a)) (Nat.pair z k) p) ↔ _
    simp only [contextRoot_succ_right, mapContext_succ_right]
    exact exists_congr (fun k => not_congr (by simpa only [Nat.unpair_pair] using
      (ih (fun a => h a.unpair.1) (fun a => Nat.pair (f a.unpair.1) a.unpair.2) (Nat.pair z k))))

/-- A natural-number syntax index names one closed matrix program. -/
def universal (ε : ℕ → ℕ) (n e : ℕ) : Set (ℕ → ℕ) :=
  {p | alternating n (matrixDomain ε (Term.closedProgram e)) 0 p}

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The finite-level universal-set construction in §{sec:finite-borel-universal} also has a lightface version obtained by
    effective induction on $n$: at a successor, an index uniformly enumerates the $\lPi^0_n$ sections whose union it codes.
    The corresponding diagonals show $\lSigma^0_n\ne\lPi^0_n$ for every positive integer $n$.
-/
theorem sigma_iff_universal_section (ε : ℕ → ℕ) (n : ℕ) (A : Set (ℕ → ℕ)) :
    Sigma ε n A ↔ ∃ e, A = universal ε n e := by
  constructor
  · rintro ⟨P, hP, h⟩
    obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
    refine ⟨e, ?_⟩
    ext p
    simpa only [universal, Set.mem_ofPred_eq, he] using h p
  · rintro ⟨e, rfl⟩
    exact ⟨Term.closedProgram e, Term.closedProgram_closed e, fun _ => Iff.rfl⟩

/-- One program interprets the whole indexed family at this level. Its
numerical context holds the section index and all quantified coordinates. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The finite-level universal-set construction in §{sec:finite-borel-universal} also has a lightface version obtained by
    effective induction on $n$: at a successor, an index uniformly enumerates the $\lPi^0_n$ sections whose union it codes.
    The corresponding diagonals show $\lSigma^0_n\ne\lPi^0_n$ for every positive integer $n$.
-/
theorem universal_uniform (ε : ℕ → ℕ) (n : ℕ) : UniformSigma ε n (universal ε n) := by
  have hf := (contextRootProgram_computes n).pair
    (mapContextProgram_computes (numericalConstant_computes 0) n)
  obtain ⟨Q, hQ, h⟩ := domain_reindex uniformInterpreterProgram_closed hf.uniform
  have hb (z : ℕ) (p : ℕ → ℕ) : matrixDomain ε Q z p ↔
      matrixDomain ε (Term.closedProgram (contextRoot n z)) (mapContext n (fun _ => 0) z) p := by
    apply (h (LambdaTree.sectionParameter ε p) z).trans
    apply exists_congr
    intro m
    exact uniformInterpreterProgram_runs_iff _ _ _ _
  refine ⟨Q, hQ, fun e p => ?_⟩
  exact ((alternating_congr n hb e p).trans
    (alternating_root n (fun e => matrixDomain ε (Term.closedProgram e)) id (fun _ => 0) e p)).symm

theorem universal_section (ε : ℕ → ℕ) (n e : ℕ) : Sigma ε n (universal ε n e) :=
  (universal_uniform ε n).section e

/-- Read the first point digit and put it in the initial matrix context.
The parameter coordinate of the paired input remains untouched. -/
def diagonalContextProgram : ℕ → AlphaTerm
  | 0 => mapOutputProgram (numericalProjectionTerm false)
      (queryOutputProgram (constantProgram 0))
  | n + 1 => pairOutputProgram
      (reindexProgram (diagonalContextProgram n) (numericalProjectionTerm true))
      (liftNumericalProgram (numericalProjectionTerm false))

theorem diagonalContextProgram_computes (n : ℕ) :
    UniformNumericalComputes (diagonalContextProgram n)
      (fun q z => mapContext n (fun _ => (q 0).unpair.2) z) := by
  induction n with
  | zero =>
    simpa only [diagonalContextProgram, mapContext, Bool.false_eq_true, ite_false] using
      (uniform_constant 0).query.map (projection_computes false)
  | succ n ih =>
    simpa only [diagonalContextProgram, mapContext, ite_true, Bool.false_eq_true, ite_false] using
      (ih.reindex (projection_computes true)).pair (projection_computes false).uniform

/-- The first-coordinate pullback of the universal family stays in Sigma
at the same positive level, with a constructed closed lambda matrix. -/
theorem universal_diagonalPreimage (ε : ℕ → ℕ) (n : ℕ) :
    Sigma ε n {p | p ∈ universal ε n (p 0)} := by
  obtain ⟨P, hP, h⟩ := universal_uniform ε n
  obtain ⟨Q, hQ, hQP⟩ := domain_reindex hP (diagonalContextProgram_computes n)
  have hb (z : ℕ) (p : ℕ → ℕ) : matrixDomain ε Q z p ↔
      matrixDomain ε P (mapContext n (fun _ => p 0) z) p := by
    simpa only [matrixDomain, LambdaTree.sectionParameter, Nat.unpair_pair] using
      hQP (LambdaTree.sectionParameter ε p) z
  refine ⟨Q, hQ, fun p => ?_⟩
  exact (h (p 0) p).trans ((alternating_congr_point n 0 p (fun z => hb z p)).trans
    (alternating_reindex n (matrixDomain ε P) (fun _ => p 0) 0 p)).symm

/-- Complementary diagonals separate Sigma and Pi at every positive finite
level and relative to every fixed original parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The finite-level universal-set construction in §{sec:finite-borel-universal} also has a lightface version obtained by
    effective induction on $n$: at a successor, an index uniformly enumerates the $\lPi^0_n$ sections whose union it codes.
    The corresponding diagonals show $\lSigma^0_n\ne\lPi^0_n$ for every positive integer $n$.
-/
theorem sigma_pi_strict (ε : ℕ → ℕ) (n : ℕ) :
    ∃ D : Set (ℕ → ℕ), Pi ε n D ∧ ¬ Sigma ε n D := by
  let U := universal ε n
  refine ⟨firstCoordinateDiagonal U, ?_, ?_⟩
  · change Sigma ε n (firstCoordinateDiagonal U)ᶜ
    convert universal_diagonalPreimage ε n using 1
    ext p
    simp only [firstCoordinateDiagonal, Set.mem_ofPred_eq, Set.mem_compl_iff, not_not, U]
  · intro hD
    obtain ⟨e, he⟩ := (sigma_iff_universal_section ε n _).mp hD
    exact firstCoordinateDiagonal_ne_section U e he

end LambdaFinite
end PolishSpaceBook
