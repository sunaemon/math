module

public import PolishSpaceBook.LambdaRelativeComposition
public import PolishSpaceBook.LambdaProducts

@[expose] public section

/-! # Iterating a numerical lambda program at a fixed parameter

The input pairs an initial numerical state and an iteration count. A Church
numeral directly repeats the supplied program; each call keeps the same input
name. No separate language for states or transitions is introduced.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Input `(initial state, number of updates)`. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first construct an iterator that retains its oracle argument. For a closed program $P$, put
    \begin{mathmeta}
      \define{LambdaIterateProgram}
    \end{mathmeta}
    $$\LambdaIterateProgram{P}:=\lambdaab{o}{\lambdaab{z}{
     (\LambdaNumericProjection{2}z)(Po)(\LambdaNumericProjection{1}z)}}.$$
    If $P$ computes a total numerical function $f$ at parameter $\varepsilon$, this program computes
    $\NatPair{x}{n}\mapsto f^n(x)$ at the same parameter, where $f^0(x)=x$.
-/
def relativeIterationProgram (P : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app (app (app (numericalProjectionTerm false) (var 2))
    (app P (var 1))) (app (numericalProjectionTerm true) (var 2))))

theorem relativeIterationProgram_closed {P : AlphaTerm} (hP : P.Closed) :
    (relativeIterationProgram P).Closed := by
  unfold relativeIterationProgram Closed
  simp only [fv_lam,fv_app,fv_var,show P.fv = ∅ from hP,
    show (numericalProjectionTerm false).fv = ∅ from (projection_computes false).1,
    show (numericalProjectionTerm true).fv = ∅ from (projection_computes true).1]
  decide

theorem relativeIterationProgram_start {P : AlphaTerm} (hP : P.Closed) (z : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (relativeIterationProgram P) (var 0)) (numeral z))
      (app (app (numeral z.unpair.2) (app P (var 0))) (numeral z.unpair.1)) := by
  have h₁ : Beta (app (relativeIterationProgram P) (var 0))
      (lam 2 (app (app (app (numericalProjectionTerm false) (var 2))
        (app P (var 0))) (app (numericalProjectionTerm true) (var 2)))) := by
    convert Beta.contract 1 _ (var 0) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app,subst_var,subst_closed _ _ _ hP,
      subst_closed _ _ _ ((projection_computes false).1),subst_closed _ _ _ ((projection_computes true).1)]
  have h₂ : Beta
      (app (lam 2 (app (app (app (numericalProjectionTerm false) (var 2))
        (app P (var 0))) (app (numericalProjectionTerm true) (var 2)))) (numeral z))
      (app (app (app (numericalProjectionTerm false) (numeral z))
        (app P (var 0))) (app (numericalProjectionTerm true) (numeral z))) := by
    convert Beta.contract 2 _ (numeral z) using 1
    simp [subst_app,subst_var,subst_closed _ _ _ hP,
      subst_closed _ _ _ ((projection_computes false).1),subst_closed _ _ _ ((projection_computes true).1)]
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    ((beta_steps_app_left (beta_steps_app_left ((projection_computes false).2 z) _) _).trans
      (beta_steps_app_right _ ((projection_computes true).2 z)))

theorem iterate_program_runs {ε : ℕ → ℕ} {P : AlphaTerm} (f : ℕ → ℕ)
    (hP : ∀ z, OracleRuns ε P z (f z)) (x n : ℕ) :
    Relation.ReflTransGen (OracleStep ε) (iterateApp (app P (var 0)) (numeral x) n)
      (numeral ((f^[n]) x)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    simpa only [iterateApp,Function.iterate_succ_apply'] using
      (oracle_steps_app_right (app P (var 0)) ih).trans (hP ((f^[n]) x))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The two projections reduce to the numerals for $n$ and $x$. Applying the Church numeral for $n$
    then gives $n$ nested applications of $Po$ to the numeral for $x$. Induction on $n$ combines the
    finite beta/query derivations supplied by $P$ into the required derivation. The oracle argument
    is unchanged throughout. Closedness follows from closedness of $P$ and the projections, with fresh binders.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first construct an iterator that retains its oracle argument. For a closed program $P$, put
    \begin{mathmeta}
      \define{LambdaIterateProgram}
    \end{mathmeta}
    $$\LambdaIterateProgram{P}:=\lambdaab{o}{\lambdaab{z}{
     (\LambdaNumericProjection{2}z)(Po)(\LambdaNumericProjection{1}z)}}.$$
    If $P$ computes a total numerical function $f$ at parameter $\varepsilon$, this program computes
    $\NatPair{x}{n}\mapsto f^n(x)$ at the same parameter, where $f^0(x)=x$.
-/
theorem relativeIterationProgram_runs {ε : ℕ → ℕ} {P : AlphaTerm} (hP : P.Closed)
    (f : ℕ → ℕ) (h : ∀ z, OracleRuns ε P z (f z)) (x n : ℕ) :
    OracleRuns ε (relativeIterationProgram P) (Nat.pair x n) ((f^[n]) x) := by
  have hf : 2 ∉ (app P (var 0)).fv := by simp [fv_app,show P.fv = ∅ from hP,fv_var]
  have hs := relativeIterationProgram_start hP (Nat.pair x n)
  simp only [Nat.unpair_pair] at hs
  exact (beta_steps_oracle hs).trans
    ((beta_steps_oracle (numeral_apply n (app P (var 0)) (numeral x) hf)).trans
      (iterate_program_runs f h x n))

end PolishSpaceBook.NamedLambda.AlphaTerm

namespace PolishSpaceBook.LambdaRelative
open NamedLambda NamedLambda.AlphaTerm

theorem Computes.iterate {ε : ℕ → ℕ} {P : AlphaTerm} {f : ℕ → ℕ}
    (hP : Computes ε P f) :
    Computes ε (relativeIterationProgram P) (fun z : ℕ => (f^[z.unpair.2]) z.unpair.1) := by
  refine ⟨relativeIterationProgram_closed hP.1,fun z => ?_⟩
  simpa only [Nat.pair_unpair,Encodable.encode,id_eq] using
    relativeIterationProgram_runs hP.1 f hP.2 z.unpair.1 z.unpair.2

end PolishSpaceBook.LambdaRelative
