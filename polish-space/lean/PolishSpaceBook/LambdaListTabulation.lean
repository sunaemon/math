module

public import PolishSpaceBook.LambdaListPrefixes

@[expose] public section

/-! # Finite tables computed by closed numerical lambda terms

The accumulator starts empty and appends f(x,k) at stage k. This also
constructs paired words and the witness rows needed by countable operations.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Input is (parameter,(stage,accumulator-code)). -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{LambdaListTabulate}
    \end{mathmeta}
    Let a closed numerical term $F$ compute $f(x,k)$ on the paired input $\NatPair{x}{k}$.
    To generate its first $n$ values while retaining $x$, expand
    $$\begin{aligned}
    B&:=\lambdaab{x}{\ChurchNumeral{0}},\\
    H_F&:=\lambdaab{x}{\lambdaab{k}{\lambdaab{r}{
     \LambdaListAppend\,r\,(\LambdaListCons\,(F(\LambdaNumericPair\,x\,k))\,\ChurchNumeral{0})}}},\\
    \LambdaListTabulate{F}&:=\lambdaab{z}{\LambdaParamRec{B}{H_F}\,
     (\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.
    \end{aligned}$$
    All bound variables are distinct and fresh for the component terms. The initial value is the empty-list
    code; the update appends one newly computed value.
-/
def tabulateStep (F : AlphaTerm) : AlphaTerm :=
  numericalCombine listAppendTerm
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
    (numericalCombine listConsTerm
      (numericalCompose F (pairNumerical (numericalProjectionTerm true)
        (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))
      (numericalConstant 0))

def tabulateStepValue (f : ℕ → ℕ) (z : ℕ) : ℕ :=
  NatListCode.encode (NatListCode.decode z.unpair.2.unpair.2 ++
    [f (Nat.pair z.unpair.1 z.unpair.2.unpair.1)])

theorem tabulateStep_computes {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    NumericalComputes (tabulateStep F) (tabulateStepValue f) := by
  have hv := hF.comp ((projection_computes true).pair
    ((projection_computes true).comp (projection_computes false)))
  have hs := hv.combine (numericalConstant_computes 0) listConsTerm_closed
    (fun a d => Nat.pair a d + 1) listConsTerm_apply
  have hr := ((projection_computes false).comp (projection_computes false)).combine hs
    listAppendTerm_closed (fun a b => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode b))
    listAppendTerm_apply
  unfold tabulateStep
  convert hr using 1
  funext z
  simp [tabulateStepValue,NatListCode.decode]

def listTabulateTerm (F : AlphaTerm) : AlphaTerm := numericalRecursion (numericalConstant 0) (tabulateStep F)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induct on the number of updates. Zero updates return the empty-list code. At stage $k$, pairing computes
    the input for $F$, whose output becomes a singleton list. Concatenation appends it to the accumulated
    first $k$ values, giving exactly the first $k+1$ values in their original order. The parameterized numerical
    recursor realizes this recurrence by beta reduction. Every component terminates, and abstraction binds
    all added variables, proving totality and closedness.
    \end{proof}
-/
theorem tabulate_recursion (f : ℕ → ℕ) (x n : ℕ) :
    primitiveRec 0 (fun k r => tabulateStepValue f (Nat.pair x (Nat.pair k r))) n =
      NatListCode.encode ((List.range n).map (fun k => f (Nat.pair x k))) := by
  induction n with
  | zero => simp [primitiveRec,NatListCode.encode]
  | succ n ih =>
    rw [primitiveRec,ih]
    simp only [tabulateStepValue,Nat.unpair_pair,NatListCode.decode_encode,
      List.range_succ,List.map_append,List.map_cons,List.map_nil]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Finite tabulation by a lambda term
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    If a closed term $F$ computes a total function $f(x,k)$ on input $\NatPair{x}{k}$, then $\LambdaListTabulate{F}$ takes
    $\NatPair{x}{n}$ and returns the list of $f(x,0),\ldots,f(x,n-1)$, empty for $n=0$, as proved in
    §{sec:lambda-finite-tabulation}. Finite grids and coefficient lists use this operation; finite sums use recursion
    with a rational accumulator.
-/
theorem listTabulate_computes {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    NumericalComputes (listTabulateTerm F) (fun z =>
      NatListCode.encode ((List.range z.unpair.2).map (fun k => f (Nat.pair z.unpair.1 k)))) := by
  simpa only [listTabulateTerm,tabulate_recursion] using
    numericalRecursion_computes (numericalConstant_computes 0) (tabulateStep_computes hF)
end PolishSpaceBook.NamedLambda.AlphaTerm
