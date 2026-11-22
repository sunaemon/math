module

public import PolishSpaceBook.LambdaNumericalQueries

@[expose] public section

/-! # Input substitution depending on numerical data

A numerical argument determines a new input accessor. All queries remain
relative to the original parameter.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose closed programs $\LambdaTermName{functionProg}, \LambdaTermName{digitProg}$ compute total numerical
    functions $f(p,z)$ and $g(p,z)$.
    To supply the input $\Sequence{g(p,\NatPair{z}{k})}{k\in\omega}$ to $\LambdaTermName{functionProg}$, form
    $$\begin{aligned}
    \LambdaTermName{subInput}(o,z)&:=\lambdaab{k}{\LambdaTermName{digitProg}o(\LambdaNumericPair\,z\,k)},\\
    \LambdaTermName{composeInput}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{functionProg}(
    \LambdaTermName{subInput}(o,z))z}}.
    \end{aligned}$$
    Expand $\LambdaTermName{subInput}$ and choose its binder fresh. Then, relative to $p$, the term
    $\LambdaTermName{composeInput}o \ChurchNumeral{z}$ computes
    $$f(\Sequence{g(p,\NatPair{z}{k})}{k\in\omega},z).$$
-/
def dataInputAccessor (A O Z : AlphaTerm) : AlphaTerm :=
  lam 43 (app (app A O) (app (app numericalPairTerm Z) (var 43)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose closed programs $\LambdaTermName{functionProg}, \LambdaTermName{digitProg}$ compute total numerical
    functions $f(p,z)$ and $g(p,z)$.
    To supply the input $\Sequence{g(p,\NatPair{z}{k})}{k\in\omega}$ to $\LambdaTermName{functionProg}$, form
    $$\begin{aligned}
    \LambdaTermName{subInput}(o,z)&:=\lambdaab{k}{\LambdaTermName{digitProg}o(\LambdaNumericPair\,z\,k)},\\
    \LambdaTermName{composeInput}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{functionProg}(
    \LambdaTermName{subInput}(o,z))z}}.
    \end{aligned}$$
    Expand $\LambdaTermName{subInput}$ and choose its binder fresh. Then, relative to $p$, the term
    $\LambdaTermName{composeInput}o \ChurchNumeral{z}$ computes
    $$f(\Sequence{g(p,\NatPair{z}{k})}{k\in\omega},z).$$
-/
def dataInputProgram (P A : AlphaTerm) : AlphaTerm :=
  lam 41 (lam 42 (app (app P (dataInputAccessor A (var 41) (var 42))) (var 42)))

theorem dataInputAccessor_fv {A : AlphaTerm} (hA : A.Closed) (z : ℕ) :
    (dataInputAccessor A (var 0) (numeral z)).fv ⊆ {0} := by
  simp only [dataInputAccessor,fv_lam,fv_app,fv_var]
  rw [hA,numeral_closed,numericalPairTerm_closed]
  decide

theorem dataInputAccessor_runs {A : AlphaTerm} {g : (ℕ → ℕ) → ℕ → ℕ}
    (hA : UniformNumericalComputes A g) (p : ℕ → ℕ) (z k : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (dataInputAccessor A (var 0) (numeral z)) (numeral k))
      (numeral (g p (Nat.pair z k))) := by
  have hb : Beta (app (dataInputAccessor A (var 0) (numeral z)) (numeral k))
      (app (app A (var 0)) (app (app numericalPairTerm (numeral z)) (numeral k))) := by
    convert Beta.contract 43 _ (numeral k) using 1 <;> try rfl
    simp [subst_app,subst_var,subst_closed _ _ _ hA.1,
      subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed z)]
  exact (Relation.ReflTransGen.single (.beta hb)).trans
    ((oracle_steps_app_right _ (beta_steps_oracle (numericalPairTerm_apply z k))).trans
      (hA.2 p (Nat.pair z k)))

theorem dataInputProgram_closed {P A : AlphaTerm} (hP : P.Closed) (hA : A.Closed) :
    (dataInputProgram P A).Closed := by
  unfold dataInputProgram dataInputAccessor Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [hP,hA,numericalPairTerm_closed]
  decide

theorem dataInputProgram_start {P A : AlphaTerm} (hP : P.Closed) (hA : A.Closed) (z : ℕ) :
    Relation.ReflTransGen Beta (app (app (dataInputProgram P A) (var 0)) (numeral z))
      (app (app P (dataInputAccessor A (var 0) (numeral z))) (numeral z)) := by
  have h₁ : Beta (app (dataInputProgram P A) (var 0))
      (lam 42 (app (app P (dataInputAccessor A (var 0) (var 42))) (var 42))) := by
    convert Beta.contract 41 _ (var 0) using 1 <;> try rfl
    simp only [dataInputAccessor]
    rw [subst_lam_fresh _ _ 42 41 (by decide) (by simp [fv_var])]
    simp only [subst_app,subst_closed _ _ _ hP]
    rw [subst_lam_fresh _ _ 43 41 (by decide) (by simp [fv_var])]
    simp [subst_app,subst_var,
      subst_closed _ _ _ hA,subst_closed _ _ _ numericalPairTerm_closed]
  have h₂ : Beta (app (lam 42 (app (app P (dataInputAccessor A (var 0) (var 42))) (var 42))) (numeral z))
      (app (app P (dataInputAccessor A (var 0) (numeral z))) (numeral z)) := by
    convert Beta.contract 42 _ (numeral z) using 1
    simp only [dataInputAccessor,subst_app,subst_closed _ _ _ hP]
    rw [subst_lam_fresh _ _ 43 42 (by decide) (by rw [numeral_closed]; simp)]
    simp [subst_app,subst_var,
      subst_closed _ _ _ hA,subst_closed _ _ _ numericalPairTerm_closed]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Two beta steps expose $\LambdaTermName{functionProg}(\LambdaTermName{subInput}(o,\ChurchNumeral{z}))\ChurchNumeral{z}$.
    For each queried numeral $k$, one beta step and numerical pairing turn the accessor call into
    $\LambdaTermName{digitProg}o\ChurchNumeral{\NatPair{z}{k}}$, which returns the required digit by hypothesis.
    The substitution theorem in §{sec:lambda-input-composition} replaces each query in the finite computation
    of $\LambdaTermName{functionProg}$ by this computation of $\LambdaTermName{digitProg}$. Both component programs
    terminate on every numerical input;
    the resulting program is closed and queries only the original parameter.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose closed programs $\LambdaTermName{functionProg}, \LambdaTermName{digitProg}$ compute total numerical
    functions $f(p,z)$ and $g(p,z)$.
    To supply the input $\Sequence{g(p,\NatPair{z}{k})}{k\in\omega}$ to $\LambdaTermName{functionProg}$, form
    $$\begin{aligned}
    \LambdaTermName{subInput}(o,z)&:=\lambdaab{k}{\LambdaTermName{digitProg}o(\LambdaNumericPair\,z\,k)},\\
    \LambdaTermName{composeInput}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{functionProg}(
    \LambdaTermName{subInput}(o,z))z}}.
    \end{aligned}$$
    Expand $\LambdaTermName{subInput}$ and choose its binder fresh. Then, relative to $p$, the term
    $\LambdaTermName{composeInput}o \ChurchNumeral{z}$ computes
    $$f(\Sequence{g(p,\NatPair{z}{k})}{k\in\omega},z).$$
-/
theorem UniformNumericalComputes.dataInput {P A : AlphaTerm}
    {f g : (ℕ → ℕ) → ℕ → ℕ} (hP : UniformNumericalComputes P f)
    (hA : UniformNumericalComputes A g) :
    UniformNumericalComputes (dataInputProgram P A)
      (fun p z => f (fun k => g p (Nat.pair z k)) z) := by
  refine ⟨dataInputProgram_closed hP.1 hA.1,fun p z => ?_⟩
  apply (beta_steps_oracle (dataInputProgram_start hP.1 hA.1 z)).trans
  have hs := oracle_steps_subst_input (hP.2 (fun k => g p (Nat.pair z k)) z)
    (dataInputAccessor_runs hA p z)
  simpa only [subst_app,subst_var,ite_true,subst_closed _ _ _ hP.1,
    subst_closed _ _ _ (numeral_closed z),subst_closed _ _ _ (numeral_closed _)] using hs

end PolishSpaceBook.NamedLambda.AlphaTerm
