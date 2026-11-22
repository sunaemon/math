module

public import PolishSpaceBook.LambdaBairePreimages
public import PolishSpaceBook.LambdaRelativeComposition

@[expose] public section

/-! # Numerical quantifiers with a Baire-space input

The matrix can query arbitrarily far into the input, provided each numerical
trial terminates. No uniform bound on its input use or running time is assumed.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance quantifierListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance quantifierPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

private theorem prefix_getD (x : ℕ → ℕ) {i n : ℕ} (hi : i < n) :
    (seqPrefix x n).getD i 0 = x i := by
  simp [seqPrefix,hi,List.getD_eq_getElem?_getD]

/-- The singleton constant-one sequence has a parameter-free tree test. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First consider any predicate $S(x,i)$ decided by one such total program. Let $F(x)(i)$ be its decision
    bit. This program computes the Baire-space map $F$. The singleton consisting of the constant-one
    sequence has a pair-tree presentation: on equal-length words require every entry of the first word
    to be one, leaving the second word unrestricted. List access, equality, and a bounded product decide
    this finite condition. The computable-inverse-image construction gives a tree presentation of
    $\{x:\forall i\ S(x,i)\}$ as the inverse image of that singleton. No advance bound on the input
    positions read by the decision program is needed.

    For $A$, work on a coded pair $\NamePair{x}{q}$ and test $R(x,n,q(n))$ in row $n$.
    The parameter and the first point coordinate can be passed to the original program, while the
    second coordinate supplies the numerical witness. The explicit accessors in
    §{sec:lambda-graph-tests} give a total row program at the same parameter.
    Apply the preceding construction and project onto $x$. A branch supplies a witness for each $n$;
    conversely, choosing the numerical witnesses gives a sequence $q$. This last step proves existence,
    without asserting that a suitable sequence can be computed from $x$.

    For $\exists n\,\forall k\ R(x,n,k)$, store the chosen number in $q(0)$ and test
    $R(x,q(0),k)$ in row $k$. Again take the inverse image of the constant-one singleton and project.
    Finally apply this construction to $\neg R$ to obtain the complement of $A$.
    All trials terminate by hypothesis, but their running times and input uses may depend on every
    argument. The construction retains the original parameter throughout.
    \end{proof}
-/
theorem projected_allOnes (ε : ℕ → ℕ) : Projected ε {x | ∀ n, x n = 1} := by
  have hread := listGet_computes.comp
    (((projection_computes true).comp (projection_computes false)).pair (projection_computes true))
  have heq := hread.combine (numericalConstant_computes 1)
    equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply
  have hd : LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair => z.2.1.getD z.1 0 = 1) := by
    apply numericalDecision heq ε
    · intro z hz; simpa [Encodable.encode,Encodable.encodeSigma,List.getD_eq_getElem?_getD] using hz
    · intro z hz; simpa [Encodable.encode,Encodable.encodeSigma,List.getD_eq_getElem?_getD] using hz
  have h := projected_forall_finitePrefixTests (p := fun i z => z.1.getD i 0 = 1)
    hd successor_computes
  have he : {x | ∃ q : ℕ → ℕ, ∀ i, (seqPrefix x (i+1)).getD i 0 = 1} = {x | ∀ i, x i = 1} := by
    ext x
    simp only [mem_ofPred_eq,prefix_getD _ (Nat.lt_succ_self _)]
    exact exists_const _
  exact he ▸ h

/-- A total decision program for every row gives a tree for their conjunction. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First consider any predicate $S(x,i)$ decided by one such total program. Let $F(x)(i)$ be its decision
    bit. This program computes the Baire-space map $F$. The singleton consisting of the constant-one
    sequence has a pair-tree presentation: on equal-length words require every entry of the first word
    to be one, leaving the second word unrestricted. List access, equality, and a bounded product decide
    this finite condition. The computable-inverse-image construction gives a tree presentation of
    $\{x:\forall i\ S(x,i)\}$ as the inverse image of that singleton. No advance bound on the input
    positions read by the decision program is needed.

    For $A$, work on a coded pair $\NamePair{x}{q}$ and test $R(x,n,q(n))$ in row $n$.
    The parameter and the first point coordinate can be passed to the original program, while the
    second coordinate supplies the numerical witness. The explicit accessors in
    §{sec:lambda-graph-tests} give a total row program at the same parameter.
    Apply the preceding construction and project onto $x$. A branch supplies a witness for each $n$;
    conversely, choosing the numerical witnesses gives a sequence $q$. This last step proves existence,
    without asserting that a suitable sequence can be computed from $x$.

    For $\exists n\,\forall k\ R(x,n,k)$, store the chosen number in $q(0)$ and test
    $R(x,q(0),k)$ in row $k$. Again take the inverse image of the constant-one singleton and project.
    Finally apply this construction to $\neg R$ to obtain the complement of $A$.
    All trials terminate by hypothesis, but their running times and input uses may depend on every
    argument. The construction retains the original parameter throughout.
    \end{proof}
-/
theorem projected_forall_baire {ε : ℕ → ℕ} {P : AlphaTerm} {R : (ℕ → ℕ) → ℕ → Prop}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P (R x)) :
    Projected ε {x | ∀ n, R x n} := by
  classical
  let F : (ℕ → ℕ) → (ℕ → ℕ) := fun x n => if R x n then 1 else 0
  have hF : ∀ x n, OracleRuns (pairBaire ε x) P n (F x n) := fun x n => (hP x).runs n
  have h := (projected_allOnes ε).computablePreimage (hP (fun _ => 0)).1 hF
  convert h using 1
  ext x
  simp [F]

/-- Keep the fixed parameter and the first point coordinate; discard the witness. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose $\LambdaTermName{namePredicate}$ decides $\mathcal S(x,n,k)$ on input name $\NamePair{ \varepsilon}{x}$
    and numerical argument
    $\NatPair{n}{k}$. To add a witness sequence $q$, supply the new input name
    $\NamePair{\varepsilon}{\NamePair{x}{q}}$. For this input variable $o$ define
    $$\begin{aligned}
    \LambdaTermName{baseInput}(o)&:=\lambdaab{h}{\LambdaNumericPair\,(\LambdaNumericProjection{1}(oh))\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(oh)))},\\
    \LambdaTermName{allExistsArgs}(o,n)&:=\LambdaNumericPair\,n\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on))),\\
    \LambdaTermName{existsAllArgs}(o,k)&:=\LambdaNumericPair\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})))\,k.
    \end{aligned}$$
    Expand the accessors, choosing fresh binders. The two closed row programs are
    $$\begin{aligned}
    \LambdaTermName{nameRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{allExistsArgs}(o,n))}},\\
    \LambdaTermName{nameRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{k}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{existsAllArgs}(o,k))}}.
    \end{aligned}$$
-/
def quantifierInputAccessor : AlphaTerm := mapOutputProgram
  (pairNumerical (numericalProjectionTerm true)
    (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)))
  (queryOutputProgram (liftNumericalProgram numericalIdentity))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each query to $\LambdaTermName{baseInput}(o)$ returns the pair of the original parameter digit and the first
    point digit.
    Thus substitution of this accessor in the computation of $\LambdaTermName{namePredicate}$ supplies exactly its
    required input
    $\NamePair{ \varepsilon}{x}$. The argument program $\LambdaTermName{allExistsArgs}$ computes
    $\NatPair{n}{q(n)}$, and $\LambdaTermName{existsAllArgs}$ computes
    $\NatPair{q(0)}{k}$. Pairing and numerical projections establish these equations after finitely many
    beta/query steps. Composition first computes the numerical argument and then feeds it to
    $\LambdaTermName{namePredicate}$ with
    the substituted accessor. The returned bits therefore decide $\mathcal S(x,n,q(n))$ and $\mathcal S(x,q(0),k)$,
    respectively. Both programs are closed and total at every prescribed input name because
    $\LambdaTermName{namePredicate}$ is.
    \end{proof}
-/
theorem quantifierInputAccessor_computes : UniformNumericalComputes quantifierInputAccessor
    (fun p n => Nat.pair (p n).unpair.1 (p n).unpair.2.unpair.1) := by
  exact numericalIdentity_computes.uniform.query.map
    ((projection_computes true).pair ((projection_computes true).comp (projection_computes false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose $\LambdaTermName{namePredicate}$ decides $\mathcal S(x,n,k)$ on input name $\NamePair{ \varepsilon}{x}$
    and numerical argument
    $\NatPair{n}{k}$. To add a witness sequence $q$, supply the new input name
    $\NamePair{\varepsilon}{\NamePair{x}{q}}$. For this input variable $o$ define
    $$\begin{aligned}
    \LambdaTermName{baseInput}(o)&:=\lambdaab{h}{\LambdaNumericPair\,(\LambdaNumericProjection{1}(oh))\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(oh)))},\\
    \LambdaTermName{allExistsArgs}(o,n)&:=\LambdaNumericPair\,n\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on))),\\
    \LambdaTermName{existsAllArgs}(o,k)&:=\LambdaNumericPair\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})))\,k.
    \end{aligned}$$
    Expand the accessors, choosing fresh binders. The two closed row programs are
    $$\begin{aligned}
    \LambdaTermName{nameRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{allExistsArgs}(o,n))}},\\
    \LambdaTermName{nameRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{k}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{existsAllArgs}(o,k))}}.
    \end{aligned}$$
-/
def forallExistsBaireArgument : AlphaTerm := pairOutputProgram
  (liftNumericalProgram numericalIdentity)
  (mapOutputProgram (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
    (queryOutputProgram (liftNumericalProgram numericalIdentity)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each query to $\LambdaTermName{baseInput}(o)$ returns the pair of the original parameter digit and the first
    point digit.
    Thus substitution of this accessor in the computation of $\LambdaTermName{namePredicate}$ supplies exactly its
    required input
    $\NamePair{ \varepsilon}{x}$. The argument program $\LambdaTermName{allExistsArgs}$ computes
    $\NatPair{n}{q(n)}$, and $\LambdaTermName{existsAllArgs}$ computes
    $\NatPair{q(0)}{k}$. Pairing and numerical projections establish these equations after finitely many
    beta/query steps. Composition first computes the numerical argument and then feeds it to
    $\LambdaTermName{namePredicate}$ with
    the substituted accessor. The returned bits therefore decide $\mathcal S(x,n,q(n))$ and $\mathcal S(x,q(0),k)$,
    respectively. Both programs are closed and total at every prescribed input name because
    $\LambdaTermName{namePredicate}$ is.
    \end{proof}
-/
theorem forallExistsBaireArgument_computes : UniformNumericalComputes forallExistsBaireArgument
    (fun p n => Nat.pair n (p n).unpair.2.unpair.2) :=
  numericalIdentity_computes.uniform.pair
    (numericalIdentity_computes.uniform.query.map
      ((projection_computes false).comp (projection_computes false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose $\LambdaTermName{namePredicate}$ decides $\mathcal S(x,n,k)$ on input name $\NamePair{ \varepsilon}{x}$
    and numerical argument
    $\NatPair{n}{k}$. To add a witness sequence $q$, supply the new input name
    $\NamePair{\varepsilon}{\NamePair{x}{q}}$. For this input variable $o$ define
    $$\begin{aligned}
    \LambdaTermName{baseInput}(o)&:=\lambdaab{h}{\LambdaNumericPair\,(\LambdaNumericProjection{1}(oh))\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(oh)))},\\
    \LambdaTermName{allExistsArgs}(o,n)&:=\LambdaNumericPair\,n\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on))),\\
    \LambdaTermName{existsAllArgs}(o,k)&:=\LambdaNumericPair\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})))\,k.
    \end{aligned}$$
    Expand the accessors, choosing fresh binders. The two closed row programs are
    $$\begin{aligned}
    \LambdaTermName{nameRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{allExistsArgs}(o,n))}},\\
    \LambdaTermName{nameRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{k}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{existsAllArgs}(o,k))}}.
    \end{aligned}$$
-/
def existsForallBaireArgument : AlphaTerm := pairOutputProgram
  (mapOutputProgram (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
    (queryOutputProgram (constantProgram 0)))
  (liftNumericalProgram numericalIdentity)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each query to $\LambdaTermName{baseInput}(o)$ returns the pair of the original parameter digit and the first
    point digit.
    Thus substitution of this accessor in the computation of $\LambdaTermName{namePredicate}$ supplies exactly its
    required input
    $\NamePair{ \varepsilon}{x}$. The argument program $\LambdaTermName{allExistsArgs}$ computes
    $\NatPair{n}{q(n)}$, and $\LambdaTermName{existsAllArgs}$ computes
    $\NatPair{q(0)}{k}$. Pairing and numerical projections establish these equations after finitely many
    beta/query steps. Composition first computes the numerical argument and then feeds it to
    $\LambdaTermName{namePredicate}$ with
    the substituted accessor. The returned bits therefore decide $\mathcal S(x,n,q(n))$ and $\mathcal S(x,q(0),k)$,
    respectively. Both programs are closed and total at every prescribed input name because
    $\LambdaTermName{namePredicate}$ is.
    \end{proof}
-/
theorem existsForallBaireArgument_computes : UniformNumericalComputes existsForallBaireArgument
    (fun p n => Nat.pair (p 0).unpair.2.unpair.2 n) :=
  ((uniform_constant 0).query.map
    ((projection_computes false).comp (projection_computes false))).pair numericalIdentity_computes.uniform

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose $\LambdaTermName{namePredicate}$ decides $\mathcal S(x,n,k)$ on input name $\NamePair{ \varepsilon}{x}$
    and numerical argument
    $\NatPair{n}{k}$. To add a witness sequence $q$, supply the new input name
    $\NamePair{\varepsilon}{\NamePair{x}{q}}$. For this input variable $o$ define
    $$\begin{aligned}
    \LambdaTermName{baseInput}(o)&:=\lambdaab{h}{\LambdaNumericPair\,(\LambdaNumericProjection{1}(oh))\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(oh)))},\\
    \LambdaTermName{allExistsArgs}(o,n)&:=\LambdaNumericPair\,n\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on))),\\
    \LambdaTermName{existsAllArgs}(o,k)&:=\LambdaNumericPair\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})))\,k.
    \end{aligned}$$
    Expand the accessors, choosing fresh binders. The two closed row programs are
    $$\begin{aligned}
    \LambdaTermName{nameRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{allExistsArgs}(o,n))}},\\
    \LambdaTermName{nameRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{k}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{existsAllArgs}(o,k))}}.
    \end{aligned}$$
-/
def quantifierRowProgram (P A : AlphaTerm) : AlphaTerm :=
  relativeComposeProgram (compositionProgram P quantifierInputAccessor) A

theorem quantifierRowProgram_closed {P A : AlphaTerm} (hP : P.Closed) (hA : A.Closed) :
    (quantifierRowProgram P A).Closed :=
  relativeComposeProgram_closed (compositionProgram_closed hP quantifierInputAccessor_computes.1) hA

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each query to $\LambdaTermName{baseInput}(o)$ returns the pair of the original parameter digit and the first
    point digit.
    Thus substitution of this accessor in the computation of $\LambdaTermName{namePredicate}$ supplies exactly its
    required input
    $\NamePair{ \varepsilon}{x}$. The argument program $\LambdaTermName{allExistsArgs}$ computes
    $\NatPair{n}{q(n)}$, and $\LambdaTermName{existsAllArgs}$ computes
    $\NatPair{q(0)}{k}$. Pairing and numerical projections establish these equations after finitely many
    beta/query steps. Composition first computes the numerical argument and then feeds it to
    $\LambdaTermName{namePredicate}$ with
    the substituted accessor. The returned bits therefore decide $\mathcal S(x,n,q(n))$ and $\mathcal S(x,q(0),k)$,
    respectively. Both programs are closed and total at every prescribed input name because
    $\LambdaTermName{namePredicate}$ is.
    \end{proof}
-/
theorem quantifierRowProgram_runs {ε x : ℕ → ℕ} {P A : AlphaTerm}
    (hP : P.Closed) (hA : A.Closed) {n a b : ℕ}
    (ha : OracleRuns (pairBaire ε x) A n a)
    (hp : OracleRuns (pairBaire ε (leftBaire x)) P a b) :
    OracleRuns (pairBaire ε x) (quantifierRowProgram P A) n b := by
  apply relativeComposeProgram_runs
    (compositionProgram_closed hP quantifierInputAccessor_computes.1) hA ha
  apply compositionProgram_runs hP quantifierInputAccessor_computes.1 hp
  intro k
  simpa only [pairBaire,leftBaire,Nat.unpair_pair] using
    quantifierInputAccessor_computes.2 (pairBaire ε x) k

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each query to $\LambdaTermName{baseInput}(o)$ returns the pair of the original parameter digit and the first
    point digit.
    Thus substitution of this accessor in the computation of $\LambdaTermName{namePredicate}$ supplies exactly its
    required input
    $\NamePair{ \varepsilon}{x}$. The argument program $\LambdaTermName{allExistsArgs}$ computes
    $\NatPair{n}{q(n)}$, and $\LambdaTermName{existsAllArgs}$ computes
    $\NatPair{q(0)}{k}$. Pairing and numerical projections establish these equations after finitely many
    beta/query steps. Composition first computes the numerical argument and then feeds it to
    $\LambdaTermName{namePredicate}$ with
    the substituted accessor. The returned bits therefore decide $\mathcal S(x,n,q(n))$ and $\mathcal S(x,q(0),k)$,
    respectively. Both programs are closed and total at every prescribed input name because
    $\LambdaTermName{namePredicate}$ is.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose $\LambdaTermName{namePredicate}$ decides $\mathcal S(x,n,k)$ on input name $\NamePair{ \varepsilon}{x}$
    and numerical argument
    $\NatPair{n}{k}$. To add a witness sequence $q$, supply the new input name
    $\NamePair{\varepsilon}{\NamePair{x}{q}}$. For this input variable $o$ define
    $$\begin{aligned}
    \LambdaTermName{baseInput}(o)&:=\lambdaab{h}{\LambdaNumericPair\,(\LambdaNumericProjection{1}(oh))\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(oh)))},\\
    \LambdaTermName{allExistsArgs}(o,n)&:=\LambdaNumericPair\,n\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on))),\\
    \LambdaTermName{existsAllArgs}(o,k)&:=\LambdaNumericPair\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})))\,k.
    \end{aligned}$$
    Expand the accessors, choosing fresh binders. The two closed row programs are
    $$\begin{aligned}
    \LambdaTermName{nameRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{allExistsArgs}(o,n))}},\\
    \LambdaTermName{nameRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{k}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{existsAllArgs}(o,k))}}.
    \end{aligned}$$
-/
theorem forallExistsBaire_decides {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : (ℕ → ℕ) → ℕ → ℕ → Prop}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P
      (fun z : ℕ => R x z.unpair.1 z.unpair.2)) :
    ∀ x, LambdaRelative.Decides (pairBaire ε x)
      (quantifierRowProgram P forallExistsBaireArgument)
      (fun n => R (leftBaire x) n (rightBaire x n)) := by
  intro x
  refine ⟨quantifierRowProgram_closed (hP (leftBaire x)).1 forallExistsBaireArgument_computes.1,
    fun n => ⟨?_,?_⟩⟩ <;> intro hn
  · apply quantifierRowProgram_runs (hP (leftBaire x)).1 forallExistsBaireArgument_computes.1
      (by simpa only [pairBaire,rightBaire,Nat.unpair_pair,Encodable.encode_nat] using forallExistsBaireArgument_computes.2 (pairBaire ε x) n)
    apply ((hP (leftBaire x)).2 (Nat.pair n (rightBaire x n))).1
    simpa only [Nat.unpair_pair] using hn
  · apply quantifierRowProgram_runs (hP (leftBaire x)).1 forallExistsBaireArgument_computes.1
      (by simpa only [pairBaire,rightBaire,Nat.unpair_pair,Encodable.encode_nat] using forallExistsBaireArgument_computes.2 (pairBaire ε x) n)
    apply ((hP (leftBaire x)).2 (Nat.pair n (rightBaire x n))).2
    simpa only [Nat.unpair_pair] using hn

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each query to $\LambdaTermName{baseInput}(o)$ returns the pair of the original parameter digit and the first
    point digit.
    Thus substitution of this accessor in the computation of $\LambdaTermName{namePredicate}$ supplies exactly its
    required input
    $\NamePair{ \varepsilon}{x}$. The argument program $\LambdaTermName{allExistsArgs}$ computes
    $\NatPair{n}{q(n)}$, and $\LambdaTermName{existsAllArgs}$ computes
    $\NatPair{q(0)}{k}$. Pairing and numerical projections establish these equations after finitely many
    beta/query steps. Composition first computes the numerical argument and then feeds it to
    $\LambdaTermName{namePredicate}$ with
    the substituted accessor. The returned bits therefore decide $\mathcal S(x,n,q(n))$ and $\mathcal S(x,q(0),k)$,
    respectively. Both programs are closed and total at every prescribed input name because
    $\LambdaTermName{namePredicate}$ is.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose $\LambdaTermName{namePredicate}$ decides $\mathcal S(x,n,k)$ on input name $\NamePair{ \varepsilon}{x}$
    and numerical argument
    $\NatPair{n}{k}$. To add a witness sequence $q$, supply the new input name
    $\NamePair{\varepsilon}{\NamePair{x}{q}}$. For this input variable $o$ define
    $$\begin{aligned}
    \LambdaTermName{baseInput}(o)&:=\lambdaab{h}{\LambdaNumericPair\,(\LambdaNumericProjection{1}(oh))\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(oh)))},\\
    \LambdaTermName{allExistsArgs}(o,n)&:=\LambdaNumericPair\,n\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on))),\\
    \LambdaTermName{existsAllArgs}(o,k)&:=\LambdaNumericPair\,
     (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})))\,k.
    \end{aligned}$$
    Expand the accessors, choosing fresh binders. The two closed row programs are
    $$\begin{aligned}
    \LambdaTermName{nameRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{allExistsArgs}(o,n))}},\\
    \LambdaTermName{nameRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{k}{ \LambdaTermName{namePredicate}(
    \LambdaTermName{baseInput}(o))( \LambdaTermName{existsAllArgs}(o,k))}}.
    \end{aligned}$$
-/
theorem existsForallBaire_decides {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : (ℕ → ℕ) → ℕ → ℕ → Prop}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P
      (fun z : ℕ => R x z.unpair.1 z.unpair.2)) :
    ∀ x, LambdaRelative.Decides (pairBaire ε x)
      (quantifierRowProgram P existsForallBaireArgument)
      (fun n => R (leftBaire x) (rightBaire x 0) n) := by
  intro x
  refine ⟨quantifierRowProgram_closed (hP (leftBaire x)).1 existsForallBaireArgument_computes.1,
    fun n => ⟨?_,?_⟩⟩ <;> intro hn
  · apply quantifierRowProgram_runs (hP (leftBaire x)).1 existsForallBaireArgument_computes.1
      (by simpa only [pairBaire,rightBaire,Nat.unpair_pair,Encodable.encode_nat] using existsForallBaireArgument_computes.2 (pairBaire ε x) n)
    apply ((hP (leftBaire x)).2 (Nat.pair (rightBaire x 0) n)).1
    simpa only [Nat.unpair_pair] using hn
  · apply quantifierRowProgram_runs (hP (leftBaire x)).1 existsForallBaireArgument_computes.1
      (by simpa only [pairBaire,rightBaire,Nat.unpair_pair,Encodable.encode_nat] using existsForallBaireArgument_computes.2 (pairBaire ε x) n)
    apply ((hP (leftBaire x)).2 (Nat.pair (rightBaire x 0) n)).2
    simpa only [Nat.unpair_pair] using hn

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First consider any predicate $S(x,i)$ decided by one such total program. Let $F(x)(i)$ be its decision
    bit. This program computes the Baire-space map $F$. The singleton consisting of the constant-one
    sequence has a pair-tree presentation: on equal-length words require every entry of the first word
    to be one, leaving the second word unrestricted. List access, equality, and a bounded product decide
    this finite condition. The computable-inverse-image construction gives a tree presentation of
    $\{x:\forall i\ S(x,i)\}$ as the inverse image of that singleton. No advance bound on the input
    positions read by the decision program is needed.

    For $A$, work on a coded pair $\NamePair{x}{q}$ and test $R(x,n,q(n))$ in row $n$.
    The parameter and the first point coordinate can be passed to the original program, while the
    second coordinate supplies the numerical witness. The explicit accessors in
    §{sec:lambda-graph-tests} give a total row program at the same parameter.
    Apply the preceding construction and project onto $x$. A branch supplies a witness for each $n$;
    conversely, choosing the numerical witnesses gives a sequence $q$. This last step proves existence,
    without asserting that a suitable sequence can be computed from $x$.

    For $\exists n\,\forall k\ R(x,n,k)$, store the chosen number in $q(0)$ and test
    $R(x,q(0),k)$ in row $k$. Again take the inverse image of the constant-one singleton and project.
    Finally apply this construction to $\neg R$ to obtain the complement of $A$.
    All trials terminate by hypothesis, but their running times and input uses may depend on every
    argument. The construction retains the original parameter throughout.
    \end{proof}
-/
theorem projected_forall_exists_baire {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : (ℕ → ℕ) → ℕ → ℕ → Prop}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P
      (fun z : ℕ => R x z.unpair.1 z.unpair.2)) :
    Projected ε {x | ∀ n, ∃ m, R x n m} := by
  have h := (projected_forall_baire (forallExistsBaire_decides hP)).projectLeft
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨q,hq⟩ := Classical.skolem.mp hx
    exact ⟨pairBaire x q,by simpa using hq,by simp⟩
  · rintro ⟨p,hp,rfl⟩ n
    exact ⟨rightBaire p n,hp n⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First consider any predicate $S(x,i)$ decided by one such total program. Let $F(x)(i)$ be its decision
    bit. This program computes the Baire-space map $F$. The singleton consisting of the constant-one
    sequence has a pair-tree presentation: on equal-length words require every entry of the first word
    to be one, leaving the second word unrestricted. List access, equality, and a bounded product decide
    this finite condition. The computable-inverse-image construction gives a tree presentation of
    $\{x:\forall i\ S(x,i)\}$ as the inverse image of that singleton. No advance bound on the input
    positions read by the decision program is needed.

    For $A$, work on a coded pair $\NamePair{x}{q}$ and test $R(x,n,q(n))$ in row $n$.
    The parameter and the first point coordinate can be passed to the original program, while the
    second coordinate supplies the numerical witness. The explicit accessors in
    §{sec:lambda-graph-tests} give a total row program at the same parameter.
    Apply the preceding construction and project onto $x$. A branch supplies a witness for each $n$;
    conversely, choosing the numerical witnesses gives a sequence $q$. This last step proves existence,
    without asserting that a suitable sequence can be computed from $x$.

    For $\exists n\,\forall k\ R(x,n,k)$, store the chosen number in $q(0)$ and test
    $R(x,q(0),k)$ in row $k$. Again take the inverse image of the constant-one singleton and project.
    Finally apply this construction to $\neg R$ to obtain the complement of $A$.
    All trials terminate by hypothesis, but their running times and input uses may depend on every
    argument. The construction retains the original parameter throughout.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Numerical quantifiers with a Baire-space input
-/
theorem projected_exists_forall_baire {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : (ℕ → ℕ) → ℕ → ℕ → Prop}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P
      (fun z : ℕ => R x z.unpair.1 z.unpair.2)) :
    Projected ε {x | ∃ n, ∀ m, R x n m} := by
  have h := (projected_forall_baire (existsForallBaire_decides hP)).projectLeft
  convert h using 1
  ext x
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨pairBaire x (fun _ => n),by simpa using hn,by simp⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨rightBaire p 0,hp⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    To decide the negated predicate, replace $P$ by the closed term
    $$P^-:=\lambdaab{o}{\lambdaab{z}{\LambdaZeroTest\,(Poz)\,\ChurchNumeral{1}\,\ChurchNumeral{0}}}.$$
    The original output is zero or one, so the zero test reverses these two answers in finitely many
    beta steps. Use $P^-$ in the second row construction for the complement of the universal-existential
    condition. The constant-one target tree tests $s(i)=1$ for $i<|s|$ by list access, equality, and a
    bounded product, with equal word lengths imposed. The inverse-image and projection programs then
    supply the trees in §{sec:edst-baire-quantifiers}. Their correctness uses totality of each row, without
    requiring a uniform time or input-use bound.
-/
theorem negatedBaireMatrix_decides {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : (ℕ → ℕ) → ℕ → ℕ → Prop}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P
      (fun z : ℕ => R x z.unpair.1 z.unpair.2)) :
    ∀ x, LambdaRelative.Decides (pairBaire ε x) (mapOutputProgram reverseZeroTerm P)
      (fun z : ℕ => ¬ R x z.unpair.1 z.unpair.2) := by
  intro x
  refine ⟨mapOutputProgram_closed reverseZero_computes.1 (hP x).1,fun n => ⟨?_,?_⟩⟩
  · intro hn
    simpa using mapOutputProgram_runs reverseZero_computes.1 (hP x).1
      (((hP x).2 n).2 hn) (reverseZero_computes.2 0)
  · intro hn
    simpa using mapOutputProgram_runs reverseZero_computes.1 (hP x).1
      (((hP x).2 n).1 (not_not.mp hn)) (reverseZero_computes.2 1)

/-- Both numerical quantifier orders, with arbitrary input queries in the matrix. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Numerical quantifiers with a Baire-space input
-/
theorem complemented_forall_exists_baire {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : (ℕ → ℕ) → ℕ → ℕ → Prop}
    (hP : ∀ x, LambdaRelative.Decides (pairBaire ε x) P
      (fun z : ℕ => R x z.unpair.1 z.unpair.2)) :
    Complemented ε {x | ∀ n, ∃ m, R x n m} := by
  refine ⟨projected_forall_exists_baire hP,?_⟩
  convert projected_exists_forall_baire (R := fun x n m => ¬ R x n m)
    (negatedBaireMatrix_decides hP) using 1
  ext x
  simp

end LambdaTree
end PolishSpaceBook
