# Weihrauch Reducibility {#sec:weihrauch-reducibility}

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

The prerequisites are represented maps and paired names from §{sec:type-two-lambda-realizers} and
§{sec:tte-represented-constructions}. No measure, randomness, or effective ordinal theory is required. This
chapter defines reductions between multivalued problems and explains how one solver call, together with
computable preprocessing and postprocessing, supplies another solver. By the end, readers should be able to
identify the input representation, the permitted solutions, and the information available to the
postprocessor. The named degrees and comparison table are reference landmarks; their full lattice theory is
left to the cited literature.

<!-- formalization: skip-end -->

## Problems and Reductions {#sec:tte-weihrauch-reducibility}

\begin{mathmeta}
  \vars{p}{Name}
\end{mathmeta}
\index{Weihrauch reducibility}
\index{reducibility!Weihrauch}

<!-- formalization: skip (conceptual comparison among reducibility notions) -->
\termuse{Wadge reducibility} compares sets by continuous preimages, and \termuse{Borel reducibility} compares
classification problems by Borel transformations. **\termdefine{Weihrauch reducibility}** is the corresponding
comparison notion for computational problems. It is central in modern computable analysis because many theorems are not
single-valued functions but multivalued tasks: given input data satisfying a hypothesis, output some object whose
existence is guaranteed by a theorem.

A \termdefineas{Weihrauch problem}{problem} from $\mathbf X$ to $\mathbf Y$ is specified by a domain
$\DomainOf{F}\IncludedIn X$ and a nonempty set $F(x)\IncludedIn Y$ of admissible solutions for every
$x\in\DomainOf{F}$. A
\termdefineas{Weihrauch realizer}{realizer} of $F$ is a partial function
$$\PartialFunctionMap{\Phi}{\BaireSpace}{\BaireSpace}$$
such that, whenever $p$ names $x\in \DomainOf{F}$, the output $\Phi(p)$ names some element of $F(x)$.

\begin{mathmeta}
  \define{WeihrauchReducesTo}
\end{mathmeta}

For problems $F$ from $\mathbf X$ to $\mathbf Y$ and $G$ from $\mathbf U$ to $\mathbf V$, write
$$F\WeihrauchReducesTo G$$
if there are computable partial operators
$$
\PartialFunctionMap{K}{\BaireSpace}{\BaireSpace}
\qquad\text{and}\qquad
\PartialFunctionMap{H}{\BaireSpace}{\BaireSpace}
$$
such that, for every realizer $\Gamma$ of $G$, the map
$$p\longmapsto H\bigl(\NamePair{p}{\Gamma(K(p))}\bigr)$$
is a realizer of $F$. The operator $K$ preprocesses an instance of $F$ into an instance of $G$; a single call to a
solver for $G$ supplies one solution; the pairing code lets the unary operator $H$ postprocess the original input
together with that solution into a solution of the original problem.

<!-- formalization: skip (editorial notation distinction) -->
The roman subscript in $\WeihrauchReducesTo$ distinguishes Weihrauch reducibility from the italic subscript in the Wadge
relation $\le_W$ of §{sec:wadge-reducibility}. The two relations compare different kinds of objects.

<!-- formalization: skip-begin (survey table and external Weihrauch landmarks) -->
This makes \termuse{Weihrauch reducibility} a formal calculus of uniform theorem use:

| reducibility | objects compared | allowed translator |
|--------------|------------------|--------------------|
| Wadge | subsets of Polish spaces | continuous preimage |
| Borel | equivalence relations / classification problems | Borel reduction |
| Weihrauch | computational tasks on represented spaces | computable pre- and postprocessing with one oracle call |

Standard landmarks include closed choice, compact choice, the limit operator, and unique choice. For example, the
intermediate value theorem, the maximum theorem on compact intervals, and weak König's lemma can be represented as
multivalued maps and then compared by $\WeihrauchReducesTo$. A Weihrauch equivalence does not merely say that
two theorems
are both noncomputable; it says that they contain the same uniform computational content.
<!-- formalization: skip-end -->

\begin{mathmeta}
  \define{StrongWeihrauchReducesTo}
\end{mathmeta}

There is also a strong version $F\StrongWeihrauchReducesTo G$ in which the postprocessor may not reuse the
original input after
the call to $G$: its output has the form $H(\Gamma(K(p)))$. Strong reducibility is useful when one wants the oracle call
to contain all information passed from the instance to the solution. The ordinary version $\WeihrauchReducesTo$ is more
flexible and is the default comparison in the Weihrauch lattice [@BrattkaGherardiPauly2021].

## Worked Example: LPO and Natural-Number Closed Choice {#sec:weihrauch-lpo-choice}

\begin{mathmeta}
  \define{LimitedOmniscienceProblem,NaturalChoiceSet,ClosedChoiceNaturals}
  \vars{a,p,q}{Name}
  \vars{i,k,m,n,N,s,t}{Nat}
\end{mathmeta}

Name a natural number by the first coordinate of a Baire name: $\delta_{\NN}(q):=q(0)$. A
\termdefineas{negative name of a subset of the natural numbers}{negative name} $a\in\BaireSpace$ describes the set
$$\NaturalChoiceSet{a}:=\{m\in\NN:\forall s\in\NN,\ a(s)\ne m+1\}.$$
An entry $m+1$ excludes $m$, while entry $0$ excludes nothing. Repetitions and empty stages are allowed.
Every subset of discrete $\NN$ is closed, so this is a negative representation of closed subsets.

The \termdefine{limited principle of omniscience problem} $\LimitedOmniscienceProblem$ asks whether an input name
has a nonzero coordinate:
$$\LimitedOmniscienceProblem(p)=
\begin{cases}
0,&\forall k\in\NN,\ p(k)=0,\\
1,&\exists k\in\NN,\ p(k)\ne0.
\end{cases}$$
The output natural number uses $\delta_{\NN}$. The problem
\termdefine{closed choice on the natural numbers}, denoted by $\ClosedChoiceNaturals$, takes a negative name $a$
with $\NaturalChoiceSet{a}\ne\emptyset$ and permits any output in $\NaturalChoiceSet{a}$, again named by
$\delta_{\NN}$.

\begin{theorem*}[A concrete strong Weihrauch reduction]
$$\LimitedOmniscienceProblem\StrongWeihrauchReducesTo\ClosedChoiceNaturals.$$
The preprocessing and postprocessing below are total lambda-computable operators on names.
\end{theorem*}

\begin{proof}[Proof]
\emph{Preprocessing.} Decode a stage as $s=\NatPair{t}{k}$ and define the negative name $K(p)$ by
$$K(p)(\NatPair{t}{k})=
\begin{cases}
k+2,&t=0\text{ and }p(k)=0,\\
1,&t=1\text{ and }p(k)\ne0,\\
0,&\text{otherwise}.
\end{cases}$$
The two rows have different jobs. Row $0$ excludes $k+1$ exactly when $p(k)=0$.
Row $1$ excludes $0$ as soon as any nonzero input coordinate is found. Hence
$$\NaturalChoiceSet{K(p)}=
\begin{cases}
\{0\},&\forall k\in\NN,\ p(k)=0,\\
\{k+1:k\in\NN,\ p(k)\ne0\},&\exists k\in\NN,\ p(k)\ne0.
\end{cases}$$

Indeed, only the $t=1$ row can exclude $0$, and only the stage $\NatPair{0}{k}$ can exclude $k+1$.
The displayed set is nonempty in both cases. Thus $K$ always supplies a valid instance of $\ClosedChoiceNaturals$
without first deciding which case holds.

\emph{One oracle call and postprocessing.} Let $\Gamma$ be any realizer of $\ClosedChoiceNaturals$ and put
$q:=\Gamma(K(p))$. The natural number $m:=q(0)$ belongs to $\NaturalChoiceSet{K(p)}$.
Define a constant output name by
$$H(q)(n):=\begin{cases}0,&q(0)=0,\\1,&q(0)\ne0.\end{cases}$$
If $m=0$, every coordinate of $p$ is zero. If $m>0$, write $m=k+1$; then $p(k)\ne0$.
Consequently $\delta_{\NN}(H(q))=\LimitedOmniscienceProblem(p)$ for every permitted choice returned by $\Gamma$.
The postprocessor uses only the oracle's answer, so this is a strong reduction.

\begin{mathmeta}
  \forward{LambdaEqual,LambdaZeroTest,LambdaNumericProjection,LambdaAdd,ChurchNumeral}
\end{mathmeta}

\emph{Closed lambda programs.} The numerical projections, equality test, addition, and zero test are the
closed terms of §{sec:lambda-basic-data}. For variables $o,z$, abbreviate
$$\begin{aligned}
&\LambdaTermName{tag}(z):=\LambdaNumericProjection{1}\,z,\\
&\LambdaTermName{index}(z):=\LambdaNumericProjection{2}\,z,\\
&\LambdaTermName{rowZero}(o,z):= \LambdaZeroTest\,(o( \LambdaTermName{index}(z)))\,( \LambdaAdd\,
\LambdaTermName{index}(z)\, \ChurchNumeral{2})\, \ChurchNumeral{0},\\
&\LambdaTermName{rowOne}(o,z):=\LambdaZeroTest\,(o(\LambdaTermName{index}(z)))\,\ChurchNumeral{0}\,\ChurchNumeral{1}.
\end{aligned}$$
Now put
$$\begin{aligned}
&\LambdaTermName{prepareChoice}:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaZeroTest\,\LambdaTermName{tag}(z)\,\LambdaTermName{rowZero}(o,z)\,
\bigl(\LambdaZeroTest\,(\LambdaEqual\,\LambdaTermName{tag}(z)\,\ChurchNumeral{1})\,
\ChurchNumeral{0}\,\\
&\quad \LambdaTermName{rowOne}(o,z)\bigr)
\end{aligned}}},\\
&\LambdaTermName{readChoice}:=\lambdaab{o}{\lambdaab{z}{
\LambdaZeroTest\,(o\ChurchNumeral{0})\,\ChurchNumeral{0}\,\ChurchNumeral{1}}}.
\end{aligned}$$
Expand $\LambdaTermName{tag}$, $\LambdaTermName{index}$, $\LambdaTermName{rowZero}$, $\LambdaTermName{rowOne}$ inside
these abstractions. The numerical routines are closed, and all remaining variables are
bound, so $\LambdaTermName{prepareChoice}$ and $\LambdaTermName{readChoice}$ are closed lambda terms.

Two outer beta steps expose each program body. On input $\ChurchNumeral{s}$ with $s= \NatPair{t}{k}$, the
numerical projections reduce
to $\ChurchNumeral{t}$ and $\ChurchNumeral{k}$, and the query to $o( \LambdaTermName{index}(
\ChurchNumeral{s}))$ returns $\ChurchNumeral{p(k)}$.
Zero testing then gives the stated values of $\LambdaTermName{rowZero}$ and $\LambdaTermName{rowOne}$. The outer
test selects row $0$ when $t=0$;
otherwise equality testing selects row $1$ exactly when $t=1$, and every other row returns zero.

For $\LambdaTermName{readChoice}$, the single query returns $\ChurchNumeral{q(0)}$, whose zero test returns the
required bit. Thus
$$\LambdaInputSteps{p}{\LambdaTermName{prepareChoice}\,o\,\ChurchNumeral{s}}{\ChurchNumeral{K(p)(s)}},\qquad
\LambdaInputSteps{q}{\LambdaTermName{readChoice}\,o\,\ChurchNumeral{n}}{\ChurchNumeral{H(q)(n)}}.$$
All these derivations are finite for arbitrary input names; the names need not themselves be computable.
Numerical-output uniqueness proves that these terms realize exactly the two specified operators.
\end{proof}

\begin{lemma*}[No computable LPO realizer]
The problem $\LimitedOmniscienceProblem$ has no lambda-computable realizer.
\end{lemma*}

\begin{proof}[Proof]
Suppose a closed lambda program realizes $\LimitedOmniscienceProblem$. On the all-zero input name, its computation
of output coordinate $0$ returns $\ChurchNumeral{0}$. Finite use in §{sec:type-two-lambda-continuity} gives a bound
$N$ such that every input agreeing at coordinates $i<N$ admits the same reduction to $\ChurchNumeral{0}$.
Change only coordinate $N$ to $1$. This new input still admits that reduction, but its required output coordinate
is $1$. The realizer must therefore also return $\ChurchNumeral{1}$, contradicting uniqueness of numerical outputs.
\end{proof}

The preprocessor can enumerate an exclusion once a finite query justifies it. It does not choose a member of
$\NaturalChoiceSet{K(p)}$. That choice is precisely what the oracle supplies. The postprocessor then reads the
answer
without using the original input, illustrating the additional restriction in a strong reduction.

<!-- formalization: skip-begin (external Weihrauch classification of perfect-set problems) -->
The classical results in §{sec:perfect-set-theorem} and §{sec:cantor-bendixson} also give rise to uniform
computational problems. Cipriani--Marcone--Valenti [@CiprianiMarconeValenti2025] study their Weihrauch degrees,
distinguishing the task of finding a nonempty perfect subset of an uncountable closed set from computing its
\termuse{perfect kernel} or a Cantor--Bendixson decomposition with an enumeration of the
\termuse{scattered part}. The representations of the input and output are part of each problem's specification;
for some of these tasks, the degree also depends on the underlying Polish space. Their analysis reaches the
level of coanalytic comprehension and connects the existence theorems of the first part of this book with the
uniform computational comparisons developed here. The classifications and their proofs are left to the cited
paper.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (external connections between Weihrauch degrees and realizability) -->
Weihrauch degrees also help construct realizability interpretations. Kihara [@Kihara2025Realizability]
uses Lifschitz-like relative realizability to transfer selected separations between Weihrauch degrees to
separations between principles over intuitionistic Zermelo--Fraenkel set theory, without assuming countable
choice. A complementary connection is his game description of
\termforwardas{Lawvere--Tierney topology}{Lawvere--Tierney topologies} on the effective
topos [@Kihara2023]. That description extends generalized Weihrauch reducibility using imperfect information;
it does not identify the ordinary one-call Weihrauch degrees with the lattice of all such topologies.
§{sec:inside-effective-topos} returns to this connection from the perspective of internal logic.
<!-- formalization: skip-end -->
