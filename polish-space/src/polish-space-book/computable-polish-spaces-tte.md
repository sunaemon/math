# Type-2 Theory of Effectivity and Computable Polish Spaces {#sec:computable-polish-tte}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{p}{Name}
\end{mathmeta}
\index{computable Polish space}

<!-- formalization: skip-begin (chapter synthesis) -->
Type-2 Theory of Effectivity is the operational version of the coding philosophy used throughout the text.
A Polish-space point
is accessed by a name in $\BaireSpace$, and a computable map has a lambda realizer transforming names uniformly.
For a continuous realizer, each output coordinate is determined locally by a finite input prefix. Computability further
requires an algorithm that finds enough input information and computes that coordinate.

The presentation matters already for real numbers and open sets: a computable name carries information that
topology alone does not specify. This chapter establishes the realizer language and the effective Cauchy
representation. §{sec:computable-analysis} applies it to compactness, measures, and analysis;
§{sec:computational-choice-randomness} studies effective null tests; and §{sec:weihrauch-reducibility} compares the
information needed to solve multivalued problems.
<!-- formalization: skip-end -->

The \termuse{Cauchy representation} in §{sec:cauchy-representation-admissibility} was purely topological: a name was an
element of
$\BaireSpace$ coding a fast Cauchy sequence, and a continuous translator between name spaces witnessed reducibility of
representations. **\termdefineas{Type-Two Effectivity}{Type-2 Theory of Effectivity}** (TTE) adds the algorithmic
requirement: names are input functions $p:\NN\to\NN$, and a realizer is a lambda program transforming names into names.
The program obtains information from an input name by querying its entries as needed.

<!-- formalization: skip (chapter overview of effective presentation data) -->
Concretely, the earlier representation fixed a dense sequence $\Sequence{q_n}{n\in\omega}$ and read a name $p$ as the
limit of the fast
Cauchy sequence $q_{p(0)},q_{p(1)},\ldots$. This chapter keeps that picture but requires the presentation itself to be
effective: distances between basic points must be computably approximable, rational balls must be enumerable, and the
finite prefix of an input name needed to produce each output digit must be found by an algorithm. Thus the slogan
"continuous maps are continuous realizers" becomes the stricter slogan "computable maps are lambda-computable
realizers."

This is the operational form of computable analysis. A real number is computable when it has a computable
\termuse{Cauchy name}; a function is computable when there is a single lambda realizer which, given any name for an
input as a function argument, produces a name for the output.

<!-- formalization: skip (chapter roadmap and prerequisites) -->
We begin with Type-Two realizers and represented maps, then introduce computable metric presentations and
concrete examples of real numbers. Basic constructions on represented spaces lead to effective open sets,
computable maps, and changes of dense presentation. The binary and signed-digit examples close the chapter:
the continuous contrast in §{sec:binary-expansion-example} becomes a test of which name translations can be
computed. These results are the prerequisites for the later computational chapters.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
読者の前提知識と付録の読む順序を説明する案内。各lambda構成の証明は参照先で別途監査し、この案内を新たな局所定理として数えない。)
-->
Readers familiar with untyped lambda calculus and the basic theory of partial recursive functions can read this chapter
without first reading §{sec:appendix-lambda-computability}. We use Church numerals, capture-avoiding substitution, the
usual closure under composition, primitive recursion, and search, and standard coding and finite simulation of programs.
The additional conventions for infinite input names, realizer domains, and represented maps are stated in this chapter.
§{sec:appendix-lambda-computability} develops the underlying calculus.
§{sec:appendix-type-two-computation} gives the precise input-query, uniqueness, finite-use, composition,
and search results, starting in §{sec:lambda-input-realizers}. These syntax trees and detailed reduction proofs
are not prerequisites for the arguments here.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限データ操作・pairing・tagging・finite trialの証明の所在を示す案内。操作の正しさの主張は後続の各定理と付録で別途監査する。)
--> §{sec:tte-finite-data} summarizes the finite-data operations used below, with their input, output, and
termination conventions. Their lambda terms and beta-reduction proofs are given in §{sec:lambda-basic-data}.
§{sec:appendix-type-two-computation} constructs pairing and tagging of names, finite trials,
and universal evaluation.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \forward{ChurchNumeral,LambdaTrue,LambdaFalse,LambdaZeroTest,LambdaPair,LambdaSucc,LambdaPred,LambdaAdd,LambdaMul}
  \forward{NatPair,LambdaNumericPair,LambdaNumericProjection,LambdaRecursor,LambdaParamRec}
  \forward{LambdaListCode,LambdaListCons,LambdaListAppend,LambdaListLength,LambdaListGet}
  \forward{LambdaListFold,LambdaListTabulate}
  \forward{RationalCode,NamePair,NameProjection,LambdaPairOutputs,LambdaProjectOutput}
  \forward{NameTail,LambdaNameTail,LambdaNamePrefix,LambdaTagBranch,LambdaCoproductCase,LambdaFiniteTrial}
  \forward{LambdaResultSearch,LambdaQueryOutputSearch,LambdaUniformInterpreter,LambdaIndexSpecialization}
\end{mathmeta}

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Begin with Cauchy names and continuous representation translations in
§{sec:cauchy-representation-admissibility}. If lambda computation is new, read the syntax and finite-data
operations in §{sec:lambda-calculus} and §{sec:lambda-basic-data}, using §{sec:lambda-input-realizers} for
input queries. The program-index and reduction-certificate proofs can be consulted when needed. Neither
forcing nor the three effective-DST chapters is required for this entry route. By the end, readers should be
able to state what data a computable metric presentation supplies and verify the input and output names of a
computable map.

<!-- formalization: skip-end -->

## Type-Two Computation and Realizers {#sec:type-two-lambda-realizers}
\index{Type-Two Effectivity}
\index{lambda calculus!Type-Two}

### Computations on Names {#sec:tte-name-computations}

\begin{mathmeta}
  \forward{ChurchNumeral}
  \define{LambdaInputStep,LambdaInputSteps}
  \vars{m,n}{Nat}
  \vars{p}{Name}
\end{mathmeta}

Use ordinary untyped lambda calculus, identifying terms that differ only by renaming bound variables. Write
$\ChurchNumeral{n}$ for the Church numeral representing $n$. A name $p:\NN\to\NN$ is supplied as a function argument:
fix a free variable $o$ for that argument and add the query rule
$$\LambdaInputStep{p}{o\ChurchNumeral{i}}{\ChurchNumeral{p(i)}}.$$
Together with beta-reduction, this gives the one-step relation $\LambdaInputStep{p}{M}{N}$. Only free occurrences of $o$
query the input; a bound occurrence retains its ordinary lambda-calculus meaning. As usual, bound variables may be
renamed to avoid capture. These conventions suffice to use function arguments in the calculations below.

A program $\Phi$ is a closed lambda term. Given $p$ and a coordinate $n$, start with $\Phi\,o\,\ChurchNumeral{n}$. Write
$\LambdaInputSteps{p}{M}{N}$ for a finite sequence of beta/query steps, including the empty sequence. We say that $\Phi$
returns $m$ on this input when
$$
\LambdaInputSteps{p}{\Phi\,o\,\ChurchNumeral{n}}{\ChurchNumeral{m}}.
$$
The name $p$ supplies query answers; it is not required to have a finite lambda description. Church numerals admit no
further steps: they are closed beta-normal forms, and a query requires a free occurrence of the input parameter.

A \termdefine{Type-Two lambda realizer} for a partial map $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ is one
closed term $\Phi$ such that, for every $p\in\DomainOf{F}$ and $n,m\in\NN$,
$$
\LambdaInputSteps{p}{\Phi\,o\,\ChurchNumeral{n}}{\ChurchNumeral{m}}
\quad\Longleftrightarrow\quad F(p)(n)=m.
$$
Thus each output coordinate is obtained, and every numeral output has the specified value. No condition is imposed
outside the domain. In particular, the domain may be smaller than the set of names on which all coordinate computations
terminate. The same closed term must work for every valid name and every coordinate; choosing a different term
separately for each name does not suffice. A partial map on names is called computable when it has such a realizer.

### Numerical Outputs {#sec:type-two-lambda-confluence}

<!-- formalization: skip (external input or background; see coverage-scope-review.json) -->
\begin{recall*}[\termdefineas{input-query confluence theorem}{Confluence with input queries}]
For every name $p$, if $\LambdaInputSteps{p}{M}{N}$ and $\LambdaInputSteps{p}{M}{P}$, there is a term $Q$ such that
$\LambdaInputSteps{p}{N}{Q}$ and $\LambdaInputSteps{p}{P}{Q}$. In particular, two numeral outputs from the same term
have the same natural-number value.
\end{recall*}

This is the usual confluence property with the input function held fixed. It makes numerical output unambiguous. The
complete reduction proof is given in §{sec:lambda-input-confluence}; the applications in this chapter use only the
stated conclusion.

Consequently, to verify that a closed term realizes $F$, it suffices to exhibit a reduction to $\ChurchNumeral{F(p)(n)}$
for every valid name $p$ and coordinate $n$. The theorem rules out every other numerical output. For example,
$\lambdaab{a}{a}$ realizes the identity on names: one beta step exposes the query $o\ChurchNumeral{n}$. The term
$\lambdaab{a}{\lambdaab{b}{\ChurchNumeral{m}}}$ realizes the constant name whose every coordinate is $m$: two beta steps
return that numeral. Both terms are closed.

### Continuity and Finite Use {#sec:type-two-lambda-continuity}

\begin{mathmeta}
  \vars{c}{Name}
\end{mathmeta}

The finite-use argument concerns a finite beta/query derivation of the lambda term itself. It does not require a
translation into another programming language or a prescribed evaluation strategy.

\begin{lemma*}[\termdefineas{Type-Two finite-use lemma}{Finite use and continuity}]
If a closed program $\Phi$ returns $m$ on input $p$ at coordinate $n$, there is a finite prefix length $k$ such that
every name agreeing with $p$ below $k$ makes the same program return $m$ at coordinate $n$. Consequently, every
computable $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ is continuous on its domain with the subspace topology.
The domain need not be open or decidable.
\end{lemma*}

\begin{proof}[Proof]
Take a terminating computation at the given input and coordinate. It makes finitely many queries, including any
addresses chosen from earlier answers. Choose $k$ larger than every queried address. A name agreeing on this prefix
gives the same answers, so the same finite computation returns the same value.

For a realizer and a fixed output coordinate, start with a reduction to its required numeral. Intersect the cylinder
supplied by finite use with the specified name domain. At each name in this intersection, the same reduction still
returns the original value, so the exact-output condition in the definition of a realizer makes the coordinate function
constant there. It is therefore continuous into the discrete natural numbers. Continuity into Baire space is equivalent
to continuity of every coordinate, which proves the assertion. Restricting the domain retains the same closed lambda
term and needs no decision procedure for membership in the domain.
\end{proof}

The finite-use bound $k=k(p,n)$ is a local modulus of continuity. Computability strictly refines continuity, but the
refinement has two parts. A realizer must eventually find enough input to determine the $n$-th output coordinate, and it
must also compute the value of that coordinate. A continuous function with a computable modulus need not be computable:
the constant map $p\mapsto c$ has the trivial modulus for every $c\in\BaireSpace$, but it is computable only when the
point $c$ is \termforwardas{computable point}{computable}.


### Represented Spaces and Their Maps {#sec:tte-realizers}

\begin{mathmeta}
  \vars{X,Y,Z}{Set}
  \vars{p}{Name}
\end{mathmeta}
\index{realizer}
\index{represented space}

A \termdefine{represented space} is a pair
$$\mathbf X=\Pair{X}{\delta_X}$$
where $X$ is a set and $\PartialFunctionMap{\delta_X}{\BaireSpace}{X}$ is a partial function whose range is all of $X$.
A point $p\in \DomainOf{\delta_X}$ is a \termdefineas{represented-space name}{name} of $x$ when $\delta_X(p)=x$. The
topology induced by $\delta_X$ is the final topology: $U\IncludedIn X$ is open when $\delta_X^{-1}(U)$ is open in
$\DomainOf{\delta_X}$. For
\termuseas{admissible representation of topological space}{admissible representations} of Polish spaces this recovers
the original topology.

Let $\PartialFunctionMap{\delta_X}{\BaireSpace}{X}$ and $\PartialFunctionMap{\delta_Y}{\BaireSpace}{Y}$ be
representations. A partial map
$$\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$$
\termdefineas{represented-space realization}{realizes} $f:X\to Y$ if
$$\delta_Y(F(p))=f(\delta_X(p)) \qquad (p\in \DomainOf{\delta_X}).$$
The function $f$ is:

*   \termdefine{continuously realizable} if some continuous $F$ realizes it;
*   \termdefine{computably realizable} if some \termuse{Type-Two lambda realizer} computes such an $F$.

\begin{recall*}[Continuous-realizer characterization]
For \termuseas{admissible representation of topological space}{admissible representations} of Polish spaces,
continuously realizable maps are exactly continuous maps.
\end{recall*}

\begin{proof}[Proof] Suppose first that $F$ is a continuous realizer of $f:X\to Y$. If $U\IncludedIn Y$ is
open, then, restricting the inverse image under $F$ to $\DomainOf{\delta_X}$,
$$
\delta_X^{-1}(f^{-1}(U))=F^{-1}(\delta_Y^{-1}(U))
$$
is open in $\DomainOf{\delta_X}$. The final topology induced by $\delta_X$ therefore makes $f^{-1}(U)$ open. Conversely,
if $f$ is continuous, then $f\circ\delta_X:\DomainOf{\delta_X}\to Y$ is a continuous partial map. The partial-map form
of admissibility recalled in §{sec:kreitz-weihrauch-admissibility} gives a continuous map
$F:\DomainOf{\delta_X}\to\DomainOf{\delta_Y}$ with $\delta_Y\circ F=f\circ\delta_X$, so $F$ realizes $f$.
\end{proof}

<!-- formalization: skip-begin (external input or explanatory background) -->
Thus admissibility says that the representation has no artificial discontinuities and no artificial extra continuity.
Computability refines ordinary continuity by requiring the finite information used by the realizer to be found
effectively.
<!-- formalization: skip-end -->


\begin{corollary*}[Continuity of computably realizable maps]
A computably realizable map between Polish spaces equipped with admissible representations is continuous.
\end{corollary*}

\begin{proof}[Proof]
Finite use makes the name realizer continuous on the input representation's domain. Composing it with the continuous
output representation gives the original map composed with the input representation. The input representation is a
quotient map by topology recovery in §{sec:kreitz-weihrauch-admissibility}, so continuity descends to the represented
spaces.
\end{proof}

**Composition.** Realizers compose. If $F$ realizes $f:\mathbf X\to\mathbf Y$ and $G$ realizes $g:\mathbf Y\to\mathbf
Z$, then $G\circ F$ realizes $g\circ f$, because
$$
\delta_Z(G(F(p)))
=g(\delta_Y(F(p)))
=g(f(\delta_X(p))).
$$

\begin{lemma*}[\termdefineas{uniform oracle substitution lemma}{Lambda substitution and composition}]
Computable partial maps on names are closed under composition whenever the intermediate names lie in the domain of the
second map. If closed terms $Q$ and $P$ compute the inner and outer maps, respectively, their composite is computed by
the closed term
$$C_{P,Q}:=\lambdaab{a}{\lambdaab{b}{P\,(Q\,a)\,b}}.$$
Here $a,b$ are distinct variables different from $o$. The identity is computed by $\lambdaab{a}{a}$.
\end{lemma*}

\begin{proof}[Proof]
To compute an output coordinate, run the outer program and answer each request for an intermediate digit by running the
inner program at that digit. Every such inner computation terminates on a valid input. The outer computation uses
finitely many requests, so replacing each request by its inner computation still gives a finite computation with the
required output. Substitution implements exactly this procedure in the displayed term. Output uniqueness excludes any
other numeral. The domains require only that every intermediate name be valid for the outer map. The substitution
argument in full is proved in §{sec:lambda-input-composition}.
\end{proof}

Apply this substitution to realizers and the preceding realization identity. Identity and composition are therefore
computably realizable, so represented spaces and computably realizable maps form a category. The composition
construction uses only the specified name domains; no behavior is required on names outside them.

### Finite Data Used in This Chapter {#sec:tte-finite-data}

<!-- formalization: skip (guide to the appendix operations) -->
The constructions below use the following fixed operations. Their definitions, closed lambda terms, and beta-reduction
proofs are collected in §{sec:lambda-basic-data}.

| Data | Operations and outputs | Construction |
|---|---|---|
| Natural numbers | Successor, arithmetic, and numerical comparisons | §{sec:lambda-numeral-operations} |
| Selectors | Choose one of two branches | §{sec:lambda-numeral-operations} |
| Functional pairs | Store two terms and select a component | §{sec:lambda-numeral-operations} |
| Numerical pairs | Encode two numbers and recover both components | §{sec:lambda-numerical-pairing} |
| Rational codes | Addition, strict comparison, and dyadic error bounds | §{sec:lambda-rational-arithmetic} |
| Finite lists | Constructors, concatenation, and traversal | §{sec:lambda-finite-lists} |
| List access | Length, suffixes, and entries with zero defaults | §{sec:lambda-list-access} |
| Iteration | Update an indexed state while retaining parameters | §{sec:lambda-primitive-recursion} |

#### Numbers, Branches, and Pairs {#sec:tte-finite-numbers}

Natural numbers are supplied as Church numerals. Numerical predicates return the numeral one for true and zero for
false; the selectors $\LambdaTrue,\LambdaFalse$ instead select the first and second branch. An unselected branch need
not terminate. Functional pairs store terms; numerical pairs encode two natural numbers as a single numerical input.
The arithmetic operations and numerical projections terminate on every numerical input.

#### Rational Data {#sec:tte-finite-rationals}

\begin{mathmeta}
  \vars{a,b,c}{Nat}
\end{mathmeta}

Use the rational codes of §{sec:lambda-rational-arithmetic}, whose decoded values are $(a-b)/(c+1)$ for $a,b,c\in\NN$.
Addition, strict comparison, and the program producing $2^{-k}$ terminate on every numerical input. Rational lists store
polynomial coefficients and finite approximations; dyadic codes supply error bounds in the metric searches below.

#### Finite Lists and Iteration {#sec:tte-finite-lists}

\begin{mathmeta}
  \vars{k,n,x}{Nat}
\end{mathmeta}

Every natural number decodes to a finite list. The empty-list code is zero, and list access returns entry $j$ when
$j<\Length{s}$, and zero otherwise. List recursion may return a numeral, a pair, or a function. Indexed recursion
retains its
parameters in both the initial value and the update; only the updates actually visited must terminate.

If a closed term $F$ computes a total function $f(x,k)$ on input $\NatPair{x}{k}$, then $\LambdaListTabulate{F}$ takes
$\NatPair{x}{n}$ and returns the list of $f(x,0),\ldots,f(x,n-1)$, empty for $n=0$, as proved in
§{sec:lambda-finite-tabulation}. Finite grids and coefficient lists use this operation; finite sums use recursion
with a rational accumulator.

## Computable Metric Presentations and Real Numbers {#sec:computable-metric-presentations}

\begin{mathmeta}
  \vars{i,j,k,n}{Nat}
  \vars{e,m,s,t,c_a,c_b}{Nat}
  \vars{a,b}{Rat}
  \vars{\delta,\varepsilon,\varepsilon_*}{Real}
  \vars{X}{Set}
  \vars{p}{Name}
\end{mathmeta}

A \termdefine{computable metric presentation} is a triple
$$\mathcal X=\Tuple{X,d,\Sequence{q_n}{n\in\omega}}$$
where $\Pair{X}{d}$ is a nonempty complete separable metric space, $\Sequence{q_n}{n\in\omega}$ is dense in $X$, and the
distance data is effective
in the following uniform sense: the set
$$\{\Tuple{i,j,a,b}\in\omega^2\times\QQ^2 : a<d(q_i,q_j)<b\}$$
is recursively enumerable after fixing an effective coding of rationals. The next proposition justifies the equivalent
formulation by rational approximations.

\begin{mathmeta}
  \forward{NatPair}
\end{mathmeta}

\begin{proposition*}[\termdefineas{Effective distance data equivalence}{Effective distance data equivalence}]
Let $\Sequence{q_n}{n\in\omega}$ be a sequence in a metric space. The joint relation $a<d(q_i,q_j)<b$ on
$\Tuple{i,j,a,b}\in\NN^2\times\QQ^2$ is
recursively enumerable if and only if there is a total computable rational-valued function $A$ such that
$$\Abs{A(i,j,k)-d(q_i,q_j)}\le 2^{-k}$$
for every $i,j,k\in\NN$. In both formulations a single closed lambda program works for all the indicated numerical
inputs: on the left its numeral-output domain is exactly the relation, and on the right it returns a rational code of
the approximation. These are ordinary beta computations, with no input-name queries. Completeness and density are not
needed for the equivalence.
\end{proposition*}

\begin{proof}[Proof]
First suppose that $A$ is given. On input $\Tuple{i,j,a,b}$, put $\varepsilon_k=2^{-k}$ and test, for $k=0,1,\ldots$,
$$a+\varepsilon_k<A(i,j,k)\quad\text{and}\quad A(i,j,k)+\varepsilon_k<b.$$
These rational tests terminate. A successful test implies $a<d(q_i,q_j)<b$ by the error bound. Conversely, if the
distance lies strictly between $a$ and $b$, choose $k$ so that $2\varepsilon_k$ is smaller than both gaps to the
endpoints. Since $A(i,j,k)$ differs from the distance by at most $\varepsilon_k$, both inequalities then hold. Search
through these total tests therefore semidecides the joint relation. Concretely, encode the input by
$\NatPair{\NatPair{i}{j}}{\NatPair{c_a}{c_b}}$, where $c_a,c_b$ code the endpoints. Numerical projections, the
approximation program, rational arithmetic and multiplication of zero-or-one answers give a total closed stage term.
Result search returns the least successful precision and has no numeral output if every stage fails.

Conversely, fix one closed semideciding term $P_e$ for the joint relation. On input $\Tuple{i,j,k}$, enumerate all
triples
$\Tuple{c_a,c_b,t}$ of natural numbers, where $c_a,c_b$ are rational codes and $t=\NatPair{m}{s}$ is a proposed numeral
output
together with a finite certificate-search bound. Check $b<a+2^{-k}$ and apply the total numerical-output candidate
tester to $e$, the encoded interval input, and $t$. If both tests succeed, output $c_a$. Each trial is finite.
Enumerating certificate bounds together with the intervals ensures that a computation without an output cannot block the
search.

To prove termination, put $\delta=d(q_i,q_j)$ and $\varepsilon=2^{-k}$. By density of the rationals choose
$$\delta-\varepsilon<a<\delta<b<a+\varepsilon.$$
The semidecider returns a numeral on this interval. Its finite beta reduction has a certificate, so some pair
$t=\NatPair{m}{s}$ is accepted by the candidate tester. The corresponding triple occurs in the enumeration. Every
accepted interval satisfies $a<\delta<b<a+\varepsilon$, hence $\Abs{a-\delta}<\varepsilon$.
Thus the search defines the required total computable approximation, uniformly in $i,j,k$.
Numerical projections, the rational width test, the candidate tester and
result search construct its closed lambda term. §{sec:lambda-rational-ball-programs} gives both programs and their
reduction proofs.
\end{proof}

The associated Cauchy representation is the one already defined:
$$p \in \DomainOf{\rho_X}
\quad\Longleftrightarrow\quad
d(q_{p(n)},q_{p(m)})\le 2^{-n}\quad(m\ge n),$$
and
$$\rho_X(p)=\lim_n q_{p(n)}.$$
The representation is \termdefineas{effective Cauchy representation}{effective} because the Cauchy-name condition is a
uniformly effectively closed condition on finite coordinates: failure is witnessed by rational bounds proving
$d(q_{p(n)},q_{p(m)})>2^{-n}$ for some $m\ge n$. Metric balls around dense points can likewise be semidecided at
rational precisions from the computable distance data.

For a fixed complete metric, changing the dense sequence preserves computability exactly when the basic points of each
sequence can be approximated uniformly by those of the other. The construction and the converse are proved in
§{sec:tte-effective-dense-changes}. Compatibility of metrics alone does not supply an effective change of presentation.

### Computable and Noncomputable Reals {#sec:tte-real-examples}

\begin{mathmeta}
  \vars{J,e,n,r}{Nat}
  \vars{s}{Nat}
  \vars{a,b,m}{Real}
\end{mathmeta}

For real numbers, computability means that one algorithm produces, from $n\in\NN$, a rational $q_n$ with
$\Abs{x-q_n}\le2^{-n}$. This is equivalent to having a computable fast Cauchy name: shifting the approximation index by
two
gives the required pairwise Cauchy bounds. An exact finite expression for a number and an algorithm for its
approximations are different kinds of information.

\begin{mathmeta}
  \forward{LambdaMul,LambdaRecursor,RationalCode}
\end{mathmeta}

\begin{example*}[A computable irrational: $\sqrt2$]
The real number $\sqrt2$ is irrational and computable.
\end{example*}

\begin{proof}[Proof]
Start with $I_0=\ClosedInterval{1}{2}$. If $I_j=\ClosedInterval{a}{b}$, compute the rational midpoint $m=(a+b)/2$. Put
$I_{j+1}=\ClosedInterval{m}{b}$ when $m^2\le2$,
and $I_{j+1}=\ClosedInterval{a}{m}$ otherwise. To implement this bisection with natural-number operations, write
$$I_j=\ClosedInterval{\frac{k_j}{2^j}}{\frac{k_j+1}{2^j}},\qquad k_0=1.$$
The midpoint test, after multiplication by the positive denominator squared, gives the recurrence
$$k_{j+1}=\begin{cases}
2k_j+1,&(2k_j+1)^2\le2(2^{j+1})^2,\\
2k_j,&(2k_j+1)^2>2(2^{j+1})^2.
\end{cases}$$
These are exact integer comparisons, so no test of equality between real numbers is needed.

Inductively,
$$k_j\le\sqrt2\,2^j\le k_j+1.$$
The initial case is $1\le\sqrt2\le2$. In the first branch of the recurrence the midpoint is at most $\sqrt2$,
so the right half of $I_j$ still contains $\sqrt2$; in the second branch the left half does.
Thus $I_j$ contains $\sqrt2$ and has length $2^{-j}$. Its midpoint at stage $n+2$ is
$$q_n:=\frac{2k_{n+2}+1}{2^{n+3}},\qquad \Abs{q_n-\sqrt2}\le2^{-(n+3)}.$$
Thus $q_n\to\sqrt2$, and for $m\ge n$,
$$\Abs{q_n-q_m}\le2^{-(n+3)}+2^{-(m+3)}\le2^{-(n+2)}\le2^{-n}.$$
This verifies the pairwise bounds required of a fast Cauchy name, as well as its limit.

For completeness, the program can be built from the elementary lambda procedures as follows. The closed term
$$D:=\lambdaab{u}{u\,(\LambdaMul\,\ChurchNumeral{2})\,\ChurchNumeral{1}}$$
computes $j\mapsto2^j$. Compose it with addition, multiplication, and the numerical comparison from
§{sec:lambda-numerical-comparisons} to obtain a closed step term $G$ computing the displayed update from $j,k_j$.
The recursor of §{sec:lambda-primitive-recursion} gives the closed term
$$A:=\LambdaRecursor\,G\,\ChurchNumeral{1},\qquad
A\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{k_j}.$$
The reduction follows by induction on $j$: the initial value is $1$, and each recursion step performs precisely the
integer test and update above.

Use the rational codes of §{sec:lambda-rational-arithmetic}, where $\RationalCode{a}{b}{c}$ represents $(a-b)/(c+1)$.
Compose $A,D$ with addition, multiplication, predecessor, and numerical pairing to produce the code
$$p(n):=\RationalCode{2k_{n+2}+1}{0}{2^{n+3}-1}.$$
Here the predecessor is applied to the positive integer $2^{n+3}$, so the displayed subtraction is ordinary subtraction.
Every component terminates on Church numerals; their composition is a closed term $P$ satisfying
$$P\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{p(n)}.$$
The rational represented by $p(n)$ is exactly $q_n$. The bounds already proved show that $p$ is a computable fast
Cauchy name of $\sqrt2$.

Irrationality is separate: if $\sqrt2=a/b$ in lowest terms with positive integers $a,b$, then $a^2=2b^2$ forces $a$
to be even. Writing $a=2c$ gives $b^2=2c^2$, so $b$ is also even, contradicting coprimality.
\end{proof}

\begin{mathmeta}
  \forward{LambdaAdd,LambdaSucc}
\end{mathmeta}

\begin{example*}[Computing $e$ by its series]
The real number $e=\exp(1)=\sum_{j=0}^{\infty}1/j!$ is computable.
\end{example*}

\begin{proof}[Proof]
Put $S_J:=\sum_{j=0}^{J}1/j!$. Compute its numerator and denominator by the integer recurrences
$$f_0=a_0=1,\qquad f_{j+1}=(j+1)f_j,\qquad a_{j+1}=(j+1)a_j+1.$$
Induction gives $f_j=j!$ and $S_j=a_j/f_j$: adding $1/(j+1)!$ multiplies the old numerator by $j+1$ and adds $1$.
No division of integers is needed to construct this fraction.

For $J,r\in\NN$, each of the $r$ additional factors in $(J+1+r)!$ is at least $2$, so
$$(J+1+r)!\ge(J+1)!\,2^r.$$
Comparing the tail term by term with a geometric series therefore gives
$$\begin{aligned}
0\le e-S_J&=\sum_{r=0}^{\infty}\frac1{(J+1+r)!}\\
&\le\frac1{(J+1)!}\sum_{r=0}^{\infty}2^{-r}=\frac2{(J+1)!}.
\end{aligned}$$
The same factorial inequality with initial factorial $1!$ gives $(J+1)!\ge2^J$.
Thus the explicit choice $J=n+4$ suffices: the rational $q_n:=S_{n+4}$ satisfies
$$\Abs{q_n-e}\le\frac2{(n+5)!}\le2^{-(n+3)}.$$
In particular $q_n\to e$, and the triangle inequality gives
$$\Abs{q_n-q_m}\le2^{-(n+3)}+2^{-(m+3)}\le2^{-n}\qquad(m\ge n).$$
These estimates specify the precision in advance; they require no test on an unknown real-valued error.

Here are closed terms for the two integer recurrences. Define
$$\begin{aligned}
H_f&:=\lambdaab{u}{\lambdaab{v}{\LambdaMul\,(\LambdaSucc\,u)\,v}},\\
H_a&:=\lambdaab{u}{\lambdaab{v}{\LambdaAdd\,(H_fuv)\,\ChurchNumeral{1}}},\\
F&:=\LambdaRecursor\,H_f\,\ChurchNumeral{1},\qquad
A:=\LambdaRecursor\,H_a\,\ChurchNumeral{1}.
\end{aligned}$$
The arithmetic reductions and the recursor theorem give
$$F\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{f_j},\qquad
A\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{a_j}.$$
Indeed, at stage $j$ the step terms return $(j+1)f_j$ and $(j+1)a_j+1$, respectively, so induction proves both
reductions with initial value $1$.

Compose these terms with addition, predecessor, and numerical pairing to output
$$p(n):=\RationalCode{a_{n+4}}{0}{f_{n+4}-1}.$$
Since $f_{n+4}>0$, the subtraction in the denominator code is ordinary subtraction.
The resulting closed term $P$ satisfies
$$P\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{p(n)}.$$
This code represents $a_{n+4}/f_{n+4}=q_n$. The preceding bounds show that $p$ is a computable fast Cauchy name of $e$.
\end{proof}

\begin{mathmeta}
  \forward{LambdaNumericPair,LambdaRationalAdd,RationalValue}
\end{mathmeta}

\begin{example*}[Computing $\pi$ by Machin's formula]
The real number $\pi$ is computable.
\end{example*}

\begin{proof}[Proof]
The arctangent addition and doubling formulas give
$$\begin{aligned}
2\arctan(1/5)&=\arctan(5/12),\\
2\arctan(5/12)&=\arctan(120/119),\\
\arctan(1)+\arctan(1/239)&=\arctan(120/119).
\end{aligned}$$
In each use of the addition formula the product of the two arguments is less than $1$, so no correction by $\pi$ is
needed. Since $\arctan(1)=\pi/4$, these identities prove Machin's formula
$$\pi=16\arctan(1/5)-4\arctan(1/239).$$

For $0\le t<1$, write the first $N$ terms of the arctangent series as
$$T_N(t):=\sum_{j<N}(-1)^j\frac{t^{2j+1}}{2j+1}.$$
The nonnegative magnitudes $t^{2j+1}/(2j+1)$ decrease and are bounded by $t^j$, so they form a summable sequence.
The series sums to $\arctan t$, and the alternating-series estimate bounds the error by the next term:
$$\Abs{T_N(t)-\arctan t}\le\frac{t^{2N+1}}{2N+1}.$$
Both arguments in Machin's formula are at most $1/2$. For $N=n+4$, we have $2N+1\ge n+8$, so each arctangent error
is at most $2^{-(n+8)}$. Consequently the rational
$$q_n:=16T_{n+4}(1/5)-4T_{n+4}(1/239)$$
satisfies
$$\Abs{q_n-\pi}\le(16+4)2^{-(n+8)}\le2^{-(n+3)}.$$
As in the preceding examples, this proves convergence to $\pi$ and the pairwise bounds for a fast Cauchy name.

We next implement these rational partial sums. Represent the alternating sign by two natural numbers:
$$\Pair{u_0}{v_0}=\Pair{1}{0},\qquad \Pair{u_{j+1}}{v_{j+1}}=\Pair{v_j}{u_j}.$$
Taking the difference in the integers, induction gives $u_j-v_j=(-1)^j$. For a fixed positive integer $b$, set
$$c_{b,j}:=\RationalCode{u_j}{v_j}{(2j+1)b^{2j+1}-1}.$$
Its denominator is positive, and its rational value is
$$\RationalValue{c_{b,j}}=\frac{(-1)^j}{(2j+1)b^{2j+1}}.$$
The two sign components are computed by swapping numerical projections in a recursion starting at the code of
$\Pair{1}{0}$.
A second recursion, starting at $1$ and multiplying by $b$ at each step, computes $k\mapsto b^k$.
Compose these recursions with addition, multiplication, predecessor, and pairing. This constructs a closed term $B_b$
with
$$B_b\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{c_{b,j}}.$$
The subtraction in the denominator code is ordinary subtraction because $(2j+1)b^{2j+1}>0$.

The rational-zero code is $\RationalCode{0}{0}{0}=0$. Define the closed step term and recursor
$$\begin{aligned}
H_b&:=\lambdaab{u}{\lambdaab{v}{\LambdaRationalAdd\,(\LambdaNumericPair\,v\,(B_bu))}},\\
Q_b&:=\LambdaRecursor\,H_b\,\ChurchNumeral{0}.
\end{aligned}$$
At step $j$, the accumulator code is added to $c_{b,j}$ by the rational-addition program. Induction on $N$ gives
$$Q_b\ChurchNumeral{N}\to_\beta^*\ChurchNumeral{s_{b,N}},\qquad
\RationalValue{s_{b,N}}=T_N(1/b).$$
Every step terminates and preserves this value identity, including the initial empty sum.

Finally, multiplication of a rational code by a natural number $k$ and negation are the operations
$$\RationalCode{u}{v}{d}\longmapsto\RationalCode{ku}{kv}{d},\qquad
\RationalCode{u}{v}{d}\longmapsto\RationalCode{v}{u}{d}.$$
They use only multiplication, projection, and pairing, and hence have closed lambda implementations.
On input $n$, run $Q_5$ and $Q_{239}$ at $n+4$, multiply their rational outputs by $16$ and $4$, negate the second,
and add them. The resulting closed term $P$ satisfies
$$P\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{p(n)},\qquad \RationalValue{p(n)}=q_n.$$
The error estimate above shows that $p$ is a computable fast Cauchy name of $\pi$.
\end{proof}

Fix an effective enumeration $(\varphi_e)$ of the partial numerical functions computed by closed lambda terms, and let
$$K:=\{e\in\NN:\varphi_e(e)\downarrow\}.$$
Here the downward arrow means that the computation returns a numeral. The set $K$ is recursively enumerable by finite
simulation, but undecidable. Indeed, a decider would give a program that returns zero on $e\notin K$ and diverges on
$e\in K$; applying that program to its own index gives a contradiction.

\begin{mathmeta}
  \define{HaltingReal}
  \forward{LambdaRationalLess,LambdaDyadic,LambdaOutputCandidate}
\end{mathmeta}

\begin{example*}[\termdefineas{halting-set real}{A noncomputable irrational from the halting set}]
The real number
$$\HaltingReal:=\sum_{e\in K}4^{-(e+1)}$$
is noncomputable, hence irrational. It is the limit of a computable increasing sequence of rational numbers, but that
sequence has no computable convergence bound.
\end{example*}

\begin{proof}[Proof]
Put $w_e:=4^{-(e+1)}$ and $S_e:=\sum_{j<e,\,j\in K}w_j$. The geometric series gives
$$\sum_{j\ge0}w_j=\frac13,\qquad \sum_{j>e}w_j=\frac{w_e}{3}.$$
Thus the defining series converges, and removing the prefix gives the two bounds
$$\begin{cases}
0\le\HaltingReal-S_e\le w_e/3,&e\notin K,\\
\HaltingReal-S_e\ge w_e,&e\in K.
\end{cases}$$
Suppose a closed term $P$ computes a rational-code name $p$ of $\HaltingReal$. The Cauchy-name estimate gives
$$\Abs{\RationalValue{p(n)}-\HaltingReal}\le2^{-n}.$$
At $n=2e+5$ the error is at most $w_e/8$. Consequently, writing $q=\RationalValue{p(2e+5)}$, we have
$$\begin{cases}
q-S_e\le 11w_e/24<2w_e/3,&e\notin K,\\
q-S_e\ge 7w_e/8>2w_e/3,&e\in K.
\end{cases}$$
In particular, the rational comparison $S_e+2w_e/3<q$ decides the next digit once the prefix has been recovered.

Here is the recursion on codes that implements this argument. Let $W,H$ be the closed terms computing
$$d_e:=\RationalCode{1}{0}{2^{2e+2}-1},\qquad
h_e:=\RationalCode{2}{0}{3\cdot2^{2e+2}-1}.$$
Their values are $w_e$ and $2w_e/3$. Powers of two, multiplication, predecessor, and numerical pairing construct $W,H$;
both denominators are positive, so the displayed subtractions are ordinary subtraction. A closed term $T$ takes the
encoded pair of $e$ and a rational prefix code $s$. It adds $s$ to $h_e$ using $\LambdaRationalAdd$, evaluates $P$ at
$2e+5$, and compares the two rational codes using $\LambdaRationalLess$. Thus
$$T\ChurchNumeral{\NatPair{e}{s}}\to_\beta^*\ChurchNumeral{b(e,s)},\qquad
b(e,s):=\begin{cases}
1,&\RationalValue{s}+2w_e/3<\RationalValue{p(2e+5)},\\
0,&\text{otherwise}.
\end{cases}$$
All the operations are total on natural inputs.

Start with the zero code $s_0=0$. At step $e$, retain $s_e$ if $b(e,s_e)=0$, and otherwise replace it by the code
obtained by adding $d_e$ to $s_e$. The numerical recursor, with the zero test and rational addition for its step,
therefore gives a closed term $R$ satisfying
$$R\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{s_e}.$$
Induction proves $\RationalValue{s_e}=S_e$: the comparison gives $b(e,s_e)=1$ exactly when $e\in K$, so the update adds
exactly the next summand of the prefix. Hence the closed term
$$D:=\lambdaab{u}{T\,(\LambdaNumericPair\,u\,(R\,u))}$$
returns $1$ on $K$ and $0$ outside $K$, contradicting the diagonal argument. Every rational has a constant computable
name, so $\HaltingReal$ is also irrational. The strict gap in the comparison avoids any ambiguity of positional
expansions.

To construct an increasing approximation, let $c_e(k)\in\{0,1\}$ be the result of the finite certificate test
$\LambdaOutputCandidate$ for $\varphi_e(e)$ at candidate $k$. Thus $e\in K$ exactly when some $c_e(k)=1$. Define
$$K_s:=\{e<s:\exists k<s\ (c_e(k)=1)\},\qquad a_s:=\sum_{e\in K_s}w_e.$$
Both bounds increase with $s$, so $K_s\IncludedIn K_{s+1}$ and $a_s\le a_{s+1}\le\HaltingReal$.
For each fixed $e$, the contribution to $a_s$ is eventually $w_e$ if $e\in K$, and is always zero otherwise.
These contributions are bounded by the summable sequence $\Sequence{w_e}{e\in\omega}$; dominated convergence for series
therefore gives
$a_s\to\HaltingReal$.

The rational codes of $a_s$ are computed by two bounded recursions. For each $e<s$, scan all $k<s$ and retain
whether an accepted certificate has appeared. This flag selects $d_e$ or the zero code. Starting with zero, the outer
recursion adds these selected codes for $e<s$ using $\LambdaRationalAdd$. The parameterized numerical
recursor keeps $s$ available in both loops. Thus a single closed term $A$ computes codes $u_s$ with
$$A\ChurchNumeral{s}\to_\beta^*\ChurchNumeral{u_s},\qquad \RationalValue{u_s}=a_s.$$
For $s=0$, the outer loop is empty and outputs the zero code.
Only finite certificate checks are performed, even when the indexed programs diverge.

Finally, suppose a closed term $M$ computed a total function $h$ with
$$0\le\HaltingReal-a_{h(n)}\le2^{-n}\qquad(n\in\NN).$$
Then $\lambdaab{v}{A\,(M\,v)}$ would compute rational approximations to $\HaltingReal$ with that error bound.
The same digit-reading construction would decide $K$, a contradiction. Thus even this increasing computable
convergent sequence has no computable convergence bound.
\end{proof}

## Basic Constructions on Represented Spaces {#sec:tte-represented-constructions}
\index{represented space!products}
\index{represented space!function space}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
空間構成を読むための案内。valid namesと表現値を確認するという作業方針で、独立した数学的主張や構成はここにはない。)
--> The name operations of §{sec:tte-name-operations} supply the realizers. For each space construction, the
remaining task is to specify its valid names and check their represented values.<!--
formalization: skip-end
-->

### Products, Coproducts, and Subspaces {#sec:tte-space-constructions}

\begin{mathmeta}
  \vars{p,r}{Name}
  \vars{n}{Nat}
  \vars{q}{Name}
\end{mathmeta}

**Products.** For represented spaces $\mathbf X=\Pair{X}{\delta_X}$ and $\mathbf Y=\Pair{Y}{\delta_Y}$, define the
product
representation by
$$\delta_{X\times Y}(r):=
\Pair{\delta_X(\NameProjection{1}{r})}{\delta_Y(\NameProjection{2}{r})},$$
with domain
$$\bigl\{r\in\BaireSpace:\NameProjection{1}{r}\in\DomainOf{\delta_X},\;
\NameProjection{2}{r}\in\DomainOf{\delta_Y}\bigr\}.$$
The inverse identities show that its valid names are exactly the pairs of valid component names. In particular,
$$\delta_{X\times Y}(\NamePair{p}{q})=\Pair{\delta_X(p)}{\delta_Y(q)}.$$
For any point of $X\times Y$, choose names of its two coordinates and pair them. This proves surjectivity, so the
construction is indeed a representation.

\begin{proposition*}[\termdefineas{computable product criterion}{Product criterion}]
A function $h:\mathbf Z\to\mathbf X\times\mathbf Y$ is computable if and only if its coordinate functions $\pi_X\circ h$
and $\pi_Y\circ h$ are computable. In particular, the two coordinate projections from the product are computable.
\end{proposition*}

\begin{proof}[Proof]
Suppose that a closed program $P$ computes a name realizer $H$ of $h$. By §{sec:tte-name-pairs},
$\LambdaProjectOutput{1}{P}$ and $\LambdaProjectOutput{2}{P}$ compute the corresponding projections of $H$. The
definition of the product representation
makes these valid names of the two coordinates of $h(\delta_Z(p))$ for every valid input name $p$. Thus they realize the
coordinate maps.

Conversely, let closed programs $P,Q$ compute name realizers $H_X,H_Y$ of the coordinate maps.
The pairing lemma shows that $\LambdaPairOutputs{P}{Q}$ computes
$$p\longmapsto\NamePair{H_X(p)}{H_Y(p)}.$$
For every valid $p$, the inverse identities place this paired name in the product representation's domain, and the
defining equation sends it to $h(\delta_Z(p))$. This proves the reverse implication. Apply the criterion to the identity
map of the product to obtain computability of its two projections. These constructions use the same fixed lambda
expressions for any supplied component programs; they require no decision procedure for the name domains.
\end{proof}

**Coproducts.** The coproduct $X\disjointUnion Y$ is represented by tagging names:
$$
\delta_{X\disjointUnion Y}(0\concat p)=\iota_X(\delta_X(p)),
\qquad
\delta_{X\disjointUnion Y}(1\concat q)=\iota_Y(\delta_Y(q)).
$$
A valid name has tag zero with a valid name for the left summand as its tail, or tag one with a valid name for the right
summand as its tail. No other tags are valid. Surjectivity follows by taking a name in the relevant summand and
prefixing its tag.

\begin{proposition*}[\termdefineas{computable coproduct criterion}{Coproduct criterion}]
The canonical injections into the coproduct are computable. A map $h:X\disjointUnion Y\to Z$ is computable if and only
if $h\circ\iota_X$ and $h\circ\iota_Y$ are computable.
\end{proposition*}

\begin{proof}[Proof]
The prefixing terms $\LambdaNamePrefix{0}$ and $\LambdaNamePrefix{1}$ send every valid component name to a valid
coproduct name of its image under the corresponding injection. The prefix lemma proves their computability. Composing a
realizer of $h$ with these terms proves the forward implication.

Conversely, let $P,Q$ compute name realizers of the two restricted maps. On a valid coproduct name $p$, the tag is zero
or one, and $\NameTail{p}$ is valid for the selected summand. Its realizer therefore returns a valid output name. The
tag-directed computation lemma shows that the single closed term $\LambdaCoproductCase{P}{Q}$ computes that output name
coordinate by coordinate. Its represented value is $h$ of the input point. There is no requirement that the other
realizer work on the same tail, or that membership in either name domain be decidable.
\end{proof}

**Subspaces.** If $A\IncludedIn X$, restrict the allowed names to those representing points of $A$ and put
$$\delta_A:=\restrict{\delta_X}{\delta_X^{-1}(A)},$$
regarding its values as elements of $A$. Every point still has a name, since the original representation is surjective.
This defines the represented subspace without requiring an algorithm to decide which names belong to its domain.

\begin{proposition*}[\termdefineas{computable represented-subspace restriction}{Restriction of computable realizers}]
The inclusion $A\to X$ is computable. Every computable map $f:X\to Y$ restricts to a computable map on $A$. A map
$g:Y\to A$ is computable exactly when its composite with the inclusion into $X$ is computable. No decidability
assumption on $A$ is needed.
\end{proposition*}

\begin{proof}[Proof]
The inclusion passes the input name through unchanged. The closed term $\lambdaab{o}{o}$ does this: after application to
the name parameter and a numeral, one beta step exposes the requested input query.

For a restriction of the input space, reuse the same closed lambda term on the smaller set of valid names. Its
exact-output property is retained on that domain. If the values of a map lie in the subspace, every output name of its
realizer already belongs to the restricted output domain, so the same term realizes the map with that smaller codomain.
Conversely, regard those same output names as names in the original space; their digits and computed values do not
change. None of these operations tests membership in the subspace.
\end{proof}

\begin{proposition*}[\termdefineas{Admissible represented subspaces}{Admissible represented subspaces}]
Let $\delta_X$ be an admissible representation of a topological space $X$, and give $A\IncludedIn X$ its ordinary
subspace topology. Then the restricted representation $\delta_A$ is admissible. If $A$ is metrizable, a set
$U\IncludedIn A$ is open in $A$ if and only if $\delta_A^{-1}(U)$ is open in $\DomainOf{\delta_A}$.
In particular, when $X$ is metrizable, every represented subspace has the ordinary subspace topology. Neither closedness
nor completeness of the subspace is required.
\end{proposition*}

\begin{proof}[Proof]
The restriction is continuous as a map into the subspace. To prove admissibility, take a continuous partial map $g:E\to
A$, where $E\IncludedIn\BaireSpace$. Composing with the inclusion into $X$ and using the partial-map characterization of
admissibility gives a continuous $H:E\to\DomainOf{\delta_X}$ such that $\delta_X(H(p))=g(p)$, with the right-hand side
regarded as a point of $X$. Every value of $H$ therefore belongs to $\DomainOf{\delta_A}$. Corestricting $H$ to this
domain preserves continuity and gives a lift of $g$ through $\delta_A$. This proves admissibility without any assumption
on $A$.

For the topology assertion, apply the convergent-sequence argument for topology recovery in
§{sec:kreitz-weihrauch-admissibility}; that argument uses metrizability and admissibility, but not completeness. More
explicitly, suppose $\delta_A^{-1}(U)$ is open and $U$ is not. Metrizability gives $x\in U$ and a sequence
$\Sequence{x_n}{n\in\omega}$ in
$\SetDifference{A}{U}$ converging to $x$. Let $e_\infty$ be the zero name and let $e_n$ have a single one at coordinate
$n$. On $E=\{e_\infty\}\cup\{e_n:n\in\NN\}$, the map sending $e_\infty$ to $x$ and $e_n$ to $x_n$ is continuous.
Admissibility lifts it continuously to the restricted name domain. Pulling back the open set $\delta_A^{-1}(U)$ along
this lift makes $\{e_\infty\}$ open in $E$, contradicting $e_n\to e_\infty$. The other implication follows from
continuity. The empty subspace satisfies the assertion trivially, and every subspace of a metrizable space is
metrizable.
\end{proof}

\begin{example*}[\termdefineas{Failure of quotient-map restriction}{Failure of quotient-map restriction}]
There is a total representation of a three-point space which is a quotient map, but whose restriction to a two-point
subspace induces a strictly finer topology than the ordinary subspace topology. Thus restricting a quotient
representation need not preserve the quotient-map property.
\end{example*}

\begin{proof}[Construction and proof]
\begin{samepage}
Put $X=\{a,b,c\}$ and, for $p\in\BaireSpace$, write $P(p)$ for $\exists n\;p(n+1)\ne0$. Define
$$
\delta(p)=
\begin{cases}
a & p(0)=0,\ P(p),\\
b & p(0)=0,\ \neg P(p),\\
b & p(0)\ne0,\ P(p),\\
c & p(0)\ne0,\ \neg P(p).
\end{cases}
$$
\end{samepage}
Zero and nonzero tails with initial tags zero and one supply names of all three points. Give $X$ the quotient topology
induced by $\delta$, so a set is open exactly when its preimage is open in $\BaireSpace$.

Use the names $e_n,e_\infty$ from the preceding proof. Prefixing a fixed tag is continuous, and
$$
\begin{aligned}
\delta(\SingletonSeq{0}\concat e_n)&=a,
&\delta(\SingletonSeq{0}\concat e_\infty)&=b,\\
\delta(\SingletonSeq{1}\concat e_n)&=b,
&\delta(\SingletonSeq{1}\concat e_\infty)&=c.
\end{aligned}
$$
Since $\delta$ is continuous, every open neighborhood of $b$ contains $a$, and every open neighborhood of $c$ contains
$b$. Consequently every open neighborhood of $c$ contains $a$. In the subspace $A=\{a,c\}$, the set $\{c\}$ is therefore
not open.

On the restricted name domain, however, a name has value $c$ exactly when its initial coordinate is nonzero: the
alternative value $b$ has been excluded. Hence
$$\delta_A^{-1}(\{c\})=\{p\in\DomainOf{\delta_A}:p(0)\ne0\}$$
is relatively open, since the zeroth-coordinate projection is continuous and the naturals are discrete. Thus $\{c\}$ is
open for the restricted representation's induced topology. Continuity of the restriction ensures that all ordinary
subspace opens remain open for that induced topology, so the inclusion of topologies is strict.
\end{proof}

### Semidecision and Open Sets {#sec:tte-semidecision}

**\termdefineas{Sierpinski space}{Sierpi\'nski space} and open sets.** Give $\mathbb S=\{\bot,\top\}$ the topology
$\{\varnothing,\{\top\},\mathbb S\}$ and the total representation
$$
\delta_{\mathbb S}(p)=\top \iff \exists n\; p(n)\ne 0,
\qquad
\delta_{\mathbb S}(p)=\bot \iff \forall n\; p(n)=0.
$$
The constant zero and constant one names show surjectivity. For $U\IncludedIn X$, let $\chi_U(x)=\top$ exactly when
$x\in U$. Membership in $U$ is semidecidable from names if one closed lambda program, run with a name $p$ and numerical
input zero, has a numeral output exactly when $\delta_X(p)\in U$. This requirement applies to every valid name; no
behavior is prescribed outside $\DomainOf{\delta_X}$.

The finite-trial lemma in §{sec:tte-finite-trials} supplies a closed term $\LambdaFiniteTrial$. On a name $p$,
program index $e$, input $n$, and stage $k$, it always returns zero for failure or $m+1$ for a certified output $m$.
Every output of the indexed program is certified at some stage, even though the program itself may be partial.

\begin{proposition*}[\termdefineas{Sierpinski semidecision criterion}{Sierpi\'nski semidecision criterion}]
The map $\chi_U:\mathbf X\to\mathbb S$ is computable if and only if membership in $U$ is semidecidable from names. Both
conversions are primitive-recursive transformations of finite lambda-program codes.
\end{proposition*}

\begin{proof}[Proof]
Let $P$ realize $\chi_U$, and let $q$ be its output name on a valid input name $p$. For a free input variable $o$,
define
$$G_o:=\lambdaab{k}{\LambdaZeroTest\,(Pok)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
\qquad I:=\lambdaab{x}{x}.$$
The closed program
$$\lambdaab{o}{\lambdaab{n}{\LambdaResultSearch\,G_o\,I}}$$
ignores $n$ and searches the output digits in order. Every digit is defined. If $j$ is the first nonzero digit, the test
is positive before $j$ and zero at $j$, so the search returns $\ChurchNumeral{j}$. If all digits are zero, every stage
continues and the search has no numeral output, by the result-search lemma in §{sec:lambda-input-universal-evaluation}.
This last assertion includes arbitrary reduction orders, not just the displayed search order. Thus the program is a
semidecider.

Conversely, let $P_e$ be a semidecider. Use the closed program
$$\lambdaab{o}{\LambdaFiniteTrial\,o\,\ChurchNumeral{e}\,\ChurchNumeral{0}}$$
to produce the name whose $k$th digit is the numerical result of the $k$th finite trial. Every digit is defined,
including when the semidecider has no output. A digit is nonzero exactly when that trial succeeds, and some trial
succeeds exactly when $P_e$ has a numeral output on input zero. This name therefore represents $\chi_U(x)$ for every
name of $x$. Both displayed constructions use fixed lambda terms and the given finite program or its index; neither
chooses a program after the input name has been supplied. At the code level, the first construction inserts the supplied
closed term into a fixed syntax template, and the second inserts the numeral for its syntax code. Syntax constructors
and the numeral-code construction are primitive recursive, proving the asserted uniformity.
\end{proof}

The representation of $\mathbb S$ is continuous: the preimage of $\{\top\}$ is the union, over all coordinates, of the
open sets where that coordinate is nonzero. A semidecidable subset therefore has an open preimage in the domain of
names. When the representation is a quotient map, the subset itself is open. We call a represented subset effectively
open when its characteristic map into $\mathbb S$ is computable. At the topological level, $U$ is open exactly when
$\chi_U$ is continuous, since $\{\top\}$ is the only nontrivial open subset of $\mathbb S$.

### Function Spaces and Evaluation {#sec:tte-function-spaces}

\begin{mathmeta}
  \vars{r}{Name}
  \vars{n}{Nat}
  \vars{s}{Seq}
  \vars{a,p,q,w}{Name}
  \vars{N,e,j,v}{Nat}
\end{mathmeta}

The universal interpreter in §{sec:lambda-program-specialization} evaluates a supplied program index on a supplied
numerical input with the same name argument. It preserves both numerical outputs and undefinedness, and fixing
the program index is a primitive-recursive transformation of syntax codes. We use it below to evaluate function names.

\begin{mathmeta}
  \forward{LambdaListCode,LambdaContinuousReader}
\end{mathmeta}

The infinite oracle in a function name is essential for representing arbitrary continuous realizers. The following
construction shows that a single finite reader suffices; all information about the particular realizer can be placed in
its auxiliary oracle.

\begin{samepage}
\begin{theorem*}[\termdefineas{Oracle coding of continuous partial maps}{Oracle coding of continuous partial maps}]
There is a fixed closed lambda term $c$ with the following property. For every subset $D\IncludedIn\BaireSpace$ and
every continuous map $F:D\to\BaireSpace$, there is an auxiliary oracle $r\in\BaireSpace$ such that $c$, with oracle
$\NamePair{r}{p}$ and numerical input $n$, returns $F(p)(n)$ for every $p\in D$ and $n\in\NN$. Conversely, any map
computed on $D$ by a lambda term with such a fixed auxiliary oracle is continuous on $D$. No openness or effective
description of $D$ is required, and the program's behavior outside $D$ is unrestricted.
\end{theorem*}
\end{samepage}

\begin{proof}[Proof]
Encode finite lists by $\LambdaListCode{[]}=0$ and $\LambdaListCode{j::s}=\NatPair{j}{\LambdaListCode{s}}+1$. Use
$\NatPair{n}{\NatPair{\LambdaListCode{s}}{v}}$ for the code of $\Tuple{n,s,v}$. These numerical functions are primitive
recursive and have lambda implementations. Define a certificate relation by
$$
R(n,s,v)\quad\Longleftrightarrow\quad
\forall q\in D\cap\cyl{s},\ F(q)(n)=v.
$$
Let $r$ return one on codes satisfying this relation and zero on all other inputs. This defines an infinite oracle; it
does not assert that the relation is decidable or that the oracle can be computed from a description of $F$.
Certificates for cylinders disjoint from $D$ may be vacuous, but such cylinders never contain a valid input.

For numerical input $n$, search all pairs $\Pair{N}{v}$ in their numerical coding order. At each stage read the prefix
$s=\restrict{p}{N}$ and query $r$ at the code of $\Tuple{n,s,v}$. Return $v$ if the answer is nonzero, and continue
otherwise.
Each trial reads only finitely many input digits and makes one certificate query, so it terminates for every joined
oracle. The prefix reader in §{sec:lambda-input-prefixes} produces the numerical list code of the first $N$ input values
by appending one value at each recursion step. Its accessor may itself be a lambda term, so it also reads the second
component of a joined name. Triple encoding, the two oracle projections, and the test use the numerical lambda terms
already constructed. The uniform search lemma therefore gives a single closed lambda term, independent of $D$ and $F$.
The explicit reader $\LambdaContinuousReader$ and its behavior on arbitrary joined names are proved in
§{sec:lambda-continuous-reader}.

If a trial succeeds on $p\in D$, its prefix satisfies $p\in\cyl{s}$, so the certificate implies $F(p)(n)=v$. Thus every
successful trial gives the correct value. For termination, the coordinate map $q\mapsto F(q)(n)$ is continuous into the
discrete space $\NN$. Its fiber through $p$ is a neighborhood of $p$ in $D$, and the cylinder basis supplies a prefix
$s=\restrict{p}{N}$ on which this coordinate is constantly $F(p)(n)$ relative to $D$. The trial $\Pair{N}{F(p)(n)}$
therefore
succeeds. It occurs at a finite stage of the search; any earlier success has the same value. This proves both
termination and correctness on the whole prescribed domain.

Conversely, fix the auxiliary oracle $r$ and a program computing $F$ on $D$. A terminating computation of $F(p)(n)$ uses
only finitely many coordinates of $\NamePair{r}{p}$. Keep $r$ fixed and require $q\in D$ to agree with $p$ below a
bound for those coordinates. The same computation then returns the same value on $\NamePair{r}{q}$. Hence each output
coordinate is locally constant on $D$, and $F$ is continuous in the product topology.
\end{proof}

\begin{mathmeta}
  \define{RepresentedFunctionSpace}
\end{mathmeta}
For represented spaces $\mathbf X$ and $\mathbf Y$, let the \termdefine{represented function space}
$\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ consist of all maps $f:X\to Y$ that have a continuous realizer. A
function name has the form $a=e\concat r$: its first entry is the syntax index of a closed lambda program $P_e$, and its
tail is an arbitrary auxiliary name. On an input name $p$, the program uses the joined name $\NamePair{r}{p}$ to
compute the output coordinates.
The program enumeration is the one used by the universal lambda interpreter in §{sec:lambda-program-specialization}.

Such a name is valid if every $p\in\DomainOf{\delta_X}$ produces an entire name $q_p\in\DomainOf{\delta_Y}$, and
$\delta_Y(q_p)$ depends only on $\delta_X(p)$. The latter condition is extensionality: different names of the same input
must give the same output point, although the output names themselves may differ. Neither condition is required to be
decidable. Define the value of a valid function name by $f(\delta_X(p))=\delta_Y(q_p)$.

\begin{theorem*}[\termdefineas{Function-space representation theorem}{Function-space representation}]
The preceding rule is a well-defined partial surjection onto $\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$. A
function has a computable name for this representation if and only if it has a computable realizer.
\end{theorem*}

\begin{proof}[Proof]
A valid name determines a function because the input representation is surjective and the output is extensional. The
function is unique: two proposed values agree on every represented input. Fixing the auxiliary oracle, finite use makes
its name realizer continuous on the entire input-name domain. Thus the value belongs to the specified function space.

Conversely, choose a continuous realizer of any member of the function space. The oracle-coding theorem supplies an
auxiliary oracle and a finite program which computes this realizer on all valid input names. Prefix the program index to
that oracle. This is a valid function name with the required value, proving surjectivity without restricting the
function space to computable maps.

Here a name $a$ is computable when one closed lambda term $A$ satisfies
$A\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{a(n)}$ for every $n$. Equivalently, one closed Type-Two program produces
$a$ independently of the supplied input name. In one direction, use $\lambdaab{o}{A}$. In the other direction, supply
the constant-zero name by the closed term $\lambdaab{k}{\ChurchNumeral{0}}$. Input substitution preserves every required
output, and the resulting computation starts from a closed term. No query step is possible from a closed term, and
reduction preserves closedness, so the entire computation consists of beta steps.

If the function name $a$ is computable, let $B$ be a closed program producing it independently of its input. Put
$I:=\lambdaab{o}{o}$ and
$$S:=\LambdaPairOutputs{C_{\LambdaNameTail,B}}{I}.$$
On input $p$, this program produces $\NamePair{\NameTail{a}}{p}$. Hence $C_{P_{a(0)},S}$ realizes the named function,
by input substitution. Conversely, let $P$ be a computable realizer and put $R:=\LambdaProjectOutput{2}{I}$. The closed
program $C_{P,R}$ ignores the auxiliary component of a joined name and runs $P$ on its input component. Choose its
syntax index $e$. Then $e\concat r_0$, where $r_0(n)=0$ for every $n$, is a computable function name for the original
map: prefix the fixed index to the constant-zero name.
\end{proof}

\begin{theorem*}[\termdefineas{Computable evaluation theorem}{Computable evaluation}]
The evaluation map
$$
\mathrm{eval}:\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}\times\mathbf X\to\mathbf Y,
\qquad
\mathrm{eval}(f,x)=f(x),
$$
has one finite realizer that works for every valid function name and argument name.
\end{theorem*}

\begin{proof}[Proof]
Use the already constructed closed terms
$$\begin{aligned}
I&:=\lambdaab{o}{o},\qquad
L:=\LambdaProjectOutput{1}{I},\qquad R:=\LambdaProjectOutput{2}{I},\\
T&:=\LambdaPairOutputs{C_{\LambdaNameTail,L}}{R}.
\end{aligned}$$
For $w=\NamePair{a}{p}$, the program $T$ produces $\NamePair{\NameTail{a}}{p}$. Define the fixed evaluator by
$$E:=\lambdaab{o}{\lambdaab{n}{
\LambdaUniformInterpreter\,(To)\,
\bigl(\LambdaNumericPair\,(Lo\ChurchNumeral{0})\,n\bigr)}}.$$
All component terms are closed, so $E$ is closed. Two beta steps expose its body. The term $Lo\ChurchNumeral{0}$ returns
$a(0)=e$, and numerical pairing supplies the input $\ChurchNumeral{\NatPair{e}{n}}$ to the universal interpreter. Each
digit requested from $To$ is computed by the tail, projection and pairing routines. The input-substitution lemma
therefore carries any output of $P_e$ with name $\NamePair{\NameTail{a}}{p}$ into an output of $E$ with name $w$. This
is the same finite lambda term for every function name, argument name, and coordinate; it need not construct either
infinite component in advance.

For a valid function name and a valid argument name, every such coordinate computation terminates and the resulting
sequence is a valid output name. By the defining extensionality condition, its represented value is the named function
applied to the named argument. This proves computability of evaluation; it never requires a test for whether a function
name is valid.
\end{proof}

\begin{theorem*}[\termdefineas{Computable exponential law}{Computable exponential law}]
If $g:\mathbf Z\times\mathbf X\to\mathbf Y$ is computable, then each section is continuously realizable and the map
$$
\overline g:\mathbf Z\to\RepresentedFunctionSpace{\mathbf X}{\mathbf Y},
\qquad
\overline g(z)(x)=g(z,x),
$$
is computable. Conversely, a computable map into this function space gives a computable map on the product by
evaluation. These operations are inverse and are uniform in finite realizer codes.
\end{theorem*}

\begin{proof}[Proof]
Let a finite program with index $e$ realize $g$. Given a name $p$ of $z$, output $e\concat p$. On an argument name, this
function name runs the original program with the paired names as its oracle, so it realizes the section at $z$. The
section realizer is continuous by finite use with $p$ fixed as its auxiliary oracle. Different names of $z$ give the
same represented section because the original program realizes $g$.

The program producing the function name is exactly $\LambdaNamePrefix{e}$, whose beta/query reductions were proved
above. It outputs the fixed index at coordinate zero and copies one input digit at each later coordinate. The header is
the original realizer index; the infinite parameter remains in the tail. Constructing this prefixing term from the
original code uses only the numeral-code construction and fixed syntax constructors, so it is primitive recursive.

Conversely, let $Q$ realize a map into the function space. With $L,R,E$ as in the evaluation proof, form
$$C_{E,\LambdaPairOutputs{C_{Q,L}}{R}}.$$
On a paired input name, $C_{Q,L}$ computes the function name from the first component, and $R$ reads the second
component. Pair their outputs and apply the fixed evaluator. Input substitution produces each requested intermediate
digit when needed. This is an explicit finite lambda term, and inserting the supplied closed term $Q$ into this fixed
expression is primitive recursive on syntax codes. Evaluation after currying returns the original map on every pair of
points. In the other direction, every resulting section agrees pointwise with the original function-space value, so
extensionality gives equality of the curried maps.
\end{proof}

The code transformations used above have concrete lambda implementations: §{sec:lambda-function-code-transforms}
constructs prefixing and uncurrying directly from syntax constructors and the numeral-code program. For an arbitrary
enumeration index, first specialize the universal evaluator to that index. This gives a closed syntax code with the same
partial numerical behavior for every input name, to which the templates apply. The normalization and subsequent
transformation are both primitive recursive and are computed by closed lambda terms.

The same function-space representation also supports currying for continuous realizers. Here the auxiliary oracle coding
the original realizer must be retained together with the parameter name.

\begin{theorem*}[\termdefineas{Continuous-realizer exponential law}{Continuous-realizer exponential law}]
A map $g:\mathbf Z\times\mathbf X\to\mathbf Y$ has a continuous realizer if and only if there is a continuously
realizable map $h:\mathbf Z\to\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ satisfying $h(z)(x)=g(z,x)$ for all
$z,x$. Such a map $h$ is unique. The function-space representation is exactly the one used in the computable exponential
law; continuity here is continuity of realizers on their name domains.
\end{theorem*}

\begin{proof}[Proof]
Choose a continuous realizer $G$ of $g$. Apply oracle coding once to this entire partial name map, obtaining one
auxiliary oracle $r$ and one finite program $c$. Thus, on a paired input name $\NamePair{p}{q}$, the program computes
the output of $G$ using the oracle $\NamePair{r}{\NamePair{p}{q}}$. The choices of $r$ and $c$ are fixed before
the parameter name $p$ is supplied.

With the projection terms $L,R$ from the evaluation proof, put
$$A:=\LambdaPairOutputs{\LambdaProjectOutput{1}{L}}{
\LambdaPairOutputs{\LambdaProjectOutput{2}{L}}{R}},
\qquad c':=C_{c,A}.$$
On a name $\NamePair{\NamePair{r}{p}}{q}$, the three projections read $r,p,q$ and the two pairings produce $\NamePair{
r}{\NamePair{p}{q}}$. Thus the fixed closed term $A$ changes only the brackets in this triple of names. The
composition lemma carries every required output of $c$ on the latter name to an output of $c'$ on the former name.
Confluence excludes a different numeral output. The term $c'$ is closed and is fixed before $r,p,q$ are supplied. On
named syntax codes, its construction inserts the code of $c$ into one fixed composition template.
§{sec:lambda-function-code-transforms} proves that this operation is primitive recursive and gives its closed lambda
implementation.

Let $e'$ be the index of $c'$. Given a name $p$ of a parameter point $z$, output the function name $e'\concat\NamePair{
r}{p}$. On an argument name $q$, its program computes precisely $G(\NamePair{p}{q})$, so the name represents the
section $x\mapsto g(z,x)$. This section is continuously realizable by finite use with its auxiliary oracle fixed. Since
$G$ realizes $g$, different names of $z$ produce names of the same section.

The name transformation $p\mapsto e'\concat\NamePair{r}{p}$ is continuous: its first coordinate is constant, and each
later coordinate pairs a fixed auxiliary digit with one input digit. This gives a continuous realizer of the section
map. It need not be computable when $r$ is noncomputable.

Conversely, a continuous realizer of $h$ can be paired with the unchanged argument name and followed by the fixed
evaluation realizer. Pairing and composition preserve continuity on the specified name domains, and the evaluator is
continuous by finite use. The composite realizes $g$ by the stated pointwise identity. Finally, any two possible maps
$h$ have the same values at every parameter and argument, so extensionality gives their equality. Thus currying and
evaluation are inverse for continuous realizers as well.
\end{proof}

<!-- formalization: skip-begin (comparison with the effective topos) -->
This construction illustrates the role of realizers in function-space objects. It is related to, but distinct from,
the exponential construction in $\EffCat$: the latter uses natural-number realizability, whereas TTE retains
possibly noncomputable infinite names.
<!-- formalization: skip-end -->

## Cauchy Names and Computable Maps {#sec:tte-polish-as-represented}

### Cauchy Names and Metric Products {#sec:tte-cauchy-products}

\begin{mathmeta}
  \vars{i,j}{Nat}
\end{mathmeta}

A \termuse{computable metric presentation} $\mathcal X=\Tuple{X,d,(q_n)}$ gives a represented space $\Pair{X}{\rho_X}$
by its fast
Cauchy representation. A \termdefine{computable Polish space} is a Polish space equipped with such a computable metric
presentation, viewed through its fast Cauchy representation. The preceding constructions specialize to the expected
operations on computable Polish spaces.

\begin{proposition*}[\termdefineas{Computable metric products}{Computable metric products}]
Let $\mathcal X=\Tuple{X,d_X,(q_i)}$ and $\mathcal Y=\Tuple{Y,d_Y,(r_j)}$ be computable metric presentations. The
maximum metric
$$d_{X\times Y}(\Pair{x}{y},\Pair{x'}{y'}):=\max\{d_X(x,x'),d_Y(y,y')\}$$
and the sequence $s_{\NatPair{i}{j}}:=\Pair{q_i}{r_j}$ give a computable metric presentation of $X\times Y$.
With the pointwise pairing of names in §{sec:tte-name-pairs}, its Cauchy representation
equals the product representation
$\rho_X\times\rho_Y$. In particular, the identity on names is a computable translator in both directions.
\end{proposition*}

\begin{proof}[Proof]
For the maximum metric, convergence and the Cauchy condition are both coordinatewise. Completeness of the two
factors therefore gives completeness of the product, and the metric induces the product topology. The sequence
enumerates every pair of component centers: given $\Pair{x}{y}$ and
$\varepsilon>0$, choose $q_i$ within $\varepsilon$ of $x$ and $r_j$ within $\varepsilon$ of $y$. Then
$$d_{X\times Y}(s_{\NatPair{i}{j}},\Pair{x}{y})<\varepsilon.$$

Let $A_X(i,i',k)$ and $A_Y(j,j',k)$ be the given rational distance approximations with error at most $2^{-k}$.
Define
$$A(\NatPair{i}{j},\NatPair{i'}{j'},k):=\max\{A_X(i,i',k),A_Y(j,j',k)\}.$$
The elementary estimate
$$\Abs{\max\{a,b\}-\max\{x,y\}}\le\varepsilon
\quad\text{if}\quad \Abs{a-x}\le\varepsilon,\ \Abs{b-y}\le\varepsilon$$
shows that $A$ has the same error bound $2^{-k}$. Indeed, both $a,b$ are at most $\max\{x,y\}+\varepsilon$,
and both $x,y$ are at most $\max\{a,b\}+\varepsilon$.

There is a single closed lambda program for $A$. Decode the two center indices by the numerical projections,
retain the precision $k$, and run the supplied distance programs on $\Tuple{i,i',k}$ and $\Tuple{j,j',k}$. Compare the
two
returned rational codes using §{sec:lambda-rational-arithmetic}; return the second code if the first rational is
strictly smaller, and otherwise return the first. Numerical pairing, projections, comparison, and the Church
conditional compose to a closed term. Both distance computations and the comparison terminate on every input.
Selecting one of the existing codes avoids any need to choose a canonical code for the maximum.

For a name $p$, put $p_1:=\NameProjection{1}{p}$ and $p_2:=\NameProjection{2}{p}$. For $m\ge n$,
$$\begin{aligned}
d_{X\times Y}(s_{p(n)},s_{p(m)})\le2^{-n}
\quad\Longleftrightarrow\quad& d_X(q_{p_1(n)},q_{p_1(m)})\le2^{-n}\\
&\text{and}\quad d_Y(r_{p_2(n)},r_{p_2(m)})\le2^{-n}.
\end{aligned}$$
Thus the two representations have exactly the same name domain. Convergence in the maximum metric is coordinatewise,
so on this common domain
$$\rho_{X\times Y}(p)=\Pair{\rho_X(p_1)}{\rho_Y(p_2)}=(\rho_X\times\rho_Y)(p).$$

The closed term $\lambdaab{a}{a}$ therefore realizes both translations: on input name $p$ and coordinate $n$,
one beta step exposes the query $o\ChurchNumeral{n}$, which returns $\ChurchNumeral{p(n)}$.
If the two component names are needed separately, apply the numerical projections to each digit; in the other
direction, pair their digits. The previously constructed pairing and projection programs implement these operations
without changing the precision index or testing membership in a name domain.
\end{proof}

### Effective Open and Closed Sets {#sec:tte-effective-open-closed}

\begin{mathmeta}
  \vars{\ell,N}{Nat}
  \vars{r}{Rat}
  \vars{b,c,e,h,i,j,k,m,n,v,t_*,z_*}{Nat}
  \vars{s}{Seq(Nat)}
  \vars{\theta}{Seq(Prod(Nat,Nat))}
  \vars{p}{Name}
  \forward{LambdaAnswerTableCode,LambdaCertificateCode}
\end{mathmeta}

For a computable Polish space $X$, a subset $U\IncludedIn X$ is \termdefine{effectively open} if there is a lightface
$\lSigma^0_1$ set $V\IncludedIn\BaireSpace$ such that
$$
\rho_X^{-1}(U)=\DomainOf{\rho_X}\cap V.
$$
Thus the preimage is $\lSigma^0_1$ relative to the name space; it need not be $\lSigma^0_1$ as a subset of all of
$\BaireSpace$. By the effective-basis lemma proved below, this is equivalent to giving $U$ as an r.e. union of
rational balls
$$U=\bigcup_{e\in J} \Ball{q_{i_e}}{r_e},$$
where $J$ is recursively enumerable and the centers and rational radii are effectively decoded.

Membership in an effectively open set is semidecidable from a Cauchy name: watch the name until some approximation is
accurate enough to certify containment in one of the listed balls. The complement of an effectively open set is
\termdefine{effectively closed}. Nonmembership in such a closed set is therefore semidecidable: one can eventually
recognize that a point does not belong to the closed set, but cannot in general recognize membership.


**Basic opens.** A rational ball $\Ball{q_i}{r}$ is effectively open because from a Cauchy name $p$ for $x$ one can
search for $n$ with
$$
d(q_{p(n)},q_i)+2^{-n}<r.
$$
If such an $n$ is found, then $x\in \Ball{q_i}{r}$.

To implement the metric searches, use the approximation form of the distance data. Fix a total computable
rational-valued function $A$ such that
$$
\Abs{A(i,j,k)-d(q_i,q_j)}\le 2^{-k}.
$$
The same algorithm must work for all $i,j,k$. The rational operations from
§{sec:tte-finite-data} implement each test below.

\begin{mathmeta}
  \forward{LambdaBallTest,LambdaBallSemidecider}
\end{mathmeta}

\begin{proposition*}[\termdefineas{Uniform semidecision of rational balls}{Uniform semidecision of rational balls}]
Membership in $\Ball{q_i}{r}$, for $r\in\QQ$, is semidecidable from every fast Cauchy name, uniformly in $i$ and a
rational code for $r$. With the distance-approximation program fixed, the transformation from the center and radius
codes to a semideciding program is primitive recursive on syntax codes and is computed by a closed lambda term. In
particular, the characteristic map of each such ball into $\mathbb S$ is computable.
\end{proposition*}

\begin{proof}[Proof]
\clubpenalties 2 10000 0
Put $\varepsilon_n=2^{-n}$ and $A_n=A(p(n),i,n)$. At stage $n$, query $p(n)$, compute $A_n$, and test the rational
inequality
$$A_n+2\varepsilon_n<r.$$
Each stage terminates. If it succeeds, the Cauchy-name estimate and the error bound on $A$ give
$$
d(x,q_i)\le d(x,q_{p(n)})+d(q_{p(n)},q_i)
\le \varepsilon_n+(A_n+\varepsilon_n)<r.
$$
Conversely, if $d(x,q_i)<r$, then
$$
A_n+2\varepsilon_n
\le d(q_{p(n)},q_i)+3\varepsilon_n
\le d(x,q_i)+4\varepsilon_n.
$$
Choose $n$ so large that the last expression is less than $r$. Thus sequential search through the terminating stage
tests halts exactly on names of points in the ball.

To make the program explicit, fix a code $c$ for the radius $r$ and put $b=\NatPair{i}{c}$. Queries, numerical pairing,
the fixed distance-approximation term, and the rational arithmetic just constructed give a closed stage program
$\LambdaBallTest{b}$. On every name and stage it returns one if the displayed inequality holds and zero otherwise. Put
$$G_o:=\lambdaab{k}{\LambdaZeroTest\,(\LambdaBallTest{b}\,o\,k)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
\qquad I:=\lambdaab{x}{x}.$$
The closed term
$$\LambdaBallSemidecider{b}:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_o\,I}}$$
ignores $a$ and returns the least successful stage. If every stage fails, the result-search lemma excludes every numeral
output, under any reduction order. Combined with the two estimates above, this proves exact semidecision on all valid
Cauchy names. The Sierpi\'nski semidecision criterion gives the computable characteristic map.

At the code level, insert the numeral for $b$ into a fixed stage template and then into the displayed search template.
The syntax constructors and the numeral-code program compute this transformation by a closed lambda term; the same
formulas prove primitive recursiveness. The construction is independent of the input name.
§{sec:lambda-rational-ball-programs} gives the stage term, the code templates and their correctness proofs. No positive
lower bound on the distance to the boundary is required as input.
\end{proof}

\begin{proposition*}[\termdefineas{Effective closedness of the Cauchy-name domain}{Effective closedness of the
Cauchy-name domain}]
There is one closed lambda program which returns a numeral on a sequence $p$ exactly when $p\notin\DomainOf{\rho_X}$.
The characteristic map of this complement into $\mathbb S$ is computable when Baire space is represented by the
identity. Thus the domain of the fast Cauchy representation is effectively closed in Baire space.
\end{proposition*}

\begin{proof}[Proof]
Enumerate all triples $\Tuple{n,m,k}$ by the stage index $j=\NatPair{n}{\NatPair{m}{k}}$. For each triple, read $p(n)$
and
$p(m)$ and test
$$
n\le m
\quad\text{and}\quad
2^{-n}+2^{-k}<A(p(n),p(m),k).
$$
Every test terminates. Success implies $d(q_{p(n)},q_{p(m)})>2^{-n}$ by the approximation error bound, so it certifies
an invalid name. Conversely, an invalid name has some $n\le m$ with this strict inequality. Choose $k$ so that
$2\cdot2^{-k}$ is smaller than the positive gap $d(q_{p(n)},q_{p(m)})-2^{-n}$. The approximation error bound then makes
the displayed test succeed.

For the actual program, use numerical projections to recover $n,m,k$. Compute the two tests as zero-or-one values and
multiply them. Queries, the fixed distance-approximation term, dyadic rational codes, rational addition, and comparison
give a closed stage term $T$ which returns one on success and zero on failure. Reverse its answers by zero testing and
apply result search with the identity as its result function. This closed program returns the least successful stage
index. If all stages fail, the no-output part of the result-search lemma excludes every numeral output, irrespective of
reduction order. The Sierpi\'nski semidecision criterion now gives the characteristic map.
§{sec:lambda-rational-ball-programs} constructs these terms explicitly. The error argument uses only the Cauchy
inequalities and the distance-approximation bound; it requires neither completeness nor density.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のeffective-basis lemmaとmargin lemmaの位置付け・引用を述べる導入。
両補題の定義・主張・証明はそれぞれ別途監査する。)
--> We now prove the effective-basis lemma for the fast Cauchy representation. It identifies the Sierpi\'nski-space
definition of effective openness with enumeration by rational balls [@HoyrupRojas2009]. The following margin estimate
makes the extraction explicit.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefineas{Cauchy-prefix margin lemma}{Cauchy-prefix margin lemma}]
Let $s\in\finseq{\NN}$ have length $N$. If
$$d(q_{s(n)},q_i)+r<2^{-(n+1)}\qquad(n<N),$$
then every point of $\Ball{q_i}{r}$ has a fast Cauchy name extending $s$.
\end{lemma*}

\begin{proof}[Proof]
For $y\in\Ball{q_i}{r}$, retain $p(n)=s(n)$ for $n<N$. For every $n\ge N$, use density to choose $p(n)$ with
$d(q_{p(n)},y)<2^{-(n+1)}$. The triangle inequality and the assumed margins give the same strict bound for $n<N$. Thus,
for $m\ge n$,
$$d(q_{p(n)},q_{p(m)})<2^{-(n+1)}+2^{-(m+1)}\le 2^{-n}.$$
The sequence converges to $y$, so $p$ is a name of $y$ extending $s$. The extension is used to prove containment; the
extraction algorithm does not need a name of $y$ as input.
\end{proof}

\begin{lemma*}[\termdefineas{total finite Cauchy-margin test}{Total finite Cauchy-margin test}]
Fix a closed distance-approximation term. There is a closed lambda program which, given a finite list $s$, a center
index $i$, a radius exponent $\ell$ and a precision $k$, returns one exactly when
$$A(s(n),i,k)+2^{-k}+2^{-\ell}<2^{-(n+1)}\qquad(n<\Length{s}),$$
and returns zero otherwise. It terminates on every input, and returns one for an empty list. If it returns one, every
point of $\Ball{q_i}{2^{-\ell}}$ has a valid Cauchy name extending $s$.
\end{lemma*}

\begin{proof}[Proof]
The finite-list programs compute $\Length{s}$ and read each $s(n)$. Numerical projections, the supplied approximation
term and
rational arithmetic decide each displayed inequality as a zero-or-one value $t_n$. Starting with $z_0=1$, use numerical
primitive recursion to set $z_{n+1}=z_nt_n$ for $n<\Length{s}$. The resulting value is one exactly when every test
succeeds;
the empty product is one. All component calculations terminate, so the whole test is total. The constructions and
reductions are given in §{sec:lambda-prefix-margin-programs}.

On success, the distance error bound gives $d(q_{s(n)},q_i)+2^{-\ell}<2^{-(n+1)}$ for every $n<\Length{s}$. Apply the
Cauchy-prefix margin lemma to each point of the ball. This last step is geometric: it supplies a valid extension,
without computing a name for an arbitrary point of the ball.
\end{proof}

\begin{theorem*}[\termdefineas{Effective-basis lemma}{Effective-basis lemma}]
For the fast Cauchy representation of a computable metric presentation, a subset $U\IncludedIn X$ is semidecidable from
names if and only if it is an r.e. union of rational balls. An enumeration may have empty stages, so this includes the
empty set. With the distance-approximation algorithm fixed, the ball extraction is computable jointly in the semidecider
code and enumeration stage. Radii $2^{-\ell}$ with $\ell\in\NN$ already suffice for the extracted balls. Conversely, a
program for a total ball enumeration can be converted primitively recursively into a semidecider.
\end{theorem*}

\begin{proof}[Proof]
Let $P_e$ semidecide membership in $U$ on every valid name. Enumerate all finite tuples $\Tuple{s, \theta,
\gamma,m,i, \ell,k}$,
where $s$
is a finite prefix, $\theta$ an answer table, $\gamma$ a reduction certificate, and the other entries are
natural numbers. Enumerate the natural-number codes of these tuples, using $\LambdaListCode{s}$,
$\LambdaAnswerTableCode{ \theta}$, and $\LambdaCertificateCode{ \gamma}$ for the three finite objects. Check
that every $\Pair{j}{v}\in \theta$ satisfies $j<\Length{s}$ and $s(j)=v$, and that $\gamma$ certifies a reduction from
$P_eo\ChurchNumeral{0}$
to $\ChurchNumeral{m}$ using $\theta$. Check also
$$A(s(n),i,k)+2^{-k}+2^{-\ell}<2^{-(n+1)}\qquad(n<\Length{s}).$$
If all tests succeed, emit $\Ball{q_i}{2^{-\ell}}$; otherwise emit nothing. The closed program constructed in
§{sec:lambda-metric-realizer-programs} performs these tests and encodes either a ball or an empty stage. It
terminates on
every pair consisting of a program index and a trial code, so the enumeration is uniform in $e$.

Every emitted ball is contained in $U$. By the total finite Cauchy-margin test, each point of the ball has a valid name
extending $s$. The checked answer table agrees with every such extension. Soundness of the finite reduction certificate
therefore makes $P_e$ halt on that name, so the point belongs to $U$. No behavior on invalid names is used.

Conversely, fix $x\in U$ and choose a name $p$ with $d(q_{p(n)},x)<2^{-(n+1)}$ at every coordinate, using density. The
program $P_e$ returns some numeral on $p$. Finite-certificate completeness supplies an answer table $\theta$, a
certificate
$\gamma$ and a prefix $s$ of length $N$ containing every queried address. There are only finitely many positive gaps
$2^{-(n+1)}-d(q_{p(n)},x)$ for $n<N$. Choose $\ell$ so large that
$$d(q_{p(n)},x)+4\cdot2^{-\ell}<2^{-(n+1)}\qquad(n<N).$$
For $N=0$ there are no constraints. Choose $i$ with $d(x,q_i)<2^{-\ell}$ and use precision $k=\ell$. The triangle
inequality and the approximation error give
$$A(s(n),i,\ell)+2\cdot2^{-\ell}
\le d(q_{p(n)},q_i)+3\cdot2^{-\ell}
<d(q_{p(n)},x)+4\cdot2^{-\ell}.$$
Thus the corresponding tuple passes every test and emits a ball containing $x$. This proves that the emitted balls cover
exactly $U$.

For the reverse implication, encode a total ball enumeration by a numerical function $f$: output zero denotes an empty
stage, and output $b+1$ denotes the ball whose center-radius code is $b$. Let $P_e$ compute $f$. Enumerate all
quadruples $\Tuple{j,b,h,n}$. First apply the finite numerical-output test to the proposed computation
$P_e\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{b+1}$, searching only certificates below bound $h$. Also apply the
rational-ball test at precision $n$ to ball $b$ and the input name. Multiply the two zero-or-one answers. Every trial
terminates, even without assuming that $P_e$ is total.

On a valid name, a successful trial certifies both $f(j)=b+1$ and membership in the corresponding ball. Conversely, if
the represented point belongs to the union, some $f(j)$ codes a ball containing it. The finite computation of that
output has a certificate below some bound $h$, and the ball test succeeds at some precision $n$. Hence the corresponding
quadruple succeeds. Result search therefore gives a semidecider with exactly the required domain; empty stages never
cause acceptance.

For uniformity, use the single trial term of §{sec:lambda-metric-realizer-programs}, whose numerical input pairs $e$
with the quadruple code. Insert $\ChurchNumeral{e}$ into this fixed template, reverse its zero-or-one answers, and apply
result search. The same section constructs a primitive-recursive transformation of syntax codes, itself computed by a
closed lambda term, which performs these operations. It does not need to decide whether the indexed enumeration is
total. Under the stated totality assumption, the preceding argument proves that its output semidecides the enumerated
union.
\end{proof}

This matches the lightface hierarchy of §{sec:effective-dst}. A subset $E\IncludedIn X$ is
\termdefineas{effective analytic set}{effectively analytic} when
$$
\rho_X^{-1}(E)=\DomainOf{\rho_X}\cap W
$$
for some lightface $\lSigma^1_1$ set $W\IncludedIn\BaireSpace$. Since $\DomainOf{\rho_X}$ is lightface
$\lPi^0_1$, this preimage is itself lightface $\lSigma^1_1$; the analogous simplification fails for effective openness.

### Computable Maps and Pullbacks {#sec:tte-computable-maps}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{b,j,k,t}{Nat}
\end{mathmeta}

A function $f:X\to Y$ between \termuseas{computable Polish space}{computable Polish spaces} is
computable iff there is a Type-Two lambda realizer which transforms every fast Cauchy name of $x$ into a fast Cauchy
name of $f(x)$.

For the criterion below, uniform enumeration means one total numerical lambda program computing $E(b,k)$ from
$\NatPair{b}{k}$, where $b$ codes a basic ball in $Y$ and $k$ is a stage. Output zero denotes an empty stage, and
output $c+1$ denotes the rational ball in $X$ coded by $c$. For each fixed $b$, the union of the emitted balls must be
the preimage of the ball coded by $b$. The same closed term serves every target ball.

\begin{proposition*}[\termdefineas{Inverse-image criterion}{Inverse-image criterion}]
The function $f$ is computable iff it is continuous and, uniformly from a basic rational ball $\Ball{q_j}{r}$ in $Y$,
one can enumerate rational balls in $X$ whose union is $f^{-1}(\Ball{q_j}{r})$. In fact, the uniform enumeration
condition alone implies computability, so continuity need not be assumed separately.
\end{proposition*}

\begin{proof}[Proof]
Let $Q$ compute a realizer $F$ of $f$. Finite use and admissibility give continuity. For each target ball code $b$,
compose the total rational-ball stage test with $Q$: on a valid input name $p$ and precision $k$, compute the stage
answer using the name $F(p)$. Substitution of the name-producing term preserves this finite computation. Each stage
therefore terminates and returns exactly the stage answer for the output name. Searching these zero-or-one answers
for a nonzero digit yields a semidecider whose domain is exactly the preimage of the ball. This conclusion uses the
exact search theorem for total tests, including exclusion of numeral outputs when every stage fails.

The construction in §{sec:lambda-metric-realizer-programs} inserts the numeral for $b$ into one fixed syntax template.
Its code $c(b)$ is primitive recursive in $b$ and computed by a closed lambda term. Apply the source-space extraction
program of §{sec:lambda-prefix-margin-programs} to $\NatPair{c(b)}{k}$. The resulting program is total on every pair
$\NatPair{b}{k}$ and enumerates precisely the ball preimage, by the effective-basis lemma. Thus the enumeration is
uniform in both the target ball and its stage.

Conversely, let $E$ be such a uniform enumeration and let $p$ name $x$. To compute output coordinate $n$, enumerate
triples $\Tuple{j,k,\ell}$ using codes $t=\NatPair{j}{\NatPair{k}{\ell}}$. Let $b$ code the target ball
$$\Ball{q_j}{2^{-(n+2)}}.$$
Compute $E(b,k)$. If its output is zero, this trial fails. If it is $c+1$, apply the input-space rational-ball test
at precision $\ell$ to the ball coded by $c$ and the name $p$. On success, output $j$. Each trial terminates. The search
tests all centers, enumeration stages and precisions, so failure to certify one candidate cannot obstruct another.

This search terminates for every valid input name and every $n$. Density supplies a target center whose ball contains
$f(x)$. Exactness of its preimage enumeration supplies an emitted input ball containing $x$, and the rational-ball
test succeeds at some precision. Conversely, every successful trial places $x$ in that preimage and hence $f(x)$ in
the target ball. The closed trial term in §{sec:lambda-metric-realizer-programs} takes $\NatPair{n}{t}$ as its numerical
input. Reverse its zero/nonzero answers and use the sequential-search term to find the first successful triple.
Numerical projection returns its center index. Thus one closed term computes every output coordinate on every valid
input name; no decision procedure for validity of names is used.

Write $j_n$ for the index found at coordinate $n$ and $y=f(x)$. Then $d(q_{j_n},y)<2^{-(n+2)}$, so for $m\ge n$ the
triangle inequality gives
$$
d(q_{j_n},q_{j_m})
<2^{-(n+2)}+2^{-(m+2)}
\le 2^{-(n+1)}
\le 2^{-n}.
$$
Thus $\Sequence{q_{j_n}}{n\in\omega}$ is a fast Cauchy sequence, and the same estimates show that it converges to $y$.
Hence the search
computes a Cauchy name of the image point. This constructs a computable realizer using only the uniform enumeration
assumption; continuity follows from the already proved continuity of computably realizable maps.
\end{proof}

\begin{proposition*}[\termdefineas{Computable pullback of semidecidable sets}{Computable pullback of semidecidable
sets}]
Let $f:X\to Y$ have a computable realizer for representations $\delta_X,\delta_Y$. If membership in $V\IncludedIn Y$ is
semidecidable from a $\delta_Y$-name, then membership in $f^{-1}(V)$ is semidecidable from a $\delta_X$-name. In
particular, computable maps between computable Polish spaces pull effectively open sets back to effectively open sets.
\end{proposition*}

\begin{proof}[Proof]
Let $Q$ compute a realizer $F$ of $f$, and let $P_e$ semidecide membership in $V$. By the Sierpi\'nski semidecision
criterion, the closed term
$$C_e:=\lambdaab{o}{\LambdaFiniteTrial\,o\,\ChurchNumeral{e}\,\ChurchNumeral{0}}$$
produces a total name whose $k$th digit is nonzero exactly when the $k$th finite trial succeeds. Compose $C_e$ with $Q$
by lambda substitution. On a valid input name $p$, every digit of the composite is the corresponding finite-trial
answer for $F(p)$. Search for a nonzero digit. The exact search theorem gives a numeral output precisely when some
trial succeeds, equivalently when $P_e$ has an output on $F(p)$. Since $F(p)$ names $f(\delta_X(p))$, this is exactly
$\delta_X(p)\in f^{-1}(V)$. All terms are fixed before the input name is supplied. For Cauchy representations, the
effective-basis lemma identifies these semidecidable sets with the effectively open sets.
\end{proof}

For computable Polish spaces with their effective Cauchy representations, the inverse-image criterion above
proves the converse: uniform effective pullback of basic opens yields a computable realizer.
Topological admissibility alone gives a continuous realizer; an effective version needs effective information
about the representation as well.

The \termuse{signed-digit representation} from §{sec:signed-digit-representation} illustrates why admissibility
matters. The \termuse{binary expansion} is a representation of $\ClosedInterval{0}{1}$, but it is not admissible because
dyadic
rationals force discontinuous choices of tails. Signed digits add redundancy, making enough room for continuous choices
and restoring equivalence with the Cauchy representation.

#### Effective Changes of Dense Presentation {#sec:tte-effective-dense-changes}

\begin{mathmeta}
  \vars{i,j}{Nat}
  \vars{k}{Nat}
\end{mathmeta}

A representation $\delta$ of $X$ \termdefineas{computable reducibility of representations}{computably reduces} to
another representation $\gamma$ of the same set if the identity on $X$ has a computable realizer from $\delta$ to
$\gamma$. Thus one program converts every valid $\delta$-name into a $\gamma$-name of the same point. The
representations are \termdefineas{computable equivalence of representations}{computably equivalent} if such translators
exist in both directions. A point is \termforwardas{computable point in represented space}{computable} relative to a
representation if it has an ordinary computable name.

\begin{proposition*}[\termdefineas{Invariance under computable change of representation}{Invariance under
computable change of representation}]
Computably equivalent representations have the same computable points and the same subsets whose membership is
semidecidable from names. Replacing the source and target representations by computably equivalent ones also preserves
computability of every map between the represented sets.
\end{proposition*}

\begin{proof}[Proof]
Let $A$ be a closed numerical lambda term computing an input name $p$, and let $P$ compute a translator $F$.
Then the closed application $PA$ computes the name $F(p)$. Indeed, substitute $A$ for the free input variable
in each finite computation of $P$: a query at $i$ becomes the ordinary beta reduction of
$A\ChurchNumeral{i}$ to $\ChurchNumeral{p(i)}$. The substitution lemma in §{sec:lambda-input-composition}
justifies this replacement under every term context. Thus computable points are preserved; the reverse translator
proves the converse. For subsets, apply the computable pullback proposition to the identity in each direction.
For a map, first translate a name from the new source representation to the old one, then apply the old realizer,
and finally translate its output to the new target representation. Lambda composition gives one closed realizer
for these three operations. The reverse translations give the converse.
\end{proof}

\begin{proposition*}[\termdefineas{Effective dense-sequence criterion}{Effective dense-sequence criterion}]
Fix a complete metric space $\Pair{X}{d}$ and two dense sequences $\Sequence{q_i}{i\in\omega}$ and
$\Sequence{r_j}{j\in\omega}$. Write $\rho_q,\rho_r$ for their fast
Cauchy representations. Then $\rho_q$ computably reduces to $\rho_r$ if and only if there is a total computable function
$T:\NN^2\to\NN$ such that
$$d(q_i,r_{T(i,k)})\le 2^{-k}\qquad\Pair{i}{k}\in \NN.$$
Consequently, the two representations are computably equivalent exactly when such uniform approximations exist in both
directions. This criterion does not require the distances themselves to be computable.
\end{proposition*}

\begin{proof}[Proof]
Suppose first that $T$ is given, computed by a closed term $B$ on the paired input $\NatPair{i}{k}$.
Let $N$ be a closed term computing $n\mapsto n+2$. The closed term
$$Q:=\lambdaab{o}{\lambdaab{n}{B\bigl(\LambdaNumericPair\,(o(Nn))\,(Nn)\bigr)}}$$
computes
$$F(p)(n)=T(p(n+2),n+2).$$
Its reductions first compute the shifted coordinate, query that coordinate, pair the answer with the coordinate,
and apply $B$. If $p$ names $x$, the input Cauchy estimate and the approximation bound give
$$
\begin{aligned}
d(r_{F(p)(n)},x)
&\le d(r_{F(p)(n)},q_{p(n+2)})\\
&\quad+d(q_{p(n+2)},x)\\
&\le 2\cdot2^{-(n+2)}=2^{-(n+1)}.
\end{aligned}
$$
For $m\ge n$, the triangle inequality therefore yields
$$d(r_{F(p)(n)},r_{F(p)(m)})\le 2^{-(n+1)}+2^{-(m+1)}\le 2^{-n}.$$
Thus the output satisfies the fast Cauchy condition, and the first estimate proves convergence to $x$. It is a valid
name of the same point.

Conversely, let a closed term $P$ compute a translator $F$ from $\rho_q$ to $\rho_r$.
The constant sequence $p_i(n)=i$ is a valid name of $q_i$, computed by
$K_i:=\lambdaab{u}{\ChurchNumeral{i}}$. Define
$$T(i,k)=F(p_i)(k).$$
By the preceding substitution argument, $PK_i\ChurchNumeral{k}$ reduces by ordinary beta steps to
$\ChurchNumeral{T(i,k)}$. This is uniform in both arguments: the fixed closed term
$$H:=\lambdaab{a}{\lambdaab{b}{P\,(\lambdaab{u}{a})\,b}}$$
computes $T$ on two numerals. Numerical projections turn it into a program on $\NatPair{i}{k}$.
Each computation terminates because the constant name is valid. Its output is the $k$th coordinate of a Cauchy
name of $q_i$, so
$$d(q_i,r_{T(i,k)})\le 2^{-k}.$$
Applying the criterion in both directions proves the assertion about computable equivalence.
\end{proof}

Together with invariance under computable change of representation, the criterion gives an explicit test for
independence from the dense sequence. It also preserves effectively open sets when both sequences give computable metric
presentations. If the metric changes as well, one must instead verify computability of the identity in both directions
between the two presentations. The inverse-image criterion can be used for that purpose. Equality of the induced
topologies supplies continuity, but does not supply the required uniform enumerations of basic-ball preimages.

### Binary and Signed-Digit Names {#sec:tte-binary-signed-digit}

\begin{mathmeta}
  \vars{p,q,r}{Name}
  \vars{a,b,d,i,j,k,m,n}{Nat}
\end{mathmeta}

Fix the following explicit enumeration of the dyadic points:
$$\nu_{\NatPair{a}{b}}:=\frac{\min(a,2^b)}{2^b}\qquad a,b\in\NN.$$
Every index names a point of $\ClosedInterval{0}{1}$, and every dyadic point of that interval occurs. The sequence is
dense:
the signed-digit partial sums in §{sec:signed-digit-representation} are dyadic and converge to every point.
Let $\rho_\nu$ be its fast Cauchy representation. We regard a binary name as a Baire-space name whose entries
all belong to $\{0,1\}$, with the same binary-expansion value as in §{sec:binary-expansion-example}.

\begin{mathmeta}
  \forward{LambdaParamRec}
\end{mathmeta}

\begin{theorem*}[\termdefineas{computable binary-to-Cauchy translation}{Computable binary-to-Cauchy translation}]
The identity on $\ClosedInterval{0}{1}$ is computable from $\rho_{ \mathrm{bin}}$ to $\rho_ \nu$, but not from
$\rho_ \nu$ to
$\rho_{\mathrm{bin}}$.
\end{theorem*}

\begin{proof}[Proof]
Given a binary name $p$, define the numerator of its finite binary expansion by
$$t_0:=0,\qquad t_{n+1}:=2t_n+p(n),\qquad \beta(p)(n):=\NatPair{t_n}{n}.$$
Induction gives $t_n<2^n$ and
$$\nu_{\beta(p)(n)}=\frac{t_n}{2^n}=\sum_{k<n}p(k)2^{-(k+1)}.$$
The tail estimate in §{sec:binary-expansion-example} shows that these partial sums form a fast Cauchy name
of $\rho_{\mathrm{bin}}(p)$. Only the first $n$ input digits are needed for the $n$-th output coordinate.

For an explicit realizer, let $\LambdaTermName{binaryStep}$ be a closed numerical term computing
$\NatPair{m}{d}\mapsto2m+d$, obtained from multiplication, addition, and numerical projections. Set
$$\begin{aligned}
&\LambdaTermName{binaryBase}:=\lambdaab{o}{\ChurchNumeral{0}},\\
&\LambdaTermName{binaryUpdate}:= \lambdaab{o}{ \lambdaab{n}{ \lambdaab{m}{ \LambdaTermName{binaryStep}(
\LambdaNumericPair\,m\,(on))}}},\\
&\LambdaTermName{binaryNumerator}:=\LambdaParamRec{\LambdaTermName{binaryBase}}{\LambdaTermName{binaryUpdate}},\\
&\LambdaTermName{binaryToCauchy}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericPair\,(
\LambdaTermName{binaryNumerator}on)\,n}}.
\end{aligned}$$
Recursion with an input name from §{sec:lambda-input-recursion} gives the numeral for $t_n$ from
$\LambdaTermName{binaryNumerator}o \ChurchNumeral{n}$, after finitely many beta steps and queries. Pairing it
with $n$ shows that $\LambdaTermName{binaryToCauchy}$
realizes $\beta$. These terms are closed independently of the input name.

For the reverse direction, §{sec:binary-expansion-example} proves that no continuous translator from Cauchy
names to binary names exists for any enumeration of the unit dyadics. The explicit enumeration $\nu$ satisfies
that hypothesis. A computable translator would be continuous by §{sec:type-two-lambda-continuity}, contradicting
that result. Thus the obstruction already proved there rules out a uniform computable translator as well.
\end{proof}

Signed digits avoid this obstruction. Encode the signed digits $-1,0,1$ by $0,1,2$, respectively,
and use the same dyadic enumeration $\nu$.

\begin{theorem*}[\termdefineas{computable signed-digit equivalence}{Computable signed-digit equivalence}]
The representations $\rho_{\mathrm{sd}}$ and $\rho_\nu$ are computably equivalent. Both translators are given by
closed lambda terms using natural-number recursion, queries to the input name, and exact rational comparisons.
\end{theorem*}

\begin{proof}[Proof]
For a coded signed-digit name $p$, set
$$u_0(p):=1,\qquad u_{n+1}(p):=2u_n(p)+p(n)-1,\qquad \varphi(p)(n):=\NatPair{u_n(p)}{n+1}.$$
Induction gives $1\le u_n(p)<2^{n+1}$, so every subtraction displayed here has a nonnegative result. Moreover,
$$\nu_{\varphi(p)(n)}=\frac{u_n(p)}{2^{n+1}}
=\frac12+\sum_{k<n}(p(k)-1)2^{-(k+2)}.$$
These are exactly the signed-digit partial sums of §{sec:signed-digit-representation}, with digit
$\zeta(k)=p(k)-1$. The tail estimate proved there makes $\varphi(p)$ a fast Cauchy name of $\rho_{\mathrm{sd}}(p)$.
Its $n$-th coordinate uses only $p(0),\ldots,p(n-1)$.

Conversely, let $p$ be a $\rho_\nu$-name of $x$. Starting with $v_0(p)=1$, at stage $n$ compute the rational numbers
$$c_n:=\frac{v_n(p)}{2^{n+1}},\qquad h_n:=2^{-(n+2)},\qquad e_n:=\nu_{p(n+4)}-c_n,$$
choose the digit code
$$d_n:=\begin{cases}0,&e_n<-h_n/2,\\2,&h_n/2<e_n,\\1,&-h_n/2\le e_n\le h_n/2,\end{cases}$$
and put $v_{n+1}(p):=2v_n(p)+d_n-1$ and $\psi(p)(n):=d_n$. All comparisons are between rational numbers, including
the equality cases at the thresholds. The bounds $1\le v_n(p)<2^{n+1}$ hold for every input stream, since
$d_n\in\{0,1,2\}$ regardless of whether that stream is a valid Cauchy name.

To check the represented value, identify $\eta(n)=d_n-1$ and the center $c_n$ with those in
§{sec:signed-digit-representation}. The displayed thresholds and the queried approximation $p(n+4)$ are
exactly the recurrence proved there. Its invariant $\Abs{x-c_n}\le2^{-(n+1)}$ therefore gives
$\rho_{\mathrm{sd}}(\psi(p))=x$. The $n$-th output uses only
$p(4),\ldots,p(n+4)$ and finite rational arithmetic. The remaining task is to realize these numerical
recurrences by closed lambda terms.

Here are closed terms for these recurrences. Let $\LambdaTermName{signedBase}:= \lambdaab{o}{
\ChurchNumeral{1}}$, and let $\LambdaTermName{signedStep}$ compute
$\NatPair{m}{d}\mapsto2m+d-1$ when $m\ge1$. On the unused input $m=d=0$, let $\LambdaTermName{signedStep}$ return $0$.
Multiplication, addition, and predecessor give such a total closed term. Let $\LambdaTermName{selectDigit}$ be
the closed term that, on
input $o,\ChurchNumeral{\NatPair{n}{m}}$, performs the rational comparisons defining $d_n$, using the center
$\min(m,2^{n+1})/2^{n+1}$. It reads $o\ChurchNumeral{n+4}$, decodes the dyadic index, subtracts the center,
and compares with $\pm2^{-(n+3)}$. The rational-code procedures in §{sec:lambda-rational-arithmetic} give
$\LambdaTermName{selectDigit}$;
the minimum is computed by comparing natural numbers and selecting the smaller one. Define
$$\begin{aligned}
&\LambdaTermName{signedUpdate}:= \lambdaab{o}{ \lambdaab{n}{ \lambdaab{m}{ \LambdaTermName{signedStep}(
\LambdaNumericPair\,m\,(on))}}},\\
&\LambdaTermName{selectedUpdate}:=\\
&\quad \lambdaab{o}{ \lambdaab{n}{ \lambdaab{m}{ \LambdaTermName{signedStep}(
\LambdaNumericPair\,m\,
(\LambdaTermName{selectDigit}\,o\,(\LambdaNumericPair\,n\,m)))}}},\\
&\LambdaTermName{signedNumerator}:= \LambdaParamRec{ \LambdaTermName{signedBase}}{
\LambdaTermName{signedUpdate}},\\
&\LambdaTermName{selectedNumerator}:= \LambdaParamRec{
\LambdaTermName{signedBase}}{ \LambdaTermName{selectedUpdate}}.
\end{aligned}$$

By recursion with an input name in §{sec:lambda-input-recursion}, $\LambdaTermName{signedNumerator}$ and
$\LambdaTermName{selectedNumerator}$ compute the corresponding
numerators $u_n(p)$ and $v_n(p)$, respectively. Thus, with the successor term $\LambdaSucc$, the required
translators are
$$\begin{aligned}
\LambdaTermName{signedToCauchy}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericPair\,(
\LambdaTermName{signedNumerator}on)\,( \LambdaSucc\,n)}},\\
\LambdaTermName{cauchyToSigned}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{selectDigit}\,o\,(
\LambdaNumericPair\,n\,( \LambdaTermName{selectedNumerator}on))}}.
\end{aligned}$$
Every numerical subroutine terminates, and computing an output involves only finitely many recursion steps
and queries. The displayed bounds on $v_n(p)$ ensure that the clamped center used by $\LambdaTermName{selectDigit}$
equals $c_n$ throughout
the recurrence. The value calculations above prove that these terms realize the identity in both directions.
\end{proof}

For the output interval $\ClosedInterval{0}{2}$, use the scaled signed-digit representation
$$\sigma_{\mathrm{sd}}(p):=2\rho_{\mathrm{sd}}(p).$$
Its domain is the same set of coded signed-digit names. Scaling is surjective onto $\ClosedInterval{0}{2}$, so this is a
representation of that interval.

\begin{proposition*}[\termdefineas{computable signed-digit addition}{Computable signed-digit addition}]
Addition $+:\ClosedInterval{0}{1}^2\to\ClosedInterval{0}{2}$ is computable from the product of two copies of
$\rho_{\mathrm{sd}}$ to $\sigma_{\mathrm{sd}}$.
\end{proposition*}

\begin{proof}[Proof]
Let $p,q$ be signed-digit names of $x,y$. The forward translator above computes their partial sums
$$s_n(p)=\frac{u_n(p)}{2^{n+1}},\qquad s_n(q)=\frac{u_n(q)}{2^{n+1}}.$$
Use their common denominator to form a name for the average:
$$\alpha(p,q)(n):=\NatPair{u_n(p)+u_n(q)}{n+2},\qquad
\nu_{\alpha(p,q)(n)}=\frac{s_n(p)+s_n(q)}2.$$
The numerator is less than $2^{n+2}$ because each $u_n(p)$ is less than $2^{n+1}$, so the dyadic enumeration
returns exactly this average. For $n\le j$, the fast Cauchy estimates give
$$\begin{aligned}
\Abs{\nu_{\alpha(p,q)(n)}-\nu_{\alpha(p,q)(j)}}
&\le\frac{\Abs{s_n(p)-s_j(p)}+\Abs{s_n(q)-s_j(q)}}{2}\\
&\le\frac{2^{-n}+2^{-n}}2=2^{-n}.
\end{aligned}$$
Since the two partial sums converge to $x$ and $y$, the name $\alpha(p,q)$ represents $(x+y)/2$.

Let $\psi$ be the Cauchy-to-signed-digit translator just constructed. Its correctness gives
$$\sigma_{\mathrm{sd}}(\psi(\alpha(p,q)))
=2\rho_{\mathrm{sd}}(\psi(\alpha(p,q)))=2\frac{x+y}{2}=x+y.$$
Thus the average is only an intermediate value: interpreting the output with $\sigma_{\mathrm{sd}}$ yields
the required sum, including when it exceeds $1$.

To give one closed program, encode the input pair as $r:=\NamePair{p}{q}$ and set
$$\LambdaTermName{input}_i:=\lambdaab{o}{\lambdaab{n}{\LambdaNumericProjection{i}(on)}}\qquad(i=1,2).$$
Recall the numerator program $\LambdaTermName{signedNumerator}$ and the reverse translator
$\LambdaTermName{cauchyToSigned}$ from the preceding proof. Define
$$\begin{aligned}
&\LambdaTermName{sumNumerators}:=\\
&\quad \lambdaab{o}{\lambdaab{n}{\begin{aligned}[t]
&\LambdaAdd\,( \LambdaTermName{signedNumerator}(
\LambdaTermName{input}_1o)n)\,( \LambdaTermName{signedNumerator}(\\
&\quad \LambdaTermName{input}_2o)n)
\end{aligned}}},\\
&\LambdaTermName{average}:=\lambdaab{o}{\lambdaab{n}{\LambdaNumericPair\,(\LambdaTermName{sumNumerators}on)\,
(\LambdaAdd\,n\,\ChurchNumeral{2})}},\\
&\LambdaTermName{addSigned}:=\lambdaab{o}{\lambdaab{n}{\LambdaTermName{cauchyToSigned}(\LambdaTermName{average}o)n}}.
\end{aligned}$$
The projection terms supply the two input names to $\LambdaTermName{signedNumerator}$. Addition and pairing then
make $\LambdaTermName{average}$ compute
$\alpha(p,q)$. Substituting this computed name into $\LambdaTermName{cauchyToSigned}$ preserves every finite
beta/query derivation by
§{sec:lambda-input-composition}; each requested coordinate is answered by the corresponding finite
computation of $\LambdaTermName{average}$. All variables are bound, and the value calculation above proves that
$\LambdaTermName{addSigned}$ realizes addition.
\end{proof}
