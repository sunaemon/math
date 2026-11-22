# Appendix: Computational Constructions for Effective Descriptive Set Theory {#sec:appendix-effective-computations}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
この付録が先行する数値lambda構文とType-Two beta/query規則を再利用する旨の導入。
後続の個別構成で実際の閉項・計算の仮定・保存するパラメータを別に確認し、この導入を新たな計算モデルや独立の存在定理とは数えない。)
-->
This appendix collects the lambda programs used in the effective descriptive-set-theoretic chapters. Numerical syntax
and program indices come from §{sec:appendix-lambda-computability}; input-query computation, recursion, search, and
uniform specialization come from §{sec:appendix-type-two-computation}. Every construction uses those same beta/query
rules and retains its stated numerical and real parameters.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
付録の構成順序と、応用先のeffective DSTおよびTTE章を示す案内。列挙された各構成の数学的・計算的主張は後続で別に対応する。)
--> The sections organize the constructions by their mathematical use: metric tests and enumerations; trees, jumps, and
ordinal computations; effective tree operations and Borel codes; transfinite tree constructions; graphs and refinements;
and the compilation of metric realizers. These are supporting constructions for
§{sec:effective-dst} and §{sec:computable-polish-tte}, rather than additional definitions of computation.<!--
formalization: skip-end
-->

## Metric Tests and Effective Enumerations {#sec:lambda-metric-tests}

### Rational Tests on Cauchy Names {#sec:lambda-rational-ball-programs}

\begin{mathmeta}
  \define{RationalValue,LambdaBallTest,LambdaBallSemidecider}
  \vars{i}{Nat}
  \vars{a,b,c,j,k,m,n,t,u,v,w,x,z}{Nat}
\end{mathmeta}
We construct the numerical test used for rational balls. The construction itself needs no metric space. For a rational
code $c=\RationalCode{a}{b}{d}$, write $\RationalValue{c}:=(a-b)/(d+1)$. Let $A:\NN^3\to\NN$ be a total function whose
outputs are rational codes, and suppose one closed term $M$ satisfies
$$M\,\ChurchNumeral{\NatPair{i}{\NatPair{j}{n}}}\to_\beta^*\ChurchNumeral{A(i,j,n)}$$
for all $i,j,n$. Given an input name $p$, a center index $i$, a radius code $c$, and a stage $n$, the desired test is
$$\RationalValue{A(p(n),i,n)}+2\cdot2^{-n}<\RationalValue{c}.$$
It uses only a query to $p$, the supplied program $M$, and the arithmetic of §{sec:lambda-rational-arithmetic}.

The joint numerical input is $z=\NatPair{\NatPair{i}{c}}{n}$. In the following expressions, abbreviate
$$\begin{aligned}
n&:=\LambdaNumericProjection{2}z,\\
i&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{1}z),\\
c&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{1}z).
\end{aligned}$$
With $o$ the input-name variable, put
$$\begin{aligned}
V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,i\,n)),\\
E&:=\LambdaDyadic\,n,\\
U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
 (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,E),\\
T\,o\,z&\to_\beta^*\LambdaRationalLess\,(\LambdaNumericPair\,U\,c).
\end{aligned}$$
Here $T$ is the closed program assembled by composition and pairing of the component procedures. Expand the
abbreviations before supplying its arguments; the helper beta-redexes then give the displayed reduction. All internal
bound variables can be fixed fresh once. For a ball code $b=\NatPair{i}{c}$, define
$$F_b:=\lambdaab{k}{\LambdaNumericPair\,\ChurchNumeral{b}\,k},\qquad
\LambdaBallTest{b}:=\lambdaab{o}{\lambdaab{k}{T\,o\,(F_bk)}}.$$
Thus the same stage term $T$ serves every center and radius.

\begin{proposition*}[\termdefineas{lambda rational stage test}{Total rational stage test}]
The term $\LambdaBallTest{b}$ is closed. On every input name $p$ and every stage $n$, it returns one exactly when the
displayed rational inequality holds, and zero otherwise. No Cauchy-name condition is needed for termination of the stage
test.
\end{proposition*}

\begin{proof}[Proof]
Contract the outer abstractions and compute $F_b\ChurchNumeral{n}$. Numerical projections recover $i,c,n$. One query
supplies $p(n)$, and the two numerical pairings prepare the input for $M$. Its assumed reduction gives the code
$A(p(n),i,n)$. The dyadic term gives a code of $2^{-n}$. Twice applying rational addition gives a code whose value is
$\RationalValue{A(p(n),i,n)}+2\cdot2^{-n}$. The rational comparison term then gives the asserted answer. All these
reductions are finite and may be performed inside application contexts. The outer abstractions bind the only free
variables, and confluence excludes other numeral outputs.
\end{proof}

Put
$$G_{b,o}:=\lambdaab{k}{\LambdaZeroTest\,(\LambdaBallTest{b}\,o\,k)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
\qquad I:=\lambdaab{x}{x},$$
and define the closed semidecision program
$$\LambdaBallSemidecider{b}:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_{b,o}\,I}}.$$
Its numerical argument $a$ is unused. The zero test reverses the answers so that the result-search term stops exactly on
a successful stage.

\begin{proposition*}[\termdefineas{lambda rational test semidecision}{Exact semidecision and its code transformation}]
For every name $p$ and numerical input, $\LambdaBallSemidecider{b}$ has a numeral output if and only if some stage
satisfies the rational inequality. If a stage succeeds, the output is its least index. If none succeeds, there is no
numeral output. With $M$ fixed, the function sending $b$ to a syntax code of $\LambdaBallSemidecider{b}$ is primitive
recursive and is computed by a closed lambda term.
\end{proposition*}

\begin{proof}[Proof]
Every stage test terminates, so if a successful stage exists, take its least index. The reversed tests are positive at
earlier stages and zero at that successful stage. The result-search lemma with input queries returns the identity
applied to that index's
numeral, hence the numeral itself. If there is no successful stage, all reversed tests are positive; the no-output part
of the same lemma applies. These conclusions hold for arbitrary reduction orders.

For the code transformation, fix named representatives of $T$, numerical pairing, zero testing, result search and the
identity. First compute the code of $\ChurchNumeral{b}$. Application and abstraction constructors then build $F_b$,
insert it into the fixed template $\LambdaBallTest{b}$, and insert that result into $G_{b,o}$ and
$\LambdaBallSemidecider{b}$. Decoding each constructed code recovers exactly the corresponding named term. Closedness
ensures that the program enumeration retains this term. The constructors are the numerical maps
$\Pair{u}{v}\mapsto3\NatPair{u}{v}+1$ and $\Pair{x}{u}\mapsto3\NatPair{x}{u}+2$. They and the numeral-code map are
primitive
recursive and computed by closed lambda terms. Their finite composition proves both assertions about the compiler. No
digit of $p$ is used in constructing the code.
\end{proof}

Let $A:\NN^3\to\NN$ be a total rational-code-valued function computed by a closed term $M$, so that
$$M\,\ChurchNumeral{\NatPair{i}{\NatPair{j}{k}}}\to_\beta^*\ChurchNumeral{A(i,j,k)}.$$
For a sequence $p$, the test at stage $z=\NatPair{n}{\NatPair{m}{k}}$ is
$$n\le m\quad\text{and}\quad
2^{-n}+2^{-k}<\RationalValue{A(p(n),p(m),k)}.$$
This construction makes no metric assumption about $A$. It is a numerical test on two digits of an arbitrary sequence.

In the term expressions below, abbreviate
$$\begin{aligned}
n&:=\LambdaNumericProjection{1}z,\\
m&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
k&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z).
\end{aligned}$$
Define the closed stage program $T$ by composition and pairing of the following component procedures:
$$\begin{aligned}
V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,(om)\,k)),\\
U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,(\LambdaDyadic\,n)\,(\LambdaDyadic\,k)),\\
B&:=\LambdaLeCase{n}{m}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
T\,o\,z&\to_\beta^*\LambdaMul\,B\,
 (\LambdaRationalLess\,(\LambdaNumericPair\,U\,V)).
\end{aligned}$$
Expand the abbreviations before supplying the arguments. The helper beta-redexes give the displayed reduction, and all
internal binders are chosen fresh once. Put
$$\begin{aligned}
G_o&:=\lambdaab{z}{\LambdaZeroTest\,(T\,o\,z)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
I&:=\lambdaab{x}{x},\\
S&:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_o\,I}}.
\end{aligned}$$
The argument $a$ is unused.

\begin{proposition*}[\termdefineas{lambda Cauchy test semidecision}{Total two-query test and exact search}]
The terms $T$ and $S$ are closed. On every sequence $p$ and stage $z$, $T$ returns one exactly when the test succeeds,
and zero otherwise. Its answer depends only on $p(n)$ and $p(m)$. On every numerical input, $S$ returns the least
successful stage if one exists, and has no numeral output otherwise.
\end{proposition*}

\begin{proof}[Proof]
Numerical projections recover the three indices. The two queries and numerical pairings supply the input to $M$, whose
assumed computation gives $V$. Dyadic coding and rational addition give $U$ with value $2^{-n}+2^{-k}$. Natural-number
comparison returns one exactly when $n\le m$, and rational comparison returns one exactly when the strict inequality
holds. Multiplication therefore returns one exactly when both conditions hold. All component computations terminate, so
the stage program is total on every sequence. Only the two stated queries occur; replacing the sequence by another with
the same two answers leaves the result unchanged. The abstractions bind the only free variables, proving closedness.

The zero test in $G_o$ returns zero exactly at successful stages. Since every stage terminates, the result-search lemma
with input queries returns the least such stage, with $I$ returning its numeral unchanged. If no stage succeeds, the
same lemma excludes every numeral output under any reduction order. This proves the exact domain assertion for $S$. When
$A$ approximates distances with error at most $2^{-k}$, the two error estimates in §{sec:tte-polish-as-represented}
identify this domain with the complement of the fast Cauchy-name domain.
\end{proof}

We first make ordinary numerical search with a parameter explicit. Let a closed term $T$ compute a total numerical
function $t$ on paired inputs. Put
$$\begin{aligned}
I&:=\lambdaab{x}{x},\\
G_z&:=\lambdaab{k}{\LambdaZeroTest\,(T\,(\LambdaNumericPair\,z\,k))\,
  \ChurchNumeral{1}\,\ChurchNumeral{0}},\\
S_T&:=\lambdaab{z}{\LambdaResultSearch\,G_z\,I}.
\end{aligned}$$
All these computations use ordinary beta reduction. There is no input-name variable.

\begin{lemma*}[\termdefineas{parameterized numerical lambda search}{Parameterized numerical search}]
The term $S_T$ is closed. For every numerical parameter $z$, it returns the least $k$ with $t(\NatPair{z}{k})\ne0$ if
such a $k$ exists, and has no numeral output otherwise. If a successful stage exists for every $z$, this is a total
computable numerical function.
\end{lemma*}

\begin{proof}[Proof]
Contract the outer abstraction, compute the numerical pair and run $T$. Every stage terminates. The zero test returns
zero exactly when $T$ returns a positive numeral. The result-search lemma therefore reaches the least successful stage
and applies $I$ to its numeral. If no stage succeeds, the reversed test always returns one, so the same lemma excludes
every numeral output. Confluence transports this conclusion across the outer contraction. To implement the displayed
formula by our composition helpers, curry the paired-input term, compose with zero testing, and pass the resulting unary
test to result search; the additional beta contractions give exactly the same test. All free variables are bound, so the
assembled program is closed.
\end{proof}

Now let $\Sequence{q_i}{i\in\omega}$ be a sequence in a metric space and suppose a closed term $M$ computes rational
codes $A(i,j,k)$ with
distance error at most $2^{-k}$. Encode an interval input by $w=\NatPair{\NatPair{i}{j}}{\NatPair{a}{b}}$, where $a,b$
now denote rational codes. On input $\NatPair{w}{k}$, numerical projections recover these components. Put
$$\begin{aligned}
V&:=M\,(\LambdaNumericPair\,i\,(\LambdaNumericPair\,j\,k)),\\
E&:=\LambdaDyadic\,k,\\
L&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E).
\end{aligned}$$
Composition gives a closed stage term whose body reduces to
$$\LambdaMul\,(\LambdaRationalLess\,(\LambdaNumericPair\,L\,V))\,
 (\LambdaRationalLess\,(\LambdaNumericPair\,H\,b)).$$
It returns one exactly when both rational margin tests hold, and zero otherwise. The parameterized search just proved
returns a numeral exactly when some precision succeeds. The error bound shows that success implies
$\RationalValue{a}<d(q_i,q_j)<\RationalValue{b}$. Conversely, if these strict inequalities hold, choose $k$ so that
$2\cdot2^{-k}$ is smaller than both endpoint gaps. Then both margin tests succeed. Thus this closed program semidecides
the interval relation.

For the reverse construction, fix a closed term $P_e$ whose numeral-output domain is exactly that interval relation. Let
$z=\NatPair{i}{\NatPair{j}{k}}$ be the approximation input and let $u=\NatPair{a}{\NatPair{b}{t}}$ enumerate two
rational codes and an output-certificate candidate. Numerical projections recover every component. Put
$$\begin{aligned}
W&:=\LambdaNumericPair\,(\LambdaNumericPair\,i\,j)\,
 (\LambdaNumericPair\,a\,b),\\
E&:=\LambdaDyadic\,k,\\
H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
B&:=\LambdaRationalLess\,(\LambdaNumericPair\,b\,H),\\
C&:=\LambdaOutputCandidate\,\ChurchNumeral{e}\,W\,t.
\end{aligned}$$
The closed stage term $T_e$ on input $\NatPair{z}{u}$ is assembled from these procedures and reduces to
$\LambdaMul\,B\,C$. Define
$$D_e:=\lambdaab{z}{\LambdaNumericProjection{1}(S_{T_e}z)}.$$
Both stage tests are total: $B$ checks the interval width, and $C$ checks a bounded set of finite beta-reduction
certificates. A failed candidate does not assert that $P_e$ diverges.

\begin{proposition*}[\termdefineas{lambda distance approximation from intervals}{Distance approximation from
interval semidecision}]
For every $i,j,k$, $D_e$ returns a rational code $a$ with
$$\Abs{\RationalValue{a}-d(q_i,q_j)}\le2^{-k}.$$
The construction uses the same closed term for every input and requires neither completeness of the metric space nor
density of $\Sequence{q_i}{i\in\omega}$.
\end{proposition*}

\begin{proof}[Proof]
Write $d=d(q_i,q_j)$ and $\varepsilon=2^{-k}>0$. Choose rational endpoints with
$d-\varepsilon<\RationalValue{a}<d<\RationalValue{b}<\RationalValue{a}+\varepsilon$. Such endpoints exist by density of
the rationals. The program $P_e$ returns a numeral on their encoded interval. Completeness of the finite candidate
tester supplies a candidate $t$ which it accepts, so the triple $u=\NatPair{a}{\NatPair{b}{t}}$ passes both tests. Every
stage terminates; hence parameterized search reaches the least successful stage. Soundness of its accepted candidate
gives the interval inequalities, and the width test gives $\RationalValue{b}<\RationalValue{a}+\varepsilon$. Therefore
$\Abs{\RationalValue{a}-d}<\varepsilon$. Finally, the first numerical projection extracts exactly the lower-endpoint
code
from the successful triple. This proves termination and the stated error bound. Different codes for the same rational
cause no difficulty, since the tests and estimate use their values.
\end{proof}

### Finite Prefixes and Parameter Tests {#sec:lambda-prefix-margin-programs}

\begin{mathmeta}
  \define{LambdaBoundedProduct,LambdaPrefixMargins}
  \vars{N,x}{Nat}
  \vars{e,i,k,n,r,u,w}{Nat}
\end{mathmeta}

Next let a closed term $T$ compute a total numerical test $t$ on paired inputs. Numerical projections, pairing and
multiplication construct a closed handler $H_T$ with
$$H_T\,\ChurchNumeral{x}\,\ChurchNumeral{n}\,\ChurchNumeral{r}
 \to_\beta^*\LambdaMul\,\ChurchNumeral{r}\,
 (T\,\ChurchNumeral{\NatPair{x}{n}}).$$
More explicitly, first form the unary function on $\NatPair{x}{\NatPair{n}{r}}$ by these operations, and then curry it
to three numerical arguments. With $B:=\lambdaab{x}{\ChurchNumeral{1}}$, put
$$\LambdaBoundedProduct{T}:=\lambdaab{z}{
 \LambdaParamRec{B}{H_T}\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.$$

\begin{lemma*}[\termdefineas{lambda bounded product of tests}{Bounded products of numerical tests}]
On input $\NatPair{x}{N}$, the closed term $\LambdaBoundedProduct{T}$ returns $b_N$, where
$$b_0:=1,\qquad b_{n+1}:=b_n\,t(\NatPair{x}{n}).$$
It terminates for every $x,N$. Its output is nonzero exactly when $t(\NatPair{x}{n})\ne0$ for every $n<N$. If each test
value is zero or one, the output is also zero or one. The output for $N=0$ is one.
\end{lemma*}

\begin{proof}[Proof]
Apply parameterized primitive recursion to $B,H_T$. Its reduction theorem gives the recurrence for $b_n$. Induction on
$N$, using that a product of natural numbers is nonzero exactly when both factors are nonzero, gives the stated
criterion. The same induction proves the zero-or-one assertion. The initial case is the empty product, so it imposes no
tests.
\end{proof}

We apply this bounded product to Cauchy margins. Suppose a closed term $M$ returns the rational code $A(u,i,k)$ from the
numerical input $\NatPair{u}{\NatPair{i}{k}}$. Encode the finite data by
$$w:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}}.$$
On input $\NatPair{w}{n}$, projections recover the list code and all four indices. In the following term expressions,
$e,i,\ell,k,n$ abbreviate those projection terms. Form
$$\begin{aligned}
V&:=M\,(\LambdaNumericPair\,(\LambdaListGet\,(\LambdaNumericPair\,e\,n))
       (\LambdaNumericPair\,i\,k)),\\
E&:=\LambdaDyadic\,k,\qquad R:=\LambdaDyadic\,\ell,\\
U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
 (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,R),\\
D&:=\LambdaDyadic\,(\LambdaSucc\,n).
\end{aligned}$$
Composition gives a closed stage term $T_M$ whose body reduces to $\LambdaRationalLess\,(\LambdaNumericPair\,U\,D)$.
Finally put
$$\LambdaPrefixMargins{M}:=\lambdaab{w}{\LambdaBoundedProduct{T_M}\,
 (\LambdaNumericPair\,w\,(\LambdaListLength\,(\LambdaNumericProjection{1}w)))}.$$

\begin{proposition*}[\termdefineas{lambda finite margin program}{Exact finite margin program}]
The term $\LambdaPrefixMargins{M}$ is closed and returns one exactly when
$$\RationalValue{A(s(n),i,k)}+2^{-k}+2^{-\ell}<2^{-(n+1)}\qquad(n<\Length{s}),$$
and zero otherwise. It terminates on every numerical code and accepts the empty prefix. No metric assumptions are needed
for these computational assertions.
\end{proposition*}

\begin{proof}[Proof]
List access gives the entry $s(n)$ whenever $n<\Length{s}$. The supplied term computes its distance-approximation code;
the
dyadic terms and two additions give the left side of the inequality. Successor and dyadic coding give the right side.
Rational comparison returns the correct zero-or-one value. The length term computes the exact number of entries, and the
bounded-product lemma tests precisely those indices. Every ingredient is total and closed, so their composition has the
stated properties, including the empty-prefix case.
\end{proof}

\begin{mathmeta}
  \define{LambdaListTake,LambdaListPrefix}
\end{mathmeta}
To extract a prefix, retain the original list code $e$ and accumulate the output code $r$. At stage $k$, append
the $k$th entry only if that entry exists. The following abbreviations are expanded inside the displayed
abstractions:
$$\begin{aligned}
A(e,k,r)&:=\LambdaListAppend\,r\,
 \bigl(\LambdaListCons\,(\LambdaListGet\,(\LambdaNumericPair\,e\,k))\,\ChurchNumeral{0}\bigr),\\
J(e,k,r)&:=\LambdaLeCase{\LambdaSucc\,k}{\LambdaListLength\,e}{A(e,k,r)}{r},\\
B&:=\lambdaab{e}{\ChurchNumeral{0}},\qquad
H:=\lambdaab{e}{\lambdaab{k}{\lambdaab{r}{J(e,k,r)}}},\\
\LambdaListTake&:=\lambdaab{z}{\LambdaParamRec{B}{H}\,
 (\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.
\end{aligned}$$
The comparison in $J$ is $k+1\le\Length{\LambdaListDecode{e}}$. If it fails, the previous output code is retained.

\begin{proposition*}[\termdefineas{Lambda prefix extraction}{Prefix extraction by a lambda term}]
The closed term $\LambdaListTake$ is total on numerical inputs. On input $\NatPair{\LambdaListCode{s}}{n}$ it
returns the code of the first $\min\{n,\Length{s}\}$ entries of $s$. In particular, it returns the empty-list code at
$n=0$ and the original list code when $n\ge\Length{s}$.
\end{proposition*}

\begin{proof}[Proof]
Induct on the number of recursion steps. Initially the accumulator is the empty-list code. If $k<\Length{s}$, list
access returns the $k$th entry, the constructor makes its singleton list, and concatenation appends that entry
to the prefix already accumulated. If $k\ge\Length{s}$, the comparison selects the unchanged accumulator, which
already codes all of $s$. These are exactly the two cases for taking $k+1$ entries. Numerical primitive
recursion realizes this recurrence by beta reduction. Every component is closed and total, including list
access outside its range, so the construction works for every code and every requested length.
\end{proof}

Define the prefix test by
$$\begin{aligned}
P(e,d)&:=\LambdaEqual\,e\,
 \bigl(\LambdaListTake\,(\LambdaNumericPair\,d\,(\LambdaListLength\,e))\bigr),\\
\LambdaListPrefix&:=\lambdaab{z}{P(\LambdaNumericProjection{1}z,\LambdaNumericProjection{2}z)}.
\end{aligned}$$
Expand $P$ inside the abstraction.

\begin{proposition*}[\termdefineas{Lambda prefix decision}{Prefix decision}]
On input $\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}$, the closed term $\LambdaListPrefix$ returns one
if $s$ is a prefix of $t$, and zero otherwise. It terminates on every pair of list codes.
\end{proposition*}

\begin{proof}[Proof]
A list is a prefix of another exactly when it equals the first list's length of entries taken from the second.
The extraction term computes that prefix, and injectivity of list coding turns list equality into equality
of the numerical codes. The numerical equality term supplies the stated answer. This includes the empty list
and the case where the first list is longer than the second.
\end{proof}

Finally, let a closed term $F$ compute the code of a forbidden word $s_i$ from $i$. On input $\NatPair{e}{i}$,
a closed term $T_F$ computes the prefix-test answer for $s_i$ and $\LambdaListDecode{e}$ and reverses zero and one.
Explicitly, expand the abbreviations
$$\begin{aligned}
i&:=\LambdaNumericProjection{2}z,\qquad e:=\LambdaNumericProjection{1}z,\\
D_F(z)&:=\LambdaListPrefix\,(\LambdaNumericPair\,(Fi)\,e),\\
T_F&:=\lambdaab{z}{\LambdaZeroTest\,(D_F(z))\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
\end{aligned}$$
The tree decider is the closed term
$$C_F:=\lambdaab{e}{\LambdaBoundedProduct{T_F}\,
 \bigl(\LambdaNumericPair\,e\,(\LambdaSucc(\LambdaListLength\,e))\bigr)}.$$
The bounded-product lemma shows that $C_F$ terminates and returns one exactly when none of the first
$\Length{\LambdaListDecode{e}}+1$ forbidden words is a prefix of the decoded list. Its other output is zero.
Thus it decides precisely the stage-cutoff tree in §{sec:edst-recursive-trees}. Lifting this ordinary numerical
term to ignore an input-name argument gives the same decider relative to any fixed real parameter.

\begin{mathmeta}
  \define{LambdaRelativeProduct}
\end{mathmeta}

Let $T$ be a closed lambda program whose numerical input codes a pair. To multiply its answers while keeping
one parameter fixed, expand the following abbreviations inside their enclosing abstractions:
$$\begin{aligned}
G_T(o,x)&:=\lambdaab{k}{\lambdaab{r}{
 \LambdaMul\,r\,\bigl(To(\LambdaNumericPair\,x\,k)\bigr)}},\\
x(z)&:=\LambdaNumericProjection{1}z,\qquad
N(z):=\LambdaNumericProjection{2}z,\\
\LambdaRelativeProduct{T}&:=\lambdaab{o}{\lambdaab{z}{
 \LambdaRecursor\,G_T(o,x(z))\,\ChurchNumeral{1}\,N(z)}}.
\end{aligned}$$
Choose all displayed binders distinct, and choose the recursor's internal binders fresh for the input variable.
The resulting term is closed. The same $o$ occurs in every call to $T$; it is never replaced by a new parameter.

\begin{lemma*}[\termdefineas{Bounded products relative to a fixed parameter}{Bounded products relative to a
fixed parameter}]
Fix $\varepsilon$, $x,N\in\NN$, and numbers $a_k$ for $k<N$. Suppose that $T$, with parameter $\varepsilon$,
returns $\ChurchNumeral{a_k}$ on input $\ChurchNumeral{\NatPair{x}{k}}$ for each $k<N$. Then
$\LambdaRelativeProduct{T}$, with the same parameter, returns
$\ChurchNumeral{\prod_{k<N}a_k}$ on input $\ChurchNumeral{\NatPair{x}{N}}$.
For $N=0$ the result is one and no input query is needed. No behavior of $T$ on the other inputs or parameters
is required. If all $a_k$ are zero or one, the output is one exactly when all the tested answers are one,
and zero otherwise.
\end{lemma*}

\begin{proof}[Proof]
Two outer beta steps expose the recursor. The numerical projections give $x$ and $N$. Set $b_0=1$ and
$b_{k+1}=b_k a_k$ for $k<N$. At stage $k$, two beta steps expose the body of $G_T$; numerical pairing produces
$\ChurchNumeral{\NatPair{x}{k}}$, the assumed computation of $T$ gives $\ChurchNumeral{a_k}$, and multiplication
returns $\ChurchNumeral{b_{k+1}}$. The update has only the input variable free, and every state is a closed numeral.
The finite-stage recursion theorem of §{sec:lambda-input-recursion} therefore gives $\ChurchNumeral{b_N}$.
Induction identifies $b_N$ with the displayed product. For zero stages, the Church numeral selects the initial
value without evaluating the update. For zero-or-one factors, multiplication preserves this range and returns one
exactly when every factor is one. All reductions use the same parameter, and output uniqueness excludes a
different numerical answer.
\end{proof}

To apply this to trees, let $F$, with parameter $\varepsilon$, compute the code of $s_i$ on input $i$.
Replace the ordinary trial above by
$$\begin{aligned}
i(z)&:=\LambdaNumericProjection{2}z,\qquad e(z):=\LambdaNumericProjection{1}z,\\
D_F(o,z)&:=\LambdaListPrefix\,(\LambdaNumericPair\,(Fo\,i(z))\,e(z)),\\
T_F&:=\lambdaab{o}{\lambdaab{z}{
 \LambdaZeroTest\,(D_F(o,z))\,\ChurchNumeral{1}\,\ChurchNumeral{0}}},\\
C_F&:=\lambdaab{o}{\lambdaab{e}{\LambdaRelativeProduct{T_F}\,o\,
 \bigl(\LambdaNumericPair\,e\,(\LambdaSucc(\LambdaListLength\,e))\bigr)}}.
\end{aligned}$$
As before, expand the abbreviations inside the abstractions. At a decoded list $t$, the bounded-product lemma
applies to exactly $\Length{t}+1$ reversed prefix tests. It proves that $C_F$ is the relative decider asserted in
§{sec:edst-recursive-trees}. Termination of $F$ for every index with this fixed parameter suffices.

### Total enumerations from semidecision {#sec:lambda-total-enumerations}

\begin{mathmeta}
  \define{LambdaRelativeSearch,LambdaAcceptanceTest,LambdaTotalEnumeration}
  \vars{k,n}{Nat}
\end{mathmeta}

First make the acceptance convention precise. For a closed paired-input test $T$, expand
$$\begin{aligned}
H_T(o,n)&:=\lambdaab{k}{\LambdaZeroTest\,
 \bigl(To(\LambdaNumericPair\,n\,k)\bigr)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
\LambdaRelativeSearch{T}&:=\lambdaab{o}{\lambdaab{n}{
 \LambdaResultSearch\,H_T(o,n)\,(\lambdaab{j}{\ChurchNumeral{1}})}}.
\end{aligned}$$
The constant-one function is the result branch of the search and is used only after a successful test.
All binders are chosen fresh as in §{sec:lambda-input-search}.

\begin{lemma*}[\termdefineas{Exact relative search for acceptance}{Exact relative search for acceptance}]
Fix $\varepsilon$ and suppose that $T$, with that parameter, computes a total numerical function $t$ on paired
inputs. On input $n$, $\LambdaRelativeSearch{T}$ has a numerical output exactly when
$t(\NatPair{n}{k})\ne0$ for some $k$, and its output is then one.
\end{lemma*}

\begin{proof}[Proof]
Two outer beta steps expose the result-search term. At stage $k$, beta reduction, numerical pairing, and the
assumed computation of $T$ make $H_T$ return zero exactly when $t(\NatPair{n}{k})\ne0$.
If a successful stage exists, take the least one. Every earlier test returns one, so the search reaches that
stage and applies its result function, returning one. If every stage fails, the no-output theorem in
§{sec:lambda-input-search} excludes every normal-form numeral. Output uniqueness excludes a second numerical
answer in the successful case. These are reductions with the same fixed parameter throughout.
\end{proof}

\begin{proposition*}[\termdefineas{Acceptance and numerical halting domains}{Acceptance and numerical halting domains}]
A predicate on coded inputs has a closed program accepting exactly its members if and only if it is the
numerical halting domain of a closed program. This equivalence holds relative to each fixed parameter.
Here acceptance means output one; a numerical halting domain permits any numeral output.
\end{proposition*}

\begin{proof}[Proof]
Given an accepting program with index $e$, use the total candidate checker of §{sec:lambda-input-universal-evaluation}
to search bounds for a computation with output one. Conversely, for a program with a prescribed numerical halting
domain, search pairs consisting of a proposed output numeral and a certificate bound. Each candidate test is
total. Its soundness and completeness say that some test succeeds exactly when the specified output, or some
numerical output, respectively, exists. Apply the exact relative search lemma, which returns one on success and
has no numerical output otherwise. This proves both implications without deciding nontermination.
\end{proof}

Now fix an accepting program index $e$ and a code $a_\ast$ known to be accepted. Write
$$\begin{aligned}
a(z)&:=\LambdaNumericProjection{1}z,\qquad r(z):=\LambdaNumericProjection{2}z,\\
\LambdaAcceptanceTest{e}&:=\lambdaab{o}{\lambdaab{z}{
 \LambdaQueryOutputCandidate\,o\,\ChurchNumeral{e}\,a(z)
 \,\bigl(\LambdaNumericPair\,\ChurchNumeral{1}\,r(z)\bigr)}},\\
\LambdaTotalEnumeration{e}{a_\ast}&:=\lambdaab{o}{\lambdaab{z}{
 \LambdaLeCase{\ChurchNumeral{1}}{\LambdaAcceptanceTest{e}\,o\,z}{a(z)}{\ChurchNumeral{a_\ast}}}}.
\end{aligned}$$
Expand the abbreviations inside the displayed abstractions. The acceptance test returns one exactly when the
finite bound certifies output one, and returns zero otherwise. Thus the comparison selects the candidate code
on success and the fixed accepted code on failure. Every component computation terminates.

\begin{proposition*}[\termdefineas{Total enumeration by finite acceptance tests}{Total enumeration by finite
acceptance tests}]
With a fixed parameter, the preceding closed term computes a total sequence whose range is exactly the accepted
set of natural-number codes. The default code must belong to that set. Applied to the bijective finite-list
coding, the same construction enumerates exactly the accepted words.
\end{proposition*}

\begin{proof}[Proof]
The candidate checker, projections, pairing, and comparison give totality. A successful test certifies an
accepting computation, while the default belongs to the accepted set by hypothesis; hence every output belongs
to that set. If a code is accepted, completeness of the finite checker supplies a bound, and the stage pairing
that code with the bound returns it. This proves the reverse range inclusion. Decoding the output codes gives
the word sequence; the two inverse identities of finite-list coding preserve both range inclusions. No code
validity test is needed because every natural number decodes to exactly one finite word.
\end{proof}

For the parameter-free application, take $\varepsilon(k)=0$ for every $k$ and substitute the closed numerical
term $\lambdaab{k}{\ChurchNumeral{0}}$ for the input argument. The substitution theorem of
§{sec:lambda-input-composition} replaces every query by ordinary beta reduction. Thus both the total
enumerator and every total tree decider above have ordinary closed numerical implementations. This establishes
the unrelativized closed-set tree representation as well as its fixed-parameter version. The empty forbidden
family is handled separately by the full tree and its constant-one decider.

## Trees, Jumps, and Ordinal Computations {#sec:lambda-tree-jump-programs}

### Pair Trees and Uniform Indices {#sec:lambda-pair-tree-programs}

\begin{mathmeta}
  \vars{a,c,e,i,j,k,r,u,v,w,z,\beta}{Nat}
  \vars{s,t,\sigma}{Seq(Nat)}
  \vars{p,\delta,\varepsilon}{Name}
  \vars{\kappa}{Fun(Prod(Nat,Nat),Nat)}
\end{mathmeta}

Use $i=1,2$ for the two numerical projections. On a list code, the closed term
$$\LambdaTermName{wordProjection}_i:= \LambdaListMap\, \LambdaNumericProjection{i}$$ computes the code of the list
obtained by projecting each
entry. To keep the first word and project the witness word, use
$$\LambdaTermName{nodeProjection}_i:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericProjection{1}z)
\bigl(\LambdaTermName{wordProjection}_i(\LambdaNumericProjection{2}z)\bigr)}.$$
For relative membership deciders $P,Q$, the intersection decider is
$$\lambdaab{o}{ \lambdaab{z}{ \LambdaMul\, \bigl(Po( \LambdaTermName{nodeProjection}_1z) \bigr)\, \bigl(Qo(
\LambdaTermName{nodeProjection}_2z) \bigr)}}.$$
All abbreviations are expanded before abstraction. The bound variables are distinct and fresh for the component
terms, which are closed.

\begin{lemma*}[Pair-tree decision programs]
The preceding terms compute the two witness projections and decide membership in the intersection tree of
§{sec:edst-recursive-trees}, relative to the same fixed parameter as the original deciders.
Prefix comparisons give a decider for restriction to two cylinders, and length comparison gives a decider for
the full synchronized tree.
\end{lemma*}

\begin{proof}[Proof]
The list-map reduction theorem applies to each numerical projection, so it computes every projected entry and
preserves the list's length and order. Numerical pairing then constructs exactly the two input codes required
by $P,Q$. Both decisions terminate at the fixed parameter; their zero-or-one outputs multiply to one exactly when
both hold. For a fixed word $\sigma$, test whether $\sigma$ is a prefix of the variable word or conversely,
using the two
orientations of the list-prefix test. Boolean disjunction combines them. Do this in both coordinates and conjoin
the results with the original membership test. This retains short nodes compatible with the cylinder. Finally,
apply the list-length term to each coordinate and use numerical equality to decide equal lengths.
\end{proof}

For sections, combine the two parameters as $\delta(n)=\NatPair{\varepsilon(n)}{p(n)}$. Define accessors
$$\LambdaTermName{inputProjection}_i:=\lambdaab{o}{\lambdaab{k}{\LambdaNumericProjection{i}(ok)}}.$$
Using the finite-prefix reader, define
$$\begin{aligned}
\LambdaTermName{sectionInput}&:=\lambdaab{o}{\lambdaab{z}{\LambdaNumericPair\,
 \bigl(\LambdaInputPrefix\,(\LambdaTermName{inputProjection}_2o)\,(\LambdaListLength z)\bigr)\,z}},\\
\LambdaTermName{section}_P&:= \lambdaab{o}{ \lambdaab{z}{P( \LambdaTermName{inputProjection}_1o)(
\LambdaTermName{sectionInput}oz)}}.
\end{aligned}$$
The accessors recover the original parameter and the base point from the same supplied input. In particular,
$\LambdaTermName{sectionInput}$ computes the code of $\Pair{\restrict{p}{\Length{t}}}{t}$ on the list code of $t$.

\begin{lemma*}[Section decision program]
If $P$ decides membership in a pair tree $T$ relative to $\varepsilon$, then $\LambdaTermName{section}_P$
decides membership in $T_p$
relative to $\delta$.
\end{lemma*}

\begin{proof}[Proof]
Each accessor query reduces to the corresponding projection of the numerical pair returned by the input.
The prefix-reader theorem therefore gives the first $\Length{t}$ entries of $p$, and numerical pairing gives the
required membership input. Substitution of the first accessor in the finite beta/query derivation for $P$
replaces each query by a computation of the same answer. Finally, two outer beta steps feed the output of
$\LambdaTermName{sectionInput}$
into this substituted program. All these steps retain the same supplied parameter, and both component
computations terminate. The result is exactly the zero-or-one answer for membership in $T_p$.
\end{proof}

The finite output-candidate checker is total even when the indexed program is partial. Supply its program
index as data together with the node code. To truncate a pair of word codes, expand
$$\begin{aligned}
\LambdaTermName{truncatePair}(w,j):=\LambdaNumericPair\,
 &\bigl(\LambdaListTake\,(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,j)\bigr)\\
 &\bigl(\LambdaListTake\,(\LambdaNumericPair\,(\LambdaNumericProjection{2}w)\,j)\bigr).
\end{aligned}$$
On input $\NatPair{w}{j}$, the corresponding closed numerical term computes the code of the pair of
length-$j$ truncations. Both projections, both prefix extractions, and the final pairing are total.

Decode a trial input as $v=\NatPair{\NatPair{e}{w}}{\NatPair{j}{r}}$, using the four compositions of numerical
projections, and abbreviate these four projected terms by $e,w,j,r$ inside the following body:
$$\begin{aligned}
\LambdaTermName{rejectCandidate}(o,v)&:=\LambdaQueryOutputCandidate\,o\,e\,\LambdaTermName{truncatePair}(w,j)
  \,\bigl(\LambdaNumericPair\,\ChurchNumeral{0}\,r\bigr),\\
\LambdaTermName{acceptTrial}&:= \lambdaab{o}{ \lambdaab{v}{ \LambdaZeroTest\,
\LambdaTermName{rejectCandidate}(o,v)\, \ChurchNumeral{1}\, \ChurchNumeral{0}}}.
\end{aligned}$$
Thus $\LambdaTermName{rejectCandidate}$ returns one exactly when the trial certifies output zero, and
$\LambdaTermName{acceptTrial}$ reverses that bit. The universal
candidate test makes the program independent of the supplied index. Each trial terminates at every parameter.

For the family input $z=\NatPair{e}{w}$, let
$$\begin{aligned}
&\LambdaTermName{firstLength}(z):=\LambdaListLength(\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z)),\\
&\LambdaTermName{secondLength}(z):=\LambdaListLength(\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z)),\\
&\LambdaTermName{sameLength}(z):=\LambdaEqual\,\LambdaTermName{firstLength}(z)\,\LambdaTermName{secondLength}(z),\\
&\LambdaTermName{indexedTree}:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaMul\,\LambdaTermName{sameLength}(z)\,
 \bigl( \LambdaRelativeProduct{ \LambdaTermName{acceptTrial}}\,o\,( \LambdaNumericPair\,\\
&\quad z\,
\LambdaTermName{firstLength}(z)) \bigr)
\end{aligned}}}.
\end{aligned}$$
As throughout, expand the abbreviations before abstraction and choose distinct fresh binders.
For a fixed parameter $\varepsilon$, define
$T_e$ here as the set of equal-length pairs $\Pair{s}{t}$ for which the reversed trial
$\LambdaTermName{acceptTrial}$ returns one at every
$i<\Length{s}$, on input $\NatPair{\NatPair{e}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}}{i}$.

\begin{lemma*}[Uniform indexed-tree decider]
The closed program $\LambdaTermName{indexedTree}$ decides membership in the family $T_e$ of
§{sec:edst-pair-tree-indices}, uniformly in
the index and node code, with the fixed parameter supplied as input. It terminates for every numerical index,
including those whose programs fail to decide any tree.
\end{lemma*}

\begin{proof}[Proof]
The candidate checker and the truncation program give precisely the rejection test used in the definition of
$T_e$. The relative bounded product of $\Length{s}$ reversed bits is one exactly when none of
the first $\Length{s}$ trials
rejects. Multiplication by the length-equality bit enforces synchronization. At length zero the product is
one, with no trial evaluated. Each component is total on its supplied numerical inputs, so this also proves
termination without any hypothesis on the indexed program.
\end{proof}

For specialization, choose fixed named representatives of a closed family decider $P$ and the numerical-pairing
term, with syntax codes $u,\beta$. Use binder names $x_1,x_2$, whose variable codes are $3,6$. With the application
and abstraction code constructors
$$\operatorname{app}(a,c)=3\NatPair{a}{c}+1,\qquad
\operatorname{lam}(k,a)=3\NatPair{k}{a}+2,$$
the specialized program has code
$$\begin{aligned}
f(i)=\operatorname{lam}\bigl(1,\operatorname{lam}\bigl(2,
 &\operatorname{app}\bigl(\operatorname{app}(u,3),\\
 &\operatorname{app}(\operatorname{app}(\beta,\LambdaSyntaxCode{\ChurchNumeral{i}}),6)\bigr)\bigr)\bigr).
\end{aligned}$$
This is exactly the code of $\lambdaab{o}{\lambdaab{z}{Po(\LambdaNumericPair\,\ChurchNumeral{i}\,z)}}$ with
$o=x_1$ and $z=x_2$.

\begin{lemma*}[Computed specialization of relative predicates]
The displayed map $f$ is computed by a closed numerical lambda term. If $P$ decides a predicate jointly in a
natural number and a coded input relative to a fixed parameter, then $P_{f(i)}$ decides its $i$th section at that
same parameter.
\end{lemma*}

\begin{proof}[Proof]
Compute the numeral code with $\LambdaNumeralCodeProgram$, the four application codes with
$\LambdaTaggedCode{1}$, and the two abstraction codes with $\LambdaTaggedCode{2}$. Pointwise composition of these
closed numerical programs gives a closed term computing $f$. The coding inverses recover the stated template;
its only added variables are bound, so its code denotes the intended closed program. On a valid input code,
two beta contractions expose the family decider applied to a numerically paired input. Pairing supplies the
exact family code and the original decider supplies its answer. The parameter remains unchanged throughout.
\end{proof}

The source program code may also be supplied as an input. Keep only the representative of numerical pairing
fixed. In the preceding code recipe, replace the constant source code by the first input projection and compute
the inserted numeral code from the second projection. This gives a total numerical map $\Pair{u}{a}\mapsto \kappa(u,a)$.
Whenever $u$ decodes to a closed term, its output is the syntax code of a closed term satisfying
$$P_{\kappa(u,a)}=\lambdaab{o}{\lambdaab{z}{P_uo(\LambdaNumericPair\,\ChurchNumeral{a}\,z)}}.$$
Here $o=x_1$ and $z=x_2$. This identity does not require the source program to terminate. The index computation
constructs syntax and is total on every pair of natural-number inputs.

### Jumps, Quantifiers, and Joins {#sec:lambda-relative-jump}

\begin{mathmeta}
  \vars{b,e,k,m,n,t}{Nat}
  \vars{\varepsilon}{Name}
\end{mathmeta}

Fix an arbitrary parameter $\varepsilon:\NN\to\NN$ and put
$$K^\varepsilon:=\{e:\exists m\;\LambdaInputSteps{\varepsilon}{P_eo\ChurchNumeral{e}}{\ChurchNumeral{m}}\}.$$
For $A\IncludedIn\NN$, let $\chi_A$ be one on $A$ and zero outside $A$.
Thus $K^\varepsilon$ records numerical halting on the program's own index. When $\varepsilon=\chi_A$, it is
$A'$ from §{sec:hyperarithmetic-hierarchy}. Write $p_i:=\LambdaNumericProjection{i}$. With fresh binders, set
$$\begin{aligned}
T&:=\lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,(p_1z)\,(p_1z)\,(p_2z)}},\\
J&:=\LambdaRelativeSearch{T}.
\end{aligned}$$
The paired input of $T$ is $\NatPair{e}{k}$, where $k$ codes an output candidate and a finite certificate bound.
Each trial terminates for every parameter and every input.

\begin{lemma*}[\termdefineas{relative jump search}{Exact search for the relative jump}]
The term $J$ returns one on input $e$ exactly when $e\in K^\varepsilon$, and it has no numerical output otherwise.
The complement of $K^\varepsilon$ is not semidecidable relative to $\varepsilon$.
\end{lemma*}

\begin{proof}[Proof]
Numerical projections supply $e,e,k$ to the total candidate checker. Its soundness and completeness identify
existence of a successful trial with $e\in K^\varepsilon$. The exact relative search lemma gives the asserted
output and excludes every numerical output if all trials fail.

Suppose the complement had an accepting program. By the acceptance/domain equivalence, it would have a
closed program $D$ whose numerical halting domain is exactly that complement. Choose an index $d$ for $D$.
The definition of $K^\varepsilon$ then gives $d\notin K^\varepsilon$ if and only if $d\in K^\varepsilon$.
Both cases contradict this equivalence. A decider for $K^\varepsilon$ would semidecide its complement by
reversing the output bit, so no such decider exists either.
\end{proof}

To recover the original parameter bits, use the closed terms
$$\begin{aligned}
Q&:=\lambdaab{o}{\lambdaab{z}{o(p_1(p_1z))}},\qquad P:=\LambdaRelativeSearch{Q},\\
S_n&:=\lambdaab{o}{\lambdaab{t}{Po(\LambdaNumericPair\,\ChurchNumeral{n}\,t)}}.
\end{aligned}$$
On input $\NatPair{\NatPair{n}{t}}{k}$, the trial $Q$ returns $\varepsilon(n)$ independently of $t,k$.
Apply the syntax-code construction in §{sec:lambda-pair-tree-programs} to this fixed $P$: it gives
an index $f(n)$ for $S_n$ and a closed numerical lambda term $F$ computing $f$.
The same code construction applies to a partial program; totality was needed for the decision conclusion,
not for constructing the specialized syntax. Both $F$ and $f$ are independent of $\varepsilon$.

\begin{lemma*}[\termdefineas{parameter recovery from the jump}{Recovering parameter bits from the jump}]
For every $\varepsilon,n$, one has $f(n)\in K^\varepsilon$ if and only if $\varepsilon(n)\ne0$.
In particular, for every $A\IncludedIn\NN$, the closed term
$$\lambdaab{o}{\lambdaab{n}{o(Fn)}}$$
computes $\chi_A$ with input function $\chi_{A'}$.
\end{lemma*}

\begin{proof}[Proof]
Every trial for $P$ on input $\NatPair{n}{t}$ has the same value $\varepsilon(n)$. The exact search theorem
therefore says that $P$ returns one exactly when this value is nonzero, and has no numerical output otherwise.
Two beta contractions and numerical pairing reduce the specialized program $S_n$ on input $t$ to this
computation. Conversely, confluence carries any numeral output of $S_n$ to the reduced computation, because
numerals are terminal. Thus specialization preserves both outputs and numerical nontermination.
Apply this equivalence with $t=f(n)$ to obtain the first assertion. For a characteristic function, being
nonzero means being one, so $\chi_{A'}(f(n))=\chi_A(n)$. The computation of $F$ followed by one input query
proves the second assertion. No test of emptiness or choice of a terminating index is used.
\end{proof}

Retain $K^\varepsilon$ from §{sec:lambda-relative-jump}, and put $\varepsilon':=\chi_{K^\varepsilon}$.
Choose the named closed representative of $P_e$ supplied by the program enumeration. Define
$$D_{e,n}:=\lambdaab{o}{\lambdaab{t}{P_eo\ChurchNumeral{n}}},\qquad
 h(e,n):=\LambdaSyntaxCode{D_{e,n}}.$$
Here the syntax code is formed from that named representative, and the bound variables are fresh.
The program enumeration retains this closed term at its syntax index.

\begin{lemma*}[\termdefineas{uniform halting reduction}{Uniform reduction of numerical halting}]
A closed numerical term $F$ computes $\NatPair{e}{n}\mapsto h(e,n)$. With every parameter $\varepsilon$,
$$h(e,n)\in K^\varepsilon\quad\Longleftrightarrow\quad
 \exists m\;\LambdaInputSteps{\varepsilon}{P_eo\ChurchNumeral{n}}{\ChurchNumeral{m}}.$$
Consequently the closed term
$$H:=\lambdaab{o}{\lambdaab{z}{o\bigl((\lambdaab{u}{F})oz\bigr)}}$$
decides arbitrary numerical halting with input function $\varepsilon'$.
\end{lemma*}

\begin{proof}[Proof]
The enumeration supplies the code of the selected closed program from $e$, and
$\LambdaNumeralCodeProgram$ supplies the code of $\ChurchNumeral{n}$. Two application-code constructors
and two abstraction-code constructors form the displayed term. Composing their closed numerical
implementations gives $F$, independently of $\varepsilon$.
For every numerical input $t$, two beta contractions reduce $D_{e,n}o\ChurchNumeral{t}$ to
$P_eo\ChurchNumeral{n}$. Prefixing those steps preserves every output. Conversely, confluence and
terminality of numerals carry every output of the first term to the second. Set $t=h(e,n)$ to obtain
the equivalence. The term $H$ computes this index and makes one query, so it returns exactly the
zero-or-one answer to the halting question.
\end{proof}

Now put $Z:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$.
It reverses decision bits. For each $e$, form named representatives of
$$\begin{aligned}
S_e&:=\LambdaRelativeSearch{P_e},\qquad s(e):=\LambdaSyntaxCode{S_e},\\
B_s&:=\lambdaab{z}{\LambdaNumericPair\,
 ((\lambdaab{j}{\ChurchNumeral{s}})z)\,((\lambdaab{j}{j})z)},\\
Q_e&:=\lambdaab{o}{\lambdaab{n}{Ho(B_{s(e)}n)}},\\
N_e&:=\lambdaab{o}{\lambdaab{n}{Z(P_eon)}},\\
\xi(e)&:=\LambdaSyntaxCode{Q_e},\qquad
\nu(e):=\LambdaSyntaxCode{N_e},\qquad
\upsilon(e):=\nu(\xi(\nu(e))).
\end{aligned}$$
Use fixed named representatives of the closed library terms and expand the search template from
§{sec:lambda-total-enumerations} before taking its code. These choices are made once, before any
$e$ or $\varepsilon$ is supplied.

\begin{proposition*}[\termdefineas{lambda quantifier index transformations}{Lambda index transformations
for quantifiers}]
The functions $\xi,\nu,\upsilon$ are computed by total closed numerical lambda terms. If $P_e$ decides
$R(n,k)$ at $\varepsilon$, then $P_{\xi(e)}$ decides $\exists k\,R(n,k)$ at $\varepsilon'$, and
$P_{\upsilon(e)}$ decides $\forall k\,R(n,k)$ at $\varepsilon'$. The program $P_{\nu(e)}$ reverses any
predicate decided by $P_e$ while retaining its parameter.
The code transformations are total on every index; their decision assertions require the stated
decision hypothesis on $P_e$.
\end{proposition*}

\begin{proof}[Proof]
The search template consists of fixed closed terms, applications, abstractions, and the inserted
representative of $P_e$. Hence the code constructors compute $s(e)$. The numeral-code term then supplies
$\LambdaSyntaxCode{\ChurchNumeral{s(e)}}$, and the same constructors compute $\xi(e)$. They also compute
$\nu(e)$ directly from the template $N_e$. Composition gives $\upsilon$.
All resulting syntax is closed, so decoding these indices gives the displayed programs.

Suppose $P_e$ decides $R$. Every trial of $S_e$ terminates; the exact-search theorem says that $S_e$ on
input $n$ returns one precisely when some $k$ satisfies $R(n,k)$, and has no numerical output otherwise.
The halting reduction shows that $Q_e$ with parameter $\varepsilon'$ returns the characteristic bit
of this existential statement. The term $N_e$ reverses zero and one, proving the negation assertion.
Negate the original predicate, apply the existential construction, and negate the answer to obtain
the universal assertion. These finite code constructions precede every use of the input parameter.
Applying $\xi$ to a decider on $\NatPair{\NatPair{n}{t}}{b}$ and then $\upsilon$ gives a decider for
$\forall t\,\exists b\,R(n,t,b)$ at $(\varepsilon')'$.
\end{proof}

Let $A_n\IncludedIn\NN$ and put
$$B:=\EffectiveJoin{n}{A_n}=\{\NatPair{n}{m}:m\in A_n\}.$$
Thus $\chi_B(\NatPair{n}{m})=\chi_{A_n}(m)$, where each characteristic function takes values one and zero.
Using the closed numerical-pairing term, define
\begin{mathmeta}
  \define{LambdaJoinSection}
\end{mathmeta}
$$\LambdaJoinSection{n}:=\lambdaab{o}{\lambdaab{m}{o(\LambdaNumericPair\,\ChurchNumeral{n}\,m)}}.$$
The numeral for the selected component is part of this finite term.

\begin{lemma*}[\termdefineas{lambda effective join sections}{Reading a component of an effective join}]
For every $n$, the term $\LambdaJoinSection{n}$ is closed. With input function $\chi_B$, it returns
$\ChurchNumeral{\chi_{A_n}(m)}$ on numerical input $m$. More generally, with any input function
$\varepsilon$, it returns $\ChurchNumeral{\varepsilon(\NatPair{n}{m})}$.
\end{lemma*}

\begin{proof}[Proof]
All variables are bound, and the pairing term and numeral are closed. Two beta contractions supply the input
function and the numeral for $m$. Numerical pairing reduces the query argument to the numeral for
$\NatPair{n}{m}$; one input-query step then returns its value under $\varepsilon$. With $\varepsilon=\chi_B$,
the defining identity for the join gives the required component bit. This construction is independent of the
sets in the sequence. It supplies the limit-step accessor for §{sec:edst-ordinal-notations}.
\end{proof}

### Recursive Orders and Ordinal Notations {#sec:lambda-recursive-order-programs}

\begin{mathmeta}
  \vars{a,k,n,q,r}{Nat}
\end{mathmeta}

A presentation at a fixed parameter $\varepsilon$ consists of total closed decision programs $D,R$ for a
subset of $\NN$ and a relation on $\NN$, whose restriction to that subset is a strict well order. The
program $R$ receives a numerical pair. This is the presentation used in §{sec:hyperarithmetic-hierarchy}.
Its well-foundedness is an external assumption. The operations below preserve that assumption; they do
not test it.
For numerical terms $X,Y$, abbreviate
$$\begin{aligned}
N(X)&:=\LambdaZeroTest\,X\,\ChurchNumeral{1}\,\ChurchNumeral{0},\\
U(X,Y)&:=N(\LambdaMul\,(N(X))\,(N(Y))).
\end{aligned}$$
On decision bits these compute negation and disjunction. Write $p_i:=\LambdaNumericProjection{i}$.

For an element with code $a$ in the original domain, the initial-segment membership program is
$$D_{<a}:=\lambdaab{o}{\lambdaab{n}{\LambdaMul\,(Do\,n)\,
 (Ro(\LambdaNumericPair\,n\,\ChurchNumeral{a}))}}.$$
Its comparison program remains $R$. For the successor, zero codes the new largest element and $n+1$
codes the old element $n$. Set
$$\begin{aligned}
D^+&:=\lambdaab{o}{\lambdaab{n}{U(N(n),Do(\LambdaPred\,n))}},\\
a(z)&:=p_1z,\qquad b(z):=p_2z,\\
V(o,z)&:=Ro(\LambdaNumericPair\,(\LambdaPred\,a(z))\,(\LambdaPred\,b(z))),\\
R^+&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(N(N(a(z))))\,U(N(b(z)),V(o,z))}}.
\end{aligned}$$
Expand the abbreviations with fresh binders. Equivalently, compose the numerical reindexing and Boolean-program
constructors; on numeral inputs
they perform these same bit computations.
The empty presentation uses constant-zero programs for both membership and comparison.

\begin{lemma*}[\termdefineas{recursive well-order presentation programs}{Decision
programs for initial segments and successors}]
The displayed terms decide the initial-segment and successor presentations at the original parameter.
They terminate on every numerical input. The corresponding order types are the position of $a$ and the
successor of the original order type, respectively.
\end{lemma*}

\begin{proof}[Proof]
In the initial-segment term, pairing supplies the original comparison input and multiplication computes
conjunction. For the successor domain, $N(n)$ is one at zero, so $U$ accepts zero; at a positive input,
predecessor recovers the old element and $U$ returns its membership bit. In the comparison term, the first
factor is zero when the first input is zero. If that input is positive, the second factor is one when
the second input is zero, and otherwise it is the comparison bit of the two predecessors. These are
exactly the stated order clauses. All component calls terminate, even when a discarded old comparison
is evaluated. The initial-segment inclusion is an order isomorphism onto the elements below $a$.
For the successor, send a positive code to its predecessor and send zero to a new last point; this is
an order isomorphism with the ordered sum of the old domain and a singleton.
\end{proof}

\begin{lemma*}[\termdefineas{elimination of a computable input parameter}{Eliminating a computable input parameter}]
Suppose a closed numerical term $E$ computes $\varepsilon$. Substituting $E$ for the input variable in
any finite beta/query computation at $\varepsilon$ gives a finite beta computation with the same output.
In particular, if $P$ is a decision program at $\varepsilon$, the closed term $PE$ is an ordinary
numerical decision program for the same predicate. Taking $E=\lambdaab{k}{\ChurchNumeral{0}}$ removes
the constant-zero parameter.
\end{lemma*}

\begin{proof}[Proof]
Strengthen the substitution claim to finite substitution lists and induct on one beta/query step.
A beta contraction remains a beta contraction under capture-avoiding substitution. A query at $n$ is
replaced by the assumed finite reduction of $E\ChurchNumeral{n}$ to $\ChurchNumeral{\varepsilon(n)}$.
Application contexts preserve these reductions. Under an abstraction, first rename its binder to a
variable fresh for the substitution list, both bodies, and the input variable; the induction hypothesis
then applies to the renamed body. Concatenating the finite reductions handles an entire computation.
Closed numerals are unchanged by substitution. For $P$, closedness also leaves the program unchanged,
so substitution in $Po\ChurchNumeral{n}$ gives $PE\ChurchNumeral{n}$. This proves the decision assertion.
\end{proof}

Fix a recursive well-order presentation $W=\Pair{D}{R}$, with pure numerical decision terms for membership and
comparison.
We use $D,R$ for these terms as well. The constant-zero input parameter can be eliminated by the preceding lemma.
The following finite procedure is defined for every numerical $a,n$, even if $a$ is outside the domain.
Start with $\KleenePredMax{a}{0}=0$. At stage $k$, let $r$ be the current state. If $k$ is not in the domain or $kRa$
fails, keep $r$. Otherwise replace zero by $k+1$; if $r=b+1$, replace it by $k+1$ exactly when $bRk$, and keep it
otherwise. Thus positive states encode selected predecessors, while zero means that none has been found.

For the update, extract $a,k,r$ from the numerical input $\NatPair{a}{\NatPair{k}{r}}$ by projections and expand
$$\begin{aligned}
A&:=\LambdaMul\,(Dk)\,(R(\LambdaNumericPair\,k\,a)),\\
B&:=R(\LambdaNumericPair\,(\LambdaPred\,r)\,k),\\
J&:=\LambdaLeCase{\ChurchNumeral{1}}{A}{
 \bigl(\LambdaLeCase{r}{\ChurchNumeral{0}}{\LambdaSucc\,k}{
 (\LambdaLeCase{\ChurchNumeral{1}}{B}{\LambdaSucc\,k}{r})}\bigr)}{r}.
\end{aligned}$$
Use the closed composition term for this update in numerical primitive recursion with initial value zero. Denote the
resulting closed program by $C$; its input is $\NatPair{a}{n}$.

\begin{lemma*}[\termdefineas{lambda finite predecessor maximum}{Finite predecessor maxima}]
The program $C$ computes $\KleenePredMax{a}{n}$. The result is zero exactly when no domain element $k<n$ satisfies
$kRa$. Otherwise it is $b+1$, where $b<n$ is a domain element with $bRa$ and every domain element $k<n$ satisfying
$kRa$ is equal to $b$ or precedes it. Once a positive state is reached, the selected element stays unchanged or
increases at the next stage. Every predecessor of $a$ is at or below the selected element at each sufficiently large
stage.
\end{lemma*}

\begin{proof}[Proof]
The membership and comparison bits make $A$ the conjunction of the two tests. The nested numerical comparisons then
implement precisely the stated update, so numerical primitive recursion proves termination and the output formula.
For the maximum property, induct on the window size. At the new number, an empty selection becomes that number. If an
old maximum exists and precedes the new number, transitivity makes the new number a maximum. Otherwise linearity on
the domain shows that the new number is at or below the old maximum. Rejected numbers leave the invariant unchanged.
These same update cases prove monotonicity of the selection. A predecessor with code $b$ lies in every window of size
larger than $b$, so the maximum property proves the final assertion. Only the finite scan is computed; well-foundedness
is not tested.
\end{proof}

\begin{proposition*}[\termdefineas{uniform predecessor-selector indices}{Uniform predecessor-selector indices}]
There is a total computable map $\Pair{d}{r}\mapsto c(d,r)$ with the following property. Suppose $d,r$ are syntax
codes of closed numerical terms deciding the domain and relation of a recursive well-order presentation
$W=\Pair{D}{R}$, with output one for true and zero for false. Then $c(d,r)$ is the syntax code of a closed program
computing
$$\NatPair{a}{n}\longmapsto\KleenePredMax{a}{n}.$$
The map generating this index is total even on input codes that do not decide a well-order presentation.
\end{proposition*}

\begin{proof}[Proof]
Write $C(D,R)$ for the finite-scan program just constructed. Replace its two decision terms by free variables
$x_{86},x_{87}$ and fix a named representative $M$ of the resulting expression. The two-input substitution
construction of §{sec:lambda-code-substitution} computes $c(d,r)$ by inserting the terms decoded from $d,r$
in those two places, in that order. The chosen variables are distinct from the binders introduced by the
composition and numerical-recursion expressions. When the inserted terms are closed, substitution passes under
those binders and preserves all closed arithmetic and projection components. The second substitution also
preserves the first inserted term. Thus the decoded output is alpha-equivalent to $C(P_d,P_r)$.
The preceding finite-predecessor lemma proves that this is a closed program with the required numerical values.
Only the two syntactic substitutions are performed while computing the index; the decision programs are run
later, when the generated program is applied to a numerical input.
\end{proof}

We also need numerical programs for the notation constructors. Recall
$\KleeneSuccIter{a}{0}=a$ and $\KleeneSuccIter{a}{k+1}=2^{\KleeneSuccIter{a}{k}}$.
\begin{mathmeta}
  \define{LambdaNotationIterate,LambdaLimitCodeProgram}
\end{mathmeta}
Primitive recursion, with initial value $a$ and update $r\mapsto2^r$, gives a closed term
$\LambdaNotationIterate$ computing $\KleeneSuccIter{a}{n}$ on input $\NatPair{a}{n}$.
Primitive recursion with initial value one and update $r\mapsto5r$, followed by multiplication by three, gives a closed
term $\LambdaLimitCodeProgram$ computing $e\mapsto3\cdot5^e$. Both computations terminate on all numerical inputs.
For a valid starting notation, successor iteration remains valid and is strictly increasing in its iteration count.

Fix any closed numerical selector $C$, and let $\sigma(a,n)$ be its value at $\NatPair{a}{n}$. This may be the
predecessor selector just constructed. For numerical arguments $q,a,n$, expand the following expressions before
abstracting their variables:
$$\begin{aligned}
Z&:=C(\LambdaNumericPair\,a\,n),\\
V&:=\LambdaLeCase{Z}{\ChurchNumeral{0}}{\ChurchNumeral{1}}{
 \LambdaOutputSearch\,q\,(\LambdaPred\,Z)},\\
L(q,a,n)&:=\LambdaNotationIterate\,(\LambdaNumericPair\,V\,(\LambdaSucc\,n)),\\
T&:=\lambdaab{n}{\lambdaab{z}{
 L(\LambdaNumericProjection{1}z,\LambdaNumericProjection{2}z,n)}}.
\end{aligned}$$
Use $n=x_{84}$ and $z=x_{85}$ as the two outer binders. Fix a named representative of the closed term $T$, with code
$u$, and put
$$s(q,a):=\LambdaSpecializationCode{u}{\NatPair{q}{a}},\qquad
 g_q(a):=3\cdot5^{s(q,a)}.$$
The specialization-code term, numerical pairing and $\LambdaLimitCodeProgram$ compute these total maps. They do not run
$T$ or $P_q$ while producing the codes.

\begin{proposition*}[\termdefineas{lambda delayed notation family}{A total family of delayed limit codes}]
Suppose $C$ is total. There is a single index $q$ such that $P_q$ computes $g_q$. For this $q$, the index $s(q,a)$
computes, for every $a$, the total sequence
$$n\longmapsto\KleeneSuccIter{b_a(n)}{n+1},\qquad
 b_a(n):=\begin{cases}1,&\sigma(a,n)=0,\\g_q(b),&\sigma(a,n)=b+1.\end{cases}$$
Moreover, for all $q,a,n,m$, including indices $q$ that are not total,
$$P_{s(q,a)}\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}
 \quad\Longleftrightarrow\quad
 T\ChurchNumeral{n}\ChurchNumeral{\NatPair{q}{a}}\to_\beta^*\ChurchNumeral{m}.$$
These are statements about total numerical code construction and exact program behavior. Validity as ordinal
notations additionally requires validity and strict increase of the sequence values.
\end{proposition*}

\begin{proof}[Proof]
By numerical composition, construct a closed term $F_u$ computing
$\NatPair{q}{a}\mapsto3\cdot5^{\LambdaSpecializationCode{u}{\NatPair{q}{a}}}$.
Let $H$ be its numerical currying, so $H\ChurchNumeral{q}\ChurchNumeral{a}$ reduces to
$F_u\ChurchNumeral{\NatPair{q}{a}}$. The self-reference lemma of §{sec:lambda-index-recursion} gives $q$ with
$$P_q\ChurchNumeral{a}\to_\beta^*H\ChurchNumeral{q}\ChurchNumeral{a}
 \to_\beta^*\ChurchNumeral{g_q(a)}.$$
This proves totality without a hypothesis about the sequence values.

For any $q,a$, the specialization identity gives one beta step from the left-hand starting term in the displayed
equivalence to the right-hand starting term. Confluence and normality of numerals give the reverse implication for
outputs, so the equivalence is exact even when no output exists. For the selected self-index, two beta contractions
and numerical projections supply $q,a,n$ to $L$. The selector returns its state. A zero state selects one; a state
$b+1$ sends the numeral for $b$ to the universal evaluator, which returns $g_q(b)$ because $P_q$ is total.
The successor-iteration program then returns the asserted value. All these reductions are finite.
Applying the limit rule when the sequence is valid and increasing proves the final qualification.
The well-founded argument in §{sec:edst-ordinal-notations} establishes those hypotheses for the predecessor selector.
\end{proof}

\begin{corollary*}[\termdefineas{uniform delayed limit indices}{Uniform delayed-limit indices}]
There is a total computable map $u\mapsto q(u)$ such that, for every numerical input $u$, the program
$P_{q(u)}$ computes the total function
$$a\longmapsto3\cdot5^{\LambdaSpecializationCode{u}{\NatPair{q(u)}{a}}}.$$
No assumption on the program with index $u$ is needed to generate these indices or to compute these values.
\end{corollary*}

\begin{proof}[Proof]
Fix representatives of $\LambdaLimitCodeProgram$ and $\LambdaSpecializationCodeProgram$. The numeral-code,
application-code and abstraction-code constructors compute from $u$ the code of the closed term
$$F_u:=\lambdaab{z}{\LambdaLimitCodeProgram
 (\LambdaSpecializationCodeProgram\,\ChurchNumeral{u}\,z)}.$$
This term computes $z\mapsto3\cdot5^{\LambdaSpecializationCode{u}{z}}$ on every input.
Apply the uniform self-indexed-family constructor of §{sec:lambda-index-recursion} to its code.
Composition computes the resulting $q(u)$ from $u$. The family identity gives the displayed value at every $a$.
These assertions concern numerical codes; validity of a resulting ordinal notation still requires the
validity and strict-increase hypotheses for the sequence it codes.
\end{proof}

\begin{proposition*}[\termdefineas{uniform upper-sequence indices}{Uniform upper-sequence indices}]
Write $T(C)$ for the sequence template above with selector $C$. There are total computable numerical maps
$c\mapsto u(c)$, $c\mapsto q(c)$ and $\Pair{c}{a}\mapsto s(c,a)$ with the following properties. If $c$ decodes to a
closed term, then $u(c)$ is a code of $T(P_c)$. For every $c$, the program $P_{q(c)}$ computes
$$\begin{aligned}
g_c(a)&:=3\cdot5^{s(c,a)},\\
s(c,a)&:=\LambdaSpecializationCode{u(c)}{\NatPair{q(c)}{a}}.
\end{aligned}$$
If, in addition, $P_c$ computes a total function $\sigma$, then $P_{s(c,a)}$ computes the total sequence
$$\begin{aligned}
n&\longmapsto\KleeneSuccIter{b_{c,a}(n)}{n+1},\\
b_{c,a}(n)&:=\begin{cases}
 1,&\sigma(\NatPair{a}{n})=0,\\
 g_c(b),&\sigma(\NatPair{a}{n})=b+1.
 \end{cases}
\end{aligned}$$
The index-generating maps are total even when the supplied selector is partial. Only the assertion about the
sequence's totality requires the selector to be total.
\end{proposition*}

\begin{proof}[Proof]
In $T(C)$, replace the selector by the free variable $x_{86}$, leaving the outer binders $x_{84},x_{85}$
unchanged. Fix one named representative of this term. The substitution construction of
§{sec:lambda-code-substitution} computes $u(c)$ by inserting the syntax decoded from $c$ for $x_{86}$.
For a closed inserted term, substitution passes under the two outer binders and leaves every closed component
unchanged; hence the result is exactly $T(P_c)$ up to alpha-equivalence. Apply the uniform delayed-limit
constructor to $u(c)$ to obtain $q(c)$. Pairing and specialization compute $s(c,a)$ jointly in its two inputs.
The delayed-limit identity proves totality of $g_c$ before the selector is executed. When the selector is total,
the sequence-template reductions already proved give the displayed values. No representative is chosen as a
function of the input code, and no test of totality or well-foundedness is performed by these constructors.
\end{proof}

### Descent Trees and Jump Witnesses {#sec:lambda-certified-descent}

\begin{mathmeta}
  \vars{o,q,x}{Name}
  \vars{a,b,c,e,h,i,j,k,m,n,p,r,s,t,v,w,z,\nu}{Nat}
  \vars{\prec}{Fun(Prod(Nat,Nat),Prop)}
  \vars{\tau,\rho}{Fun(Prod(Nat,Nat),Nat)}
  \vars{\eta}{Fun(Prod(Nat,Nat,Nat),Nat)}
  \vars{D}{Set(Nat)}
  \vars{\mathbf{z}}{Seq(Nat)}
  \vars{z_*,r_*,u,d}{Nat}
  \vars{G_*}{Name}
  \vars{f,g,\upsilon,\chi,\delta,\zeta}{Fun(Nat,Nat)}
  \vars{\sigma,\kappa,\mathcal A}{Fun(Prod(Nat,Nat),Nat)}
  \vars{\psi}{Fun(Prod(Nat,Nat,Nat),Nat)}
  \vars{\mu}{Fun(Prod(Nat,Nat,Nat,Nat),Nat)}
  \vars{R,\mathcal C}{Fun(Prod(Nat,Nat),Prop)}
  \vars{\ell,\ell_*}{Fun(Prod(Nat,Nat),Nat)}
  \vars{M}{Fun(Prod(Name,Nat,Nat),Prop)}
  \vars{\mathcal B}{Fun(Prod(Name,Nat,Nat,Nat),Nat)}
  \vars{\mathcal E}{Fun(Prod(Nat,Nat,Nat,Nat),Nat)}
  \define{NatProjection}
\end{mathmeta}

A finite certificate lets us decide a tree of descending chains even when the underlying relation is not decidable.
Let $\prec$ be a relation on $\NN$, and let a closed numerical term $\LambdaTermName{cert}$ decide a
predicate $\mathcal C(p,h)$ with
$$b\prec p\quad\Longleftrightarrow\quad\exists c\;\mathcal C(p,\NatPair{b}{c}).$$
For a starting number $a$, define $T_a$ to consist of the words whose entries are next-element/certificate pairs
and whose successive certificates are accepted, starting at $a$. The empty word belongs to $T_a$.
The preceding number for the first entry is $a$; for every later entry it is the first projection of the previous entry.

For $i=1,2$, write $\NatProjection{i}{z}$ for the natural-number projections determined by
$$\NatProjection{1}{\NatPair{a}{b}}=a,\qquad \NatProjection{2}{\NatPair{a}{b}}=b.$$
The closed lambda term $\LambdaNumericProjection{i}$ computes this projection on $\ChurchNumeral{z}$.
On a trial input $v=\NatPair{e}{i}$, where $e$ is a word code, expand
$$\begin{aligned}
 \LambdaTermName{seed}_{a}(e)&:=\LambdaListCons\,\ChurchNumeral{\NatPair{a}{0}}\,e,\\
\LambdaTermName{entry}(v)&:= \LambdaListGet\,( \LambdaNumericPair\,( \LambdaNumericProjection{1}v)\,(
\LambdaNumericProjection{2}v)),\\
\LambdaTermName{prev}_{a}(v)&:= \LambdaNumericProjection{1} \bigl( \LambdaListGet\,( \LambdaNumericPair\,
\LambdaTermName{seed}_{a}( \LambdaNumericProjection{1}v)\,( \LambdaNumericProjection{2}v)) \bigr),\\
\LambdaTermName{trial}_{a}&:= \lambdaab{v}{ \LambdaTermName{cert}( \LambdaNumericPair\,
\LambdaTermName{prev}_{a}(v)\, \LambdaTermName{entry}(v))},\\
 \LambdaTermName{desc}_{a}&:=\lambdaab{e}{\LambdaBoundedProduct{\LambdaTermName{trial}_{a}}
   (\LambdaNumericPair\,e\,(\LambdaListLength\,e))}.
\end{aligned}$$
All abbreviations are expanded before abstraction, with fresh binders. Prepending the dummy entry
$\NatPair{a}{0}$ makes the previous element available at the same position as the current entry in the original word.
The dummy certificate is never tested.

\begin{proposition*}[\termdefineas{certified descent tree}{Certified descent tree}]
The closed term $\LambdaTermName{desc}_{a}$ decides membership in $T_a$, and $T_a$ is closed under prefixes.
If no infinite $\prec$-descending chain starts at $a$,
then $T_a$ is well founded and its root rank bounds the $\prec$-rank of $a$. Thus that rank is strictly below the order
type of a recursive well-order presentation. The same assertion holds relative to a fixed input parameter when the
certificate decider uses that parameter.
\end{proposition*}

\begin{proof}[Proof]
List construction, lookup, and projections compute precisely the arguments expected by $\LambdaTermName{cert}$.
The bounded product
runs one trial per entry and returns one exactly when all certificates are accepted; on the empty word it is one.
Every trial terminates. The same tests apply to any prefix, giving closure under prefixes. An infinite branch would
project to an infinite $\prec$-descending chain beginning at $a$, contradicting the hypothesis.

At a node ending at $b$, every $\prec$-predecessor $d$ has some certificate, so the node has a child ending at $d$.
Well-founded induction below the starting number bounds the rank of $b$ by that node's strict-extension rank.
Apply the induction hypothesis at each such child, take successors, and then take their supremum.
This proves the root comparison.
The Kleene--Brouwer construction of §{sec:lambda-kleene-brouwer} gives the strict recursive upper bound.
For the relative assertion, replace the bounded product by its input-query version and pass the same parameter
to $\LambdaTermName{cert}$ in every trial. The tree and rank arguments are unchanged. This proof does not
assert a computable choice
of certificates from true edges.
\end{proof}

For the application to ordinal notations, call $b$ a candidate predecessor of $p$ when either $b>0$ and $p=2^b$,
or $p=3\cdot5^e$ and $P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{b}$ for some $e,n$.
On input $z=\NatPair{p}{\NatPair{b}{\NatPair{e}{\NatPair{n}{s}}}}$, use projections to extract the five fields.
The certificate test accepts exactly when
$$(b>0\text{ and }p=2^b)\quad\text{or}\quad
 (p=3\cdot5^e\text{ and }\LambdaOutputTest\,\ChurchNumeral{e}\,\ChurchNumeral{n}
 \,\ChurchNumeral{b}\,\ChurchNumeral{s}\to_\beta^*\ChurchNumeral{1}).$$
The successor alternative ignores the certificate fields. For the limit alternative, the finite-output-test theorem
proves both soundness and existence of an accepted certificate whenever the indicated numerical output exists.

Here is an explicit term for this test. For numerical terms $\LambdaTermName{left}$, $\LambdaTermName{right}$
representing natural
numbers or decision bits as appropriate, put
$$\begin{aligned}
&\LambdaTermName{parent}(z):=\LambdaNumericProjection{1}z,\\
&\LambdaTermName{child}(z):=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
&\LambdaTermName{index}(z):=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z)),\\
&\LambdaTermName{position}(z):= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(
\LambdaNumericProjection{2}( \LambdaNumericProjection{2}z))),\\
&\LambdaTermName{fuel}(z):= \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(
\LambdaNumericProjection{2}( \LambdaNumericProjection{2}z))),\\
&\LambdaTermName{le}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaLeCase{ \LambdaTermName{left}}{
\LambdaTermName{right}}{ \ChurchNumeral{1}}{
\ChurchNumeral{0}},\\
&\LambdaTermName{eq}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaMul\, \LambdaTermName{le}(
\LambdaTermName{left}, \LambdaTermName{right})\,
\LambdaTermName{le}( \LambdaTermName{right}, \LambdaTermName{left}),\\
&\LambdaTermName{nonzero}( \LambdaTermName{left}):= \LambdaLeCase{ \LambdaTermName{left}}{ \ChurchNumeral{0}}{
\ChurchNumeral{0}}{
\ChurchNumeral{1}},\\
&\LambdaTermName{or}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaLeCase{ \LambdaTermName{left}}{
\ChurchNumeral{0}}{ \LambdaTermName{right}}{
\ChurchNumeral{1}},\\
&\LambdaTermName{powTwo}:=\lambdaab{k}{k(\LambdaMul\,\ChurchNumeral{2})\ChurchNumeral{1}},\\
&\LambdaTermName{succCert}(z):=\LambdaMul\,
 (\LambdaTermName{nonzero}(\LambdaTermName{child}(z)))\,
 (\LambdaTermName{eq}(\LambdaTermName{parent}(z),\LambdaTermName{powTwo}(\LambdaTermName{child}(z)))),\\
&\LambdaTermName{limCert}(z):=\\
&\quad \LambdaMul\,
 (\LambdaTermName{eq}(\LambdaTermName{parent}(z),\LambdaLimitCodeProgram(\LambdaTermName{index}(z))))\,
 (\LambdaOutputCandidate\,(\LambdaTermName{index}(z))\,\\
&\quad (\LambdaTermName{position}(z))\,
   (\LambdaNumericPair\,(\LambdaTermName{child}(z))\,(\LambdaTermName{fuel}(z)))),\\
&\LambdaTermName{cert}:=\lambdaab{z}{\LambdaTermName{or}(\LambdaTermName{succCert}(z),\LambdaTermName{limCert}(z))}.
\end{aligned}$$
All the term bodies are expanded before abstraction. Equality is two numerical
comparisons, conjunction is multiplication, and the last alternative is disjunction of decision bits. Church
iteration computes $2^b$, and §{sec:lambda-recursive-order-programs} supplies the limit-code term. Every component
is total,
so expanding these expressions gives the required closed certificate decider. It checks finite beta evidence;
it neither runs a potentially divergent indexed computation to completion nor decides notation validity.

The starting notation can itself be a numerical input. Let $z= \NatPair{a}{e}$, and let a trial receive $v=
\NatPair{z}{j}$. Using the certificate tester $\LambdaTermName{cert}$
just constructed, put
$$\begin{aligned}
\LambdaTermName{seedAll}(z)&:= \LambdaListCons\,( \LambdaNumericPair\,( \LambdaNumericProjection{1}z)\,
\ChurchNumeral{0})\,( \LambdaNumericProjection{2}z),\\
\LambdaTermName{entryAll}(v)&:= \LambdaListGet\,( \LambdaNumericPair\,( \LambdaNumericProjection{2}(
\LambdaNumericProjection{1}v))\,( \LambdaNumericProjection{2}v)),\\
\LambdaTermName{prevAll}(v)&:= \LambdaNumericProjection{1} \bigl( \LambdaListGet\,( \LambdaNumericPair\,
\LambdaTermName{seedAll}( \LambdaNumericProjection{1}v)\,( \LambdaNumericProjection{2}v)) \bigr),\\
\LambdaTermName{trialAll}&:= \lambdaab{v}{ \LambdaTermName{cert}( \LambdaNumericPair\,
\LambdaTermName{prevAll}(v)\, \LambdaTermName{entryAll}(v))},\\
 \LambdaTermName{descAll}&:=\lambdaab{z}{\LambdaBoundedProduct{\LambdaTermName{trialAll}}
   (\LambdaNumericPair\,z\,(\LambdaListLength\,(\LambdaNumericProjection{2}z)))}.
\end{aligned}$$
Expand the abbreviations with fresh binders. The closed term $\LambdaTermName{descAll}$ decides whether the word coded
by $e$ belongs to the certified descent tree starting at $a$, jointly for all numerical inputs.

\begin{proof}[Proof]
The dummy initial entry stores the starting notation. At trial $j$, the projections and list access
supply the preceding notation and the next certified entry. The certificate test returns the
correct edge bit, and the bounded product checks every entry of the supplied word. Its value on
the empty word is one. All numerical subcomputations terminate for every starting number, so no
notation-validity test is needed. Restricting the starting number to a valid notation is used only
in the separate proof that the resulting Kleene--Brouwer order is well founded.
\end{proof}

\begin{proposition*}[\termdefineas{uniform notation presentation indices}{Uniform notation presentation indices}]
There are a total computable map $a\mapsto \DescentDomainIndex{a}$ and a fixed index $t$ such that the decoded terms
at these indices are closed for every $a$. The program $P_{\DescentDomainIndex{a}}$ decides membership in the coded
certified descent tree starting at $a$, and $P_t$ decides the Kleene--Brouwer comparison of coded
words. If $a\in\KleeneO$, these are domain and relation deciders for the well-order presentation
$W_a$ used in §{sec:edst-borel-rank-layers}. The root has code $0$.
\end{proposition*}

\begin{proof}[Proof]
Fix a named representative of the joint numerical domain tester above, with syntax code $u$,
and a named representative of the numerical Kleene--Brouwer comparison term, with syntax code $t$. Write
$\sigma(u,a)$ for the numerical parameter-index map of §{sec:lambda-index-recursion}, and put
$$\DescentDomainIndex{a}:=\sigma(u,a).$$
Parameter insertion gives a closed program that computes the joint domain test with its first
argument fixed at $a$. The comparison term is independent of the tree. Both representatives
are fixed before any starting number is supplied. The generated domain program terminates on
every node code, even for an invalid notation; validity is needed only for well-foundedness.
\end{proof}

We give the arithmetic predicate needed in §{sec:edst-hyperarithmetic-inclusion} explicitly.
Decode a sequence $q$ into
$$D:=\{b:\NatProjection{1}{q(b)}=1\},\qquad G_b(n):=\NatProjection{2}{q(\NatPair{b}{n})}.$$
The predicate $J_\emptyset(q)$ requires all row entries to be bits, downward closure of $D$ under
certified candidate steps, a zero row at notation $1$, jump rows at successors, and joined rows at
certified limit outputs. Use the certificate predicate $\mathcal C$ of §{sec:lambda-certified-descent}.
Write $\mathcal B(g,e,n,k)$ for the zero-or-one output of $\LambdaQueryOutputCandidate$ with input function $g$
and numerical arguments $e,n,k$, and write $\mathcal E(e,i,b,s)$ for the output of $\LambdaOutputTest$.
Both tests terminate for every input; no indexed computation is run to completion.

Decode $\nu=\NatPair{b}{\NatPair{n}{\NatPair{p}{c}}}$ and
$c=\NatPair{i}{s}$. Define $M(q,\nu,j)$ as the conjunction of the following six tests:
$$\begin{aligned}
&G_b(n)\in\{0,1\};\\
&p\in D,\ \mathcal C(p,\NatPair{b}{c})\ \Longrightarrow\ b\in D;\\
&1\in D\ \Longrightarrow\ G_1(n)=0;\\
&b>0,\ 2^b\in D,\ G_{2^b}(n)=1\ \Longrightarrow\ \mathcal B(G_b,n,n,j)=1;\\
&b>0,\ 2^b\in D,\ \mathcal B(G_b,n,n,c)=1\ \Longrightarrow\ G_{2^b}(n)=1;\\
&3\cdot5^p\in D,\ \mathcal E(p,i,b,s)=1\ \Longrightarrow\ G_{3\cdot5^p}(\NatPair{i}{n})=G_b(n).
\end{aligned}$$
The same field $c$ can serve different roles in different tests: universal quantification over $\nu$
ranges over every quadruple $b,n,p,c$.

\begin{lemma*}[\termdefineas{lambda jump table matrix}{A total matrix for jump tables}]
There is one total closed lambda program deciding $M(q,\nu,j)$ from the paired input encoding below, and
$$J_\emptyset(q)\quad\Longleftrightarrow\quad\forall \nu\,\exists j\ M(q,\nu,j).$$
\end{lemma*}

\begin{proof}[Proof]
\begin{mathmeta}
  \define{JumpTupleBody}
\end{mathmeta}
On input $o=\NamePair{\varepsilon}{\NumberBinding{j}{\NumberBinding{\nu}{q}}}$, use the finite term bodies
$$\begin{aligned}
&\LambdaTermName{table}(o,k):= \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(
\LambdaNumericProjection{2}(ok))),\\
&\JumpTupleBody{o}:= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(o
\ChurchNumeral{0}))),\\
&\LambdaTermName{bound}(o):=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
&\LambdaTermName{domainBit}(o,b):=\LambdaNumericProjection{1}(\LambdaTermName{table}(o,b)),\\
&\LambdaTermName{row}(o,b):= \lambdaab{m}{ \LambdaNumericProjection{2}( \LambdaTermName{table}(o,
\LambdaNumericPair\,b\,m))}.
\end{aligned}$$
Expand these abbreviations and abstract all free variables using fresh binders. They read $q(k)$, the
bound numbers, the domain entry, and the row input function. Further numerical projections of $\JumpTupleBody{o}$
supply the fields $b,n,p,c$. Powers, equality, ordering, and the finite checkers already have total
closed programs. Substituting $\LambdaTermName{row}(o,b)$ into the input position of $\LambdaQueryOutputCandidate$
therefore computes both successor tests, even though the row number depends on the input.

For terms $\LambdaTermName{left}$, $\LambdaTermName{right}$ representing decision bits, use multiplication for
conjunction and the term bodies
$$\begin{aligned}
&\LambdaTermName{not}( \LambdaTermName{left}):= \LambdaZeroTest\, \LambdaTermName{left}\, \ChurchNumeral{1}\,
\ChurchNumeral{0},\\
&\LambdaTermName{orBits}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaTermName{not}( \LambdaMul\,(
\LambdaTermName{not}(
\LambdaTermName{left}))\,( \LambdaTermName{not}( \LambdaTermName{right}))),\\
&\LambdaTermName{implies}(
\LambdaTermName{left}, \LambdaTermName{right}):=
\LambdaTermName{orBits}( \LambdaTermName{not}( \LambdaTermName{left}), \LambdaTermName{right})
\end{aligned}$$
for negation, disjunction, and implication. Combining the six tests gives one closed decision program.
Every component has a finite beta/query derivation on every input, and composition preserves those
outputs. The program ignores $\varepsilon$; no validity test is hidden in it.

If $J_\emptyset(q)$ holds, choose $j$ as a halting certificate when the fourth antecedent holds;
otherwise choose zero. All other clauses follow directly from the table conditions. Conversely, every
quadruple occurs as a decoded $\nu$. The fourth and fifth clauses together say exactly that a successor
bit is one if and only if some finite halting certificate exists. The other clauses recover the remaining
table conditions. This proves the equivalence, so two number quantifiers applied to the total matrix
make $J_\emptyset$ arithmetical.
\end{proof}

For the last output certificate in §{sec:edst-hyperarithmetic-inclusion}, fix $a,e,v$ and use
$o=\NamePair{\varepsilon}{\NamePair{x}{q}}$. Put
$$\begin{aligned}
\LambdaTermName{outTable}(o,k)&:= \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(ok)), \qquad
\LambdaTermName{outInput}(o):= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(o \ChurchNumeral{0})),\\
\LambdaTermName{outRow}(o)&:= \lambdaab{m}{ \LambdaNumericProjection{2}( \LambdaTermName{outTable}(o,
\LambdaNumericPair\, \ChurchNumeral{a}\,m))},\\
\LambdaTermName{outputCert}&:=\lambdaab{o}{\lambdaab{s}{\LambdaQueryOutputCandidate\,(\LambdaTermName{outRow}(o))\,
 \ChurchNumeral{e}\,(\LambdaTermName{outInput}(o))\,(\LambdaNumericPair\,\ChurchNumeral{v}\,s)}}.
\end{aligned}$$
Conjoin its output bit with the test $$\LambdaNumericProjection{1}( \LambdaTermName{outTable}(o,
\ChurchNumeral{a}))=1$$ for domain membership.
The same substitution and query equations show that this is a total checker for a finite computation
of $P_e$ on $x(0)$ with input function $G_a$ and output $v$. Existentially quantify its numerical
certificate, intersect with the table predicate, and project out $q$. This supplies the recursive pair
trees for both answers in the theorem.

Let $G_b$ be the rows of a jump witness table with domain $D$. Use the closed certificate decider
$\LambdaTermName{cert}$
from §{sec:lambda-certified-descent}. A certificate has numerical code
$$z=\NatPair{p}{\NatPair{b}{\NatPair{e}{\NatPair{i}{s}}}}.$$
Write $\chi(z),\delta(z),\zeta(z)$ for the corresponding numerical projections. An accepted certificate describes
an edge from $\delta(z)$ up to $\chi(z)$. Fix the pure numerical program $F$ and its function $f$ from
§{sec:lambda-relative-jump}, so that $f(m)\in K^\varepsilon$ exactly when $\varepsilon(m)\ne0$.
Define the address change
$$\tau(z,m):=\begin{cases}
f(m)&\chi(z)=2^{\delta(z)},\\
\NatPair{\zeta(z)}{m}&\chi(z)\ne2^{\delta(z)}.
\end{cases}$$
It is total even on rejected certificates. On an accepted certificate whose upper endpoint belongs to $D$,
$$G_{\chi(z)}(\tau(z,m))=G_{\delta(z)}(m).$$
For the successor case, the jump equation and the bit-valued rows prove this identity. For the limit case,
the finite output certificate and the join equation prove it. The two numerical forms are disjoint.

Here are explicit terms for composing these changes. Let
$\LambdaTermName{powTwo}$ be the closed term computing $b\mapsto2^b$ used in the certificate decider. Inside a term with
argument $w$, abbreviate
$$\begin{aligned}
&\LambdaTermName{U}(w):=\LambdaTermName{parent}(\LambdaNumericProjection{1}w),\\
&\LambdaTermName{S}(w):=\LambdaTermName{powTwo}(\LambdaTermName{child}(\LambdaNumericProjection{1}w)),\\
&\LambdaTermName{J}(w):=F(\LambdaNumericProjection{2}w),\\
&\LambdaTermName{I}(w):=\LambdaNumericPair\,
 (\LambdaTermName{position}(\LambdaNumericProjection{1}w))\,(\LambdaNumericProjection{2}w),\\
&\LambdaTermName{edgeAddr}:= \lambdaab{w}{ \LambdaLeCase{ \LambdaTermName{U}(w)}{
\LambdaTermName{S}(w)}{
\LambdaLeCase{ \LambdaTermName{S}(w)}{ \LambdaTermName{U}(w)}{
\LambdaTermName{J}(w)}{ \LambdaTermName{I}(w)}}{ \LambdaTermName{I}(w)}}.
\end{aligned}$$
The field expressions stand for compositions of numerical projection terms. Expand them before abstraction.
The two comparisons in $\LambdaTermName{edgeAddr}$ test equality, so $\LambdaTermName{edgeAddr}$ computes
$\tau(z,m)$ on input $\NatPair{z}{m}$.

For any closed total numerical term $H$ receiving $\NatPair{r}{z}$, define a list accumulator by
$$\begin{aligned}
\LambdaTermName{foldBase}&:=\lambdaab{w}{\LambdaNumericProjection{2}w},\\
\LambdaTermName{foldStep}_{H}&:=\lambdaab{w}{\lambdaab{j}{\lambdaab{r}{
 H(\LambdaNumericPair\,r\,(\LambdaListGet\,(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,j)))}}},\\
\LambdaTermName{fold}_{H}&:= \lambdaab{w}{ \LambdaParamRec{ \LambdaTermName{foldBase}}{
\LambdaTermName{foldStep}_{H}}\,w\,( \LambdaListLength\,( \LambdaNumericProjection{1}w))}.
\end{aligned}$$
Let $\mathbf{z}$ be a word of length $k$, with $j$-th entry $z_j$ for $j<k$.
On input $\NatPair{\LambdaListCode{\mathbf{z}}}{m}$, this starts with $r_0=m$ and applies
$H$ successively to $\NatPair{r_j}{z_j}$ for $j<k$. The empty list returns $m$.
Numerical currying and uncurrying give the same recursion on paired inputs.
With $H:= \lambdaab{w}{ \LambdaTermName{edgeAddr}( \LambdaNumericPair\,( \LambdaNumericProjection{2}w)\,(
\LambdaNumericProjection{1}w))}$, let $\LambdaTermName{addr}:= \LambdaTermName{fold}_{H}$.
Let $\mathcal A(c,m)$ be the final address obtained by decoding $c$ as a finite word and starting at $m$,
then replacing the current address $r$ by $\tau(z_j,r)$ at each entry $z_j$.
The term $\LambdaTermName{addr}$ computes $\mathcal A(c,m)$ on the paired numerical input $\NatPair{c}{m}$.

We must also find the paths uniformly. Scan a candidate list starting with state $\NatPair{1}{b}$.
The state consists of an acceptance bit and the current endpoint. On input $w=\NatPair{r}{z}$,
the projections of $r$ give the acceptance bit and the current endpoint. Expand
$$\begin{aligned}
&\LambdaTermName{acceptStep}(w):=\\
&\quad \LambdaMul\,
\bigl(\LambdaMul\,(\LambdaEqual\,(\LambdaNumericProjection{1}(\LambdaNumericProjection{1}w))\,\ChurchNumeral{1})
( \LambdaEqual\,( \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(
\LambdaNumericProjection{2}w)))\,\\
&\quad ( \LambdaNumericProjection{2}( \LambdaNumericProjection{1}w))) \bigr)\,(
\LambdaTermName{cert}( \LambdaNumericProjection{2}w)),\\
&\LambdaTermName{pathStep}:= \lambdaab{w}{ \LambdaNumericPair\, \LambdaTermName{acceptStep}(w)\,(
\LambdaNumericProjection{1}( \LambdaNumericProjection{2}w))}.
\end{aligned}$$
A rejected edge or a mismatched lower endpoint sets the bit to zero, and it stays zero thereafter.
The numerical test $\Theta$ on input $\NatPair{\NatPair{b}{a}}{c}$ compares
$\LambdaTermName{fold}_{ \LambdaTermName{pathStep}} \ChurchNumeral{ \NatPair{c}{ \NatPair{1}{b}}}$ with
$\ChurchNumeral{ \NatPair{1}{a}}$ using numerical equality.
It returns one exactly when the decoded list is an accepted path from $b$ to $a$. The empty path is accepted
exactly when $b=a$. Projections, pairing, the list accumulator, and equality give a closed total term for $\Theta$.

Suppose a closed numerical term $\LambdaTermName{baseProg}$ computes $g$ and every $g(n)$ has a finite accepted
path to a fixed $a$.
Define, with fresh binders,
$$\begin{aligned}
\LambdaTermName{pathTrial}&:=\lambdaab{w}{\Theta(\LambdaNumericPair\,
( \LambdaNumericPair\,( \LambdaTermName{baseProg}( \LambdaNumericProjection{1}w))\, \ChurchNumeral{a})\,(
\LambdaNumericProjection{2}w))},\\
\LambdaTermName{reject}&:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
\LambdaTermName{findPath}&:=\lambdaab{n}{\LambdaResultSearch\,
 (\lambdaab{k}{\LambdaTermName{reject}(\LambdaTermName{pathTrial}(\LambdaNumericPair\,n\,k))})\,(\lambdaab{j}{j})},\\
\LambdaTermName{readRow}&:= \lambdaab{o}{ \lambdaab{w}{o( \LambdaTermName{addr}( \LambdaNumericPair\,(
\LambdaTermName{findPath}( \LambdaNumericProjection{1}w))\,( \LambdaNumericProjection{2}w)))}}.
\end{aligned}$$
The search $\LambdaTermName{findPath}$ returns the least accepted list code, not merely an acceptance bit.

\begin{proposition*}[\termdefineas{lambda uniform jump-row reader}{A uniform jump-row reader}]
The terms $\LambdaTermName{addr}$ and $\Theta$ are total numerical programs. Under the path-existence
hypothesis, $\LambdaTermName{findPath}$ is total
as well. For every jump witness table with $a \in D$, the closed term $\LambdaTermName{readRow}$, supplied with
the input function
$G_a$, returns $G_{g(n)}(m)$ on input $\NatPair{n}{m}$. Its only query to that input function is at the final
address computed by $\LambdaTermName{addr}$.
\end{proposition*}

\begin{proof}[Proof]
The numerical recursor theorem proves the accumulator formula by induction on the number of processed
entries. Applied to $\LambdaTermName{pathStep}$, induction shows that the final state is $\NatPair{1}{a}$
exactly for an accepted
path with the prescribed endpoints: each update checks the edge and its connection to the preceding
endpoint. Once the bit is zero it cannot return to one. This proves the specification of $\Theta$.
Every trial of $\LambdaTermName{pathTrial}$ terminates. The assumed path has a finite code, so parameterized
numerical search
returns the least successful code. Thus $\LambdaTermName{findPath}$ is one total program on all $n$.

For the address identity, induct on the path by removing its last edge. Downward closure puts the
preceding endpoint in $D$. The single-edge identity followed by the induction hypothesis gives
$G_a(\mathcal A(c,m))=G_{g(n)}(m)$ for every accepted code $c$ found by $\LambdaTermName{findPath}$.
The terms computing the path and address terminate before the query in $\LambdaTermName{readRow}$, so their finite beta
reductions followed by one input-query step give the required output. No choice of a separate reader
for each $n$ occurs. Taking the canonical table gives the iterated-jump reader in
§{sec:edst-hyperarithmetic-inclusion}.
\end{proof}

For a recursion through many stages, the upper endpoint must also be an input. Use the same total
path checker $\Theta$, address accumulator $\LambdaTermName{addr}$, and zero-reversing term
$\LambdaTermName{reject}$ as above, and put
$$\begin{aligned}
\LambdaTermName{findEnds}&:=\lambdaab{v}{\LambdaResultSearch\,
 (\lambdaab{k}{\LambdaTermName{reject}(\Theta(\LambdaNumericPair\,v\,k))})\,(\lambdaab{j}{j})},\\
\LambdaTermName{readEnds}&:=\lambdaab{o}{\lambdaab{w}{
o( \LambdaTermName{addr}( \LambdaNumericPair\,( \LambdaTermName{findEnds}( \LambdaNumericProjection{1}w))\,(
\LambdaNumericProjection{2}w)))}}.
\end{aligned}$$
Thus $\LambdaTermName{findEnds}$ searches for a path with the two endpoints supplied as $v$. For input
$w= \NatPair{ \NatPair{b}{a}}{m}$, the term $\LambdaTermName{readEnds}$ receives $\ChurchNumeral{w}$, computes
the path, changes the address,
and queries the supplied upper row once. No termination claim is made when a path does not exist.

\begin{proposition*}[\termdefineas{computed jump-row reader indices}{Computed jump-row reader indices}]
There is a single total numerical map $\Tuple{e,h,a}\mapsto \psi(e,h,a)$, computed by a closed term, with the following
property. Suppose $e,h$ decode to closed terms computing the total functions $\upsilon(a)$ and $\ell(a,n)$, the latter
on paired input. For any jump witness table with domain $D$ and rows $G_b$, if $\upsilon(a)\in D$ and each $\ell(a,n)$
has a finite accepted path to $\upsilon(a)$, then the output code is closed and $P_{\psi(e,h,a)}$, with input function
$G_{\upsilon(a)}$, returns $G_{\ell(a,n)}(m)$ on input $\NatPair{n}{m}$. The map generating the index is total on all
triples, including inputs that fail these hypotheses.
\end{proposition*}

\begin{proof}[Proof]
Set $\LambdaTermName{upperProg}=P_e$ and $\LambdaTermName{lowerProg}=P_h$. Projections and numerical pairing
give a closed total term $\LambdaTermName{readerInput}$ for the change of input
$$\NatPair{a}{\NatPair{n}{m}}\longmapsto
  \NatPair{\NatPair{\ell(a,n)}{\upsilon(a)}}{m}.$$
With the abbreviations expanded before abstraction, take
$$\begin{aligned}
\LambdaTermName{lowerInput}(w)&:= \LambdaTermName{lowerProg}( \LambdaNumericPair\,(
\LambdaNumericProjection{1}w)\,( \LambdaNumericProjection{1}( \LambdaNumericProjection{2}w))),\\
\LambdaTermName{endpoints}(w)&:= \LambdaNumericPair\, \LambdaTermName{lowerInput}(w)\,(
\LambdaTermName{upperProg}( \LambdaNumericProjection{1}w)),\\
\LambdaTermName{readerInput}&:= \lambdaab{w}{ \LambdaNumericPair\, \LambdaTermName{endpoints}(w)\,(
\LambdaNumericProjection{2}( \LambdaNumericProjection{2}w))}.
\end{aligned}$$
Form the closed term
$$\LambdaTermName{varyReader}:=\lambdaab{o}{\lambdaab{w}{\LambdaTermName{readEnds}o(\LambdaTermName{readerInput}w)}}$$
and specialize its first numerical component:
$$P_{\psi(e,h,a)}=\lambdaab{o}{\lambdaab{z}{\LambdaTermName{varyReader}o(\LambdaNumericPair\,\ChurchNumeral{a}\,z)}}.$$
To compute its code uniformly, first replace $\LambdaTermName{upperProg}$, $\LambdaTermName{lowerProg}$ by two
fresh free variables in the expression for $\LambdaTermName{varyReader}$.
Fix one named representative of that expression. The two-input substitution construction in
§{sec:lambda-code-substitution} computes a code $\rho(e,h)$ of $\LambdaTermName{varyReader}$ from the supplied
syntax codes.
Now use the joint specialization map $\kappa$ from §{sec:lambda-pair-tree-programs} and put
$$\psi(e,h,a):=\kappa(\rho(e,h),a).$$
All fixed representatives are chosen before $e,h$ are supplied. Both code transformations terminate without
running $\LambdaTermName{upperProg}$, $\LambdaTermName{lowerProg}$, $\LambdaTermName{varyReader}$ or searching
for a path.

For correctness, every trial of $\LambdaTermName{findEnds}$ terminates because $\Theta$ is total. An accepted
path has a finite
list code, so least-success search terminates at each required pair of endpoints. The address-accumulator
identity then gives $G_{\upsilon(a)}(\mathcal A(c,m))=G_{\ell(a,n)}(m)$ for the selected code $c$.
Two specialization contractions, pairing, and the computation of $\LambdaTermName{readerInput}$ reduce to that
same reader run.
Thus a single total code-producing term works for all stages, although the programs it produces need
only terminate at stages satisfying the stated hypotheses.
\end{proof}

\begin{lemma*}[\termdefineas{uniform predecessor-notation indices}{Uniform predecessor-notation indices}]
There is a total computable map $\Tuple{d,r,e,k}\mapsto \mu(d,r,e,k)$ with the following property.
Let $W=\Pair{D}{R}$ be a recursive well-order presentation. Suppose $d,r,e$ are syntax codes of closed terms,
the first two deciding membership in $D$ and the relation $R$ with bits one and zero, and the third computing
a total numerical function $g$. Then $\mu(d,r,e,k)$ codes a closed term computing, on paired input,
$$\ell_k(a,b):=\begin{cases}
\KleeneSuccIter{g(b)}{k}&b\in D,\ bRa,\\
1&b\notin D\lor\neg(bRa).
\end{cases}$$
The code-producing map is total on every quadruple, independently of these hypotheses.
\end{lemma*}

\begin{proof}[Proof]
Use numerical projections to read $k,a,b$ from $\NatPair{k}{\NatPair{a}{b}}$.
The finite successor-iteration term from §{sec:lambda-recursive-order-programs} computes
$\KleeneSuccIter{g(b)}{k}$ from the output of the third program and the first projection.
Apply the numerical conditional twice: if the domain bit is at most zero, return one; otherwise, if the
relation bit is at most zero, return one; otherwise return that successor iterate. All component computations
terminate under the hypotheses, and the two bit tests give exactly the displayed cases.

Build this composite term using three fresh free variables in place of the domain, relation, and upper-notation
programs, and fix a named representative once. Three successive capture-avoiding substitutions from
§{sec:lambda-code-substitution} compute its code $\eta(d,r,e)$. Each substitution receives the code produced by
the preceding substitution. The numerical parameter construction in §{sec:lambda-index-recursion} now gives
$$\mu(d,r,e,k):=\sigma(\eta(d,r,e),k).$$
This fixes the first component of the input and leaves the pair of stage and predecessor as the argument.
Closed input programs give a closed output program. Substitution and parameter insertion do not execute the
supplied programs, so code generation terminates even when a decision or totality hypothesis fails.
\end{proof}

### Self-indexed rank decision programs {#sec:lambda-rank-decision-programs}

\begin{mathmeta}
  \vars{a,b,k,q,s,t,z}{Nat}
\end{mathmeta}

We first separate the total production of program indices from execution of the programs. For a fixed
closed relative program $T$, define the two specializations
$$\begin{aligned}
T_q&:=\lambdaab{o}{\lambdaab{z}{To(\LambdaNumericPair\,\ChurchNumeral{q}\,z)}},\\
T_{q,a}&:=\lambdaab{o}{\lambdaab{z}{T_qo(\LambdaNumericPair\,\ChurchNumeral{a}\,z)}}.
\end{aligned}$$
Thus $T_{q,a}$ receives $z$ by passing the code $\NatPair{q}{\NatPair{a}{z}}$ to $T$.
The syntax constructors compute the code $c(q,a)$ of $T_{q,a}$ jointly in $q,a$. In the specialization
code recipe, the program-code input may itself be the result of the first specialization; application,
abstraction, and numeral-code construction are total numerical operations.

\begin{proposition*}[\termdefineas{self-indexed quantified families}{Self-indexed quantified families}]
There are total computable maps $u\mapsto q(u)$ and $\Pair{u}{a}\mapsto d(u,a)$ such that, for every $u$,
$P_{q(u)}$ computes $a\mapsto d(u,a)$. Suppose $u$ is the syntax code of a closed relative program
$T=P_u$. If $T_{q(u),a}$ decides $M(s,t,b)$ on input $\NatPair{\NatPair{s}{t}}{b}$ relative to
$\varepsilon$, then $P_{d(u,a)}$ decides $\forall t\,\exists b\,M(s,t,b)$ relative to $(\varepsilon')'$.
The numerical maps and the computation of each index family are total without a termination assumption on
the specialized programs.
\end{proposition*}

\begin{proof}[Proof]
Choose the joint specialization map $\kappa$ from §{sec:lambda-pair-tree-programs} once, and put
$$c(u,v,a):=\kappa(\kappa(u,v),a),\qquad
 f(u,z):=\upsilon\bigl(\xi(c(u,p_1(z),p_2(z)))\bigr).$$
Here $p_1,p_2$ are the numerical projections and the quantifier-index maps are fixed. Composition gives one
closed numerical term computing $f$ on paired input; fix a named representative with syntax code $h$.
The numerical parameter construction in §{sec:lambda-index-recursion} computes
$$v(u):=p(h,u),$$
so that $P_{v(u)}$ computes $z\mapsto f(u,z)$ for every numerical input $u$.
Let $\tau$ be the uniform self-indexed numerical-family map from the same section. Define
$$q(u):=\tau(v(u)),\qquad d(u,a):=f\bigl(u,\NatPair{q(u)}{a}\bigr).$$
The self-indexed family theorem proves that $P_{q(u)}$ computes the displayed value for every stage.
Both maps are total compositions of numerical code constructors. If the input syntax is closed, two
specializations identify $P_{c(u,q(u),a)}$ with $T_{q(u),a}$. Applying the two quantifier-index transformations
then proves the decision assertion relative to the second jump of the supplied input function. All fixed representatives
are chosen before
the template code is supplied, and no specialized program is executed while generating an index.
\end{proof}

\begin{corollary*}[\termdefineas{self-indexed universal families}{Self-indexed universal families}]
There are total computable maps $u\mapsto q(u)$ and $\Pair{u}{a}\mapsto r(u,a)$ such that, for every $u$,
$P_{q(u)}$ computes $a\mapsto r(u,a)$. If $u$ codes a closed relative program $T=P_u$ and
$T_{q(u),a}$ decides $M(s,b)$ on input $\NatPair{s}{b}$ at $\varepsilon$, then $P_{r(u,a)}$ decides
$\forall b\,M(s,b)$ at $\varepsilon'$.
\end{corollary*}

\begin{proof}[Proof]
Use the preceding construction with
$$f(u,z):=\upsilon(c(u,p_1(z),p_2(z))),\qquad
 r(u,a):=f\bigl(u,\NatPair{q(u)}{a}\bigr).$$
Omitting the existential-quantifier transformation leaves the same total code construction and self-reference
reductions. One application of the universal-quantifier compiler proves the decision assertion at one jump.
\end{proof}

For a fixed closed template $T$, choose one named representative with code $u$.
Specializing either construction to this code gives a total index family computed by $P_{q(u)}$.
Thus the same construction supplies the fixed-template families used below.

Here is the fixed template used for rank decisions. Let $\mathcal E$ decide $E(t,s)$ on
$\NatPair{t}{s}$, let $K$ decide $b\in D$ and $bRa$ on $\NatPair{b}{a}$, and let $I$ compute the
reader index $i(a)$. These are pure closed numerical terms. Decode the argument $w$ as
$\NatPair{q}{\NatPair{a}{\NatPair{\NatPair{s}{t}}{b}}}$ by numerical projections, and abbreviate
$$\begin{aligned}
C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
D(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,(\LambdaOutputSearch\,q\,b)\,t,\\
J(w)&:=K(\LambdaNumericPair\,b\,a),\\
V(o,w)&:=\LambdaZeroTest\,J(w)\,\ChurchNumeral{0}\,D(o,w),\\
T&:=\lambdaab{o}{\lambdaab{w}{\LambdaZeroTest\,
 (\mathcal E(\LambdaNumericPair\,t\,s))\,\ChurchNumeral{1}\,V(o,w)}}.
\end{aligned}$$
Expand the field projections and abbreviations before abstraction, using a fresh binder $k$.
This makes $T$ a single closed lambda term.

\begin{lemma*}[\termdefineas{guarded lower-rank evaluation}{Guarded lower-rank evaluation}]
Suppose $P_q$ computes a total index function $d$, and fix $a$ and an upper input function $\varepsilon$.
Assume that for every $b\in D$ with $bRa$, the reader at $a$ computes a lower input function
$\eta_b$, and $P_{d(b)}$ at $\eta_b$ decides a predicate $L(b,t)$.
Then the displayed $T_{q,a}$ is total at $\varepsilon$ and decides
$$\neg E(t,s)\ \lor\ \bigl(b\in D\land bRa\land L(b,t)\bigr).$$
\end{lemma*}

\begin{proof}[Proof]
If the edge test returns zero, the outer zero test returns one without evaluating $V$. If it returns
one but the predecessor test returns zero, the inner zero test returns zero without evaluating $D$.
In the remaining case, pure universal evaluation of $P_q$ on $b$ supplies $d(b)$. For each queried
numeral $k$, universal evaluation in $C$ simulates $P_{i(a)}$ on $\NatPair{b}{k}$ and returns
$\eta_b(k)$. Substitute these finite computations for the queries in the lower decision program.
The input-substitution theorem then gives the same output bit as $P_{d(b)}$ on $t$ at $\eta_b$.
All calls in this case terminate by the hypotheses. This proves both totality and the matrix formula;
no behavior at a nonpredecessor is needed. Two pair-specializations pass $q,a$ to the same term, so
the conclusion holds for the compiled matrix code as well.
\end{proof}

## Effective Tree Operations and Borel Codes {#sec:lambda-effective-borel-programs}

### Finite Tests and Branches of Trees {#sec:lambda-kleene-brouwer}

\begin{mathmeta}
  \vars{a,b,e,i,j,n,v,w,z}{Nat}
  \vars{s,t}{Seq(Nat)}
  \vars{p,q,\varepsilon}{Name}
  \vars{f}{Fun(Nat,Nat)}
\end{mathmeta}

The comparison places the empty word last; for two nonempty words it compares their heads and, when
they agree, their tails. In particular, a proper extension precedes its prefix. Use the list code,
field programs, and list recursor already defined in this appendix. Put
$$\begin{aligned}
&\LambdaTermName{kbZero}:=\lambdaab{e}{\ChurchNumeral{0}},\\
&\LambdaTermName{kbHead}(e):=\LambdaListField{1}e,\\
&\LambdaTermName{kbTail}(e):=\LambdaListField{2}e,\\
&\LambdaTermName{kbTailCase}(a, \LambdaTermName{compare},e):= \LambdaLeCase{ \LambdaTermName{kbHead}(e)}{a}{
\LambdaTermName{compare}( \LambdaTermName{kbTail}(e))}{ \ChurchNumeral{1}},\\
&\LambdaTermName{kbCase}(a,\LambdaTermName{compare},e):=\\
&\quad \LambdaLeCase{e}{\ChurchNumeral{0}}{\ChurchNumeral{1}}{
 \LambdaLeCase{a}{ \LambdaTermName{kbHead}(e)}{ \LambdaTermName{kbTailCase}(a, \LambdaTermName{compare},e)}{
\ChurchNumeral{0}}},\\
&\LambdaTermName{kbStep}:= \lambdaab{a}{ \lambdaab{ \LambdaTermName{compare}}{ \lambdaab{e}{
\LambdaTermName{kbCase}(a, \LambdaTermName{compare},e)}}}.
\end{aligned}$$
Expand these abbreviations with distinct fresh binders. The value passed as $\LambdaTermName{compare}$ compares
the tail of
the first word with its argument. The zero branch returns one without inspecting the empty second word.

\begin{mathmeta}
  \define{LambdaKleeneBrouwer}
\end{mathmeta}
Define the closed binary comparison term by
$$\LambdaKleeneBrouwer:=\LambdaListFold{\LambdaTermName{kbZero}}{\LambdaTermName{kbStep}}.$$
A numerical-pair wrapper supplies its two arguments when a unary decision program is required.

\begin{lemma*}[\termdefineas{Kleene--Brouwer comparison program}{Kleene--Brouwer comparison program}]
For all finite words $s,t$,
$$\LambdaKleeneBrouwer\,\ChurchNumeral{\LambdaListCode{s}}\,
 \ChurchNumeral{\LambdaListCode{t}}
 \to_\beta^*
 \begin{cases}
 \ChurchNumeral{1},&\kleeneBrouwerOrder{s}{t},\\
 \ChurchNumeral{0},&\text{otherwise}.
 \end{cases}$$
Thus comparison terminates on every pair of list codes, with no input queries.
\end{lemma*}

\begin{proof}[Proof]
Define closed function values $\LambdaTermName{compare}_{[]}:= \LambdaTermName{kbZero}$ and
$\LambdaTermName{compare}_{a::s}:= \LambdaTermName{kbStep} \ChurchNumeral{a} \LambdaTermName{compare}_s$. The
list-recursion
formula reduces the first application to $\LambdaTermName{compare}_s$. Induct on $s$ to prove the claimed behavior of
$\LambdaTermName{compare}_s$ on every second word. For the empty first word, $\LambdaTermName{kbZero}$ always
returns zero. For $a::s$, three beta
contractions expose $\LambdaTermName{kbCase}$. If the second word is empty, its code is zero and the outer test
returns one.
If it is $b::t$, the two field computations return $\ChurchNumeral{b}$ and $\ChurchNumeral{
\LambdaListCode{t}}$. The two numerical
comparisons return one when $a<b$, zero when $a>b$, and the value of $\LambdaTermName{compare}_s$ on
$\ChurchNumeral{ \LambdaListCode{t}}$ when $a=b$.
The induction hypothesis supplies that last value. These are exactly the defining comparison clauses.
The recursor and handler are closed, and all reductions used here are finite beta reductions.
\end{proof}

Fix a parameter $\varepsilon$. Suppose $P$ decides $\mathcal R_i(s,t)$ on the numerical input
$\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
Define $S_i$ to consist of the equal-length pairs $\Pair{s}{t}$ for which
$\mathcal R_i(\restrict{s}{j},\restrict{t}{j})$ holds for every $j\le\Length{s}$.
Use the truncation body $\LambdaTermName{truncatePair}$, length terms $\LambdaTermName{firstLength}$,
$\LambdaTermName{secondLength}$, and equality bit $\LambdaTermName{sameLength}$ of
§{sec:lambda-pair-tree-programs}, now with $z=\NatPair{i}{w}$ as the family input. For a trial input $v$,
expand the abbreviations
$$\begin{aligned}
&\LambdaTermName{trialData}(v):= \LambdaNumericProjection{1}v,\\
&\LambdaTermName{trialLength}(v):=
\LambdaNumericProjection{2}v,\\
&\LambdaTermName{familyIndex}(v):= \LambdaNumericProjection{1} \LambdaTermName{trialData}(v),\\
&\LambdaTermName{nodeCode}(v):= \LambdaNumericProjection{2} \LambdaTermName{trialData}(v),\\
&\LambdaTermName{prefixTest}_P:=\\
&\quad \lambdaab{o}{\lambdaab{v}{\begin{aligned}[t]
&Po( \LambdaNumericPair\,
\LambdaTermName{familyIndex}(v)\, \LambdaTermName{truncatePair}( \LambdaTermName{nodeCode}(v),\\
&\quad \LambdaTermName{trialLength}(v)))
\end{aligned}}},\\
&\LambdaTermName{finiteTree}_P:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaMul\,\LambdaTermName{sameLength}(z)\,
 \bigl( \LambdaRelativeProduct{ \LambdaTermName{prefixTest}_P}\,o\,( \LambdaNumericPair\,z\,( \LambdaSucc\,\\
&\quad \LambdaTermName{firstLength}(z))) \bigr)
\end{aligned}}}.
\end{aligned}$$
Choose distinct fresh binders and expand all abbreviations before abstraction.

\begin{lemma*}[\termdefineas{finite-test tree decision program}{Decision programs for finite-test trees}]
The closed program $\LambdaTermName{finiteTree}_P$ decides membership in $S_i$, uniformly in the index and node,
relative to
$\varepsilon$. The number of trials is $\Length{s}+1$, including the empty prefix.
\end{lemma*}

\begin{proof}[Proof]
Numerical projections and $\LambdaTermName{truncatePair}$ turn the trial input into exactly the code expected by
$P$ for the two
length-$j$ prefixes. Every call terminates and returns a decision bit. The bounded-product theorem multiplies
these bits for $j<\Length{s}+1$, retaining the same parameter at every stage. Its result is one exactly when all
prefix tests pass. Multiplication by $\LambdaTermName{sameLength}(z)$ also requires equal lengths. On empty
words there is one trial,
so its failure rejects the empty node. Treating the index as ordinary input data proves uniformity; fixing
that input gives the single-predicate construction.
\end{proof}

For the coordinatewise inverse image, let $F$ compute the total numerical function $f$ and let $Q$ decide
membership in $V$. Define
$$\begin{aligned}
\LambdaTermName{mapWord}_F&:=\LambdaListMap\,F,\\
\LambdaTermName{mapNode}_F&:=\lambdaab{w}{\LambdaNumericPair\,
 \bigl(\LambdaTermName{mapWord}_F(\LambdaNumericProjection{1}w)\bigr)\,(\LambdaNumericProjection{2}w)},\\
\LambdaTermName{preimage}_{Q,F}&:=\lambdaab{o}{\lambdaab{w}{Qo(\LambdaTermName{mapNode}_Fw)}}.
\end{aligned}$$
The list-map theorem gives exactly the code of the entrywise image of the first word. Pairing leaves the
second word unchanged, and two beta contractions feed this code to $Q$ at the original parameter. Thus
$\LambdaTermName{preimage}_{Q,F}$ decides the tree used in §{sec:edst-finite-check-trees}.

A finite prefix of a tree code need not contain every digit needed to test a candidate branch prefix.
We therefore test a digit only when it is available. For finite words $s,t$, define
$$\begin{aligned}
\mathcal D(s,t)\quad\Longleftrightarrow\quad
&\forall j\ (0<j\le\Length{t}\ \Longrightarrow\\
&\quad[\LambdaListCode{\restrict{t}{j}}<\Length{s}\ \Longrightarrow\ s(\LambdaListCode{\restrict{t}{j}})\ne0]).
\end{aligned}$$
The input is $w=\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}$.
The following abbreviations build the test from total numerical programs:
$$\begin{aligned}
&\LambdaTermName{treeWord}(w):= \LambdaNumericProjection{1}w,\\
&\LambdaTermName{branchWord}(w):=
\LambdaNumericProjection{2}w,\\
&\LambdaTermName{trialData}(v):= \LambdaNumericProjection{1}v,\\
&\LambdaTermName{trialLength}(v):=
\LambdaNumericProjection{2}v,\\
&\LambdaTermName{prefixCode}(v):= \LambdaListTake( \LambdaNumericPair\, \LambdaTermName{branchWord}(
\LambdaTermName{trialData}(v))\, \LambdaTermName{trialLength}(v)),\\
&\LambdaTermName{treeDigit}(v):= \LambdaListGet( \LambdaNumericPair\, \LambdaTermName{treeWord}(
\LambdaTermName{trialData}(v))\, \LambdaTermName{prefixCode}(v)).
\end{aligned}$$
Here the list-take program returns the code of the prefix, so its result is also the address of the digit to inspect.

For terms returning Church numerals, use the comparison and nonzero tests
$$\begin{aligned}
\LambdaTermName{less}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{ \LambdaSucc\,
\LambdaTermName{left}}{ \LambdaTermName{right}}{ \ChurchNumeral{1}}{ \ChurchNumeral{0}},\\
\LambdaTermName{nonzero}( \LambdaTermName{left})&:= \LambdaLeCase{ \LambdaTermName{left}}{ \ChurchNumeral{0}}{
\ChurchNumeral{0}}{ \ChurchNumeral{1}},\\
\LambdaTermName{implies}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{
\LambdaTermName{left}}{ \ChurchNumeral{0}}{ \ChurchNumeral{1}}{ \LambdaTermName{right}}.
\end{aligned}$$
On decision bits, the last term is implication. Define
$$\begin{aligned}
&\LambdaTermName{availableDigit}(v):=\\
&\quad \LambdaMul\, \LambdaTermName{less}( \ChurchNumeral{0},
\LambdaTermName{trialLength}(v))\, \LambdaTermName{less}( \LambdaTermName{prefixCode}(v), \LambdaListLength\,
\LambdaTermName{treeWord}(\\
&\quad \LambdaTermName{trialData}(v))),\\
&\LambdaTermName{branchTrial}:= \lambdaab{o}{ \lambdaab{v}{ \LambdaTermName{implies}(
\LambdaTermName{availableDigit}(v), \LambdaTermName{nonzero}( \LambdaTermName{treeDigit}(v)))}},\\
&\LambdaTermName{branchTest}:=\\
&\quad \lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{\LambdaTermName{branchTrial}}\,o\,
 (\LambdaNumericPair\,w\,(\LambdaSucc(\LambdaListLength\,\LambdaTermName{branchWord}(w))))}}.
\end{aligned}$$
Expand the abbreviations and choose distinct fresh binders. The argument $o$ is retained for the relative-program
interface; the digit being checked comes from the finite word, not from a query to that parameter.

\begin{lemma*}[\termdefineas{delayed branch decision program}{Delayed branch decision program}]
The closed program $\LambdaTermName{branchTest}$ terminates on every pair of word codes and returns one exactly
when $\mathcal D(s,t)$ holds.
Applying the finite-test construction of §{sec:lambda-kleene-brouwer} gives a recursive pair tree $\mathcal U$
whose nodes are the equal-length pairs passing this test at every common prefix.
\end{lemma*}

\begin{proof}[Proof]
On trial $j$, the list programs return the prefix code and the digit at that address. The guard is one exactly
when $j>0$ and the address is smaller than $\Length{s}$. Implication therefore accepts the trial when its guard is zero,
and otherwise requires a nonzero digit. Each component terminates even when the address is outside the word,
since list lookup then returns zero. The bounded product runs the $\Length{t}+1$ trials, including zero, and returns
one exactly when they all succeed. The finite-test construction checks all common prefixes and equal lengths,
so its accepted pairs are downward closed. Every composition and bounded iteration retains the original
parameter, and the component computations are finite beta reductions.
\end{proof}

This tree has the precise branch property needed in §{sec:edst-boundedness}. With
$$T_p:=\{t:\forall j\ (0<j\le\Length{t}\ \Longrightarrow\ p(\LambdaListCode{\restrict{t}{j}})\ne0)\},$$
one has $$\Pair{p}{q}\in[\mathcal U]\quad\Longleftrightarrow\quad q\in[T_p].$$
Every required digit is eventually tested: for $j>0$, choose
$n\ge\max\{j,\LambdaListCode{\restrict{q}{j}}+1\}$. Conversely, a branch of the coded tree passes each finite test.
Also, for the section $\mathcal U_p:=\{t: \Pair{ \restrict{p}{ \Length{t}}}{t} \in \mathcal U\}$, one has
$T_p \IncludedIn \mathcal U_p$, since each
node passes
every available test at all its prefixes. This inclusion
preserves the root and strict extension, giving the rank comparison used in the boundedness proof.

### Graph Tests and Quantifier Trees {#sec:lambda-graph-tests}

\begin{mathmeta}
  \vars{a,e,h,i,j,k,m,n,r,z}{Nat}
  \vars{p,q,x,\varepsilon}{Name}
  \vars{s,t}{Seq(Nat)}
\end{mathmeta}

Suppose closed programs $\LambdaTermName{functionProg}$, $\LambdaTermName{digitProg}$ compute total numerical
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

\begin{proof}[Proof]
Two beta steps expose $\LambdaTermName{functionProg}(\LambdaTermName{subInput}(o,\ChurchNumeral{z}))\ChurchNumeral{z}$.
For each queried numeral $k$, one beta step and numerical pairing turn the accessor call into
$\LambdaTermName{digitProg}o\ChurchNumeral{\NatPair{z}{k}}$, which returns the required digit by hypothesis.
The substitution theorem in §{sec:lambda-input-composition} replaces each query in the finite computation
of $\LambdaTermName{functionProg}$ by this computation of $\LambdaTermName{digitProg}$. Both component programs
terminate on every numerical input;
the resulting program is closed and queries only the original parameter.
\end{proof}

Here is the graph-row tester used in §{sec:edst-computable-preimages}.
For the input
$$z=\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$$
use numerical projections to
recover $n,m,r$ from $i=\NatPair{n}{\NatPair{m}{r}}$ and put $a=\LambdaListCode{s}$.
The second word $t$ is unused. In the preceding construction take the accessor body
$$\LambdaTermName{digitProg}o(\LambdaNumericPair\,z\,k)=\LambdaNumericPair\,(ok)\,
 (\LambdaNumericProjection{1}(\LambdaListGet(\LambdaNumericPair\,a\,k))).$$
This denotes the term obtained by substituting the projections for $a$ and abstracting the displayed
inputs. It pairs the original parameter digit with the first component of the stored point digit,
using zero beyond the word. Take the body of $\LambdaTermName{functionProg}$ to be
$\LambdaQueryOutputCandidate\,o\,\ChurchNumeral{e}\,n\,(\LambdaNumericPair\,m\,r)$.
Thus $\LambdaTermName{composeInput}$ returns one precisely when this finite computation test succeeds.
The required row bit is
$$\LambdaLeCase{\LambdaTermName{composeInput}oz}{\ChurchNumeral{0}}{\ChurchNumeral{1}}
 {\LambdaEqual\,(\LambdaNumericProjection{2}(\LambdaListGet(\LambdaNumericPair\,a\,n)))\,m}.$$
Every component is total, so the row is decidable even on short words. At length $i+1$,
the stage-address bound ensures that the zero padding cannot affect the answer.
The bounded-prefix construction in §{sec:lambda-recursive-borel-separation}, with bound $i+1$,
checks all rows without requiring an input-use modulus for the program with index $e$.

Let a closed program $\LambdaTermName{numberPredicate}$ decide $\mathcal R(e,n,k)$ at parameter $\varepsilon$,
with numerical input
$\NatPair{e}{\NatPair{n}{k}}$. On a row input $z=\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
use the following term abbreviations:
$$\begin{aligned}
\LambdaTermName{rowIndex}(z)&:=\LambdaNumericProjection{1}z,\\
\LambdaTermName{pointWord}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
\LambdaTermName{witnessWord}(z)&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z),\\
\LambdaTermName{entry}(a,j)&:=\LambdaListGet(\LambdaNumericPair\,a\,j),\\
\LambdaTermName{firstEntry}(z)&:=\LambdaTermName{entry}(\LambdaTermName{pointWord}(z),\ChurchNumeral{0}).
\end{aligned}$$
Then the two row testers are the closed terms obtained by expanding
$$\begin{aligned}
&\LambdaTermName{numberRow}_{ \forall \exists}:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaTermName{numberPredicate}o
\bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
 ( \LambdaNumericPair\, \LambdaTermName{rowIndex}(z)\,\\
&\quad \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z),
\LambdaTermName{rowIndex}(z))) \bigr)
\end{aligned}}},\\
&\LambdaTermName{numberRow}_{ \exists \forall}:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaTermName{numberPredicate}o
\bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
 ( \LambdaNumericPair\,\\
&\quad \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z), \ChurchNumeral{0})\,
\LambdaTermName{rowIndex}(z)) \bigr)
\end{aligned}}}.
\end{aligned}$$

\begin{proof}[Proof]
Numerical projections recover the row number and both word codes. List access reads the indicated
entries, returning zero when an entry is missing. Pairing therefore feeds $\LambdaTermName{numberPredicate}$ the code of
$\Tuple{s(0),i,t(i)}$ in the first case and $\Tuple{s(0),t(0),i}$ in the second. Two outer beta contractions expose
these computations at the original parameter. Every component terminates. For prefixes of length
$i+1$, every indicated entry is present, so these tests have exactly the meanings asserted in the
numerical-quantifier lemma. Use the successor program for the prefix bound. To obtain the complement
of the first projection, apply the second construction to the decision program for $\neg \mathcal R$.
\end{proof}

For totality, the jointly deciding program is
$$\begin{aligned}
&\LambdaTermName{totalityTrial}:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,
 (\LambdaNumericProjection{1}z)\,
 (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z))\,
 (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z))}}.
\end{aligned}$$
Its numerical input is $\NatPair{e}{\NatPair{n}{k}}$.

\begin{proof}[Proof]
Two beta contractions expose the candidate tester. Numerical projections supply the three arguments
$e,n,k$. The output-candidate theorem then gives one exactly when the finite trial succeeds and zero
otherwise. In particular this program terminates even when the indexed program fails to return a
numeral. Substituting $\LambdaTermName{totalityTrial}$ for $\LambdaTermName{numberPredicate}$ in the preceding
row construction gives the two trees for totality
and its complement without deciding an unbounded search.
\end{proof}

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

To decide the negated predicate, replace $\LambdaTermName{namePredicate}$ by the closed term
$$\LambdaTermName{namePredicate}^-:= \lambdaab{o}{ \lambdaab{z}{ \LambdaZeroTest\,(
\LambdaTermName{namePredicate}oz)\, \ChurchNumeral{1}\, \ChurchNumeral{0}}}.$$
The original output is zero or one, so the zero test reverses these two answers in finitely many
beta steps. Use $\LambdaTermName{namePredicate}^-$ in the second row construction for the complement of the
universal-existential
condition. The constant-one target tree tests $s(i)=1$ for $i<\Length{s}$ by list access, equality, and a
bounded product, with equal word lengths imposed. The inverse-image and projection programs then
supply the trees in §{sec:edst-baire-quantifiers}. Their correctness uses totality of each row, without
requiring a uniform time or input-use bound.

### Borel Constructors and Rank Labels {#sec:lambda-borel-constructor-programs}

\begin{mathmeta}
  \vars{a,b,i,m,n,s,t,x}{Nat}
\end{mathmeta}

Use the label operations of §{sec:edst-borel-constructors}. A label program takes an oracle argument $o$
and a numerical word code $w$. The empty word has code zero, and
$$\LambdaListCode{(i)\concat s}=\NatPair{i}{\LambdaListCode{s}}+1.$$
Thus on a nonempty word, $\LambdaPred w$ returns the pair of the first entry and the remaining word code.
At code zero the same term returns zero, so all the auxiliary computations below remain defined.

For a numeral label $\ell$, define the closed selector
$$R_\ell:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
 {\ChurchNumeral{\ell}}{\LambdaNumericProjection{2}z}}.$$
It returns $\ell$ when the first component is zero and otherwise returns the second component.
For complement labels use
$$\begin{aligned}
T&:=\lambdaab{z}{\LambdaNumericProjection{1}(\LambdaPred(\LambdaNumericProjection{1}z))},\\
H&:=\lambdaab{z}{\LambdaLeCase{Tz}{\ChurchNumeral{0}}
 {\LambdaNumericProjection{2}z}{\ChurchNumeral{0}}},\\
D&:=\lambdaab{z}{\LambdaLeCase{\LambdaNumericProjection{1}z}{\ChurchNumeral{0}}
 {\ChurchNumeral{2}}{Hz}}.
\end{aligned}$$
Here and below, every displayed abbreviation is expanded before abstraction and all bound variables
are chosen fresh. The selectors use the numerical comparison and branching term already constructed.

The three closed programs are
$$\begin{aligned}
B_n&:=\lambdaab{o}{\lambdaab{w}{\LambdaLeCase{w}{\ChurchNumeral{0}}
 {\ChurchNumeral{n+3}}{\ChurchNumeral{0}}}},\\
V_P&:=\lambdaab{o}{\lambdaab{w}{R_1\,
 (\LambdaNumericPair\,w\,(Po(\LambdaPred w)))}},\\
C_P&:=\lambdaab{o}{\lambdaab{w}{D\,
 (\LambdaNumericPair\,w\,(Po(\LambdaNumericProjection{2}(\LambdaPred w))))}}.
\end{aligned}$$
For $V_P$, the supplied $P$ computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$.
For $C_P$, it computes $c(s)$ from $\LambdaListCode{s}$. Each hypothesis requires totality on all
numerical inputs at the fixed parameter.

\begin{lemma*}[\termdefineas{Borel-label constructor programs}{Borel-label constructor programs}]
The programs $B_n$, $C_P$, and $V_P$ compute the label maps
$\BorelLeafCode{n}$, $\BorelComplementCode{c}$, and $\BorelUnionCode{(c_i)}$, respectively,
under the hypotheses just stated. They preserve the oracle parameter.
\end{lemma*}

\begin{proof}[Proof]
Comparison with zero proves the assertion for $B_n$. For $V_P$ and $C_P$, first reduce the application of $P$
and form the numerical pair; totality permits this even at the root and at absent children.
At word code zero, the selectors then return one and two, respectively, independently of that
auxiliary label. At a nonempty word code, predecessor and numerical projection recover exactly
$i$ and $\LambdaListCode{s}$. The selector $R_1$ returns $c_i(s)$. The selector $D$ returns $c(s)$
when $i=0$ and zero otherwise. These are precisely the defining label equations.
All numerical subterms terminate by their beta-reduction theorems; the application of $P$ uses its
finite beta/query derivation at the unchanged parameter. Composition and numerical output pairing
combine these derivations into a derivation for each displayed program.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
可算和constructorに必要な仮定の適用範囲を確認する説明。unionLabelProgram_computesは族全体のjoint
label programを明示的に要求し、各添字の個別プログラムから一様な族を選択したとは扱わない。結論はラベルの計算だけで、
well-foundednessの判定やvalid codeの選択は主張していない。)
--> Separate programs for the individual $c_i$ do not suffice for the union construction: $V_P$ needs one
program accepting $i$ as data. The construction preserves computable labels for such uniform families;
it does not decide whether the resulting tree is well-founded.<!--
formalization: skip-end
-->

We first construct an iterator that retains its oracle argument. For a closed program $P$, put
\begin{mathmeta}
  \define{LambdaIterateProgram}
\end{mathmeta}
$$\LambdaIterateProgram{P}:=\lambdaab{o}{\lambdaab{z}{
 (\LambdaNumericProjection{2}z)(Po)(\LambdaNumericProjection{1}z)}}.$$
If $P$ computes a total numerical function $f$ at parameter $\varepsilon$, this program computes
$\NatPair{x}{n}\mapsto f^n(x)$ at the same parameter, where $f^0(x)=x$.

\begin{proof}[Proof]
The two projections reduce to the numerals for $n$ and $x$. Applying the Church numeral for $n$
then gives $n$ nested applications of $Po$ to the numeral for $x$. Induction on $n$ combines the
finite beta/query derivations supplied by $P$ into the required derivation. The oracle argument
is unchanged throughout. Closedness follows from closedness of $P$ and the projections, with fresh binders.
\end{proof}

For the rank-label program, let $P$ compute the edge label $e_{t,s}(v)$ from
$\NatPair{t}{\NatPair{s}{\LambdaListCode{v}}}$, and let $Q$ decide $R(b,a)$ from
$\NatPair{b}{a}$, returning one for truth and zero for falsity. Both must be total at the fixed
parameter. The desired labels obey the finite-word equations in §{sec:edst-borel-rank-layers}.
Labels zero, one, and two mean absence, union, and complement; a leaf for the whole space has label three.
Use the numerical states
$$d(m):=\NatPair{0}{m},\qquad
q(a,s,v):=\NatPair{1}{\NatPair{a}{\NatPair{s}{\LambdaListCode{v}}}}.$$
The first is finished; the second requests a rank label. These states are numerical data for lambda terms.

For readability, in the following term bodies write $p_i:=\LambdaNumericProjection{i}$ and
$\LambdaNumericPairValue{X}{Y}:=\LambdaNumericPair\,X\,Y$.
These abbreviations denote numerical lambda terms, not semantic pairing of their values.
Define
$$\begin{aligned}
A(z)&:=p_1(p_2z),&S(z)&:=p_1(p_2(p_2z)),\\
W(z)&:=p_2(p_2(p_2z)),&T(z)&:=\LambdaListDrop\,(W(z))\,\ChurchNumeral{5},\\
H_i(z)&:=\LambdaListGet\,\LambdaNumericPairValue{W(z)}{\ChurchNumeral{i}}.
\end{aligned}$$
Missing list entries are read as zero. The edge and relation input bodies are
$$U(z):=\LambdaNumericPairValue{H_1(z)}{\LambdaNumericPairValue{S(z)}{T(z)}},
\qquad V(z):=\LambdaNumericPairValue{H_4(z)}{A(z)}.$$

The numerical selector receives an augmented state $y$, consisting of the old state and the two answers.
Within its body use
$$\begin{aligned}
z&:=p_1y,&\ell&:=\LambdaListLength\,(W(z)),&h_i&:=H_i(z),\\
e&:=p_1(p_2y),&r&:=p_2(p_2y),&u&:=T(z).
\end{aligned}$$
Further abbreviate $D(X):=\LambdaNumericPairValue{\ChurchNumeral{0}}{X}$ and
$$C_k(X;Y,Z):=\LambdaLeCase{X}{\ChurchNumeral{k}}{Y}{Z}.$$
Set
$$\begin{aligned}
B&:=C_0(u;\ChurchNumeral{2},C_1(u;\ChurchNumeral{3},\ChurchNumeral{0})),\\
N&:=\LambdaNumericPairValue{\ChurchNumeral{1}}{\LambdaNumericPairValue{h_4}{\LambdaNumericPairValue{h_1}{u}}},\\
J&:=C_0(h_4;D(e),D(\ChurchNumeral{0})),\\
K&:=C_0(r;D(B),N),\\
L&:=C_0(h_3;C_4(\ell;D(\ChurchNumeral{2}),J),C_4(\ell;D(\ChurchNumeral{1}),K)),\\
M&:=C_0(h_2;C_3(\ell;D(\ChurchNumeral{1}),L),D(\ChurchNumeral{0})),\\
F&:=C_1(\ell;D(\ChurchNumeral{1}),C_2(\ell;D(\ChurchNumeral{2}),M)),\\
G&:=C_0(\ell;D(\ChurchNumeral{2}),C_0(h_0;F,D(\ChurchNumeral{0}))),\\
Z&:=\lambdaab{y}{C_0(p_1z;z,G)}.
\end{aligned}$$
Expand all abbreviations before abstraction and choose fresh bound variables. In particular $Z$ is closed.
The body $B$ gives the empty-expression label: the word codes zero and one represent the empty word
and $(0)$, whose labels are two and three; every other word has label zero.

The update program and the initial input to the iterator are
$$\begin{aligned}
\Delta_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{
 Z\LambdaNumericPairValue{z}{\LambdaNumericPairValue{Po(U(z))}{Qo(V(z))}}}},\\
I&:=\lambdaab{x}{\LambdaNumericPairValue{\LambdaNumericPairValue{\ChurchNumeral{1}}{x}}{
\LambdaSucc(\LambdaListLength(p_2(p_2x)))}}.
\end{aligned}$$
\begin{mathmeta}
  \define{LambdaRankLabelProgram}
\end{mathmeta}
The required closed program is
$$\LambdaRankLabelProgram{P}{Q}:=\lambdaab{o}{\lambdaab{x}{
 p_2(\LambdaIterateProgram{\Delta_{P,Q}}\,o\,(Ix))}}.$$
Its input is $\NatPair{a}{\NatPair{s}{\LambdaListCode{v}}}$.

\begin{lemma*}[\termdefineas{rank-label program correctness}{Correctness of the rank-label program}]
Under the totality and computation hypotheses on $P,Q$, the program
$\LambdaRankLabelProgram{P}{Q}$ computes the finite-word rank labels at the original parameter.
If $R$ is well founded and every $e_{t,s}$ is valid, fixing $a,s$ gives a program for
$\RankLayerCode{a}{s}$.
\end{lemma*}

\begin{proof}[Proof]
First run $P,Q$ on the inputs $U(z),V(z)$ and form the augmented state. Their totality justifies
these calls even when the selector will not use their answers. The numerical reduction rules for
$Z$ give a finished state at each terminal case of the finite-word equations. The zero tag leaves
finished states fixed. The only unfinished output is $N$: here the word starts with $\Tuple{0,t,0,j,b}$,
where $j>0$ and $R(b,a)$ holds, and the new state is $q(b,t,u)$ for the remaining suffix $u$.
Thus each update preserves the requested label and each unfinished update consumes five entries.

More precisely, induction on $n$ proves the following: if $n>\Length{v}$, updating $q(a,s,v)$ that many
times gives the finished state with the prescribed label. If the first update reaches a finished state, all remaining
updates leave that state finished.
In the unfinished case the suffix has length $\Length{v}-5$, and the remaining $n-1$ updates exceed this
length, so the induction hypothesis applies. Both subtractions here occur only when $\Length{v}\ge5$ and $n>0$.
Apply the iterator with $n=\Length{v}+1$ and project the second component. Its reduction theorem gives a
finite beta/query derivation of the label. No step changes the oracle. For well-founded $R$, the
finite-label lemma identifies the output with the label of the valid rank expression. Finally,
pairing constants for $a,s$ with the input word code gives the fixed-parameter label program.
\end{proof}

### Borel Separation, Validity, and Evaluation {#sec:lambda-recursive-borel-separation}

\begin{mathmeta}
  \vars{p,q,x,\iota,\varepsilon}{Name}
  \vars{a,b,e,i,j,k,n,r,u,v,w,z,\ell,h_0,h_1,\alpha,\delta,\mu,\nu,\theta,\zeta}{Nat}
  \vars{s,t,\sigma,\tau}{Seq(Nat)}
  \vars{\upsilon,\chi}{Fun(Nat,Nat)}
\end{mathmeta}

Let $P,Q$ decide membership in the pair trees $T,S$, taking a numerical pair of word codes and
returning zero or one. We give the numerical tests and the joint edge-label program needed by
§{sec:edst-recursive-borel-completeness}. All computations use the original oracle argument $o$.
In this subsection abbreviate
$$\begin{aligned}
&\LambdaTermName{wordProjection}_i:=\LambdaListMap\,\LambdaNumericProjection{i},\\
&\LambdaNumericPairValue{ \LambdaTermName{left}}{ \LambdaTermName{right}}:= \LambdaNumericPair\,
\LambdaTermName{left}\, \LambdaTermName{right},\\
&\LambdaTermName{length}(\LambdaTermName{left}):=\LambdaListLength\,\LambdaTermName{left},\\
&\LambdaTermName{chooseLe}( \LambdaTermName{left}, \LambdaTermName{right}; \LambdaTermName{onLe},\\
&\LambdaTermName{onGt}):= \LambdaLeCase{ \LambdaTermName{left}}{ \LambdaTermName{right}}{
\LambdaTermName{onLe}}{ \LambdaTermName{onGt}},\\
&\LambdaTermName{less}( \LambdaTermName{left},\\
&\LambdaTermName{right}):= \LambdaTermName{chooseLe}(
\LambdaSucc\, \LambdaTermName{left}, \LambdaTermName{right}; \ChurchNumeral{1}, \ChurchNumeral{0}).
\end{aligned}$$
Thus $\LambdaTermName{wordProjection}_i$ projects every entry of a word, and $\LambdaTermName{less}$ tests
strict numerical inequality.
Expand each abbreviation before abstraction, with fresh bound variables.

For a word code $w$, the joint-tree membership body is
$$\begin{aligned}
&\LambdaTermName{jointNode}(o,w):= \LambdaTermName{chooseLe} \bigl(w, \ChurchNumeral{0}; \ChurchNumeral{1},
\qquad \qquad \qquad \quad\\
&\LambdaMul\,(Po\\
&\LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{
\LambdaTermName{wordProjection}_1( \LambdaTermName{wordProjection}_2w)})\\
&(Qo \LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{ \LambdaTermName{wordProjection}_2(
\LambdaTermName{wordProjection}_2w)})\\
&\bigr).
\end{aligned}$$
On input $z= \NatPair{b}{a}$, write $b:= \LambdaNumericProjection{1}z$ and $a:= \LambdaNumericProjection{2}z$
within the following body. The relation
program is
$$\begin{aligned}
&\LambdaTermName{strictExtension}(a,b):=\\
&\quad \LambdaMul\,( \LambdaListPrefix \LambdaNumericPairValue{a}{b})\,(
\LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b))),\\
&\LambdaTermName{jointRelation}:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaMul\,(\LambdaTermName{jointNode}(o,b))\,
 (\LambdaMul\,(\LambdaTermName{jointNode}(o,\\
&\quad a))\,(\LambdaTermName{strictExtension}(a,b)))
\end{aligned}}}.
\end{aligned}$$
The root test in $\LambdaTermName{jointNode}$ accepts the empty word. Both node tests in
$\LambdaTermName{jointRelation}$ ensure that codes outside
the tree are isolated. Prefix and length tests give exactly strict extension.

For the edge-label program, the input is $z=\NatPair{b}{\NatPair{a}{w}}$. Inside its body put
$$\begin{aligned}
b&:= \LambdaNumericProjection{1}z,&a&:= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}z),&w&:=
\LambdaNumericProjection{2}( \LambdaNumericProjection{2}z),\\
k&:=\LambdaNumericProjection{1}(\LambdaPred w),&r&:=\LambdaNumericProjection{2}(\LambdaPred w).
\end{aligned}$$
For a nonempty address, $k$ is its first entry and $r$ is its remaining word code. The guard is
computed by
$$\begin{aligned}
&\LambdaTermName{witnessNode}(o,k,b):= \LambdaMul\,( \LambdaEqual\, \LambdaTermName{length}(k)\,
\LambdaTermName{length}(b))\,(Qo \LambdaNumericPairValue{k}{b}),\\
&\LambdaTermName{edgeGuard}(o,z):=\\
&\quad \LambdaMul\,(\LambdaListPrefix\LambdaNumericPairValue{a}{b})\,
 ( \LambdaMul\,( \LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b)))\,\\
&\quad (
\LambdaTermName{witnessNode}(o,k,b))).
\end{aligned}$$
It returns one exactly when $H(b,a,k)$ holds. All its calls terminate even when $w$ is the empty-word code.

The two possible child-label bodies are
$$\begin{aligned}
\LambdaTermName{emptyLabel}(r)&:=\LambdaTermName{chooseLe}(r,\ChurchNumeral{0};\ChurchNumeral{2},
 \LambdaTermName{chooseLe}(r,\ChurchNumeral{1};\ChurchNumeral{3},\ChurchNumeral{0})),\\
\LambdaTermName{cylinderLabel}(k,r)&:= \LambdaTermName{chooseLe}(r, \ChurchNumeral{0}; \LambdaAdd\,k\,
\ChurchNumeral{3}, \ChurchNumeral{0}).
\end{aligned}$$
They give the empty expression and the basic-cylinder leaf, respectively. The joint label program is
$$\begin{aligned}
&\LambdaTermName{edgeLabel}_Q:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaTermName{chooseLe}(w, \ChurchNumeral{0};
\ChurchNumeral{1},
 \LambdaTermName{chooseLe}( \LambdaTermName{edgeGuard}(o,z),\\
&\quad \ChurchNumeral{0}; \LambdaTermName{emptyLabel}(r),
\LambdaTermName{cylinderLabel}(k,r)))
\end{aligned}}}.
\end{aligned}$$
It computes $e_{b,a}(\LambdaListDecode{w})$.

\begin{lemma*}[\termdefineas{recursive Borel separator programs}{Programs for the recursive Borel separator}]
The closed terms $\LambdaTermName{jointRelation}$ and $\LambdaTermName{edgeLabel}_Q$ decide the joint-tree
relation and compute the
section-edge
labels, respectively, at the original parameter. Therefore
$$\lambdaab{o}{\lambdaab{w}{\LambdaRankLabelProgram{\LambdaTermName{edgeLabel}_Q}{\LambdaTermName{jointRelation}}\,o\,
 \LambdaNumericPairValue{\ChurchNumeral{0}}{\LambdaNumericPairValue{\ChurchNumeral{0}}{w}}}}$$
computes every label of the separating expression whenever the two projections are disjoint.
\end{lemma*}

\begin{proof}[Proof]
List mapping computes each coordinate of the joint word, and the supplied deciders compute the two
membership bits. Their product and the root test give $\LambdaTermName{jointNode}$. The further products, prefix
test, and
strict length comparison give $\LambdaTermName{jointRelation}$. The same numerical rules give the four factors
of $\LambdaTermName{edgeGuard}$.
At address code zero, $\LambdaTermName{edgeLabel}_Q$ returns the union label one. At a nonempty address, predecessor and
projection recover $k,r$. A true guard selects the leaf label $k+3$ at its root and zero elsewhere;
a false guard selects the empty-expression labels two at the root, three at its child zero, and zero
elsewhere. These are precisely the labels of the edge expression. Every step has a finite beta/query
derivation by the numerical reduction lemmas and totality of the supplied deciders. The rank-label
iteration theorem then applies with both root indices fixed at zero. Disjointness is used to prove
validity of the final expression; none of these programs tests disjointness or selects a branch.
\end{proof}

The labels are zero for an absent node, one for a union, two for a complement, and numbers at least
three for basic-cylinder leaves. The structural conditions require a present root, prefix closure of
present nodes, no children at a leaf, a present child at a union, and exactly one present child at a
complement. Well-foundedness means that there is no infinite chain of present children. In this section,
the label program is total jointly in the family index and the word code at the fixed parameter.

Let $\LambdaTermName{familyLabels}$ be the supplied joint label program. For numeral arguments use the term
abbreviations
$$\begin{aligned}
\LambdaTermName{childCode}(w,k)&:=\LambdaListAppend\,w\,(\LambdaListCons\,k\,\ChurchNumeral{0}),\\
\LambdaTermName{labelAt}(o,e,w)&:=\LambdaTermName{familyLabels}o(\LambdaNumericPair\,e\,w),\\
\LambdaTermName{equal}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaEqual\, \LambdaTermName{left}\,
\LambdaTermName{right}, \qquad \LambdaTermName{zero}( \LambdaTermName{left}):= \LambdaTermName{equal}(
\LambdaTermName{left}, \ChurchNumeral{0}),\\
\LambdaTermName{le}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{ \LambdaTermName{left}}{
\LambdaTermName{right}}{ \ChurchNumeral{1}}{ \ChurchNumeral{0}},\\
\LambdaTermName{implies}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{
\LambdaTermName{left}}{ \ChurchNumeral{0}}{ \ChurchNumeral{1}}{ \LambdaTermName{right}},\\
\LambdaTermName{or}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaTermName{zero}( \LambdaMul\,(
\LambdaTermName{zero} \LambdaTermName{left})\,( \LambdaTermName{zero} \LambdaTermName{right})).
\end{aligned}$$
Thus $\LambdaTermName{zero}$ tests zero; on decision bits, $\LambdaTermName{implies}$ is implication and
$\LambdaTermName{or}$ is disjunction.

For input $z=\NatPair{e}{\NatPair{i}{j}}$, projections recover these components and
$i=\NatPair{w}{\NatPair{k}{\ell}}$. In the following bodies abbreviate
$$\begin{aligned}
&\LambdaTermName{rootLabel}:= \LambdaTermName{labelAt}(o,e, \ChurchNumeral{0}),\\
&\LambdaTermName{nodeLabel}:= \LambdaTermName{labelAt}(o,e,w),\\
&\LambdaTermName{childLabel}:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w,k)),\\
&\LambdaTermName{otherLabel}:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w, \ell)),\\
&\LambdaTermName{witnessLabel}:= \LambdaTermName{labelAt}(o,e, \LambdaTermName{childCode}(w,j)).
\end{aligned}$$
The five decision bits are
$$\begin{aligned}
&\LambdaTermName{syntaxBit}_0:=\LambdaTermName{zero}(\LambdaTermName{zero}\LambdaTermName{rootLabel}),\\
&\LambdaTermName{syntaxBit}_1:= \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
\LambdaTermName{childLabel}), \LambdaTermName{zero}( \LambdaTermName{zero} \LambdaTermName{nodeLabel})),\\
&\LambdaTermName{syntaxBit}_2:= \LambdaTermName{implies}( \LambdaTermName{le}( \ChurchNumeral{3},
\LambdaTermName{nodeLabel}), \LambdaTermName{zero} \LambdaTermName{childLabel}),\\
&\LambdaTermName{syntaxBit}_3:=\\
&\quad \LambdaTermName{implies}( \LambdaTermName{or}( \LambdaTermName{equal}(
\LambdaTermName{nodeLabel}, \ChurchNumeral{1}), \LambdaTermName{equal}( \LambdaTermName{nodeLabel},
\ChurchNumeral{2})), \LambdaTermName{zero}( \LambdaTermName{zero}\\
&\quad \LambdaTermName{witnessLabel})),\\
&\LambdaTermName{syntaxBit}_4:=\\
&\quad \LambdaTermName{implies}( \LambdaTermName{equal}( \LambdaTermName{nodeLabel},
\ChurchNumeral{2}), \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
\LambdaTermName{childLabel}),\\
&\quad \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{zero}
\LambdaTermName{otherLabel}), \LambdaTermName{equal}(k, \ell)))).
\end{aligned}$$
Expand all abbreviations and numerical projections inside
$$\begin{aligned}
&\LambdaTermName{syntaxRow}:=\\
&\quad \lambdaab{o}{\lambdaab{z}{\begin{aligned}[t]
&\LambdaMul\,\LambdaTermName{syntaxBit}_0\,
 ( \LambdaMul\, \LambdaTermName{syntaxBit}_1\,( \LambdaMul\, \LambdaTermName{syntaxBit}_2\,\\
&\quad ( \LambdaMul\,
\LambdaTermName{syntaxBit}_3\, \LambdaTermName{syntaxBit}_4)))
\end{aligned}}}.
\end{aligned}$$

\begin{proof}[Proof]
Pairing, projections, list concatenation, and singleton formation all terminate with the displayed
codes. The five label calls terminate by the hypothesis on $\LambdaTermName{familyLabels}$, retaining the same
parameter.
Equality, comparison, and zero tests return bits, and the five factors express exactly the five
syntax clauses. Their product is one exactly when the whole row holds. The numerical-quantifier
construction of §{sec:lambda-graph-tests} therefore applies to this closed row program.
\end{proof}

For a descending-chain row, the input is $z=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
Use list access to obtain $e=s(0)$, $h_0=t(n)$, and $h_1=t(n+1)$, with zero for a missing entry.
Put $w=\LambdaNumericProjection{1}h_0$, $k=\LambdaNumericProjection{2}h_0$, and
$u=\LambdaNumericProjection{1}h_1$ inside the body
$$\begin{aligned}
&\LambdaMul\,\bigl(\LambdaTermName{zero}(\LambdaTermName{zero}(\LambdaTermName{labelAt}(o,e,w)))\bigr)\,
 \bigl( \LambdaMul\,( \LambdaTermName{zero}( \LambdaTermName{zero}( \LambdaTermName{labelAt}(o,e,\\
&u))))\,(
\LambdaTermName{equal}(u, \LambdaTermName{childCode}(w,k))) \bigr).
\end{aligned}$$
Abstract $o,z$ after expanding the accessors. Its prefix bound is computed by
$\lambdaab{n}{\LambdaSucc(\LambdaSucc n)}$.

\begin{proof}[Proof]
The first two factors require the current and next words to be present. The third compares the next
word code with the code of the specified child. Since list coding is bijective, equality of these codes
is precisely the required child relation. At prefix length $n+2$ all three list accesses are in range.
The label calls terminate independently of the lengths of the words they encode. Thus the bounded-prefix
construction gives exactly the chains in the validity proposition. No rank or test for well-foundedness
is needed to compute these finite rows.
\end{proof}

A label stream $x$ represents the expression $c_x(s):=x(\LambdaListCode{s})$, with the label conventions
of the preceding section. With input $\NamePair{\varepsilon}{x}$, its label reader is the closed term
$$\LambdaTermName{streamLabels}:=\lambdaab{o}{\lambdaab{w}{\LambdaNumericProjection{2}(ow)}}.$$
For the syntax row, replace $\LambdaTermName{labelAt}(o,e,w)$ by
$\LambdaTermName{streamLabels}ow$, omit the unused family index, and
use numerical input $\NatPair{i}{j}$. The same five Boolean factors test the row for every label stream.
Negation applies the zero test to a decision bit; conjunction multiplies two bits; disjunction and
implication are obtained from these operations. Each operation combines fixed closed terms, so the
result is one program for all input names. It does not choose a new term after receiving a name.

For chain witnesses, supply $\NamePair{\varepsilon}{\NamePair{x}{q}}$ and put
$$\begin{aligned}
\LambdaTermName{witnessEntry}(o,n)&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on)),\\
\LambdaTermName{streamLabel}(o,w)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(ow)),\\
h_0&:=\LambdaTermName{witnessEntry}(o,n),\quad h_1:=\LambdaTermName{witnessEntry}(o,\LambdaSucc n),\\
w&:=\LambdaNumericProjection{1}h_0,\quad k:=\LambdaNumericProjection{2}h_0,
 \quad u:=\LambdaNumericProjection{1}h_1.
\end{aligned}$$
Using $\LambdaTermName{childCode}$, $\LambdaTermName{equal}$, $\LambdaTermName{zero}$ defined above,
expand and abstract $o,n$ in
$$\begin{aligned}
&\LambdaMul\,(\LambdaTermName{zero}(\LambdaTermName{zero}(\LambdaTermName{streamLabel}(o,w))))\,
 ( \LambdaMul\,( \LambdaTermName{zero}( \LambdaTermName{zero}( \LambdaTermName{streamLabel}(o,\\
&u))))\,(
\LambdaTermName{equal}(u, \LambdaTermName{childCode}(w,k)))).
\end{aligned}$$

\begin{proof}[Proof]
The accessor $\LambdaTermName{witnessEntry}$ reads a witness entry and $\LambdaTermName{streamLabel}$ reads a
label. Pair projections extract the word codes
and chosen child. The first two factors require present words, and the third checks that the next word
is the chosen child. All accesses are to the supplied total input sequence, even when their positions
are computed from witness values. Thus every row terminates. The universal-row construction of
§{sec:edst-baire-quantifiers} applies without a predetermined bound on these positions. This gives the
chain projection; combining it with failure of the five syntax conditions gives invalid label streams.
\end{proof}

For arbitrary program indices, use the input $\NamePair{\varepsilon}{\NamePair{\iota}{p}}$, where
$\iota(0)$ is the index and $p$ stores output candidates with finite verification bounds. Define
$$\begin{aligned}
&\LambdaTermName{parameterInput}(o):=\lambdaab{j}{\LambdaNumericProjection{1}(oj)},\\
&\LambdaTermName{inputIndex}(o):=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
&\LambdaTermName{candidateTrial}:=\\
&\quad \lambdaab{o}{\lambdaab{n}{\begin{aligned}[t]
&\LambdaQueryOutputCandidate\,(
\LambdaTermName{parameterInput}(o))\, \LambdaTermName{inputIndex}(o)\,\\
&\quad n\,(
\LambdaTermName{witnessEntry}(o,n))
\end{aligned}}}.
\end{aligned}$$
The decoded output sequence is read by
$$\LambdaTermName{candidateOutput}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericProjection{1}(
\LambdaTermName{witnessEntry}(o,n))}}.$$
All these are closed terms after expanding the abbreviations and choosing fresh binders.

\begin{proof}[Proof]
Each query to $\LambdaTermName{parameterInput}(o)$ supplies the corresponding digit of the fixed parameter.
Numerical projections
supply the index, and $\LambdaTermName{witnessEntry}$ supplies the candidate for the current input. Substitution
and numerical
composition therefore turn a call to $\LambdaTermName{candidateTrial}$ into exactly the finite output-candidate
test with those
arguments. That test is total regardless of whether the indexed program is partial. Soundness gives
the claimed output from every successful trial; completeness provides a bound for every genuine
output. The term $\LambdaTermName{candidateOutput}$ extracts the output component by one numerical projection.
Hence the inverse
image, intersection, projection, and union operations in the main proof all use closed lambda terms
at the original parameter. The only choices of entire tables occur in the proof of their existence.
\end{proof}

Use the list numbering from §{sec:lambda-finite-lists}. A finite word $s$ has natural-number code
$\LambdaListCode{s}$; the corresponding closed lambda term is $\ChurchNumeral{\LambdaListCode{s}}$.
We keep the word, its code, and its numeral distinct. On the row input
$i=\NatPair{\LambdaListCode{s}}{k}$, the code of its child $s\concat(k)$ is computed by the closed term
$$\LambdaTermName{rowChild}:=\lambdaab{i}{\LambdaListAppend\,(\LambdaNumericProjection{1}i)\,
 (\LambdaListCons\,(\LambdaNumericProjection{2}i)\,\ChurchNumeral{0})}.$$
Maximum is computed by the body $\LambdaTermName{maximum}(a,b):=\LambdaLeCase{a}{b}{b}{a}$.
Write $\upsilon(i)$ for the row bound from the Borel evaluation proposition. It is computed by
$$\begin{aligned}
&\LambdaTermName{evalBound}:=\\
&\quad \lambdaab{i}{\begin{aligned}[t]
&\LambdaTermName{maximum}(\LambdaSucc(\LambdaNumericProjection{1}i),
 \LambdaTermName{maximum}( \LambdaSucc( \LambdaTermName{rowChild}i), \LambdaTermName{maximum}(
\ChurchNumeral{1},\\
&\quad \LambdaListLength( \LambdaNumericProjection{2}i))))
\end{aligned}}.
\end{aligned}$$
Expand the abbreviations and bind distinct fresh variables. List concatenation computes exactly the child
code, and the maximum and successor equations prove that $\LambdaTermName{evalBound} \ChurchNumeral{i}$ returns
$\ChurchNumeral{ \upsilon(i)}$.

For the finite row tester, write its input as $z=\NatPair{i}{\NatPair{\LambdaListCode{\sigma}}{\LambdaListCode{\tau}}}$,
where $\sigma,\tau$ are point and witness prefixes. Numerical projections recover the row, both word codes, and
$k$. List access at the codes of $s$, its child, and the root recovers the two components of each stored
pair. Run the supplied relative label program at the code of $s$ and at $\LambdaTermName{rowChild}i$, retaining
the same parameter.
List truncation, length, and numerical equality decide whether $\sigma$ starts with $\LambdaListDecode{k}$.
This comparison is made on list codes, so no separate list-equality primitive is needed.

Here is an explicit Boolean body for combining these values. All its inputs and outputs are numerals;
write $\LambdaTermName{equal}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaEqual\,
\LambdaTermName{left}\, \LambdaTermName{right}$, $\LambdaTermName{zero}( \LambdaTermName{left}):=
\LambdaTermName{equal}( \LambdaTermName{left}, \ChurchNumeral{0})$, and
$\LambdaTermName{implies}( \LambdaTermName{left}, \LambdaTermName{right}):= \LambdaLeCase{
\LambdaTermName{left}}{ \ChurchNumeral{0}}{ \ChurchNumeral{1}}{ \LambdaTermName{right}}$.
Let $\alpha,\delta$ be the two labels, $\mu,\nu$ the two truth values, $j$ the selected child, $k$ the current child,
and $\theta$ the cylinder-test bit. Put
$$\begin{aligned}
&\LambdaTermName{evalArithmetic}(\alpha,\delta,\mu,\nu,j,k,\theta):=\\
&\quad \LambdaLeCase{\mu}{\ChurchNumeral{1}}{\ChurchNumeral{1}}{\ChurchNumeral{0}} {} \cdot
\LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{0}), \LambdaTermName{equal}(
\mu, \ChurchNumeral{0})) {} \cdot \LambdaTermName{implies}(\\
&\quad \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
\LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}),
 \LambdaTermName{implies}( \LambdaTermName{equal}(j,k), \LambdaTermName{zero}( \LambdaTermName{equal}( \delta,\\
&\quad \ChurchNumeral{0})) \cdot \LambdaTermName{equal}( \nu, \ChurchNumeral{1})))) {} \cdot
\LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{1}),
\LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta,\\
&\quad \ChurchNumeral{0})),
 \LambdaTermName{implies}( \LambdaTermName{equal}( \nu, \ChurchNumeral{1}), \LambdaTermName{equal}( \mu,
\ChurchNumeral{1})))) {} \cdot \LambdaTermName{implies}( \LambdaTermName{equal}( \alpha, \ChurchNumeral{2}),\\
&\quad \LambdaTermName{implies}( \LambdaTermName{zero}( \LambdaTermName{equal}( \delta, \ChurchNumeral{0})),
 \LambdaTermName{equal}(\LambdaAdd\,\mu\,\nu,\ChurchNumeral{1}))) {}\cdot
\LambdaTermName{implies}(\LambdaTermName{equal}(\alpha,\\
&\quad \LambdaAdd\,k\,\ChurchNumeral{3}),
 \LambdaTermName{implies}( \LambdaTermName{equal}( \mu, \ChurchNumeral{1}), \theta) \cdot
\LambdaTermName{implies}( \theta, \LambdaTermName{equal}( \mu, \ChurchNumeral{1}))).
\end{aligned}$$
Products abbreviate nested applications of $\LambdaMul$. Multiply this body by the equality test for the
prescribed root bit, substitute the accessors just described, and abstract the parameter and row input.
The resulting closed program $\LambdaTermName{evalRow}_ \zeta$ decides the finite certificate clause with root
bit $\zeta$.

\begin{proof}[Verification]
Every accessor terminates by the numerical pairing and list-program theorems. The label calls terminate
by the hypothesis on the supplied program. Equality and comparison return zero or one; on such bits,
$\LambdaTermName{implies}$ computes implication, $\LambdaTermName{zero}$ negation, and multiplication
conjunction. The six displayed factors
therefore express exactly the truth-bit bound and the five certificate clauses in the main text.
The additional root test specifies the required evaluation side. Composition preserves the parameter,
and beta/query reduction gives the claimed answer on every finite input, including insufficient prefixes.
The outer construction below ensures that only sufficiently long prefixes affect a branch.
\end{proof}

More generally, let $\LambdaTermName{clausePredicate}$ decide numbered clauses on pairs of words, and let a
closed numerical term $\LambdaTermName{prefixBound}$
compute their numerical prefix-bound function $\chi$. For finite words $s,t$, let $w= \NatPair{
\LambdaListCode{s}}{ \LambdaListCode{t}}$.
For a trial $i$, put
$$\begin{aligned}
&\LambdaTermName{t}(v):= \LambdaNumericProjection{1}v,\\
&\LambdaTermName{i}(v):=
\LambdaNumericProjection{2}v,\\
&\LambdaTermName{L}(w):=\LambdaListLength(\LambdaNumericProjection{1}w),\\
&\LambdaTermName{B}(w,i):=\\
&\quad \LambdaNumericPair\,
 (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,(\LambdaTermName{prefixBound}i)))
(\LambdaListTake(\LambdaNumericPair\,\\
&\quad (\LambdaNumericProjection{2}w)\,(\LambdaTermName{prefixBound}i))),\\
&\LambdaTermName{C}(o,w,i):= \LambdaTermName{clausePredicate}o( \LambdaNumericPair\,i\,
\LambdaTermName{B}(w,i)),\\
&\LambdaTermName{guardedClause}:= \lambdaab{o}{ \lambdaab{v}{ \LambdaLeCase{ \LambdaTermName{prefixBound}
\LambdaTermName{i}(v)}{ \LambdaTermName{L}( \LambdaTermName{t}(v))}
 {\LambdaTermName{C}(o,\LambdaTermName{t}(v),\LambdaTermName{i}(v))}{\ChurchNumeral{1}}}},\\
&\LambdaTermName{boundedClauses}:=\lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{\LambdaTermName{guardedClause}}\,o\,
 (\LambdaNumericPair\,w\,\LambdaTermName{L}(w))}}.
\end{aligned}$$
The bounded product checks exactly $i<\Length{s}$, skipping a row when its bound exceeds $\Length{s}$,
and otherwise
passing the prefixes of length $\chi(i)$ to $\LambdaTermName{clausePredicate}$. Apply
§{sec:lambda-kleene-brouwer} to $\LambdaTermName{boundedClauses}$ to obtain
a downward-closed tree. On an infinite pair, every row is encountered by length
$\max\{i+1,\chi(i)\}$; truncation at that length supplies precisely the prescribed prefixes. Thus its
projection is exactly the set of points admitting a witness satisfying all numbered clauses.
Taking $\LambdaTermName{clausePredicate}= \LambdaTermName{evalRow}_ \zeta$ and $\LambdaTermName{prefixBound}=
\LambdaTermName{evalBound}$ gives the two
Borel evaluation trees.

### Sections and Countable Tree Operations {#sec:lambda-projection-programs}

\begin{mathmeta}
  \vars{p}{Nat}
  \vars{e,i,j,k,m,n,u,v,w,z}{Nat}
  \vars{s,t}{Seq}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
既出の有限tabulationプログラムを次のword pairingに使うという1文の参照案内。
tabulation本体とそのbeta還元はlambda-finite-tabulationで別に対応しており、
ここから新しい計算手続きの存在を追加したとは数えない。)
-->
The finite-tabulation program is constructed in §{sec:lambda-finite-tabulation}. We use it here to pair finite words.
<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{LambdaListPair}
\end{mathmeta}

For paired words, decode $v=\NatPair{w}{k}$ inside the following term bodies:
$$\begin{aligned}
F_{\mathrm{pair}}&:=\lambdaab{v}{\LambdaNumericPair\,
 (\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,k))\,
 (\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}w)\,k))},\\
\LambdaListPair&:=\lambdaab{z}{\LambdaListTabulate{F_{\mathrm{pair}}}\,
 (\LambdaNumericPair\,z\,(\LambdaListLength(\LambdaNumericProjection{1}z)))}.
\end{aligned}$$
Expand $w,k$ inside the body of $F_{\mathrm{pair}}$ before abstraction. On the code of $\Pair{s}{t}$,
this returns $\LambdaListCode{\WordPair{s}{t}}$: the list has length $\Length{s}$, and its $k$th entry pairs the
$k$th entries of the two words, with zero used beyond the length of $t$. The finite-tabulation lemma and
the total list-access theorem prove this even when the input lengths differ.

Suppose $P$ decides membership in a pair tree $T$ relative to a fixed parameter. Set
$A_i:=\LambdaListMap\,\LambdaNumericProjection{i}$ for $i=1,2$. For the code
$z=\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}$, abbreviate
$v(z)=\LambdaNumericProjection{2}z$, and define
$$\begin{aligned}
K&:=\lambdaab{z}{\LambdaNumericPair\,
 \bigl(\LambdaListPair(\LambdaNumericPair\,(A_1v(z))\,(\LambdaNumericProjection{1}z))\bigr)\,(A_2v(z))},\\
Q&:=\lambdaab{o}{\lambdaab{z}{Po(Kz)}}.
\end{aligned}$$
The program $Q$ decides the test $\Pair{\WordPair{t_1}{s}}{t_2}\in T$, where $t_1,t_2$ are the entrywise
projections of $t$. Indeed, list mapping supplies these two projections, $\LambdaListPair$ pairs the
first with $s$, and numerical pairing supplies the exact input for $P$. Each component terminates and
the input parameter is unchanged. Applying the finite-test construction of
§{sec:lambda-kleene-brouwer} to $Q$ gives the projection-tree decider of
§{sec:edst-coordinate-projections}. At the empty node it tests the empty pair in $T$, so it also handles
an empty original tree correctly.

Let $S$ be a pair tree whose membership is decided by $P$ at parameter $\varepsilon$. Write
$x_n(k)=n$ and $S_n:=\{t:t=[]\lor\Pair{\restrict{x_n}{\Length{t}}}{t}\in S\}$. Put
$p_i:=\LambdaNumericProjection{i}$ for $i=1,2$ and define
$$\begin{aligned}
 Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
 O(d,e)&:=Z(\LambdaMul\,(Zd)\,(Ze)),\\
 C&:=\LambdaListTabulate{p_1},\\
 F(z)&:=\LambdaNumericPair\,
  \bigl(C(\LambdaNumericPair\,(p_1z)\,(\LambdaListLength\,(p_2z)))\bigr)\,(p_2z),\\
 M&:=\lambdaab{o}{\lambdaab{z}{O(Z(p_2z),Po(F(z)))}}.
\end{aligned}$$
Expand the abbreviation $F$ and the Boolean body before abstraction. On input $\NatPair{n}{k}$, the term
$C$ computes the code of the length-$k$ constant word with value $n$.

\begin{lemma*}[\termdefineas{recursive numerical section forests}{Recursive numerical section forests}]
The term $M$ decides $s_k\in S_n$ on input $\NatPair{n}{k}$, where $s_k$ is the word with code $k$.
The relation
$$\begin{aligned}
 E(\NatPair{m}{j},\NatPair{n}{k})\quad\Longleftrightarrow\quad
 &m=n,\quad s_j,s_k\in S_n,\\
 &s_k\preceq s_j,\quad \Length{s_k}<\Length{s_j}
\end{aligned}$$
has a single total decision program at the same parameter $\varepsilon$.
\end{lemma*}

\begin{proof}[Proof]
Finite tabulation of the first projection appends the unchanged first input at each step, proving the
assertion about $C$. The list code is zero exactly for the empty word. Thus $M$ accepts that word.
The term $F$ supplies exactly the paired codes required by the decider for $S$. This proves the
membership assertion, including the case where the original pair tree has no root.

For the edge test, decode $z=\NatPair{u}{v}$ and put
$$L(d,e):=\LambdaLeCase{d}{e}{\ChurchNumeral{1}}{\ChurchNumeral{0}}.$$
Use the following product of bits, with each product implemented by $\LambdaMul$:
$$\begin{aligned}
 D(o,z):={}&L(p_1u,p_1v)\,L(p_1v,p_1u)\\
 &\cdot M o(\LambdaNumericPair\,(p_1v)\,(p_2u))\cdot M o v\\
 &\cdot\LambdaListPrefix(\LambdaNumericPair\,(p_2v)\,(p_2u))\\
 &\cdot L(\LambdaSucc(\LambdaListLength\,(p_2v)),\LambdaListLength\,(p_2u)).
\end{aligned}$$
Substitute $u=p_1z$, $v=p_2z$ and expand all abbreviations before forming
$\lambdaab{o}{\lambdaab{z}{D(o,z)}}$. The two comparisons test equality of the component indices.
The other factors test the two memberships, the prefix condition, and strict increase of length.
Every call terminates and uses only the original parameter. Pairing, tabulation, and each finite test
have the stated beta/query reductions, so their composition returns exactly the required decision bit.
\end{proof}

\begin{lemma*}[\termdefineas{bounded ranks in a coded forest}{Bounded ranks in a coded forest}]
For any well-founded bound relation, the relation below a word in $S_n$ is well founded with the
specified rank bound if and
only if the corresponding node $\NatPair{n}{k}$ satisfies the same bound in $E$. Other sections need
not be well founded.
\end{lemma*}

\begin{proof}[Proof]
Induct along the bound relation, simultaneously for every word code. The bounded-rank recursion
requires that each predecessor satisfy a lower bound. The predecessors of $\NatPair{n}{k}$ in $E$
are exactly the pairs $\NatPair{n}{j}$ for which $s_j$ strictly extends $s_k$ inside $S_n$.
Apply the induction hypothesis to each such predecessor. The two bounded-rank formulas therefore
coincide at the current bound, including a bound with no predecessors.
\end{proof}

Let $P$ be a closed program deciding $\Pair{s}{t}\in T_i$ at parameter $\varepsilon$ on input
$\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
Throughout this subsection, expand all abbreviations before abstraction and choose distinct fresh binders.
For a node code $z$, put
$$\begin{aligned}
d(z)&:=\LambdaListField{2}(\LambdaNumericProjection{2}z),\qquad
h(z):=\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,\ChurchNumeral{0}),\\
Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
\end{aligned}$$
The field program also returns zero at the empty-list code, so it computes the tail code for every list.
The term $Z$ reverses a decision bit.

For the union, define
$$\begin{aligned}
K_U&:=\lambdaab{z}{\LambdaNumericPair\,h(z)\,
 (\LambdaNumericPair\,
  (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,(\LambdaListLength\,d(z))))\,d(z))},\\
E(z)&:=Z(\LambdaNumericProjection{2}z),\qquad D(o,z):=Po(K_Uz),\\
Q_U&:=\lambdaab{o}{\lambdaab{z}{Z(\LambdaMul\,(Z(E(z)))\,(Z(D(o,z))))}}.
\end{aligned}$$
On a nonempty witness word, $K_U$ returns the selected index together with the shortened first word and
the witness tail. The bit $E(z)$ tests whether the witness word is empty; the outer expression is the
Boolean disjunction of this bit and $D(o,z)$. Thus $Q_U$ decides the union test of
§{sec:edst-uniform-countable-operations}. Every component terminates, even on unequal input lengths.
Applying the finite-test construction gives the required tree decider.

\begin{mathmeta}
  \define{LambdaWitnessRow}
\end{mathmeta}
To extract a finite witness row, decode $u=\NatPair{\NatPair{e}{i}}{j}$ inside the first term below.
In the second, abbreviate $c(z)=\LambdaNumericProjection{2}z$:
$$\begin{aligned}
F_{\mathrm{row}}&:=\lambdaab{u}{\LambdaListGet(\LambdaNumericPair\,e\,(\LambdaNumericPair\,i\,j))},\\
\LambdaWitnessRow&:=\lambdaab{z}{\LambdaListTabulate{F_{\mathrm{row}}}\,
 (\LambdaNumericPair\,
  (\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{1}c(z)))\,
  (\LambdaNumericProjection{2}c(z)))}.
\end{aligned}$$
Here $e,i,j$ mean the corresponding numerical projections of $u$ only within $F_{\mathrm{row}}$.
The list-access theorem and finite tabulation show that on input
$\NatPair{\LambdaListCode{t}}{\NatPair{i}{k}}$ the second term returns
$\LambdaListCode{\WitnessRow{t}{i}{k}}$. This works for every input, including an empty row and missing
entries, which are replaced by zero.

For an intersection trial input, decode $u=\NatPair{\NatPair{z}{i}}{k}$ and expand
$$\begin{aligned}
L(u)&:=\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,k),\\
W(u)&:=\LambdaWitnessRow(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,(\LambdaNumericPair\,i\,k)),\\
K_V&:=\lambdaab{u}{\LambdaNumericPair\,i\,(\LambdaNumericPair\,L(u)\,W(u))},\\
B(u)&:=\LambdaLeCase{\LambdaSucc(\LambdaNumericPair\,i\,k)}
 {\LambdaListLength\,(\LambdaNumericProjection{2}z)}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
Q_V&:=\lambdaab{o}{\lambdaab{u}{Z(\LambdaMul\,B(u)\,(Z(Po(K_Vu))))}}.
\end{aligned}$$
Within these bodies, $z,i,k$ are numerical projections of $u$. The guard $B(u)$ is one exactly when
$\NatPair{i}{k}<\Length{t}$, and $K_V$ constructs the input for the tree test on the first $k$ entries and the
extracted row. The last term computes implication: a failed guard returns one, and a true guard returns
the supplied tree decision. All numerical components and the joint decider terminate.

Finally put $n(z)=\LambdaListLength\,(\LambdaNumericProjection{1}z)$. With $v=\NatPair{z}{i}$ in the first body, define
$$\begin{aligned}
I&:=\lambdaab{o}{\lambdaab{v}{\LambdaRelativeProduct{Q_V}\,o\,
 (\LambdaNumericPair\,v\,n(\LambdaNumericProjection{1}v))}},\\
J&:=\lambdaab{o}{\lambdaab{z}{\LambdaRelativeProduct{I}\,o\,
 (\LambdaNumericPair\,z\,n(z))}}.
\end{aligned}$$
The inner product ranges over $k<\Length{s}$, retaining the node code and row index. The outer product ranges
over $i<\Length{s}$, retaining the node code. Both use the same parameter $o$. The bounded-product theorem
therefore proves that $J$ decides exactly the intersection test of §{sec:edst-uniform-countable-operations}.
Applying the finite-test construction once more gives its downward-closed tree. At length zero both
products are empty and return one; the later prefix tests still inspect the empty node of each component
tree. No test of an infinite witness and no program selecting such witnesses is used.

\begin{lemma*}[
\termdefineas{parameter-preserving countable tree operations}{Parameter-preserving countable tree operations}]
Fix $\varepsilon$. Suppose a single closed program decides membership in the pair trees $T_{a,k}$
jointly in the numerical indices and finite node, and put $A_{a,k}:=\pi_0([T_{a,k}])$. Then
$$U_a:=\bigcup_{k\in\NN}A_{a,k},\qquad V_a:=\bigcap_{k\in\NN}A_{a,k}$$
have pair-tree presentations with finite-node tests jointly decidable in $a$ and the node.
Consequently, their tree indices are total computable functions of $a$.
If the complements of the input sets also have jointly decidable tree presentations, the same
conclusion holds for the complements of both output families.
\end{lemma*}

\begin{proof}[Proof]
Let $P$ be the joint decider, with numerical input coding the triple consisting of the outer index,
the quantified index, and the node. Retain the outer index by using the template
$$P_a:=\lambdaab{o}{\lambdaab{w}{Po(\LambdaNumericPair\,a\,w)}}.$$
Here $w$ codes the quantified index and node. Insert this template into the union and intersection
programs of §{sec:lambda-projection-programs}, expanding its body and choosing fresh binders.
For a joint output decider, extract $a$ and the node from its numerical input and retain $a$
through both bounded products and every finite-prefix test. In the union construction the witness
head selects a component; in the intersection construction its paired positions supply all component
witnesses. Thus the previous body identities hold at every fixed $a$, while all finite tests remain
jointly decidable. Numerical specialization of these two fixed joint programs computes the required
indices. It does not search for an infinite witness or test nonemptiness. Apply the intersection
construction to the input complements to obtain the complement of the union, and the union
construction to obtain the complement of the intersection.
\end{proof}

## Transfinite Tree Constructions {#sec:lambda-transfinite-tree-programs}

### Cantor Derivatives and Transfinite Stages {#sec:lambda-cantor-derivative-programs}

\begin{mathmeta}
  \vars{N,U,V,a,b,c,d,i,j,k,m,n,q,s,t,w,x,y,z}{Nat}
\end{mathmeta}

Let $P$ decide membership in the input tree at $\varepsilon$, using the natural-list code for a
binary word. Extend the test to natural words by rejecting nonbinary words. Write
$$\begin{aligned}
 \ell(a)&:=\LambdaListLength\,a,\qquad a[i]:=\LambdaListGet(\LambdaNumericPair\,a\,i),\\
 E(a,b)&:=\LambdaEqual\,a\,b,\qquad
 F(a,b):=\LambdaListPrefix(\LambdaNumericPair\,a\,b),\\
 L(a,b)&:=\LambdaLeCase{a}{b}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
 Z&:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
\end{aligned}$$
All products below mean repeated application of $\LambdaMul$. Expand every abbreviation before
abstraction, use numerical projections to decode paired inputs, and choose distinct fresh binders.

First decide whether a word code is binary. In the first body decode $w=\NatPair{a}{i}$:
$$\begin{aligned}
 G&:=\lambdaab{o}{\lambdaab{w}{L(a[i],\ChurchNumeral{1})}},\\
 B&:=\lambdaab{o}{\lambdaab{a}{\LambdaRelativeProduct{G}\,o\,
  (\LambdaNumericPair\,a\,\ell(a))}}.
\end{aligned}$$
The product tests every entry, so $B$ returns one exactly for words with entries zero or one.

Decode the matrix input as
$$z=\NatPair{\NatPair{\NatPair{\NatPair{s}{m}}{c}}{n}}{V},\qquad c=\NatPair{N}{U}.$$
Here $s$ is a word code and $U,V$ are table codes. Put $u_i:=U[i]$, $v_i:=V[i]$, and use
$$\begin{aligned}
 A(o,z,i):={}&(Bo u_i)(Bo v_i)E(\ell(u_i),N)F(s,u_i)\\
 &\cdot E(\ell(v_i),\LambdaAdd\,N\,n)F(u_i,v_i)(Po v_i),\\
 C(z,i,j):={}&Z\bigl(\LambdaMul\,E(u_i,u_j)\,(Z(E(i,j)))\bigr).
\end{aligned}$$
The first body checks one row of $R_T$. The second checks that equality of the two word codes
implies equality of their indices. Injectivity of list coding identifies equality of codes with
equality of words.

Form $A_P:=\lambdaab{o}{\lambdaab{w}{A(o,z,i)}}$ with $w=\NatPair{z}{i}$, and
$C_0:=\lambdaab{o}{\lambdaab{w}{C(z,i,j)}}$ with $w=\NatPair{\NatPair{z}{i}}{j}$.
For $w=\NatPair{z}{i}$ define
$$C_1:=\lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{C_0}\,o\,
 (\LambdaNumericPair\,w\,m)}}.$$
Finally define
$$\begin{aligned}
 M_P:=\lambdaab{o}{\lambdaab{z}{(Bo s)
 &\cdot\bigl(\LambdaRelativeProduct{A_P}\,o\,(\LambdaNumericPair\,z\,m)\bigr)\\
 &\cdot\bigl(\LambdaRelativeProduct{C_1}\,o\,(\LambdaNumericPair\,z\,m)\bigr)}}.
\end{aligned}$$
In each body, $m$ is extracted from its retained input $z$.

\begin{lemma*}[\termdefineas{finite derivative-test program}{Finite derivative-test program}]
The closed term $M_P$ decides $R_T(s,m,c,n,V)$ at the same parameter as $P$.
\end{lemma*}

\begin{proof}[Proof]
List access and every numerical comparison terminate. Each call of $B$ is a bounded product of
comparison bits, and each tree test is one call of $P$ on the extracted word code. Hence $A_P$
returns exactly the bit for its row. The inner product in $C_1$ checks every $j<m$ for the fixed
$i$; its outer product checks every $i<m$. These are exactly the distinctness conditions.
Multiplying by the binary test for $s$ and by all row bits gives precisely $R_T$. The bounded-product
reductions keep the same input function in every call. At bound zero they return one, and missing
table entries return the empty-word code, as stipulated in the definition.
\end{proof}

The construction is uniform in both the parameter and the tree. Fix the closed term $P$ first.
All selectors and numerical comparisons above are independent of the parameter. Boolean operations
combine the supplied decision bits, reindexing changes only their numerical arguments, and bounded
products repeat the same closed body with the same input function. Thus one term $M_P$ works for
every $\varepsilon$ and every $T$ whose membership is decided by $P$ at $\varepsilon$.
This is stronger than choosing a separate matrix program after each parameter has been fixed.

If $e$ is an index of $M_P$, apply the index transformations in §{sec:lambda-relative-jump}:
$$\upsilon(\xi(\upsilon(\xi(e)))).$$
The first pair removes $V,n$, and the second removes $c,m$. The resulting program uses four
successive jumps and decides the derivative-tree predicate proved in §{sec:edst-effective-cb}.

To compute a derivative-program index directly from a tree-program index, fix
$I:=\lambdaab{o}{o}$ and let $M$ be the finite matrix program constructed above
with $P=I$. For a tree $T$, let $\chi_T$ be the function on word codes that returns $1$ for
membership in $T$ and $0$ otherwise. At input function $\chi_T$, the term $I$ decides membership
in $T$, so $M$ decides the finite matrix. If $P_e$ decides membership in $T$ at $\varepsilon$,
it computes $\chi_T$ at that parameter. Substitution of this accessor therefore gives
$$A_e:=\lambdaab{o}{\lambdaab{z}{M\,(P_eo)\,z}},$$
which decides the same matrix at $\varepsilon$.

Choose a named representative $M_0$ of $M$ once. Let $Q_e$ be the closed named representative
of $P_e$ from §{sec:lambda-program-input-codes}, whose code is computed from $e$ by
$\LambdaProgramCode$. With $o=x_1$ and $z=x_2$, define
$$a(e):=\LambdaSyntaxCode{\lambdaab{x_1}{\lambdaab{x_2}{M_0\,(Q_ex_1)\,x_2}}}.$$
Starting from the fixed code of $M_0$ and the computed code of $Q_e$, apply the application-code
constructor three times and the abstraction-code constructor twice. Thus a closed numerical
lambda term computes $a$ on every natural number, even when $e$ decodes to an open term;
in that case the definition of $Q_e$ supplies the closed zero numeral. Decoding gives exactly
$A_e$, since both inserted terms are closed.

It follows that the required transformation of tree-program indices is
$$d(e):=\upsilon(\xi(\upsilon(\xi(a(e))))).$$
All five numerical transformations have closed lambda implementations, so their composition does
too. This supplies a computable choice of derivative indices, in addition to the uniform
existence of a derivative program for each fixed tree program.

Let closed terms $P,Q,C$ decide respectively the initial-tree predicate, the joint family predicate,
and the set of retained indices. The input to $Q$ is $\NatPair{b}{s}$, whereas the quantified matrix
uses $z=\NatPair{s}{b}$. Abbreviate
$$s(z):=\LambdaNumericProjection{1}\,z,\qquad b(z):=\LambdaNumericProjection{2}\,z.$$
Let $Z:=\lambdaab{x}{\LambdaZeroTest\,x\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$ reverse a decision bit,
and form
$$\begin{aligned}
 H&:=\lambdaab{o}{\lambdaab{z}{Qo(\LambdaNumericPair\,b(z)\,s(z))}},\\
 J&:=\lambdaab{o}{\lambdaab{z}{Z\bigl(\LambdaMul\,(Co\,b(z))\,(Z(Hoz))\bigr)}},\\
 M&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(Po\,s(z))\,(Joz)}}.
\end{aligned}$$
Expand these abbreviations with fresh binders. If $e$ is the syntax index of $M$, the program with
index $\upsilon(e)$ from §{sec:lambda-relative-jump} decides the guarded intersection at one jump.
This program is fixed before the input parameter is supplied.

\begin{proof}[Proof]
The projections and pairing term first recover the two input numbers and put them in the order
expected by the family decider. The given programs terminate on every input and return bits.
The term $J$ returns zero precisely when the index is retained and the family test fails.
Multiplication with the initial-tree bit therefore decides the matrix in
§{sec:edst-effective-cb}. Beta/query reductions lift through these applications, always retaining the
same input function. The universal-quantifier compiler proves the claimed jump bound. If the set
of retained indices is empty, the implication bit is always one and the result is just the initial
tree; no nonemptiness or witness-selection assumption is used.
\end{proof}

Fix a closed relative initial-tree program $P$ and pure numerical terms $K,I,\Delta$.
They respectively decide $b\in D\land bRa$ on $\NatPair{b}{a}$, compute the reader index $i(a)$,
and compute the derivative-program index $\delta(e)$. Decode
$w=\NatPair{q}{\NatPair{a}{\NatPair{s}{b}}}$ by numerical projections and abbreviate
$$\begin{aligned}
 B(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,a\,k)},\\
 C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
 L(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,
   (\Delta(\LambdaOutputSearch\,q\,b))\,s,\\
 V(o,w)&:=\LambdaZeroTest\,(K(\LambdaNumericPair\,b\,a))\,\ChurchNumeral{1}\,L(o,w),\\
 M&:=\lambdaab{o}{\lambdaab{w}{\LambdaMul\,(P(B(o,w))s)\,V(o,w)}}.
\end{aligned}$$
Expand all projections and abbreviations before abstraction, taking fresh binders for the reader
arguments. This defines a closed term; its two pair-specializations are $M_{q,a}$.

\begin{lemma*}[\termdefineas{guarded derivative-stage evaluation}{Guarded derivative-stage evaluation}]
Suppose $P_q$ computes a total index function $r$. Fix $a$ and an upper input function
$\varepsilon$. Assume row $a$ of the reader computes an input $\eta$ at which $P$ decides a
predicate $U(s)$. For each $b\in D$ with $bRa$, assume row $b$ computes an input $\eta_b$ at
which $P_{\delta(r(b))}$ decides $V_b(s)$. Then $M_{q,a}$ decides
$$U(s)\land\bigl(b\in D\land bRa\Longrightarrow V_b(s)\bigr)$$
on input $\NatPair{s}{b}$ at $\varepsilon$.
\end{lemma*}

\begin{proof}[Proof]
For each query numeral, the first reader supplies the value of $\eta$. Input substitution therefore
reduces the first factor to the decision bit for $U(s)$. If the predecessor test returns zero,
the zero test returns one without executing $L$. Otherwise, pure universal evaluation supplies
$r(b)$, and the numerical derivative compiler supplies $\delta(r(b))$. Substituting the second
reader for each input query in that program gives its decision bit for $V_b(s)$. Multiplication
of the two bits gives the displayed conjunction. All invoked computations terminate by the
hypotheses; no lower program is executed outside the predecessor set. Pair-specialization
preserves these beta/query reductions.
\end{proof}

The self-indexed universal-family construction applied to this $M$ produces the total index
function $r$. In §{sec:edst-effective-cb}, the five-jump readers and well-founded induction verify
the hypotheses of the lemma at every stage. The final universal quantifier costs one jump of
the common upper input.

\begin{proposition*}[\termdefineas{uniform Cantor stage-template indices}{Uniform Cantor stage-template indices}]
Fix the closed derivative-index compiler $\Delta$. There are total computable maps
$\Tuple{p,c,i}\mapsto m(p,c,i)$, $\Tuple{p,c,i}\mapsto q_0(p,c,i)$, and $\Tuple{p,c,i,a}\mapsto r_0(p,c,i,a)$.
For every triple, $P_{q_0(p,c,i)}$ computes $a\mapsto r_0(p,c,i,a)$.
Suppose $p,c,i$ are syntax codes of closed terms, and $P_c,P_i$ compute total numerical functions.
Then $m(p,c,i)$ codes the closed composite stage program $M$ above with
$P=P_p$, $K=P_c$, and $I=P_i$.
If its specialization $M_{q_0(p,c,i),a}$ decides $N(s,b)$ on input $\NatPair{s}{b}$ at $\varepsilon$,
then $P_{r_0(p,c,i,a)}$ decides $\forall b\,N(s,b)$ at $\varepsilon'$.
Code generation neither executes the supplied programs nor tests their termination.
\end{proposition*}

\begin{proof}[Proof]
Replace the initial-tree program, predecessor test, and reader-index program in the composite template by three
fresh free variables. Keep the derivative compiler fixed and choose one named representative of this open template.
Successive capture-avoiding substitutions of the three decoded inputs compute $m(p,c,i)$. For closed inserted
terms, substitution commutes with the displayed composition, input-substitution, and conditional constructors;
their fresh binders cannot capture the inserted terms. Thus the result is precisely the composite stage program.
The closure lemmas for these constructors show that it is closed under the stated hypotheses.

Let $q,r$ be the uniform self-indexed universal-family maps from §{sec:lambda-rank-decision-programs}. Put
$$\begin{aligned}
q_0(p,c,i)&:=q(m(p,c,i)),\\
r_0(p,c,i,a)&:=r(m(p,c,i),a).
\end{aligned}$$
Numerical composition proves totality of both maps on all inputs. The self-indexed family theorem supplies the
stated numerical computation for every triple and the conditional decision assertion for the closed matrix.
These computations construct syntax; they run neither a tree test nor a lower-stage program.
\end{proof}

The predecessor-test index can itself be obtained from decision-program indices $d,t$. Compose the domain
program with the first numerical projection and multiply its output by the relation program's output.
For correct bit deciders this is one exactly when the first number belongs to the domain and precedes the second.
Fix this two-variable template once. Two successive syntax substitutions give a total index map $\kappa(d,t)$
for the predecessor test. No well-foundedness test is part of this construction.

For the five-jump reader, fix a named representative of the joint reader-index program from
§{sec:edst-borel-rank-layers}, with code $h$. It receives $\NatPair{\NatPair{d}{t}}{\NatPair{k}{a}}$.
Two numerical parameter insertions give
$$\iota(d,t):=p\bigl(p(h,\NatPair{d}{t}),5\bigr).$$
The program $P_{\iota(d,t)}$ computes $a\mapsto i(d,t,5,a)$ on every natural-number input, for every pair $d,t$.
The decision and well-order hypotheses are needed for the reader's interpretation, not for this index computation.

Use $B_n,C_P,V_P$ from §{sec:lambda-borel-constructor-programs} and put $E:=C_{B_0}$, the label
program for the empty expression. For numerical arguments abbreviate
$$B(n,w):=\LambdaLeCase{w}{\ChurchNumeral{0}}
 {\LambdaAdd\,n\,\ChurchNumeral{3}}{\ChurchNumeral{0}}.$$
This jointly computes the label of leaf $n$ at address code $w$. Let $H$ be the pure numerical selector
$$H:=\lambdaab{v}{\LambdaLeCase{\LambdaNumericProjection{1}v}{\ChurchNumeral{0}}
 {\LambdaNumericProjection{1}(\LambdaNumericProjection{2}v)}
 {\LambdaNumericProjection{2}(\LambdaNumericProjection{2}v)}}.$$
Thus on $\NatPair{c}{\NatPair{x}{y}}$ it returns $x$ when $c=0$, and $y$ otherwise.

Let $P,Q$ be the tree decision programs. Decode $z=\NatPair{n}{w}$ by projections and define
$$\begin{aligned}
 J_P&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,(Po\,n)\,
   (\LambdaNumericPair\,B(n,w)\,(Eo\,w)))}},\\
 O_P&:=V_{J_P},\qquad F_P:=C_{O_P},\\
 R_{P,Q}&:=\lambdaab{o}{\lambdaab{z}{H(\LambdaNumericPair\,n\,
   (\LambdaNumericPair\,(O_Po\,w)\,(F_Qo\,w)))}},\\
 D_{P,Q}&:=C_{V_{R_{P,Q}}}.
\end{aligned}$$
Expand the projections and abbreviations with fresh binders. The resulting terms are closed and
depend only on the supplied programs. They do not select a program separately for each tree or
input parameter.

\begin{lemma*}[\termdefineas{tree Borel-label programs}{Tree Borel-label programs}]
If $P,Q$ decide the binary trees $T,S$ at $\varepsilon$, then $O_P,F_P,D_{P,Q}$ compute the label
maps of $O_T,C_T,D_{T,S}$, respectively, at $\varepsilon$.
\end{lemma*}

\begin{proof}[Proof]
The numerical projections recover the leaf index and address. The tree decision and both candidate
labels terminate; pairing their outputs and applying $H$ selects the empty label for an accepted
word and the cylinder label for a rejected word. Thus $J_P$ computes the joint labels of the family
$e^T_n$. The union and complement constructor equations give the assertions for $O_P,F_P$.
In $R_{P,Q}$ the selector uses the child index: zero selects the first expression, and every positive
index selects the second. A union followed by complementation gives the difference expression.
All numerical steps are beta reductions, and every tree or label call retains the same input
function. No evaluation of membership in an arbitrary Borel set is used.
\end{proof}

\begin{proposition*}[\termdefineas{uniform tree Borel-label indices}{Uniform tree Borel-label indices}]
There are total computable maps $f(p)$, $d(p,q)$, and $u(p)$ whose outputs code closed programs,
with
$$\begin{aligned}
P_{f(p)}&=F_{P_p},\\
P_{d(p,q)}&=D_{P_p,P_q},\\
P_{u(p)}&=\lambdaab{o}{P_p(\lambdaab{n}{\ChurchNumeral{0}})}.
\end{aligned}$$
Thus the first two maps turn decision-program indices into label-program indices whenever the
input programs decide trees. The last map turns a tree decider at the constant-zero parameter
into a decider at any parameter, by ignoring that parameter. All three index maps are total even
when the supplied programs fail to decide trees.
\end{proposition*}

\begin{proof}[Proof]
Let $M_p$ be the named term decoded from $p$ if that term is closed, and the fixed named zero
numeral otherwise. Its code is computed by $\LambdaProgramCode$, and its alpha-class is $P_p$.
Fix named representatives $M,N,U$ of the three templates
$$F_{x_{86}},\qquad D_{x_{86},x_{87}},\qquad
\lambdaab{o}{x_{86}(\lambdaab{n}{\ChurchNumeral{0}})},$$
using binders different from the placeholder variables. Define
$$\begin{aligned}
N_p&:=\SubstLambda{N}{x_{86}}{M_p},\\
f(p)&:=\LambdaSyntaxCode{\SubstLambda{M}{x_{86}}{M_p}},\\
d(p,q)&:=\LambdaSyntaxCode{\SubstLambda{N_p}{x_{87}}{M_q}},\\
u(p)&:=\LambdaSyntaxCode{\SubstLambda{U}{x_{86}}{M_p}}.
\end{aligned}$$
The syntax-substitution generators of §{sec:lambda-index-recursion} compute these maps by beta
reduction. Closed substitutions commute with the displayed program constructors, so decoding
gives the asserted alpha-classes. No placeholder remains free. The representatives are fixed
before the input numbers; the finite closedness test and substitutions never run the input programs.
The preceding label-program lemma proves correctness of the first two generated programs. For the
last, substitute the constant-zero function into the original beta/query derivation. Every query
is then answered by beta reduction, and the unused outer input may be arbitrary.
\end{proof}

### Programs for arithmetic normal form {#sec:lambda-arithmetic-normal-form-programs}

\begin{mathmeta}
  \vars{q,x,y,\varepsilon}{Name}
  \vars{k,n,u,z}{Nat}
  \vars{s,t}{Seq(Nat)}
\end{mathmeta}

To compute the finite word whose entries are $\NatPair{n}{s(k)}$, take
$z=\NatPair{n}{\LambdaListCode{s}}$ and use the following closed numerical terms:
$$\begin{aligned}
F&:=\lambdaab{v}{\LambdaNumericPair\,
 (\LambdaNumericProjection{1}(\LambdaNumericProjection{1}v))\,
 (\LambdaListGet(\LambdaNumericPair\,
   (\LambdaNumericProjection{2}(\LambdaNumericProjection{1}v))\,
   (\LambdaNumericProjection{2}v)))},\\
W&:=\lambdaab{z}{\LambdaListTabulate{F}\,
 (\LambdaNumericPair\,z\,(\LambdaListLength(\LambdaNumericProjection{2}z)))}.
\end{aligned}$$
For the joint tree input $u=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
abbreviate $n=\LambdaNumericProjection{1}u$, $a=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}u)$,
and $b=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}u)$. If $P$ decides the original tree,
expand these abbreviations in
$$J:=\lambdaab{o}{\lambdaab{u}{Po(\LambdaNumericPair\,(W(\LambdaNumericPair\,n\,a))\,b)}}.$$

\begin{proof}[Proof]
On input $\NatPair{z}{k}$, the term $F$ returns $\NatPair{n}{s(k)}$ for every position in range.
Finite tabulation runs it at exactly the positions below the length of $s$, so $W$ returns the
code of the word obtained by pairing $n$ with each entry. The term $J$ retains the second word and
passes the transformed node to $P$. Every component terminates and the input parameter is unchanged.
Thus one program decides the whole family of numerical sections, including the empty word case.
\end{proof}

For the converse normal-form construction, write $\NumberBinding{n}{y}(k):=\NatPair{n}{y(k)}$.
The input name is
$\NamePair{\varepsilon}{\NumberBinding{n}{\NamePair{x}{q}}}$. Define the accessors
$$\begin{aligned}
D(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}(ok)},\\
N(o)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
X(o)&:=\lambdaab{k}{\LambdaNumericProjection{1}
 (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))},\\
Y(o)&:=\lambdaab{k}{\LambdaNumericProjection{2}
 (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(ok)))}.
\end{aligned}$$
Using the finite-prefix reader, the closed row program is
$$K:=\lambdaab{o}{\lambdaab{r}{P(D(o))(\LambdaNumericPair\,
 (\LambdaInputPrefix\,(X(o))\,(N(o)))\,
 (\LambdaInputPrefix\,(Y(o))\,(N(o))))}}.$$
Expand the accessors with fresh binders. The auxiliary numerical argument $r$ is unused.

\begin{proof}[Proof]
The paired-input equations show that $D,X,Y$ supply the parameter and the two sequences, while
$N$ returns the bound number. The finite-prefix lemma therefore supplies exactly the two list codes
for the first $n$ entries. Numerical pairing and substitution give the original tree decider its
node code and its original parameter. This proves termination and both decision values by the
same beta/query derivations. Quantifying over the bound number gives exactly the branch predicate.
Reversing atomic decision bits and combining the presentations by the preceding countable-operation
programs proves the forward construction for every finite arithmetic formula.
\end{proof}

### Programs for comparison trees {#sec:lambda-comparison-programs}

\begin{mathmeta}
  \vars{a,b,i,j,n,u,v,w,z}{Nat}
  \vars{s}{Seq(Nat)}
  \vars{x}{Name}
\end{mathmeta}

Here we give the programs used for effective separation. A pair tree is a downward-closed set of equal-length
pairs of finite words. Its section at $x$ consists of the words $s$ with $\Pair{\restrict{x}{\Length{s}}}{s}$ in the
tree,
with the empty word added. Suppose closed programs $P_T,P_S$ decide two families of pair trees at the same
parameter, on input $\NatPair{i}{\NatPair{a}{b}}$, where $a,b$ are word codes. In this subsection,
expand all abbreviations before abstraction and choose fresh binders. The symbol $Z$ denotes the numerical
zero test returning one on zero and zero otherwise.

Use the following numerical bodies and Boolean operations on bits:
$$\begin{aligned}
\ell(a)&:=\LambdaListLength\,a,\\
m(b,u)&:=\LambdaListGet(\LambdaNumericPair\,b\,u),\\
p(u,v)&:=\LambdaListPrefix(\LambdaNumericPair\,u\,v),\\
L(u,v)&:=\LambdaLeCase{u}{v}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
K(u,v)&:=L(\LambdaSucc\,u,v),\\
B(d,e)&:=Z(\LambdaMul\,d\,(Ze)),\\
O(d,e)&:=Z(\LambdaMul\,(Zd)\,(Ze)).
\end{aligned}$$
When $b$ codes a list of image-word codes, the body $m(b,u)$ computes the Church numeral for the selected
image-word code; no word decoder is needed inside the program.
The bodies $B$ and $O$ compute implication and disjunction. Juxtaposed multiplication of bits below
means repeated application of $\LambdaMul$.

For a family decider $P$, the finite section decision is the body
$$\begin{aligned}
A_P(o,i,a,u)&:=O\bigl(Zu,Po\,k(i,a,u)\bigr),\\
k(i,a,u)&:=\LambdaNumericPair\,i\,
 \bigl(\LambdaNumericPair\,(\LambdaListTake(\LambdaNumericPair\,a\,\ell(u)))\,u\bigr).
\end{aligned}$$
It accepts the empty word and otherwise queries the tree on the point prefix of the word's length.
All calls terminate even if the two supplied words have different lengths. Fix a root-test term
$r=Z$ or $r=\lambdaab{u}{Z(Zu)}$, for an empty or nonempty image root respectively.

For the following bodies extract $z=\NatPair{i}{\NatPair{a}{b}}$ by numerical projections and put
$n=\ell(a)$. In the edge body the input is $v=\NatPair{w}{j}$ with $w=\NatPair{z}{u}$:
$$\begin{aligned}
E(o,z,u,j)&:=B\bigl(K(j,n)\,p(j,u)\,K(\ell(j),\ell(u)),\\
 &\quad p(m(b,j),m(b,u))\,K(\ell(m(b,j)),\ell(m(b,u)))\bigr),\\
V&:=\lambdaab{o}{\lambdaab{v}{E(o,z,u,j)}}.
\end{aligned}$$
The products here are products of bits, not applications of one bit to another. The body checks precisely
the guarded strict-edge obligation for the words coded by $u,j$.

For the node body, with input $w=\NatPair{z}{u}$, define
$$\begin{aligned}
G(o,z,u)&:=K(u,n)\,L(\ell(u),n)\,A_{P_T}(o,i,a,u),\\
H(o,z,u)&:=B\bigl(L(\ell(m(b,u)),n),A_{P_S}(o,i,a,m(b,u))\bigr),\\
J(o,w)&:=\LambdaRelativeProduct{V}\,o\,(\LambdaNumericPair\,w\,n),\\
U&:=\lambdaab{o}{\lambdaab{w}{B\bigl(G(o,z,u),H(o,z,u)\,J(o,w)\bigr)}},\\
Q_r&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,
 B(K(\ChurchNumeral{0},n),r(m(b,\ChurchNumeral{0})))\\
 &\hspace{27mm}(\LambdaRelativeProduct{U}\,o\,(\LambdaNumericPair\,z\,n))}}.
\end{aligned}$$
The symbols $i,a,b,n,z,u,j$ in these expressions always abbreviate projections or numerical computations
from the current input. After expansion the displayed programs are closed.

\begin{proposition*}[Decision programs for comparison trees]
The program $Q_r$ decides the finite comparison test $R_r$ with the same parameter and family index.
Applying the finite-test tree program gives a joint decider for $C_r(T_i,S_i)$.
\end{proposition*}

\begin{proof}[Proof]
List access gives the correct image code, and the finite section body agrees with $R_T$.
The comparisons and Boolean operations therefore give exactly the root, image-membership, and edge
conditions. The inner bounded product ranges over $j<n$, and the outer one over $u<n$; the word code
bijection turns these into precisely the two loops of the comparison test. Every component is total, so
both products terminate, including at length zero when they return one. The outer root guard also returns
one at length zero. Prefix closure is imposed afterwards by the finite-test tree construction, which
checks all shorter prefixes as well. The family index remains input data throughout, so specialization
provides total lambda-computed indices without deciding whether the input projections are disjoint.
\end{proof}

## Graphs and Effective Refinements {#sec:lambda-graph-refinement-programs}

### Closed Graphs and Preimage Tests {#sec:lambda-closed-graph-indices}

\begin{mathmeta}
  \vars{s}{Seq(Nat)}
  \vars{e,i,j,k,m,n,r,u,v,z}{Nat}
  \vars{o}{Name}
  \vars{\alpha_+,\alpha_-,c,d}{Fun(Prod(Nat,Nat),Nat)}
\end{mathmeta}

The graph-row tester of §{sec:lambda-graph-tests} can receive the program index as numerical data.
For input $z=\NatPair{e}{\NatPair{i}{\NatPair{u}{v}}}$, regard $u$ as the output-word code and
$v$ as the input-word code. The universal tester needs the input digit first in each digit pair, so the
digit-pairing term receives $v,u$.
Extract all fields by projections, write
$i=\NatPair{n}{\NatPair{m}{r}}$, and put
$$\begin{aligned}
\LambdaTermName{pairedDigits}(z)&:=\LambdaListPair(\LambdaNumericPair\,v\,u),\\
\LambdaTermName{queryDigit}(o,z,k)&:=\LambdaNumericPair\,(ok)\,
  \bigl(\LambdaNumericProjection{1}(\LambdaListGet(\LambdaNumericPair\,\LambdaTermName{pairedDigits}(z)\,k))\bigr),\\
\LambdaTermName{rowCandidate}(o,z)&:= \LambdaQueryOutputCandidate\,( \lambdaab{k}{
\LambdaTermName{queryDigit}(o,z,k)})\,e\,n\,
  (\LambdaNumericPair\,m\,r),\\
\LambdaTermName{rowEqual}(z)&:=\LambdaEqual\,
  \bigl(\LambdaNumericProjection{2}(\LambdaListGet(\LambdaNumericPair\,\LambdaTermName{pairedDigits}(z)\,n))\bigr)\,m.
\end{aligned}$$
The row requires the implication from the candidate bit to the equality bit. Bit implication is
computed by the Boolean constructions of §{sec:lambda-comparison-programs}. Expand the fields
and use fresh binders. Every operation terminates on every finite input: the candidate test checks
bounded evidence rather than running the indexed program until it stops.

\begin{lemma*}[\termdefineas{uniform closed-graph row tests}{Uniform closed-graph row tests}]
The graph rows are decidable jointly in the map index, row number, and finite prefix pair.
Keeping a numerical family index in the bounded-prefix construction preserves this uniformity.
Consequently the conjunction of the domain-tree test and all applicable graph rows has a single
relative lambda decider, fixed before the map and domain indices are supplied.
\end{lemma*}

\begin{proof}[Proof]
List pairing and list access supply the two padded coordinate words. Input substitution supplies
the paired parameter and input digits to the universal finite-candidate tester, while the numerical
projections supply the program index and proposed output data. The equality test and Boolean
implication then give the row bit. In the bounded-prefix loop, retain the family index alongside
the word pair when forming each row query; truncate both words to the row's prescribed bound.
A relative bounded product combines the finitely many bits. Finally apply the finite-check-tree
construction. Each query uses the original parameter, and every finite node requires only finitely
many terminating tests. Specializing this joint decider gives the graph-index generator.
\end{proof}

Use $p,K,O,Z, \ell$ from §{sec:lambda-comparison-programs}. Keep the output-first, input-second tree order. For
a prefix code $j$ and an input-word code $v$, put
$$\begin{aligned}
\LambdaTermName{prefixGate}_+(j,v)&:=O\bigl(p(j,v),p(v,j)\bigr),\\
\LambdaTermName{prefixGate}_-(j,v)&:=O\bigl(K(\ell(v),\ell(j)),Zp(j,v)\bigr).
\end{aligned}$$
The first tests prefix compatibility. The second accepts a word shorter than the supplied prefix,
or a word that does not extend it. Let $P$ be the fixed joint decider for the indexed pair trees.
From $z=\NatPair{\NatPair{e}{j}}{\NatPair{u}{v}}$ extract its four numerical fields by projections and set
$$\LambdaTermName{slice}_\pm:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,
 \bigl(Po(\LambdaNumericPair\,e\,(\LambdaNumericPair\,u\,v))\bigr)\,\LambdaTermName{prefixGate}_\pm(j,v)}}.$$
Expand the abbreviations with fresh binders. Check equal lengths and apply the finite-check-tree
construction to this test: it checks every simultaneous prefix, including the empty pair.
This gives two jointly decidable tree families. Specializing their fixed joint deciders produces
total index maps $\alpha_+(e,j),\alpha_-(e,j)$. If $\operatorname{sep},\operatorname{co}$ are the two separation
index maps, use
$$\begin{aligned}
c(e,j)&:=\operatorname{sep}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr),\\
d(e,j)&:=\operatorname{co}\bigl(\alpha_+(e,j),\alpha_-(e,j)\bigr).
\end{aligned}$$

\begin{lemma*}[\termdefineas{preimage prefix slice programs}{Preimage prefix slice programs}]
The positive tree has body $[T_e]\cap(\BaireSpace\times\cyl{s})$, and the negative tree has body
$[T_e]\cap(\BaireSpace\times(\cyl{s})^{\complement})$, where $j=\LambdaListCode{s}$.
Both tree deciders terminate on all finite inputs for every tree index and word code.
\end{lemma*}

\begin{proof}[Proof]
The indexed family decider, list lengths, prefix comparisons, and bit operations are total.
The finite-check construction therefore terminates and enforces all tests along a branch.
Compatibility with every finite prefix of a sequence is equivalent to membership in the cylinder.
For the negative test, a sequence outside the cylinder never extends its defining word, so every
test accepts. A sequence in the cylinder fails the test as soon as the defining length is reached.
Thus the two branch conditions are precisely the asserted restrictions. No uniqueness or
nonemptiness test occurs in either decider or in the numerical specialization maps.
\end{proof}

### Images, Inverses, and Refinements {#sec:lambda-lusin-image-programs}

\begin{mathmeta}
  \vars{a,b,e,i,j,k,n,r,v,w,x,z}{Nat}
  \vars{a_*,c_*,d_*}{Nat}
  \vars{s,t_*,\sigma,\tau}{Seq(Nat)}
  \vars{y,\varepsilon}{Name}
  \vars{\nu,\varphi}{Fun(Nat,Nat)}
  \vars{c,d}{Fun(Prod(Nat,Nat),Nat)}
\end{mathmeta}

\begin{lemma*}[\termdefineas{uniform finite-prefix atom presentations}{Uniform finite-prefix atom presentations}]
Suppose $\Phi(i,s)$ is decidable jointly in the number and finite word at $\varepsilon$, and $\nu(i)$ is
a total computable numerical bound. The sets
$$D_i:=\{y:\Phi(i,\restrict{y}{\nu(i)})\}$$
and their complements have pair-tree presentations with jointly decidable finite-node tests.
Their indices can therefore be generated by total computable functions of $i$.
\end{lemma*}

\begin{proof}[Proof]
Let $\LambdaTermName{atomPredicate}$ decide the predicate and let $\LambdaTermName{boundProg}$ compute the
bound. On numerical input
$z=\NatPair{i}{\NatPair{\LambdaListCode{\sigma}}{\LambdaListCode{\tau}}}$, write
$$\begin{aligned}
\LambdaTermName{atomIndex}(z)&:=\LambdaNumericProjection{1}z,\\
\LambdaTermName{pointWord}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
\LambdaTermName{bound}(z)&:=\LambdaTermName{boundProg}(\LambdaTermName{atomIndex}(z)),\\
\LambdaTermName{enoughPrefix}(z)&:= \LambdaLeCase{ \LambdaTermName{bound}(z)}{ \LambdaListLength\,
\LambdaTermName{pointWord}(z)}{ \ChurchNumeral{1}}{ \ChurchNumeral{0}},\\
\LambdaTermName{atomInput}(z)&:=\LambdaNumericPair\,\LambdaTermName{atomIndex}(z)\,
 (\LambdaListTake(\LambdaNumericPair\,\LambdaTermName{pointWord}(z)\,\LambdaTermName{bound}(z))).
\end{aligned}$$
With the bit negation $Z$ of §{sec:lambda-projection-programs}, use
$$\begin{aligned}
&\LambdaTermName{atomTest}:=\\
&\quad \lambdaab{o}{ \lambdaab{z}{Z( \LambdaMul\, \LambdaTermName{enoughPrefix}(z)\,(Z(
\LambdaTermName{atomPredicate}o( \LambdaTermName{atomInput}(z)))))}}.
\end{aligned}$$
Expand the abbreviations and choose fresh binders. This program decides
$\nu(i)\le\Length{\sigma}\Rightarrow \Phi(i,\restrict{\sigma}{\nu(i)})$. Apply the finite-check-tree construction.
On a branch, the test at length $\nu(i)$ forces the desired condition, and every later prefix tests
the same word. Earlier prefixes impose no condition. The second branch coordinate is unrestricted,
so the projection is exactly the required set. Replace the decision bit of the predicate by its
negation to present the complement. All bounds, truncations, and decision calls are finite and total.
The case of bound zero checks the empty prefix. A numerical guard independent of the point is
obtained by ignoring the word and using bound zero.
\end{proof}

For the image construction of §{sec:edst-effective-ls}, retain the graph index in every numerical
input. Write $t_j$ for the unique finite word with code $j$. From the preceding separation indices set
$$C_s:=\pi_0([T_{c(e,\LambdaListCode{s})}]),\qquad
C'_s:=\pi_0([T_{d(e,\LambdaListCode{s})}]).$$
Construct the first and coherent prefix tests, together with their negative counterparts, by
$$\begin{aligned}
B_s&:=\SetDifference{C_s}{\bigcup_{\substack{j<\LambdaListCode{s}\\\Length{t_j}=\Length{s}}}C_{t_j}},\\
B_s^-&:=C'_s\cup\bigcup_{\substack{j<\LambdaListCode{s}\\\Length{t_j}=\Length{s}}}C_{t_j},\\
H_s&:=\bigcap_{0\le k\le\Length{s}}B_{\restrict{s}{k}},\\
H_s^-&:=\bigcup_{0\le k\le\Length{s}}B_{\restrict{s}{k}}^-.
\end{aligned}$$
The negative tests are complements of the corresponding positive tests whenever the separated
input presentations are complementary. All families are nevertheless constructed on every numerical
input. The index generator does not check that hypothesis.

The numerical transformations in these finite combinations are
$$\begin{aligned}
\NatPair{\NatPair{e}{j}}{k}&\longmapsto\NatPair{e}{k},\\
\NatPair{\NatPair{e}{j}}{k}&\longmapsto
 \NatPair{e}{\LambdaListCode{\restrict{t_j}{k}}}.
\end{aligned}$$
Pair projections, list length, list truncation, and numerical comparisons compute these transformations
and their guards. For a bounded intersection use the whole space outside the bound; for a bounded
union use the empty set there. The parameter-preserving countable programs then implement both
bounded operations. The finite-prefix lemma supplies both presentations of
$$D_{e,s}:=\{y:\Pair{\restrict{y}{\Length{s}}}{s}\in T_e\}.$$
Its predicate is the joint finite-node decider for the indexed trees, with the graph index and the
word code supplied as numerical data.

Finally set
$$\begin{aligned}
R_{e,n,s}^+&:=\begin{cases}H_s\cap D_{e,s},&\Length{s}=n,\\\emptyset,&\Length{s}\ne n,\end{cases}\\
R_{e,n,s}^-&:=\begin{cases}H_s^-\cup D_{e,s}^{\complement},&\Length{s}=n,\\\BaireSpace,&\Length{s}\ne n,\end{cases}\\
A_e^+&:=\bigcap_{n\in\NN}\bigcup_{j\in\NN}R_{e,n,t_j}^+,\\
A_e^-&:=\bigcup_{n\in\NN}\bigcap_{j\in\NN}R_{e,n,t_j}^-.
\end{aligned}$$
The length guard and both countable operations preserve joint finite-node decidability, including
the outer graph index. The image formula gives the positive set, and complementarity of the input
prefix tests gives the negative set. The inverse prefix sets and their negative presentations are
$$A_e^+\cap C_s,\qquad A_e^-\cup C'_s.$$
Specialize the four joint programs and substitute the graph index computed from the map and domain
indices. This is the index construction used in the uniform effective Lusin--Suslin theorem.

Let the closed term $\LambdaTermName{wordMap}$ compute the numerical word transformation $\varphi$. To retain a
family index, use the closed wrapper
$$\LambdaTermName{keepIndex}:= \lambdaab{ \LambdaTermName{mapArg}}{ \lambdaab{z}{ \LambdaNumericPair\,(
\LambdaNumericProjection{1}z)\,
 (\LambdaTermName{mapArg}(\LambdaNumericProjection{2}z))}}.$$
If $z= \NatPair{i}{w}$, then $\LambdaTermName{keepIndex} \LambdaTermName{wordMap}$ sends its numeral to the
numeral for $\NatPair{i}{ \varphi(w)}$.
Thus a joint tree decider $\LambdaTermName{familyPredicate}$ is reindexed by $\lambdaab{o}{ \lambdaab{z}{
\LambdaTermName{familyPredicate}o( \LambdaTermName{keepIndex} \LambdaTermName{wordMap}z)}}$ without changing its
parameter.
Apply this wrapper to the word operations for coordinatewise inverse images, witness intersections,
and coordinate projections. For projection, apply the finite-test construction after reindexing.
This supplies the joint family deciders used for relational-image and invalid-code indices.

For the binary union of two jointly decidable families, let $\LambdaTermName{leftFamily}$,
$\LambdaTermName{rightFamily}$ be their closed decision programs.
Write $z=\NatPair{i}{\NatPair{k}{w}}$, with these letters abbreviating numerical projections in the
following bodies. Let $Z$ be the numerical zero test from §{sec:lambda-projection-programs},
and put
$$\begin{aligned}
\LambdaTermName{firstChoice}(z)&:=Zk,\qquad \LambdaTermName{familyInput}(z):=\LambdaNumericPair\,i\,w,\\
\LambdaTermName{leftBit}(o,z)&:= \LambdaMul\, \LambdaTermName{firstChoice}(z)\,( \LambdaTermName{leftFamily}o(
\LambdaTermName{familyInput}(z))),\\
\LambdaTermName{rightBit}(o,z)&:= \LambdaMul\,(Z( \LambdaTermName{firstChoice}(z)))\,(
\LambdaTermName{rightFamily}o( \LambdaTermName{familyInput}(z))),\\
\LambdaTermName{unionRow}&:= \lambdaab{o}{ \lambdaab{z}{Z( \LambdaMul\,(Z( \LambdaTermName{leftBit}(o,z)))\,(Z(
\LambdaTermName{rightBit}(o,z))))}}.
\end{aligned}$$
On numerical input this returns the decision for the first family when $k=0$ and for the second
otherwise. Both supplied deciders terminate, so evaluating both branches causes no difficulty.
Next retain $i$ while applying the union input transformation $K_U$ to the node code $w$, and run
$\LambdaTermName{unionRow}$ on the resulting triple. Take the Boolean disjunction with the test that the witness
word is empty,
then apply the finite-test construction. Its body uses the head of the witness to select a family and
its tail as the selected witness. This gives a joint tree decider for the binary union, including empty
trees. Together with the index-retaining intersection, projection, and nonemptiness programs, it
supplies every family operation in the Silver and HKL kernel tests.

For invariant separation, let closed numerical programs $\LambdaTermName{separatorIndex}$,
$\LambdaTermName{complementIndex}$, $\LambdaTermName{saturationIndex}$ compute the separator index, its
complementary index, and the saturation index. Fix input indices $a,b$. With distinct fresh binders,
define the following terms, expanding all abbreviations before abstraction:
$$\begin{aligned}
\LambdaTermName{nextIndex}&:= \lambdaab{v}{ \LambdaTermName{saturationIndex}( \LambdaTermName{separatorIndex}(
\LambdaNumericPair\,v\, \ChurchNumeral{b}))},\\
\LambdaTermName{initialIndex}&:=\lambdaab{x}{\ChurchNumeral{a}},\\
\LambdaTermName{previousInput}&:= \lambdaab{v}{ \LambdaTermName{nextIndex}( \LambdaNumericProjection{2}(
\LambdaNumericProjection{2}v))},\\
\LambdaTermName{iterationStep}&:= \lambdaab{x}{ \lambdaab{k}{ \lambdaab{r}{ \LambdaTermName{previousInput}(
\LambdaNumericPair\,x\,( \LambdaNumericPair\,k\,r))}}},\\
\LambdaTermName{iterate}&:= \lambdaab{n}{ \LambdaParamRec{ \LambdaTermName{initialIndex}}{
\LambdaTermName{iterationStep}}\, \ChurchNumeral{0}\,n},\\
\LambdaTermName{positiveStage}&:= \lambdaab{n}{ \LambdaTermName{separatorIndex}( \LambdaNumericPair\,(
\LambdaTermName{iterate}n)\, \ChurchNumeral{b})},\\
\LambdaTermName{negativeStage}&:= \lambdaab{n}{ \LambdaTermName{complementIndex}( \LambdaNumericPair\,(
\LambdaTermName{iterate}n)\, \ChurchNumeral{b})}.
\end{aligned}$$
The two projections in $\LambdaTermName{previousInput}$ recover the previous value from the coded
parameter-counter-value triple.
Thus $\LambdaTermName{iterationStep}$ ignores the dummy parameter and counter and applies
$\LambdaTermName{nextIndex}$ to that value. Numerical currying
and uncurrying give these same computations when the recursor is implemented on paired inputs.

\begin{proposition*}[Programs for the invariant-separation stages]
The terms $\LambdaTermName{iterate}$, $\LambdaTermName{positiveStage}$, $\LambdaTermName{negativeStage}$ compute the
indices $a_n,c_n,d_n$ in the invariant-separation proof, on every input
numeral $n$. Consequently both tree families used in the final union and complementary intersection
have joint decision programs at the original parameter.
\end{proposition*}

\begin{proof}[Proof]
The numerical pairing and projection equations give
$$\LambdaTermName{iterationStep} \ChurchNumeral{0}\,
\ChurchNumeral{k}\,
\ChurchNumeral{r}\to_\beta^*\LambdaTermName{nextIndex}\ChurchNumeral{r}.$$
The initial value is $\ChurchNumeral{a}$.
The parameterized recursor theorem therefore proves by induction that $\LambdaTermName{iterate}
\ChurchNumeral{n}$ returns
$\ChurchNumeral{a_n}$. Totality of $\LambdaTermName{separatorIndex}$, $\LambdaTermName{saturationIndex}$ gives
termination at every successor stage. Composition gives
the outputs of $\LambdaTermName{positiveStage}$, $\LambdaTermName{negativeStage}$, and reindexing the uniform tree
decider by these terms gives the claimed joint
family deciders. Invariance and disjointness are used in the set-theoretic proof of separation; neither
is a condition that these programs test.
\end{proof}

To reverse a coded pair, use the closed numerical term
$$\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,(\LambdaNumericProjection{1}z)}.$$
On the numeral for a numerical pair it returns the numeral for the reversed pair, by the two projection
equations and the pairing equation. Mapping this operation over the first finite word of a pair-tree
node, while leaving its witness word unchanged, gives the inverse-image tree for the swapped relation.
Thus replacing a directed edge also supplies the presentation for its reverse.

For a fixed finite path with $k$ edges, let the closed numerical terms $\LambdaTermName{edgeMap}_0$, $\ldots$,
$\LambdaTermName{edgeMap}_{k-1}$ compute
the relational-image index transformations of its successive directed edges. Put
$$\begin{aligned}
&\LambdaTermName{pathStage}_0:=\lambdaab{e}{e},\\
&\LambdaTermName{pathStage}_{j+1}:= \lambdaab{e}{ \LambdaTermName{edgeMap}_j( \LambdaTermName{pathStage}_j e)}
\quad(0 \le j<k).
\end{aligned}$$
Expand the supplied closed terms and choose fresh binders. Induction on the path length proves that
$\LambdaTermName{pathStage}_j$ computes the index of the set obtained after the first $j$ propagation steps.
Each step terminates
on every numerical input, so the composite is total, including the identity program for a path of length
zero. The path and edge presentations are fixed finite data in this assertion. Choosing dense refinements
through infinitely many levels remains the existence construction described in the main text.

## Compiling Metric Realizers {#sec:lambda-metric-realizer-programs}

\begin{mathmeta}
  \vars{s}{Seq(Nat)}
  \vars{\theta}{Seq(Prod(Nat,Nat))}
  \vars{a,b,e,h,i,j,k,m,n,r,u,v,w,y,z,\ell,\beta,\delta_*}{Nat}
  \vars{p}{Name}
  \vars{\chi,\eta}{Fun(Nat,Nat)}
  \vars{\rho}{Fun(Prod(Nat,Nat),Nat)}
\end{mathmeta}

The finite-table checker of §{sec:lambda-input-certificates} can be used without an input name when all proposed answers
are supplied by a finite prefix. Let $s$ be a finite sequence and $\theta$ a finite answer table. For each entry
$\Pair{i}{v}$ of
$\theta$, test both
$$i<\Length{s}\qquad\text{and}\qquad s(i)=v.$$
The first condition is essential: the zero returned by list access outside its domain is not an answer supplied by the
prefix. Compute each condition as zero or one, multiply the two results, and take the bounded product over the entries
of $\theta$. This gives a closed total term $\LambdaTermName{tableSupport}$ on $\NatPair{ \LambdaListCode{s}}{
\LambdaAnswerTableCode{ \theta}}$. Here the code of an
answer table is the list code of its numerically paired entries.

\begin{mathmeta}
  \define{LambdaPrefixCertificate,LambdaExtractBall}
\end{mathmeta}

For named terms $B,D$ and a reduction certificate $\gamma$, encode the whole input as
$$z:=\NatPair{\LambdaListCode{s}}{
 \NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{
 \NatPair{\LambdaSyntaxCode{B}}{\LambdaSyntaxCode{D}}}}}.$$
Define $\LambdaPrefixCertificate$ by projecting these five components, multiplying the result of
$\LambdaTermName{tableSupport}$ by the result of
the finite-table certificate checker applied to $\theta, \gamma,B,D$, and abstracting the input variable.
Composition, numerical
projections and multiplication give a fixed closed term.

\begin{proposition*}[\termdefineas{lambda finite-prefix certificate test}{Exact finite-prefix certificate test}]
The term $\LambdaPrefixCertificate$ terminates on every numerical input and returns either zero or one. It returns one
exactly when every answer-table entry is supported by $s$ and $\gamma$ is a valid certificate from $B$ to $D$ using that
table. On success,
$$\LambdaInputSteps{p}{B}{D}\qquad(p\in\cyl{s}).$$
Conversely, every finite input-query reduction from $B$ to $D$ on a name $p$ has a certificate accepted by this test on
some finite prefix of $p$.
\end{proposition*}

\begin{proof}[Proof]
List length, indexing, comparisons and the finite-table certificate checker are total on all codes. Their zero-or-one
product therefore has exactly the stated acceptance condition. If $p$ extends $s$, each supported answer is also the
corresponding digit of $p$. Soundness of the certificate checker gives the displayed reduction on every such $p$. For
the converse, take a finite answer table and certificate for the given reduction. Choose a prefix length greater than
every address in the table; length zero suffices for an empty table. Each table entry then lies within the prefix and
has the correct value, so the product and the certificate check both return one.
\end{proof}

We can now combine this test with the Cauchy-margin program. Fix the distance-approximation term $M$, retain the indexed
programs $P_e$, and encode a trial by
$$\begin{aligned}
w&:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}},\\
a&:=\NatPair{w}{\NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{m}}}.
\end{aligned}$$
On input $\NatPair{e}{a}$, construct the syntax codes of $P_eo\ChurchNumeral{0}$ and $\ChurchNumeral{m}$ using the
programs of §{sec:lambda-input-universal-evaluation}. Prepare the five-component input to $\LambdaPrefixCertificate$
with these endpoints. Multiply its result by $\LambdaPrefixMargins{M}\ChurchNumeral{w}$, obtaining a value
$\beta\in\{0,1\}$. Define $\LambdaExtractBall{M}$ to return
$$\beta\bigl(\NatPair{i}{\delta_\ell}+1\bigr).$$
Here $\delta_ \ell$ is the rational code of $2^{- \ell}$. Output zero denotes an empty stage; output
$\NatPair{i}{r}+1$ denotes
the ball with center $q_i$ and radius given by rational code $r$.

\begin{proposition*}[\termdefineas{lambda uniform ball extraction program}{Uniform ball extraction program}]
The term $\LambdaExtractBall{M}$ is closed and total on all numerical inputs. It emits the ball $\Ball{q_i}{2^{-\ell}}$
exactly when the trial's prefix certificate and every Cauchy-margin test succeed. Hence the enumeration is computable
jointly in $e$ and the trial code, with the distance program fixed.
\end{proposition*}

\begin{proof}[Proof]
All component terms are closed and total, including the syntax-code constructors. The two tests return zero or one, so
their product is one exactly when both succeed. The final numerical pairing, successor and multiplication implement the
stated output convention. The successor makes every ball output positive, even when the paired code is zero. This
construction is independent of any assumption that $P_e$ semidecides a set. Under that additional assumption, the
Cauchy-prefix margin lemma and the soundness and completeness just proved give exact coverage, as shown in
§{sec:tte-polish-as-represented}.
\end{proof}

Keep the preceding numerical convention for enumeration outputs: zero denotes an empty stage and $b+1$ denotes the ball
encoded by $b$. Let $R_M$ be the fixed rational-ball stage term constructed in §{sec:lambda-rational-ball-programs}. Its
inputs are the name argument and $\NatPair{b}{n}$, where $b$ is a center-radius code and $n$ the metric precision. Its
output is zero or one, and it terminates on every name and every numerical input.

\begin{mathmeta}
  \define{LambdaEnumerationTrial,LambdaEnumerationSemidecider}
\end{mathmeta}

Encode a trial by $y:=\NatPair{j}{\NatPair{b}{\NatPair{h}{n}}}$ and the joint input by $z:=\NatPair{e}{y}$. Numerical
projections recover $e,j,b,h,n$. With these letters abbreviating the projection terms, define the closed term
$\LambdaEnumerationTrial{M}$ by
$$\begin{aligned}
\LambdaTermName{outputProof}&:=\LambdaOutputCandidate\,e\,j\,
 (\LambdaNumericPair\,(\LambdaSucc\,b)\,h),\\
\LambdaTermName{ballTrial}&:=R_M\,o\,(\LambdaNumericPair\,b\,n),\\
\LambdaEnumerationTrial{M}\,o\,z&\to_\beta^*\LambdaMul\,\LambdaTermName{outputProof}\,\LambdaTermName{ballTrial}.
\end{aligned}$$
The first factor uses the finite numerical-output test of §{sec:lambda-program-input-codes}: it checks whether a
reduction certificate below bound $h$ witnesses output $b+1$ for program $P_e$ on input $j$. It does not run $P_e$ until
termination. The second factor checks membership in the proposed ball at precision $n$.

\begin{proposition*}[\termdefineas{lambda enumeration trial}{Total enumeration trial}]
For every program index, name and trial code, $\LambdaEnumerationTrial{M}$ terminates and returns zero or one. It
returns one exactly when both the positive-output certificate and the rational-ball test succeed. This totality does not
require the indexed enumeration program to be total.
\end{proposition*}

\begin{proof}[Proof]
Pairing, successor and the numerical-output certificate checker are total ordinary lambda programs. The rational-ball
stage is total with input queries. Their composition and numerical product therefore compute exactly the two zero-or-one
factors displayed above. The proposed output is always positive, so no trial treats an empty enumeration stage as a
ball.
\end{proof}

Insert the fixed index $e$ and reverse the answers for result search:
$$\begin{aligned}
\LambdaTermName{enumStage}_e&:=\lambdaab{o}{\lambdaab{y}{\LambdaEnumerationTrial{M}\,o\,
 (\LambdaNumericPair\,\ChurchNumeral{e}\,y)}},\\
\LambdaTermName{enumSearch}_{e,o}&:= \lambdaab{y}{ \LambdaZeroTest\,( \LambdaTermName{enumStage}_eoy)\,
\ChurchNumeral{1}\, \ChurchNumeral{0}},\\
\LambdaTermName{identity}&:=\lambdaab{y}{y},\\
\LambdaEnumerationSemidecider{M}{e}&:= \lambdaab{o}{ \lambdaab{a}{ \LambdaResultSearch\,
\LambdaTermName{enumSearch}_{e,o}\, \LambdaTermName{identity}}}.
\end{aligned}$$
The numerical argument $a$ is unused. Choose all internal binders fresh once, and expand the abbreviations before
supplying the arguments.

\begin{proposition*}[\termdefineas{lambda enumeration semidecision compiler}{Exact search and uniform compilation}]
The term $\LambdaEnumerationSemidecider{M}{e}$ is closed. On every name, it returns the least successful trial code if
one exists, and has no numeral output otherwise. Equivalently, it has a numeral output exactly when some numerical
output $b+1$ of $P_e$ is certified and a stage of the ball test for $b$ succeeds. With $M$ fixed, there is a
primitive-recursive map sending $e$ to a syntax code of this semidecider, and one closed lambda term computes that map.
\end{proposition*}

\begin{proof}[Proof]
Each trial terminates, so the result-search theorem gives the least successful trial or excludes every numeral output
when there is no successful trial. Soundness of the finite output test identifies a successful proposal with an actual
output of $P_e$. Conversely, every finite numerical computation has a certificate below some finite bound. Pairing that
bound with its input, output code and a successful ball precision produces a successful trial.

For the compiler, fix named representatives of the trial term, pairing, zero testing, result search and the identity.
Compute the syntax code of $\ChurchNumeral{e}$, insert it into the displayed template for
$\LambdaTermName{enumStage}_e$, and form the two
remaining templates. Only the numeral-code map and finitely many application and abstraction constructors are used.
These numerical maps are primitive recursive and computed by closed lambda terms. The syntax coding identities show that
decoding the result gives precisely the displayed closed semidecider; the program enumeration therefore retains it. No
evaluation of $P_e$ and no digit of the input name is needed to compute this code.
\end{proof}

We record the uniform constructions used in the inverse-image criterion. All programs below use the same lambda
syntax and numerical pairing as above. Fix a closed term $\LambdaTermName{stagePredicate}$ and define
$$\begin{aligned}
\LambdaTermName{paramStage}_b&:=\lambdaab{o}{\lambdaab{k}{\LambdaTermName{stagePredicate}\,o\,
 (\LambdaNumericPair\,\ChurchNumeral{b}\,k)}},\\
\LambdaTermName{paramSearchTest}_{b,o}&:= \lambdaab{k}{ \LambdaZeroTest\,( \LambdaTermName{paramStage}_bok)\,
\ChurchNumeral{1}\, \ChurchNumeral{0}},\\
\LambdaTermName{identity}&:=\lambdaab{y}{y},\\
\LambdaTermName{paramSearch}_b&:= \lambdaab{o}{ \lambdaab{a}{ \LambdaResultSearch\,
\LambdaTermName{paramSearchTest}_{b,o}\, \LambdaTermName{identity}}}.
\end{aligned}$$
Choose the internal binders fresh and expand the abbreviations before supplying the arguments.

\begin{proposition*}[\termdefineas{lambda parameter search compiler}{Parameterized search compiler}]
There is a primitive-recursive map $b \mapsto \chi(b)$, computed by a closed lambda term, such that $P_{
\chi(b)}= \LambdaTermName{paramSearch}_b$.
On any name for which all tests $\LambdaTermName{paramStage}_b\,o\, \ChurchNumeral{k}$ have numerical outputs,
$\LambdaTermName{paramSearch}_b$ returns the least stage
with a nonzero answer, or has no numeral output if every answer is zero.
\end{proposition*}

\begin{proof}[Proof]
Fix named representatives of $\LambdaTermName{stagePredicate}$, numerical pairing, zero testing, result search
and the identity. Construct the code
of $\ChurchNumeral{b}$, then build $\LambdaTermName{paramStage}_b$, $\LambdaTermName{paramSearchTest}_{b,o}$ and
$\LambdaTermName{paramSearch}_b$ using application and abstraction constructors. The
coding identities identify the decoded term with the displayed closed term, so the program enumeration retains it.
Every numerical operation in this recipe is primitive recursive and has a closed lambda implementation. Exactness of
result search gives the assertion about outputs, because the test for that search is zero precisely at a nonzero
answer of $\LambdaTermName{paramStage}_b$.
\end{proof}

For the forward inverse-image construction, let $\LambdaTermName{nameRealizer}$ compute the output name and let
$R_Y$ be the total rational-ball
stage term for the target metric. Take
$$\LambdaTermName{stagePredicate}:=\lambdaab{o}{\lambdaab{z}{R_Y\,(\LambdaTermName{nameRealizer}o)\,z}}.$$
On every valid input name, lambda substitution gives exactly the stage answer for the output name. The preceding
proposition therefore supplies a semidecider for each target-ball preimage and one numerical compiler $\chi$. Compose
that compiler with the source-space extraction term:
$$\begin{aligned}
&\LambdaTermName{forwardEnumeration}:=\\
&\quad \lambdaab{z}{\LambdaExtractBall{M_X}\,
 (\LambdaNumericPair\,(\LambdaTermName{indexCompiler}(\LambdaNumericProjection{1}z))\,
 (\LambdaNumericProjection{2}z))},
\end{aligned}$$
where $\LambdaTermName{indexCompiler}$ computes $\chi$. This ordinary closed term is total on every numerical
input. At input $\NatPair{b}{k}$ it
returns precisely the $k$th extraction output for the preimage semidecider $P_{\chi(b)}$. The extraction theorem proves
that these outputs enumerate exactly the preimage, with zero representing an empty stage.

For the reverse construction, suppose a closed numerical term $\LambdaTermName{enumeration}$ computes a total
enumeration function $\eta$.
Fix a closed term $M$ computing the source-space distance approximations and let $R_M$ be its rational-ball stage
term. At coordinate $n$, write $\rho(n,j)$ for the code of the target ball of center $q_j$ and radius $2^{-(n+2)}$.
Its radius code is computed by $\LambdaDyadic\,\ChurchNumeral{n+2}$. Decode the joint input as
$$z=\NatPair{n}{\NatPair{j}{\NatPair{k}{\ell}}},\qquad u=\eta(\NatPair{\rho(n,j)}{k}).$$

\begin{mathmeta}
  \define{LambdaPreimageTrial,LambdaPreimageRealizer}
\end{mathmeta}

Define $\LambdaPreimageTrial{M}{ \LambdaTermName{enumeration}}$ using projections, addition, the dyadic-code
term, $\LambdaTermName{enumeration}$, and the rational-ball
stage test. For $u=b+1$, let $\beta$ be the zero-or-one answer of the ball test for $b$ at precision $\ell$.
The trial returns
$$\begin{cases}
0,&u=0,\\
u,&u=b+1,\ \beta=1,\\
0,&u=b+1,\ \beta=0.
\end{cases}$$
These are disjoint cases. For a positive output the predecessor term recovers $b$; an empty stage never succeeds.

\begin{proposition*}[\termdefineas{lambda preimage trial}{Total preimage trial}]
The term $\LambdaPreimageTrial{M}{ \LambdaTermName{enumeration}}$ is closed and total on every name and
numerical input. Its answer is nonzero
exactly when the enumeration emits a nonempty stage and the metric test certifies membership in its ball.
\end{proposition*}

\begin{proof}[Proof]
Numerical projections recover the four inputs. Addition and the dyadic-code term compute the target-ball code, and
$\LambdaTermName{enumeration}$ computes $u$. If $u=b+1$, predecessor recovers $b$ and the source-space stage
test returns zero or one.
Multiply this answer by $u$. If $u=0$, the result is zero regardless of the auxiliary test, which still terminates.
All operations are total lambda computations; their composition gives the asserted closed term and answer.
\end{proof}

Reverse the answers and curry the numerical input:
$$\begin{aligned}
&\LambdaTermName{preimageSearchTest}:=\\
&\quad \lambdaab{o}{\lambdaab{n}{\lambdaab{y}{
 \LambdaZeroTest\,(\LambdaPreimageTrial{M}{\LambdaTermName{enumeration}}\,o\,(\LambdaNumericPair\,n\,y))
 \,\ChurchNumeral{1}\,\ChurchNumeral{0}}}},\\
&\LambdaPreimageRealizer{M}{\LambdaTermName{enumeration}}:=\lambdaab{o}{\lambdaab{n}{
 \LambdaNumericProjection{1}(\LambdaSearchProgram{\LambdaTermName{preimageSearchTest}}\,o\,n)}}.
\end{aligned}$$

\begin{proposition*}[\termdefineas{lambda preimage realizer}{Realizer from preimage enumerations}]
Suppose $\eta$ enumerates exactly the basic-ball preimages of $f$ between the two complete metric spaces with their
dense sequences. On every valid source name, $\LambdaPreimageRealizer{M}{ \LambdaTermName{enumeration}}$
computes a fast Cauchy name of its
image. No continuity assumption on $f$ is needed for this construction.
\end{proposition*}

\begin{proof}[Proof]
For each $n$, density gives a target ball of the stated radius containing the image point. Its preimage enumeration
emits a source ball containing the input point, and the metric test succeeds at some precision. Thus some triple
succeeds. All earlier trials terminate, so sequential search returns the least successful triple and projection
extracts its center $j_n$. Every successful trial certifies
$$d(q_{j_n},f(x))<2^{-(n+2)}.$$
For $m\ge n$, the triangle inequality bounds the distance between the two selected centers by
$2^{-(n+2)}+2^{-(m+2)}\le2^{-n}$. The same error estimate implies convergence to $f(x)$. Hence the output is a valid
fast Cauchy name of the image. The construction is one closed term for all valid names and coordinates, and confluence
excludes all other numeral outputs.
\end{proof}

