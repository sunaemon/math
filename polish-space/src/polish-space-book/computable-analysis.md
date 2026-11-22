# Computable Analysis: Compactness, Measures, and Integration {#sec:computable-analysis}

<!-- formalization: skip-begin (chapter roadmap) -->
§{sec:computable-polish-tte} supplies computable metric presentations, Cauchy names, and realizers.
This chapter applies them to compact spaces and measures, then to integration and the Fourier transform.
In each construction, the input representation specifies the finite information that a lambda program may use;
existence of a mathematical value alone does not supply a program for it.

Computable compactness provides finite-cover searches. Computable measures turn enumerations of open sets into
numerical approximations. Polynomial and norm names then support the integration and Fourier constructions.
The distinction between stronger and weaker input representations is part of each result.
§{sec:computational-choice-randomness} continues with effective null tests;
§{sec:weihrauch-reducibility} compares the information needed to solve problems.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

This chapter uses computable metric presentations and effective open sets from
§{sec:computable-metric-presentations} and §{sec:tte-effective-open-closed}, together with the realizer
composition rule in §{sec:lambda-input-composition}. For the measure and integration sections, recall finite
Borel measures and Lebesgue integration; the regularity results in §{sec:borel-measures-radon} provide the
classical context. The effective-DST rank and dichotomy proofs are not prerequisites. We develop finite-net
cover tests, computable measure values, and integration and Fourier realizers. The final counterexample
identifies the tail information missing from a locally uniform name. On a first pass, follow the input,
output, and error guarantees of these constructions; return to the displayed lambda programs to verify their
implementation.

<!-- formalization: skip-end -->

## Computable Compactness {#sec:tte-computable-compactness}

\begin{mathmeta}
  \vars{N}{Nat}
  \vars{a,b,c,i,j,k,m,n,u,v,w,z}{Nat}
  \vars{p}{Name}
\end{mathmeta}

Compactness also has an effective strengthening. A compact space $K$ with a computable metric presentation is
\termdefine{computably compact} if one closed numerical lambda program, on input $n$, returns a finite list
$$E_n=\Tuple{e_{n,0},\ldots,e_{n,\ell_n-1}}$$
of basic-point indices such that
$$K=\bigcup_{k<\ell_n}\Ball{q_{e_{n,k}}}{2^{-n}}.$$
The program returns the numerical list code from §{sec:lambda-finite-lists}. It is uniform in $n$.

\begin{mathmeta}
  \forward{LambdaBoundedProduct}
\end{mathmeta}

\begin{lemma*}[\termdefineas{uniform ball-cover margin}{Uniform ball-cover margin}]
Let $K$ be a compact metric space and let $(\Pair{c_j}{r_j})_{j<m}$ be a finite list of balls covering $K$.
There is some $N\in\NN$ such that every $x\in K$ satisfies
$$d(x,c_j)+4\cdot 2^{-N}<r_j$$
for some $j<m$.
\end{lemma*}

\begin{proof}[Proof]
Put $\varepsilon_n:=2^{-n}$ and consider the increasing open sets
$$U_n:=\bigcup_{j<m}\Ball{c_j}{r_j-4\varepsilon_n}.$$
For every $x\in K$, some $r_j-d(x,c_j)$ is positive, so $x\in U_n$ for all sufficiently large $n$.
Hence the sets $U_n$ cover $K$. Compactness gives a finite subcover; since they are increasing, one $U_N$
already covers $K$. This is the required uniform margin, including when $K$ is empty.
\end{proof}

\begin{lemma*}[\termdefineas{finite-net cover semidecision}{Finite-net cover semidecision}]
For a computably compact presentation, the finite-cover relation
$$K=\bigcup_{j<m}\Ball{q_{i_j}}{r_j}$$
is semidecidable uniformly from the finite list $B=(\Pair{i_j}{r_j})_{j<m}$ of rational ball codes.
There is one closed lambda term that returns a numeral exactly for lists that cover $K$.
\end{lemma*}

\begin{proof}[Proof]
Put $\varepsilon_n:=2^{-n}$ and let $A(u,v,n)$ be the rational distance approximation, with
$$\Abs{A(u,v,n)-d(q_u,q_v)}\le\varepsilon_n.$$
At stage $n$, compute $E_n$ and test the finite condition
$$\forall k<\ell_n\;\exists j<m:\quad A(e_{n,k},i_j,n)+2\varepsilon_n<r_j.$$
Every comparison is rational and terminates. If the test succeeds, choose for each $x\in K$ a net point with
$d(x,q_{e_{n,k}})<\varepsilon_n$ and a successful ball for that point. Then
$$d(x,q_{i_j})\le d(x,q_{e_{n,k}})+d(q_{e_{n,k}},q_{i_j})
< A(e_{n,k},i_j,n)+2\varepsilon_n<r_j.$$
Thus every successful stage certifies the proposed cover.

Conversely, suppose that $B$ covers $K$. The \termuse{uniform ball-cover margin} gives a stage $N$
at which every net point belongs to a ball with
$$d(q_{e_{N,k}},q_{i_j})+4\varepsilon_N<r_j.$$
The upper error estimate then gives
$$A(e_{N,k},i_j,N)+2\varepsilon_N
\le d(q_{e_{N,k}},q_{i_j})+3\varepsilon_N<r_j.$$
Thus the finite test succeeds at stage $N$.
We now construct the numerical program. Encode each ball by pairing its center index and rational radius
code, and encode $B$ as a numerical list with code $b$. Let $C$ be the closed term that, on input
$$\NatPair{\NatPair{\NatPair{b}{n}}{k}}{j},$$
returns $1$ if the displayed rational inequality holds and $0$ otherwise. Numerical projections recover the
indices; the finite-net program, $\LambdaListGet$, the distance program, rational addition, and rational comparison
give $C$. Let $L$ compute $\ell_n$ from $z:=\NatPair{b}{n}$, and let $N$ compute $m$ from
$w:=\NatPair{z}{k}$. These are closed terms obtained from projections, the net program, and $\LambdaListLength$.

Use the bounded-product terms from §{sec:lambda-prefix-margin-programs} and define
$$\begin{aligned}
Z&:=\lambdaab{v}{\LambdaZeroTest\,v\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
D&:=\lambdaab{u}{Z(Cu)},\\
W&:=\lambdaab{w}{Z\bigl(\LambdaBoundedProduct{D}(\LambdaNumericPair\,w\,(Nw))\bigr)},\\
T&:=\lambdaab{z}{\LambdaBoundedProduct{W}(\LambdaNumericPair\,z\,(Lz))}.
\end{aligned}$$
The inner product is nonzero exactly when every candidate ball fails for the chosen net point; applying $Z$
therefore tests whether some ball succeeds. The outer product is nonzero exactly when this happens for every
net point. Empty products have value $1$, so the same formulas also handle empty lists. Each bounded product
terminates, and induction on its length verifies these assertions.

Finally set
$$I:=\lambdaab{x}{x},\qquad G_b:=\lambdaab{n}{Z(T(\LambdaNumericPair\,b\,n))},
\qquad S:=\lambdaab{b}{\LambdaResultSearch\,G_b\,I}.$$
The parameterized search in §{sec:lambda-rational-ball-programs} returns the first successful stage.
When no stage succeeds, it has no numeral output under any reduction order. Thus $S$ is a single closed
semidecider for all finite ball lists. The two metric arguments identify its domain with exactly the covering lists.
\end{proof}

\begin{theorem*}[\termdefineas{computable compactness equivalence}{Finite nets and finite-cover semidecision}]
Let $K$ be a compact space with a computable metric presentation. Then $K$ is computably compact if and only if
finite covers by basic rational balls can be semidecided uniformly. From an index of such a semidecider, the
construction below gives a closed lambda program computing finite $2^{-n}$-nets uniformly in $n$.
\end{theorem*}

\begin{proof}[Proof]
The preceding lemma proves the forward direction. For the converse, let $P_e$ semidecide finite covers:
it has a numeral output on a ball-list code exactly when that list covers $K$. Fix $n$. Density gives
$$K=\bigcup_{i\in\NN}\Ball{q_i}{2^{-n}}.$$
Compactness supplies a finite subcover. Choose $m$ larger than every index in that subcover; then the first $m$
balls already cover $K$. We therefore need only search the prefix lists
$$B_{n,m}:=(\Pair{i}{2^{-n}})_{i<m}.$$
No effective choice of the finite subcover or of this bound is used here: this argument only proves that a
successful prefix exists.

Let $b(n,m)$ be the numerical code of $B_{n,m}$. It is computable by finite tabulation. Explicitly, put
$$\begin{aligned}
H&:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,
  (\LambdaDyadic(\LambdaNumericProjection{1}z))},\\
B&:=\LambdaListTabulate{H}.
\end{aligned}$$
Then $B$ sends $\ChurchNumeral{\NatPair{n}{m}}$ to $\ChurchNumeral{b(n,m)}$.
To avoid waiting forever for a noncover, search over pairs $k=\NatPair{m}{c}$, where $c$ is an output-candidate
code for $P_e$ on input $b(n,m)$. The finite tester in §{sec:lambda-program-input-codes} gives the closed terms
$$\begin{aligned}
V&:=\lambdaab{z}{B(\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,
   (\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z)))},\\
Q&:=\lambdaab{z}{\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z)},\\
C_e&:=\lambdaab{z}{\LambdaOutputCandidate\,\ChurchNumeral{e}\,(Vz)\,(Qz)}.
\end{aligned}$$
On input $\NatPair{n}{\NatPair{m}{c}}$, it returns $1$ exactly when $c$ certifies a numeral output of
$P_e\ChurchNumeral{b(n,m)}$, and returns $0$ otherwise. Every test terminates. Soundness of the certificate tester
shows that every successful test gives a cover. Conversely, a covering prefix makes $P_e$ return a numeral,
and completeness of the tester supplies a successful certificate. Thus, for each $n$, some paired candidate succeeds.

Using $Z$ and $I$ from the preceding proof, define
$$\begin{aligned}
G_{e,n}&:=\lambdaab{k}{Z(C_e(\LambdaNumericPair\,n\,k))},\\
J_e&:=\lambdaab{n}{\LambdaResultSearch\,G_{e,n}\,I},\\
R&:=\lambdaab{k}{\LambdaListTabulate{\LambdaNumericProjection{2}}
   (\LambdaNumericPair\,\ChurchNumeral{0}\,(\LambdaNumericProjection{1}k))},\\
F_e&:=\lambdaab{n}{R(J_en)}.
\end{aligned}$$
Search returns the least successful paired candidate, and $R$ tabulates the indices $i<m$ from its first component.
Consequently, $F_e\ChurchNumeral{n}$ returns the code of a finite list whose $2^{-n}$-balls cover $K$.
Expanding the parameterized abbreviation $G_{e,n}$ in $F_e$ binds every variable; $e$ is inserted as a numeral.
Thus $F_e$ is a closed term built by fixed compositions. Finite tabulation and the exact search theorem prove
the stated beta reductions. The syntax construction
retains the given semidecider index and requires no extra oracle. This proves the converse and the equivalence.
\end{proof}

\begin{mathmeta}
  \forward{LambdaListAppend,LambdaListCons,LambdaSearch}
\end{mathmeta}

\begin{proposition*}[\termdefineas{finite subcover selection}{Computing a finite subcover}]
Fix a computably compact presentation of $K$. Supply a ball enumeration $p:\NN\to\NN$ as an input name,
with $0$ denoting an empty stage and $b+1$ denoting the ball with center-radius code $b$.
If the enumerated balls cover $K$, one closed lambda program returns a number $m$ such that the first $m$
stages already cover $K$. The program is uniform in $p$; the enumeration need not itself be computable.
\end{proposition*}

\begin{proof}[Proof]
Write $V_i$ for the set at enumeration stage $i$. Each $V_i$ is open, including the empty stages.
The cover $K=\bigcup_i V_i$ has a finite subcover by compactness. A number $m$ larger than its indices then satisfies
$$K=\bigcup_{i<m}V_i.$$
This proves existence of a covering prefix. To find one, we will search pairs of prefix lengths and net precisions.

Turn enumeration entries into raw ball codes by
$$d(v):=\begin{cases}0,&v=0,\\v-1,&v>0.\end{cases}$$
The raw code $0$ denotes the ball of radius zero at $q_0$, which is empty. Thus this conversion preserves every
stage's set. Let $b_p(m)$ code the list $(d(p(i)))_{i<m}$. The predecessor term computes $d$, and the following
recursion computes this list from the supplied name:
$$\begin{aligned}
B&:=\lambdaab{o}{\ChurchNumeral{0}},\\
H&:=\lambdaab{o}{\lambdaab{k}{\lambdaab{r}{
 \LambdaListAppend\,r\,(\LambdaListCons\,(\LambdaPred(ok))\,\ChurchNumeral{0})}}},\\
L&:=\LambdaParamRec{B}{H}.
\end{aligned}$$
The initial value is the empty-list code. Each update queries $p(k)$ and appends its converted code.
Induction on $m$ gives $Lo\ChurchNumeral{m}\to^*\ChurchNumeral{b_p(m)}$ by beta reductions and input queries.
Only the first $m$ enumeration entries are read.

Let $T$ be the total finite-net test constructed above. On input $\NatPair{b}{n}$ it returns a nonzero numeral
exactly when the ball list coded by $b$ passes the rational margin test at precision $n$. Define
$$D:=\lambdaab{o}{\lambdaab{k}{T(\LambdaNumericPair\,
 (Lo(\LambdaNumericProjection{1}k))\,(\LambdaNumericProjection{2}k))}}.$$
For $k=\NatPair{m}{n}$, the test $Dok$ first computes $b_p(m)$ and then tests that prefix at precision $n$.
Every such test terminates. A successful test certifies that the prefix covers $K$, by the finite-net lemma.
Conversely, a covering prefix exists by compactness, and that lemma supplies a precision at which it passes.
Hence some paired candidate succeeds. Enumerating pairs prevents a noncovering prefix from blocking the search.

Using the numerical bit negation $Z$ from the finite-net proof, put
$$S:=\lambdaab{o}{\lambdaab{a}{\LambdaNumericProjection{1}
 \bigl(\LambdaSearch(\lambdaab{k}{Z(Dok)})\bigr)}}.$$
The numerical argument $a$ is unused and may be set to $\ChurchNumeral{0}$. The sequential-search theorem from
§{sec:lambda-input-search} returns the least successful pair; the final projection extracts its prefix length $m$.
All constants are closed and both the enumeration argument and the dummy argument are bound, so $S$ is closed.
The reductions above prove that $So\ChurchNumeral{0}$ returns $\ChurchNumeral{m}$ and that the first $m$ stages
cover $K$. Uniqueness of numeral outputs excludes a different returned value. Discarding the empty stages leaves
a finite subcover from the original enumeration.
\end{proof}

\begin{lemma*}[\termdefineas{uniform coverage semidecision}{Uniform coverage semidecision}]
Fix a computably compact presentation of $K$. Suppose one closed numerical term $F$ computes $e(b,i)$ on
input $\NatPair{b}{i}$, with the empty-stage convention above. Then the set of parameters $b$ whose enumerated
balls cover $K$ is semidecidable by one closed lambda term. Its domain consists exactly of those parameters.
\end{lemma*}

\begin{proof}[Proof]
For each $b$, apply the prefix construction to $p_b(i):=e(b,i)$. Let $c(b,m)$ be the code of the first $m$
converted ball codes. Using the notation $\pi_i:=\LambdaNumericProjection{i}$ and the finite-net test $T$, define
$$\begin{aligned}
L_F&:=\LambdaListTabulate{\lambdaab{z}{\LambdaPred(Fz)}},\\
D&:=\lambdaab{z}{T(\LambdaNumericPair\,
 (L_F(\LambdaNumericPair\,(\pi_1z)\,(\pi_1(\pi_2z))))\,(\pi_2(\pi_2z)))},\\
G_b&:=\lambdaab{k}{Z(D(\LambdaNumericPair\,b\,k))},\\
S_F&:=\lambdaab{b}{\LambdaResultSearch\,G_b\,I}.
\end{aligned}$$
Here $Z$ and $I$ are the bit negation and identity terms used above. The tabulator returns $c(b,m)$ from
$\NatPair{b}{m}$. For $k=\NatPair{m}{n}$, the test $D\ChurchNumeral{\NatPair{b}{k}}$ returns a nonzero numeral
exactly when that prefix passes the finite-net test at precision $n$. These are total rational tests.
If the enumerated balls cover $K$, compactness gives a covering prefix, and the finite-net lemma gives a successful
precision. Conversely, every successful test certifies a covering prefix. The exact numerical-search theorem now
shows that $S_F\ChurchNumeral{b}$ has a numeral output exactly for covering parameters; if there is no successful
pair, no reduction order produces a numeral. Expanding $G_b$ binds the parameter, so $S_F$ is closed.
\end{proof}

\begin{proposition*}[\termdefineas{finite covers of a computable image}{Finite covers of a computable image}]
Let $K$ be computably compact and let $f:K\to Y$ be a computable map into a computable Polish space.
Given a finite list of basic rational balls in $Y$, a single closed lambda term semidecides whether their union
contains $f[K]$.
\end{proposition*}

\begin{proof}[Proof]
The effective inverse-image criterion in §{sec:tte-polish-as-represented} supplies a closed numerical term $F$
computing $e(c,k)$, an enumeration of the preimage of the target ball coded by $c$. For an input list
$C=(c_j)_{j<\ell}$ with code $b$, merge these enumerations by pairing the ball position and its enumeration stage:
$$\widehat e(b,\NatPair{j}{k}):=
\begin{cases}e(c_j,k),&j<\ell,\\0,&j\ge\ell.\end{cases}$$
Write $V(v)$ for the source ball represented by enumeration value $v$, with $V(0)=\varnothing$, and $W(c)$ for
the target ball coded by $c$. Then
$$\bigcup_t V(\widehat e(b,t))
=f^{-1}\!\left(\bigcup_{j<\ell}W(c_j)\right).$$
Indeed, a nonempty emitted source ball belongs to one of the preimage enumerations, and every stage of every
listed ball occurs at its paired index. Hence the merged enumeration covers $K$ exactly when the target balls
cover $f[K]$. This also handles the empty list: all merged stages are then empty.

Here is the numerical program for the merge. On input $z=\NatPair{b}{\NatPair{j}{k}}$, projections compute
$j$ and $k$; $\LambdaListLength$ computes $\ell$, and $\LambdaListGet$ extracts $c_j$ when $j<\ell$.
Let $J,Q,B$ be the closed terms computing these three extracted values, with zero-default list access outside
the list, and let $A$ be the closed numerical comparison term returning $1$ when $j<\ell$ and $0$ otherwise.
Then
$$F_{\cup}:=\lambdaab{z}{\LambdaMul\,(Az)\,
 \bigl(F(\LambdaNumericPair\,(Bz)\,(Qz))\bigr)}$$
computes $\widehat e$. Every component is total; even when $j\ge\ell$, the enumeration term returns a number,
and multiplication by zero suppresses it. Apply the uniform coverage lemma to $F_{\cup}$. Its semidecider has a
numeral output exactly when the displayed preimage is all of $K$, which is exactly the desired finite-cover relation.
The program depends on the fixed metric, finite-net and preimage-enumeration programs, while the candidate list
remains its numerical input.
\end{proof}

\begin{proposition*}[\termdefineas{metric presentation of a computable image}{Metric presentation of
a computable image}]
Let $K$ be a compact computable Polish space with basic points $q_i$, and let $f:K\to Y$ be computable,
where $Y$ has basic points $s_j$. Equip $f[K]$ with the restricted metric and the sequence $r_i:=f(q_i)$.
This is a computable Polish presentation: the metric is complete, the sequence is dense, and one closed
numerical lambda term approximates every distance $d(r_i,r_j)$ to error at most $2^{-n}$ from
$\NatPair{i}{\NatPair{j}{n}}$. This conclusion requires only classical compactness of $K$;
the construction of finite nets is an additional assertion.
\end{proposition*}

\begin{proof}[Proof]
Let $Q$ compute a realizer $F$ of $f$. The constant name $p_i(k)=i$ names $q_i$, so put
$$t(i,k):=F(p_i)(k).$$
The Cauchy-name estimate gives $d(r_i,s_{t(i,k)})\le 2^{-k}$. To obtain an ordinary numerical program,
write $\pi_a:=\LambdaNumericProjection{a}$ and define
$$\begin{aligned}
H&:=\lambdaab{i}{\lambdaab{k}{Q\,(\lambdaab{u}{i})\,k}},\\
T&:=\lambdaab{z}{H\,(\pi_1z)\,(\pi_2z)}.
\end{aligned}$$
Substituting the closed constant-name term for each input oracle turns its queries into ordinary beta
reductions, as in §{sec:tte-effective-dense-changes}. Thus $T\ChurchNumeral{\NatPair{i}{k}}$ reduces to
$\ChurchNumeral{t(i,k)}$ for all $i,k$. The same closed term works uniformly for the entire image sequence.

Let $A(a,b,k)$ be the rational distance approximation for $Y$, computed in coded form by a closed term $M$.
Define
$$B(i,j,n):=A(t(i,n+2),t(j,n+2),n+2).$$
Put $a=s_{t(i,n+2)}$ and $b=s_{t(j,n+2)}$. The triangle inequality gives
$$\begin{aligned}
\Abs{B(i,j,n)-d(r_i,r_j)}
&\le \Abs{B(i,j,n)-d(a,b)}+\Abs{d(a,b)-d(r_i,r_j)}\\
&\le 2^{-(n+2)}+d(a,r_i)+d(b,r_j)\\
&\le 3\cdot2^{-(n+2)}\le 2^{-n}.
\end{aligned}$$
Only total numerical computations are needed. On the paired triple $z=\NatPair{i}{\NatPair{j}{n}}$, use
$$\begin{aligned}
L&:=\lambdaab{z}{\LambdaSucc(\LambdaSucc(\pi_2(\pi_2z)))},\\
U&:=\lambdaab{z}{T(\LambdaNumericPair\,(\pi_1z)\,(Lz))},\\
V&:=\lambdaab{z}{T(\LambdaNumericPair\,(\pi_1(\pi_2z))\,(Lz))},\\
D&:=\lambdaab{z}{M(\LambdaNumericPair\,(Uz)\,
 (\LambdaNumericPair\,(Vz)\,(Lz)))}.
\end{aligned}$$
Beta reduction of the projections, successors, applications of $T$, and finally $M$ shows that $D$ returns
the rational code of $B(i,j,n)$. These terms are closed after expanding the displayed definitions.

Finally, $f$ is continuous by the continuity theorem for computably realizable maps. Any nonempty relatively
open subset of $f[K]$ has nonempty open preimage in $K$, which contains some $q_i$; hence it contains $r_i$.
Thus the image sequence is dense. The continuous image of compact $K$ is compact, so its restricted metric
is complete. That metric has the same distances as $Y$, and therefore the program just constructed gives
the required presentation.
\end{proof}

\begin{theorem*}[\termdefineas{computable compactness of images}{Computable compactness of images}]
Let $K$ be computably compact and let $f:K\to Y$ be computable, where $Y$ is a computable Polish space.
Then $f[K]$, with the restricted metric and basic points $r_i=f(q_i)$, is computably compact.
In particular, one closed numerical lambda term computes a finite list of indices of a $2^{-n}$-net
in this presentation from $n$.
\end{theorem*}

\begin{proof}[Proof]
Use the preceding presentation and its approximation function $t$, so that
$d(r_i,s_{t(i,n)})\le\varepsilon_n:=2^{-n}$ for the ambient basic points $s_j$.
Given a finite list $C=(\Pair{i_j}{R_j})_{j<\ell}$ of rational balls centered at the image points, form the ambient list
$$C_n:=(\Pair{t(i_j,n)}{R_j-\varepsilon_n})_{j<\ell}.$$
Nonpositive radii denote empty balls. If $C_n$ covers $f[K]$, then $C$ covers it: for a point in a ball of $C_n$,
$$d(y,r_{i_j})\le d(y,s_{t(i_j,n)})+\varepsilon_n<R_j.$$
Conversely, if $C$ covers $f[K]$, the \termuse{uniform ball-cover margin} applied to the compact metric space
$f[K]$ gives some $n$ such that each
$y\in f[K]$ satisfies $d(y,r_{i_j})+4\varepsilon_n<R_j$ for some $j<\ell$. Then
$$d(y,s_{t(i_j,n)})\le d(y,r_{i_j})+\varepsilon_n<R_j-\varepsilon_n.$$
Thus $C_n$ covers $f[K]$. We have proved that $C$ is a cover exactly when some $C_n$ is a cover.

The conversion from the code $b$ of $C$ and the precision $n$ to the code $c(b,n)$ of $C_n$ is a total
numerical computation. Here is an explicit term. Write $\pi_a:=\LambdaNumericProjection{a}$.
A rational code $\NatPair{\NatPair{u}{v}}{w}$ denotes $(u-v)/(w+1)$, so negation is computed by
$$J:=\lambdaab{z}{\LambdaNumericPair\,
 (\LambdaNumericPair\,(\pi_2(\pi_1z))\,(\pi_1(\pi_1z)))\,(\pi_2z)}.$$
Let $T$ compute $t(i,n)$ on paired input. For an entry input $z=\NatPair{\NatPair{b}{n}}{j}$, define
$$\begin{aligned}
B&:=\lambdaab{z}{\LambdaListGet(\LambdaNumericPair\,(\pi_1(\pi_1z))\,(\pi_2z))},\\
L&:=\lambdaab{z}{\pi_2(\pi_1z)},\\
H&:=\lambdaab{z}{T(\LambdaNumericPair\,(\pi_1(Bz))\,(Lz))},\\
R&:=\lambdaab{z}{\LambdaRationalAdd(\LambdaNumericPair\,(\pi_2(Bz))\,(J(\LambdaDyadic(Lz))))},\\
G&:=\lambdaab{z}{\LambdaNumericPair\,(Hz)\,(Rz)},\\
C^*&:=\lambdaab{z}{\LambdaListTabulate{G}
 (\LambdaNumericPair\,z\,(\LambdaListLength(\pi_1z)))}.
\end{aligned}$$
The term $B$ reads the old ball code, $L$ reads the precision, and $H,R$ compute the new center and radius.
Swapping numerator components computes rational negation exactly; rational addition then computes
$R_j-\varepsilon_n$. Finite tabulation gives $c(b,n)$, preserving the length and order of the list.
These beta computations also handle the empty list and balls that become empty after shrinking.

Let $P_e$ be the ambient finite-cover semidecider constructed above. Do not wait for it on one fixed precision:
a noncover need not terminate. Instead search over $k=\NatPair{n}{a}$, where $a$ is a finite output
certificate for $P_e\ChurchNumeral{c(b,n)}$. Explicitly, use
$$\begin{aligned}
W&:=\lambdaab{z}{C^*(\LambdaNumericPair\,(\pi_1z)\,(\pi_1(\pi_2z)))},\\
D_e&:=\lambdaab{z}{\LambdaOutputCandidate\,\ChurchNumeral{e}\,(Wz)\,(\pi_2(\pi_2z))},\\
G_{e,b}&:=\lambdaab{k}{Z(D_e(\LambdaNumericPair\,b\,k))},\\
S_e&:=\lambdaab{b}{\LambdaResultSearch\,G_{e,b}\,I}.
\end{aligned}$$
Here $Z$ negates the test bit and $I$ is the identity term. Each certificate test terminates. A successful test
certifies that $C_n$ covers the image, so $C$ covers it. Conversely, a covering $C$ supplies a suitable $n$;
the ambient semidecider then has a numeral output, which has a finite certificate. The exact search theorem
therefore makes $S_e$ a semidecider whose domain is precisely the image-centered finite covers.

Finally apply the \termuseas{computable compactness equivalence}{finite-cover/net equivalence} to the complete
image presentation and this semidecider. Its construction searches finite prefixes of the image sequence together
with output certificates, and returns a list $(i)_{i<m(n)}$ such that
$$f[K]\IncludedIn\bigcup_{i<m(n)}\Ball{r_i}{2^{-n}}.$$
The prefix-existence argument uses compactness and density; the certificate search supplies the computable choice.
Every returned center lies in $f[K]$, and the same closed program works for every $n$.
\end{proof}

\begin{lemma*}[\termdefineas{rational maxima and real distances}{Rational maxima and real distances}]
One closed numerical lambda term computes a code for the maximum of two coded rationals. Another computes
their distance exactly. In particular, enumerating the rationals by their codes gives a computable metric
presentation of $\R$.
\end{lemma*}

\begin{proof}[Proof]
Let $s_c$ be the rational represented by code $c$. Write $\pi_a:=\LambdaNumericProjection{a}$ and
$C:=\LambdaRationalLess$. The term
$$V:=\lambdaab{z}{\LambdaZeroTest\,(Cz)\,(\pi_1z)\,(\pi_2z)}$$
returns the second code if its value is larger and the first code otherwise. Indeed, the comparison returns
$1$ or $0$, and the zero test selects the first code on zero and the second on one. Thus its output represents
$\max(s_a,s_b)$ on input $\NatPair{a}{b}$, including when both rationals are negative.
Using the rational negation term $J$ from the preceding proof, define
$$\begin{aligned}
D&:=\lambdaab{z}{\LambdaRationalAdd(\LambdaNumericPair\,(\pi_1z)\,(J(\pi_2z)))},\\
A&:=\lambdaab{z}{V(\LambdaNumericPair\,(Dz)\,(J(Dz)))},\\
M&:=\lambdaab{z}{A(\LambdaNumericPair\,(\pi_1z)\,(\pi_1(\pi_2z)))}.
\end{aligned}$$
The first term computes a code for $s_a-s_b$, and the second computes a code for
$\max(s_a-s_b,-(s_a-s_b))=\Abs{s_a-s_b}$. The third accepts $\NatPair{a}{\NatPair{b}{n}}$ and ignores the
precision coordinate, since its answer is exact. Composition of the terminating beta computations proves
these assertions. Every rational has a code, so the basic sequence is dense; the usual real metric is complete.
\end{proof}

\begin{proposition*}[\termdefineas{computable suprema}{Computable suprema}]
A computable continuous function $f:K\to\R$ on a nonempty computably compact space has a computable supremum
as a real number. A closed numerical lambda term computes a fast Cauchy name of this supremum.
\end{proposition*}

\begin{proof}[Proof]
Put $M:=\sup f[K]$. This is finite because $f[K]$ is nonempty and compact. Write $r_i=f(q_i)$ for its basic
points. The image theorem supplies computable finite nets
$$\begin{aligned}
E_k&=(e_{k,j})_{j<\ell_k},\qquad \varepsilon_k:=2^{-k},\\
f[K]&\IncludedIn\bigcup_{j<\ell_k}\Ball{r_{e_{k,j}}}{\varepsilon_k}.
\end{aligned}$$
Applying the realizer to constant names supplies a computable function $t$ with rational approximations
$$a_{i,k}:=s_{t(i,k)},\qquad \Abs{a_{i,k}-r_i}\le\varepsilon_k.$$
Compute the finite maximum by the recurrence
$$\begin{aligned}
v_{k,0}&:=a_{0,k},\\
v_{k,j+1}&:=\max(v_{k,j},a_{e_{k,j},k})\quad(j<\ell_k),\\
b_k&:=v_{k,\ell_k}.
\end{aligned}$$
The seed is the approximation of a fixed image point. In particular, the recurrence remains valid when the
function takes only negative values.

Each value entering the maximum is at most $M+\varepsilon_k$, since its center lies in the image.
Induction over the list therefore gives $b_k\le M+\varepsilon_k$. Conversely, for every $y\in f[K]$,
choose a net index $e_{k,j}$ with $\Abs{y-r_{e_{k,j}}}<\varepsilon_k$. Then
$$y<r_{e_{k,j}}+\varepsilon_k\le a_{e_{k,j},k}+2\varepsilon_k\le b_k+2\varepsilon_k.$$
Taking the supremum yields
$$M\le b_k+2\varepsilon_k,\qquad \Abs{b_k-M}\le 2\varepsilon_k.$$
Consequently $u_n:=b_{n+2}$ satisfies $\Abs{u_n-M}\le 2^{-(n+1)}$.
For $m\ge n$ this gives
$$\Abs{u_n-u_m}\le 2^{-(n+1)}+2^{-(m+1)}\le 2^{-n},$$
so these rationals form a fast Cauchy name converging to the required supremum.

Here is the closed name-generating term. Let $N$ compute the list code of $E_k$, let $T$ compute $t(i,k)$
on paired input, and use the rational maximum term $V$ from the lemma. Define
$$\begin{aligned}
L&:=\lambdaab{k}{\lambdaab{j}{\LambdaListGet(\LambdaNumericPair\,(Nk)\,j)}},\\
W&:=\lambdaab{k}{\lambdaab{j}{T(\LambdaNumericPair\,(Lkj)\,k)}},\\
B&:=\lambdaab{k}{T(\LambdaNumericPair\,\ChurchNumeral{0}\,k)},\\
H&:=\lambdaab{k}{\lambdaab{j}{\lambdaab{a}{V(\LambdaNumericPair\,a\,(Wkj))}}},\\
C&:=\lambdaab{k}{\LambdaParamRec{B}{H}\,k\,(\LambdaListLength(Nk))},\\
P&:=\lambdaab{n}{C(\LambdaSucc(\LambdaSucc n))}.
\end{aligned}$$
The term $B$ returns the seed code. At step $j$, $L$ reads the net index, $W$ approximates that image point,
and $H$ takes the rational maximum with the accumulator. Induction on the finite recursion shows that $C$
returns a code $c(k)$ for $b_k$. All component computations terminate. Thus $P$ computes
$p(n):=c(n+2)$ by ordinary beta reduction. Expanding the auxiliary terms leaves a closed term, and the
preceding error estimate proves that its output sequence is a valid name of $M$.
\end{proof}

<!-- formalization: skip-begin (comparison with classical compactness) -->
The hypothesis is stronger than classical compactness. A compact Polish space can fail to be computably compact under a
poor effective presentation, just as a topologically closed set can fail to have computable points. Effective theorems
therefore track not only the underlying space, but also the quality of its presentation.
<!-- formalization: skip-end -->

## Computing Measures {#sec:tte-computable-measures}

### Cantor Open Sets {#sec:tte-cantor-open-measure}

\begin{mathmeta}
  \forward{LambdaListFold,LambdaListPrefix,LambdaInputPrefix,LambdaRelativeSearch}
  \vars{e}{Nat}
  \vars{s,t,w}{Seq}
  \vars{c,h,i,k,m,n,r}{Nat}
  \vars{p,\rho}{Name}
\end{mathmeta}

Let $\mu$ be the fair-coin probability measure on $\CantorSpace$. The cylinder calculation in
§{sec:random-forcing-detail} gives $\mu(\cyl{s})=2^{-\Length{s}}$. We now turn this finite formula into a uniform
calculation for enumerated open sets. Encode binary words as numerical lists. An enumeration entry $a=0$
denotes the empty set; an entry $a>0$ denotes the cylinder of the word $\LambdaListDecode{a-1}$.
A valid entry has only binary digits in that decoded word. Write $V_a$ for the set denoted by an entry and put
$$U_L:=\bigcup_{a\in L}V_a,\qquad U_p:=\bigcup_n V_{p(n)}$$
for a finite list $L$ of valid entries and a name $p:\NN\to\NN$ of valid entries.
Padding and repetitions are allowed. In particular, the constant-zero name denotes the empty open set,
and the entry $1$ denotes the whole space, because $0$ codes the empty word.

\begin{proposition*}[\termdefineas{finite Cantor open measure}{Finite cylinder union measures}]
One closed numerical lambda program, given the code of a finite list $L$ of valid entries, returns a rational code
for $\mu(U_L)$. Nested cylinders and repeated entries require no disjointness assumption on the input.
\end{proposition*}

\begin{proof}[Proof]
For a binary word $s$, compute the uncovered mass
$$G_L(s):=\mu\bigl(\SetDifference{\cyl{s}}{U_L}\bigr).$$
The empty list gives $G_{[]}(s)=2^{-\Length{s}}$. A padding entry changes nothing:
$G_{0::L}(s)=G_L(s)$. For $a>0$, put $t:=\LambdaListDecode{a-1}$. Then
$$G_{a::L}(s)=\begin{cases}
0,&t\prefixOf s,\\
G_L(s)-G_L(t),&s\prefixOf t\text{ and }t\notPrefixOf s,\\
G_L(s),&\text{otherwise}.
\end{cases}$$
In the first case the new cylinder covers all of $\cyl{s}$. In the second case,
$\SetDifference{\cyl{t}}{U_L}\IncludedIn\SetDifference{\cyl{s}}{U_L}$, and removing that measurable subset
subtracts exactly its measure. In the last case the cylinders are disjoint: two prefixes of the same infinite
sequence are comparable. This proves the recurrence, including equality of the words in the first case.
Finally, $\mu(U_L)=1-G_L(\emptySeq)$, since $\cyl{\emptySeq}=\CantorSpace$.

Here is the lambda implementation. Let $D$ be the numerical rational-subtraction program, formed from rational
addition and negation, and let $c_1:=\RationalCode{1}{0}{0}$. The list fold returns a function on word codes,
not a single accumulated number. In the following numerical term bodies, $c,h$ are numerical inputs,
and $F$ is the function
already computed for the tail. Expand the abbreviations $C,I,J$ inside $H$:
$$\begin{aligned}
Z&:=\lambdaab{c}{\LambdaDyadic(\LambdaListLength\,c)},\\
C(h,c)&:=\LambdaListPrefix(\LambdaNumericPair\,h\,c),\\
I(h,F,c)&:=\LambdaZeroTest\,(C(c,h))\,(Fc)\,
 \bigl(D(\LambdaNumericPair\,(Fc)\,(Fh))\bigr),\\
J(h,F,c)&:=\LambdaZeroTest\,(C(h,c))\,I(h,F,c)\,\ChurchNumeral{0},\\
H&:=\lambdaab{a}{\lambdaab{F}{\lambdaab{c}{
 \LambdaZeroTest\,a\,(Fc)\,J(\LambdaPred\,a,F,c)}}},\\
M&:=\lambdaab{v}{D\bigl(\LambdaNumericPair\,\ChurchNumeral{c_1}\,
 ((\LambdaListFold{Z}{H}\,v)\ChurchNumeral{0})\bigr)}.
\end{aligned}$$
The prefix routine returns $1$ for a prefix and $0$ otherwise; the zero test chooses its first branch on zero.
Thus the handler implements the recurrence exactly. Induction on the list, using the list-fold reductions,
shows that its value is a closed numerical function which, on input $\ChurchNumeral{\LambdaListCode{s}}$,
computes a rational code for $G_L(s)$ for every binary word $s$.
The dyadic, prefix, and rational routines all terminate. Applying the resulting function to the empty-word code
and subtracting from one proves the claim about $M$.
\end{proof}

\begin{theorem*}[\termdefineas{lower computation of Cantor open measure}{Computing open measure from below}]
One closed Type-Two lambda program, from every valid open name $p$, computes rational codes $b_p(n)$ such that
$$0\le q_{b_p(n)}\le q_{b_p(n+1)}\le\mu(U_p),\qquad
\lim_n q_{b_p(n)}=\mu(U_p).$$
A second closed program, on input $p$ and a rational code $r$, returns $1$ exactly when $q_r<\mu(U_p)$;
otherwise it has no numerical output. Both programs preserve the supplied name as a parameter.
\end{theorem*}

\begin{proof}[Proof]
Read the first $n$ enumeration entries into the list $L_n=\Tuple{p(0),\ldots,p(n-1)}$, with $L_0=[]$, and apply $M$.
Only these finitely many input queries are used. The closed term
$$B:=\lambdaab{o}{\lambdaab{n}{M(\LambdaInputPrefix\,o\,n)}}$$
returns the code $b_p(n)$ with $q_{b_p(n)}=\mu(U_{L_n})$. The finite unions increase and have union $U_p$.
Monotonicity and continuity from below of the finite measure give the asserted bounds and limit.
If a closed numerical term computes $p$, substituting it for the input function turns the same calculation into
ordinary beta reductions. Thus a computable open name gives a computable increasing rational approximation.

For the strict comparison, search stages $n$ using the total test
$$T:=\lambdaab{o}{\lambdaab{z}{\LambdaRationalLess\bigl(\LambdaNumericPair\,
 (\LambdaNumericProjection{1}z)\,(Bo(\LambdaNumericProjection{2}z))\bigr)}}.$$
On input $\NatPair{r}{n}$ it returns $1$ exactly when $q_r<q_{b_p(n)}$. Apply $\LambdaRelativeSearch{T}$.
Every stage terminates, and the bounds and limit prove
$$q_r<\mu(U_p)\quad\Longleftrightarrow\quad\exists n\ (q_r<q_{b_p(n)}).$$
The search therefore returns one exactly in the claimed case, with no numerical output otherwise.
\end{proof}

\begin{lemma*}[\termdefineas{effective finite open approximation}{Finite approximation from computable measure}]
Let $p$ be a computable valid name of a Cantor open set $U_p$, and suppose that $\mu(U_p)$ is computable.
From programs for these two names, one can construct a numerical program computing a stage $a(k)$ such that
$$\mu\bigl(\SetDifference{U_p}{U_{L_{a(k)}}}\bigr)<2^{-(k+1)},
\qquad L_m:=\Tuple{p(0),\ldots,p(m-1)}.$$
The precision $k$ remains an input to the program.
\end{lemma*}

\begin{proof}[Proof]
Let $P$ compute $p$, and let $Q$ compute a fast Cauchy name $\rho$ of $\mu(U_p)$.
Write $q_{\rho(m)}$ for its rational approximation at stage $m$, so
$\Abs{q_{\rho(m)}-\mu(U_p)}\le 2^{-m}$. Set
$$u_m:=q_{\rho(m)}+2^{-m},\qquad d_m:=u_m-\mu(U_{L_m}).$$
Then $u_m\ge\mu(U_p)$ and
$$0\le\mu\bigl(\SetDifference{U_p}{U_{L_m}}\bigr)
=\mu(U_p)-\mu(U_{L_m})\le d_m.$$
Both $u_m$ and $\mu(U_{L_m})$ tend to $\mu(U_p)$, hence $d_m\to0$.
The rational $d_m$ is exactly computable from the two programs and the finite-union measure algorithm.
Search for the first $m$ with $d_m<2^{-(k+1)}$ and return that stage. The convergence proves termination.

To give the lambda term, let $M$ be the finite-union measure program and $D$ the rational-subtraction program
used above. Expand the abbreviations inside the abstractions:
$$\begin{aligned}
E&:=\lambdaab{m}{\LambdaRationalAdd(\LambdaNumericPair\,(Qm)\,(\LambdaDyadic\,m))},\\
F&:=\lambdaab{m}{D(\LambdaNumericPair\,(Em)\,(M(\LambdaInputPrefix\,P\,m)))},\\
T(k,m)&:=\LambdaRationalLess(\LambdaNumericPair\,(Fm)\,(\LambdaDyadic(\LambdaSucc\,k))),\\
A&:=\lambdaab{k}{\LambdaResultSearch\,
 (\lambdaab{m}{\LambdaZeroTest\,T(k,m)\,\ChurchNumeral{1}\,\ChurchNumeral{0}})\,
 (\lambdaab{m}{m})}.
\end{aligned}$$
All tests terminate. The test supplied to $\LambdaResultSearch$ returns zero precisely at a successful stage,
and its result function returns that stage itself. The finite-prefix, rational-arithmetic, and search reductions
therefore give $A\ChurchNumeral{k}\to_\beta^*\ChurchNumeral{a(k)}$.
\end{proof}

\begin{corollary*}[\termdefineas{computable local closed measure}{Computable local measures of the complement}]
Under the same hypotheses, one closed numerical program computes fast Cauchy names of
$$\mu\bigl(\SetDifference{\cyl{w}}{U_p}\bigr)$$
uniformly in the binary word $w$ and the precision.
\end{corollary*}

\begin{proof}[Proof]
The same tail estimate controls every cylinder:
$$0\le G_{L_m}(w)-\mu\bigl(\SetDifference{\cyl{w}}{U_p}\bigr)
\le\mu\bigl(\SetDifference{U_p}{U_{L_m}}\bigr).$$
For the first inequality, use inclusion of the remaining sets. For the second, use
$$\SetDifference{\cyl{w}}{U_{L_m}}\IncludedIn
\bigl(\SetDifference{\cyl{w}}{U_p}\bigr)\cup
\bigl(\SetDifference{U_p}{U_{L_m}}\bigr)$$
and subadditivity. Thus $G_{L_{a(k)}}(w)$ has error less than $2^{-(k+1)}$.
For $k\le l$, two such rational approximations differ by at most
$2^{-(k+1)}+2^{-(l+1)}\le2^{-k}$. Hence they form a fast Cauchy name of the asserted measure.
With $Z,H$ the previously defined fold for $G_L$ and $\pi_i:=\LambdaNumericProjection{i}$, use
$$C:=\lambdaab{z}{
 ((\LambdaListFold{Z}{H})(\LambdaInputPrefix\,P\,(A(\pi_2z))))(\pi_1z)}.$$
On input $\NatPair{\LambdaListCode{w}}{k}$, this term returns the required rational code.
The word and precision both remain inputs, and the stage search is independent of the word.
\end{proof}

\begin{proposition*}[\termdefineas{computable measure of finite open unions}{Computable measure of finite unions}]
Let $U_p,U_\rho\IncludedIn\CantorSpace$ have computable valid open names and computable measures.
Then $U_p\cup U_\rho$ has a computable valid open name and computable measure, uniformly from the four programs.
The same holds for any finite family, by iteration.
\end{proposition*}

\begin{proof}[Proof]
Let $P,R$ compute $p,\rho$, respectively, and let $\pi_i:=\LambdaNumericProjection{i}$.
A name of the union is given by
$$v(\NatPair{i}{m}):=\begin{cases}p(m),&i=0,\\r(m),&i>0,\end{cases}
\qquad V:=\lambdaab{z}{\LambdaZeroTest\,(\pi_1z)\,(P(\pi_2z))\,(R(\pi_2z))}.$$
Rows $0$ and $1$ include both names, and the repeated rows add no new points.

Use the finite-approximation lemma to compute stages $a(k),b(k)$ for the two names.
At precision $k$, form the finite list
$$L_k:=\Tuple{p(0),\ldots,p(a(k+1)-1)}\concat\Tuple{\rho(0),\ldots,\rho(b(k+1)-1)}.$$
A list with stage $0$ is empty. Put $F_k:=U_{L_k}$. Then $F_k\IncludedIn U_p\cup U_\rho$, and
$$\begin{aligned}
\SetDifference{(U_p\cup U_\rho)}{F_k}
&\IncludedIn\bigl(\SetDifference{U_p}{U_{\Tuple{p(0),\ldots,p(a(k+1)-1)}}}\bigr)\\
&\qquad\cup\bigl(\SetDifference{U_\rho}{U_{\Tuple{\rho(0),\ldots,\rho(b(k+1)-1)}}}\bigr),\\
0\le\mu(U_p\cup U_\rho)-\mu(F_k)&<2^{-(k+2)}+2^{-(k+2)}=2^{-(k+1)}.
\end{aligned}$$
The rational values $\mu(F_k)$ therefore form a fast Cauchy name of the union's measure.
The finite-union algorithm accounts for overlaps between the two lists.

Let $A,B$ compute $a,b$, and let $M$ be the exact finite-union measure program. The term is
$$\begin{aligned}
L_P&:=\lambdaab{k}{\LambdaInputPrefix\,P\,(A(\LambdaSucc\,k))},\\
L_R&:=\lambdaab{k}{\LambdaInputPrefix\,R\,(B(\LambdaSucc\,k))},\\
H&:=\lambdaab{k}{M(\LambdaListAppend\,(L_Pk)\,(L_Rk))}.
\end{aligned}$$
The prefix and append reductions, followed by the reduction for $M$, give
$H\ChurchNumeral{k}\to_\beta^*\ChurchNumeral{h(k)}$ with $q_{h(k)}=\mu(F_k)$.
All stage searches terminate by the preceding lemma, and the precision remains an input.
\end{proof}

\begin{lemma*}[\termdefineas{computable finite open and cylinder complement}{Finite open sets and cylinder complements}]
Every finite union of binary cylinders has computable open and measure names.
In particular, $\SetDifference{\CantorSpace}{\cyl{w}}$ has such names for every fixed binary word $w$.
Consequently, if $K$ is effectively closed with computable measure, so is $K\cap\cyl{w}$.
\end{lemma*}

\begin{proof}[Proof]
For a finite list $L$ of valid entries, enumerate its entries in order and then return $0$ forever.
The open-name and measure-name terms are
$$P_L:=\lambdaab{m}{\LambdaListGet(\LambdaNumericPair\,\ChurchNumeral{\LambdaListCode{L}}\,m)},
\qquad Q_L:=\lambdaab{k}{M\ChurchNumeral{\LambdaListCode{L}}}.$$
The list-access term returns $0$ beyond the end of the list, and $M\ChurchNumeral{\LambdaListCode{L}}$ reduces to a code
of the exact rational $\mu(U_L)$. The constant rational sequence is a fast Cauchy name.
For the complement of $\cyl{w}$, take the finite list of entries for all binary words $t$ of length $\Length{w}$
with $t\ne w$, in any fixed order. Each entry is $1+\LambdaListCode{t}$. The cylinders in this list have union
$\SetDifference{\CantorSpace}{\cyl{w}}$, since each point has exactly one prefix of that length.
If $w$ is empty, the list is empty and represents the empty set.

Finally,
$$\SetDifference{\CantorSpace}{(K\cap\cyl{w})}
=\bigl(\SetDifference{\CantorSpace}{K}\bigr)\cup
 \bigl(\SetDifference{\CantorSpace}{\cyl{w}}\bigr).$$
Apply the finite-union proposition to these two open sets, and subtract the resulting measure from $1$.
Thus intersecting the closed set with a fixed cylinder preserves the required effective data.
\end{proof}

\begin{proposition*}[\termdefineas{no uniform exact open measure}{No uniform exact open measure}]
No closed Type-Two lambda program converts every computable valid open name $p$ into a fast Cauchy name
of $\mu(U_p)$. This fails even for names whose denoted sets are either empty or the whole Cantor space.
\end{proposition*}

\begin{proof}[Proof]
Suppose that $P$ is such a program. On the constant-zero enumeration it names measure zero. Its output at
coordinate $2$ returns a code $c$ after finitely many queries. Choose $N$ larger than all queried coordinates.
The computable enumeration
$$p_N(n):=\begin{cases}0,&n<N,\\1,&n\ge N\end{cases}$$
agrees with that input below $N$, but denotes the whole space. A numerical comparison with the fixed $N$ and
a zero test compute this enumeration, so it is among the promised inputs. Finite use and output uniqueness
force the same code $c$ at coordinate $2$ of its output. The two Cauchy error bounds would give
$$\Abs{q_c}\le1/4,\qquad \Abs{q_c-1}\le1/4.$$
This is impossible.
\end{proof}

This proposition separates uniform lower computation from uniform Cauchy-name computation. It does not by
itself exhibit a single computably enumerated open set of noncomputable measure: the two sets in its proof
have rational measures. For randomness tests, a uniform algorithm for their measures is additional information;
it cannot be obtained uniformly from their open enumerations.

\begin{example*}[\termdefineas{noncomputable open measure}{An effectively open set of noncomputable measure}]
There is a computably enumerated open set $U\IncludedIn\CantorSpace$ whose fair-coin measure is the real
$\HaltingReal$ from §{sec:tte-real-examples}. In particular, $\mu(U)$ is noncomputable and irrational.
\end{example*}

\begin{proof}[Proof]
Let $K$ be the diagonal halting set used there. For each $e\in\NN$, take the binary word
$$s_e:=\wordRepeat{0}{2e}\concat\Pair{1}{0},\qquad U:=\bigcup_{e\in K}\cyl{s_e}.$$
These cylinders are pairwise disjoint. Indeed, if $e<f$, their members have different bits at coordinate $2e$:
a member of $\cyl{s_e}$ has bit $1$, whereas a member of $\cyl{s_f}$ has bit $0$.
Their lengths and measures are
$$\Length{s_e}=2e+2,\qquad \mu(\cyl{s_e})=2^{-(2e+2)}=4^{-(e+1)}.$$

We give a closed numerical lambda program for an open name of $U$. Generate the codes
$\LambdaListCode{s_e}$ directly by the following terms:
$$\begin{aligned}
A&:=\lambdaab{x}{\ChurchNumeral{\LambdaListCode{[1,0]}}},\\
H&:=\lambdaab{x}{\lambdaab{j}{\lambdaab{r}{
 \LambdaListCons\,\ChurchNumeral{0}\,(\LambdaListCons\,\ChurchNumeral{0}\,r)}}},\\
W&:=\lambdaab{e}{\LambdaParamRec{A}{H}\,\ChurchNumeral{0}\,e}.
\end{aligned}$$
The parameter $x$ and counter $j$ are unused. The step prepends two zeros, so induction gives
$$W\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{\LambdaListCode{s_e}}.$$
This calculation terminates for every $e$ and uses only numerical list construction and recursion.

Let $c_e(k)\in\{0,1\}$ be the finite certificate test for the numerical halting of $\varphi_e(e)$ at candidate $k$.
The certificate theorem says that $e\in K$ exactly when some $k$ satisfies $c_e(k)=1$. Define an enumeration by
$$p(\NatPair{e}{k}):=\begin{cases}
\LambdaListCode{s_e}+1,&c_e(k)=1,\\
0,&c_e(k)=0.
\end{cases}$$
A closed term computing this total function is
$$\begin{aligned}
T&:=\lambdaab{e}{\lambdaab{k}{\LambdaOutputCandidate\,e\,e\,k}},\\
Q&:=\lambdaab{z}{T\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)},\\
P&:=\lambdaab{z}{\LambdaZeroTest\,(Qz)\,\ChurchNumeral{0}\,
 (\LambdaSucc(W(\LambdaNumericProjection{1}z)))}.
\end{aligned}$$
Thus $P\ChurchNumeral{z}\to_\beta^*\ChurchNumeral{p(z)}$ for every $z$. Each stage tests one finite certificate;
it never waits for the program indexed by $e$ to halt. The successor distinguishes a cylinder entry from padding.
Every nonzero entry codes a binary word, so $p$ is a valid open name.

If $e\in K$, some accepted certificate causes $\cyl{s_e}$ to appear in the enumeration. Conversely, every
nonempty entry comes from an accepted certificate, hence from an $e\in K$. Repetitions do not affect the union,
so $U_p=U$. Countable additivity on the disjoint cylinders now gives
$$\mu(U)=\sum_{e\in K}\mu(\cyl{s_e})=\sum_{e\in K}4^{-(e+1)}=\HaltingReal.$$
By §{sec:tte-real-examples}, a computable fast Cauchy name of this real would let a closed numerical lambda
program recover the digits of $K$ and decide diagonal halting. Thus the measure is noncomputable; since every
rational has a constant computable name, it is also irrational. The lower-approximation theorem still applies
to $p$, so the same measure has a computable increasing sequence of rational lower bounds converging to it.
\end{proof}

### Null Spheres {#sec:tte-null-spheres}

\begin{mathmeta}
  \vars{b,b_*,c,i,i_*,j,m,n,s,t,z,\ell,\rho_*,\tau}{Nat}
  \vars{\alpha,\beta}{Fun(Nat,Nat)}
  \vars{L}{Seq(Nat)}
  \vars{p,p_*}{Name}
  \vars{u_*,v_*,x_*,r_*,\zeta_*}{Real}
\end{mathmeta}

A \termdefineas{computable measure}{computable probability measure} on a computable Polish space is a Borel
probability measure supplied with a computable valuation: from an open name, one closed lambda program produces
rational lower bounds converging to the measure of the represented open set. The program is uniform in the open
name and the approximation stage. Use the rational-ball convention of §{sec:tte-effective-open-closed}, with zero
for an empty entry and successor codes for balls. Every numerical stream then names an open set. A lower
approximation need not come with a rate of convergence.

\begin{lemma*}[\termdefineas{complementary lower bounds}{Complementary lower bounds}]
Suppose that $\LambdaTermName{lowerBound}$ and $\LambdaTermName{complementBound}$ are closed numerical terms
computing rational
codes $\alpha( \NatPair{i}{s}), \beta( \NatPair{i}{s})$ whose values
$u_{i,s},v_{i,s}$ satisfy
$$\begin{aligned}
u_{i,s}&\le x_i,& v_{i,s}&\le 1-x_i,\\
\lim_s u_{i,s}&=x_i,& \lim_s v_{i,s}&=1-x_i.
\end{aligned}$$
One closed numerical term, on input $\NatPair{i}{n}$, returns a rational approximation to $x_i$ with error at most
$2^{-(n+1)}$. Fixing $i$ therefore gives a computable fast Cauchy name of $x_i$.
\end{lemma*}

\begin{proof}[Proof]
For input $\NatPair{i}{n}$, search through candidate codes $c=\NatPair{j}{s}$ and accept exactly when
$$j=i\quad\text{and}\quad 1-u_{j,s}-v_{j,s}<2^{-(n+1)}.$$
Let $\LambdaTermName{candidateTest}$ be the total numerical term returning one on acceptance and zero otherwise.
Numerical projections,
equality, rational arithmetic, the dyadic term, and rational comparison construct
$\LambdaTermName{candidateTest}$ from $\LambdaTermName{lowerBound}$, $\LambdaTermName{complementBound}$. With
$\LambdaTermName{reverseBit}:=\lambdaab{\tau}{\LambdaZeroTest\,\tau\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$, put
$$\begin{aligned}
&\LambdaTermName{fromBounds}:=\\
&\quad \lambdaab{z}{\LambdaResultSearch\,
 ( \lambdaab{c}{ \LambdaTermName{reverseBit}( \LambdaTermName{candidateTest}( \LambdaNumericPair\,z\,c))})\,
\LambdaTermName{lowerBound}}.
\end{aligned}$$
The test includes $j=i$, so evaluating $\LambdaTermName{lowerBound}$ on a successful candidate returns a lower
bound for the correct
family member. Since $1-u_{i,s}-v_{i,s}\to0$, an accepted candidate exists for every requested precision.
The result-search theorem gives the beta reduction to its output code.

For the returned lower bound $u_{i,s}$,
$$0\le x_i-u_{i,s}\le 1-v_{i,s}-u_{i,s}<2^{-(n+1)}.$$
If $p_i(n)$ is its code, the triangle inequality gives
$$\Abs{\RationalValue{p_i(n)}-\RationalValue{p_i(m)}}
 \le 2^{-(n+1)}+2^{-(m+1)}\le 2^{-n}\qquad(n\le m).$$
The outputs converge to $x_i$, so they form the required name. Neither monotonicity of the lower bounds nor a
modulus for their convergence was used.
\end{proof}

Fix a finite list $L=\Sequence{b_j}{j<\ell}$ of basic ball codes in $X$. Write
$b_j=\NatPair{i_j}{\rho_j}$ and $r_j=\RationalValue{\rho_j}$ for their center indices and radii, and put
$$\begin{aligned}
U_L&:=\bigcup_{j<\ell}\Ball{q_{i_j}}{r_j},\\
F_L&:=\bigcup_{j<\ell}\{x:d(x,q_{i_j})\le r_j\},\qquad V_L:=\SetDifference{X}{F_L}.
\end{aligned}$$
Here $F_L$ uses metric closed balls, which need not be the closures of the corresponding open balls.

\begin{proposition*}[\termdefineas{effective finite ball exteriors}{Finite ball unions and closed-ball exteriors}]
Both $U_L$ and $V_L$ have computable rational-ball enumerations. Their semidecision programs are constructed
from the finite list and the distance-approximation program.
\end{proposition*}

\begin{proof}[Proof]
Let $p$ be a Cauchy name of $x$, put $\varepsilon_t=2^{-t}$, and let $\zeta_{j,t}$ approximate
$d(q_{p(t)},q_{i_j})$ with error at most $\varepsilon_t$. The two total rational tests are
$$\zeta_{j,t}+2\varepsilon_t<r_j,\qquad r_j<\zeta_{j,t}-2\varepsilon_t.$$
The first certifies $x\in\Ball{q_{i_j}}{r_j}$; the second certifies $d(x,q_{i_j})>r_j$.
Indeed, the distance-approximation error and the Cauchy-name error give
$$\zeta_{j,t}-2\varepsilon_t\le d(x,q_{i_j})\le \zeta_{j,t}+2\varepsilon_t.$$
Conversely,
$$\begin{aligned}
\zeta_{j,t}+2\varepsilon_t&\le d(x,q_{i_j})+4\varepsilon_t,\\
 d(x,q_{i_j})-4\varepsilon_t&\le \zeta_{j,t}-2\varepsilon_t.
\end{aligned}$$
Each true strict inequality therefore passes its test at every sufficiently large stage.

For a single ball code $b$, let $I_b,E_b$ be the closed programs returning the acceptance bits of these tests
on input name $o$ and stage $t$. Compile the finite list by
$$\begin{aligned}
I_{[]}&:=\lambdaab{o}{\lambdaab{t}{\ChurchNumeral{0}}},\\
I_{b::L}&:=\lambdaab{o}{\lambdaab{t}{\LambdaAdd\,(I_b\,o\,t)\,(I_L\,o\,t)}},\\
E_{[]}&:=\lambdaab{o}{\lambdaab{t}{\ChurchNumeral{1}}},\\
E_{b::L}&:=\lambdaab{o}{\lambdaab{t}{\LambdaMul\,(E_b\,o\,t)\,(E_L\,o\,t)}}.
\end{aligned}$$
All stage computations terminate, including on streams that are not valid Cauchy names. Search for a nonzero
output of $I_L$ to semidecide $U_L$, and of $E_L$ to semidecide $V_L$. For the latter search, every point of
$V_L$ eventually satisfies all the finitely many tests at one common stage. The empty list gives the empty
union and the whole-space exterior. The effective-basis construction turns these two semidecision programs
into numerical enumerators of rational balls.
\end{proof}

\begin{theorem*}[\termdefineas{null-sphere measure computation}{Computing finite ball-union measures}]
Let $\mu$ be a computable probability measure. If
$$\mu(\{x:d(x,q_{i_j})=r_j\})=0\qquad(j<\ell),$$
then $\mu(U_L)$ has a computable fast Cauchy name. The program uses the valuation and the two enumerators
constructed above; it requires no rate witnessing the null-sphere hypotheses.
\end{theorem*}

\begin{proof}[Proof]
The relevant geometric comparison is
$$U_L\IncludedIn F_L,\qquad \SetDifference{F_L}{U_L}\IncludedIn
 \bigcup_{j<\ell}\{x:d(x,q_{i_j})=r_j\}.$$
For the second inclusion, a point of $\SetDifference{F_L}{U_L}$ lies in some closed ball and in none of the open
balls, so its distance to that closed ball's center equals the radius. The hypothesis makes this difference
null. The finite union $F_L$ is closed, and hence
$$\mu(U_L)=\mu(F_L),\qquad \mu(U_L)+\mu(V_L)=1.$$
Apply the valuation program to the computable enumerations of $U_L$ and $V_L$. Substitution of each numerical
enumerator for the input function gives closed numerical programs computing lower bounds $u_s,v_s$ for these
two measures, converging to them. The complementary-lower-bound lemma with the family index fixed then gives
a fast Cauchy name of $\mu(U_L)$.
\end{proof}

Null spheres are a sufficient condition. A set may have computable measure even when a sphere has positive
measure, for instance when that measure is supplied separately. For an arbitrary effectively open set, only
the lower computation is guaranteed, as the preceding Cantor-space example shows.

## Integration and the Fourier Transform {#sec:tte-fourier-examples}

### Polynomial Names and Integration {#sec:tte-polynomial-integration}

\begin{mathmeta}
  \forward{LambdaListLength,LambdaListGet,LambdaListTabulate}
  \vars{a,b,c,d,j,L,m,n,\gamma_*}{Nat}
  \vars{\ell}{Seq(Nat)}
  \vars{u,r_*}{Name}
  \vars{I}{Fun(Nat,Nat)}
  \vars{x,\varepsilon,\delta}{Real}
  \vars{p_*,q_*,q,P}{Fun(Real,Real)}
\end{mathmeta}

\begin{example*}[Integration on a compact interval]
Name $f\in C(\ClosedInterval{0}{1},\R)$ by rational polynomials $p_n$ satisfying
$$\sup_{x\in\ClosedInterval{0}{1}}\Abs{f(x)-p_n(x)}\le2^{-n}.$$
With this representation, $f\mapsto\int_0^1f(x)\,dx$ is computable.
\end{example*}

\begin{proof}[Proof]
Encode a rational polynomial by $c=\LambdaListCode{\ell}$, where $\ell$ is a finite list of rational coefficient codes.
If its length is $L$ and its entry at $j<L$ is $\gamma_j$, the polynomial is
$$q_c(x):=\sum_{j<L}\RationalValue{\gamma_j}x^j.$$
The empty list represents zero, and trailing zero coefficients are allowed. To integrate one monomial, divide its
coefficient by $j+1$. On rational codes this is the operation
$$\RationalCode{a}{b}{d}\longmapsto\RationalCode{a}{b}{(d+1)(j+1)-1}.$$
The new denominator is positive, so the subtraction is ordinary subtraction. The numerical projections, successor,
multiplication, predecessor, and pairing give a closed term for this operation. Starting with the rational-zero code,
use $\LambdaListLength$ to bound a recursion, $\LambdaListGet$ to read coefficient $j$, and $\LambdaRationalAdd$ to add
the divided coefficient to the accumulator. The coefficient list is retained as the recursion parameter. This gives a
closed term $\LambdaTermName{integratePoly}$ computing a code $I(c)$, with
$$\begin{aligned}
\LambdaTermName{integratePoly}\ChurchNumeral{c}&\to_\beta^*\ChurchNumeral{I(c)},\\
\RationalValue{I(c)}&=\sum_{j<L}\frac{\RationalValue{\gamma_j}}{j+1}=\int_0^1q_c(x)\,dx.
\end{aligned}$$
Induction on the number of processed coefficients proves the sum identity, and integration of the finite monomial sum
proves the last equality. For the empty list the recursion returns zero. Every natural input decodes as a finite list,
and every coefficient code denotes a rational, so this numerical program is total.

Write $u(n)$ for the code of the input polynomial $p_n=q_{u(n)}$. Exact polynomial integration gives the estimate
$$\Abs{\int_0^1f(x)\,dx-\RationalValue{I(u(n))}}
 \le\int_0^1\Abs{f(x)-p_n(x)}\,dx\le2^{-n}.$$
To obtain the pairwise bound required of a Cauchy name, use
$$r_u(n):=I(u(n+2)).$$
For $n\le m$, the triangle inequality gives
$$\Abs{\RationalValue{r_u(n)}-\RationalValue{r_u(m)}}
 \le2^{-(n+2)}+2^{-(m+2)}\le2^{-(n+1)}\le2^{-n}.$$
The approximation error tends to zero, so this name represents the integral.

Let $\LambdaTermName{shift}$ be a closed numerical term computing $n\mapsto n+2$. The single closed term
$$\LambdaTermName{integrate}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{integratePoly}\,(o\,(
\LambdaTermName{shift}\,n))}}$$
realizes the integral operator. Two beta steps expose the query, the numerical computation of
$\LambdaTermName{shift}$ gives $n+2$, one
input query returns $\ChurchNumeral{u(n+2)}$, and the computation of $\LambdaTermName{integratePoly}$ returns
the integral code. Hence
$$\LambdaInputSteps{u}{\LambdaTermName{integrate}\,o\,\ChurchNumeral{n}}{\ChurchNumeral{r_u(n)}}.$$
This works for every valid input name, including names that are not themselves computable. Confluence excludes other
numeral outputs, and the preceding error bounds establish correctness in the real Cauchy representation.

Finally, such names exist for every continuous function. For any $\varepsilon>0$, the Weierstrass approximation
theorem gives a real polynomial $P$ approximating $f$ within $\varepsilon/2$ on $\ClosedInterval{0}{1}$. Take $L\ge1$
large enough to
include all its coefficients. Approximate each of them by a rational within
$\delta:=\varepsilon/(2L)$. For the resulting rational polynomial $q$ and $0\le x\le1$,
$$\Abs{q(x)-P(x)}\le\sum_{j<L}\delta\Abs{x}^j\le L\delta=\varepsilon/2.$$
Together with the first approximation this gives the requested accuracy. Taking $\varepsilon=2^{-n}$ for each $n$
produces a polynomial name. Its uniform error bound is supplied by the name; values at finitely many sample points
alone do not provide that information.
\end{proof}

### Fourier Transforms from Norm Approximations {#sec:tte-fourier-norm-names}

\begin{mathmeta}
  \define{LpNorm,FourierTransform}
  \vars{M,N,R,i,j,m,n}{Nat}
  \vars{x,y,\rho}{Real}
  \vars{L,c,d,u,v,z}{Nat}
  \vars{a,b}{Real}
  \vars{\zeta,\theta}{Cplx}
  \vars{\nu_*}{Cplx}
\end{mathmeta}

For functions on the whole real line, specify how the input controls the integral. Let $L^1(\R,\C)$ consist of
integrable functions modulo equality almost everywhere, with norm $\LpNorm{1}{f}:=\int_{\R}\Abs{f(x)}\,dx$. Use finite
sums
of interval indicators with rational endpoints and coefficients in $\QQ+\mathrm i\QQ$ as dense approximants; each such
step function vanishes outside a bounded interval. An input name supplies such functions $s_n$ with
$\LpNorm{1}{f-s_n}\le2^{-n}$. Define
$$\FourierTransform{f}(\xi):=\int_{\R}f(x)e^{-2\pi\mathrm i x\xi}\,dx.$$
For the output in $C(\R,\C)$, a name supplies, for each positive integer $R$ and precision $n$, a polynomial with
rational complex coefficients approximating the function uniformly on $\ClosedInterval{-R}{R}$ within $2^{-n}$. This is
the locally
uniform representation.

<!-- formalization: skip (conceptual link to the representation-classification example) -->
The frequency $\xi$ is also the real parameter classifying irreducible representations of $C_0(\R)$ in
§{sec:borel-reducibility}: under the Fourier identification described there, evaluation at $\xi$ sends the
element represented by $f$ to $\FourierTransform{f}(\xi)$. Smoothness gives a Borel classification by real
parameters; it does not imply computability. Here we prove the additional assertion that an $L^1$ name of $f$
can be transformed computably into a locally uniform name of $\FourierTransform{f}$.

Take each interval indicator to be one on $\RightClosedInterval{a}{b}$, with $a\le b$, and zero elsewhere. Changing
either endpoint's
value does not change its almost-everywhere class. An input name determines at most one element of $L^1$: if the same
step functions name both $f$ and $g$, then
$$\LpNorm{1}{f-g}\le\LpNorm{1}{f-s_n}+\LpNorm{1}{g-s_n}\le2\cdot2^{-n}$$
for every $n$. Letting $n\to\infty$ gives $f=g$ in $L^1$.

<!-- formalization: skip (cited external density of compactly supported continuous functions in L1) -->
To prove existence of input names, we use the standard density of continuous functions with compact support in
$L^1$; see [@Faris2004, Theorem 9.16]. The complex-valued case follows by approximating the real and imaginary parts
separately.

\begin{lemma*}[\termdefineas{Rational interval step representation}{Rational interval step representation}]
Every element of $L^1(\R,\C)$ has a name by rational interval step functions with the prescribed error bounds.
\end{lemma*}

\begin{proof}[Proof]
Fix $f\in L^1(\R,\C)$ and $\varepsilon>0$. By this density, choose a continuous function $g$ with compact support and
$\LpNorm{1}{f-g}\le\varepsilon/2$. Take a positive integer
$R$ such that $g(x)=0$ outside $\OpenInterval{-R}{R}$, and put $\eta:=\varepsilon/(8R)$. Uniform continuity on
$\ClosedInterval{-R}{R}$ gives a
$\delta>0$ such that
$$\Abs{g(x)-g(y)}<\eta\qquad(x,y\in\ClosedInterval{-R}{R},\ \Abs{x-y}<\delta).$$
Choose an integer $N\ge1$ with $2R/N<\delta$, and set
$$a_i:=-R+\frac{2Ri}{N}\qquad(0\le i\le N).$$
For each $i<N$, choose $\nu_i\in\QQ+\mathrm i\QQ$ with $\Abs{g(a_i)-\nu_i}<\eta$. Define
$$s(x):=\begin{cases}
\nu_i,&a_i<x\le a_{i+1}\text{ for some }i<N,\\
0,&x\notin\RightClosedInterval{-R}{R}.
\end{cases}$$
The intervals are disjoint and cover $\RightClosedInterval{-R}{R}$, so this defines a rational interval step function.
On its $i$th
interval,
$$\Abs{g(x)-s(x)}\le\Abs{g(x)-g(a_i)}+\Abs{g(a_i)-\nu_i}<2\eta.$$
Outside $\RightClosedInterval{-R}{R}$, both functions vanish. Hence
$$\LpNorm{1}{g-s}\le2R\cdot2\eta=\varepsilon/2,\qquad
\LpNorm{1}{f-s}\le\LpNorm{1}{f-g}+\LpNorm{1}{g-s}\le\varepsilon.$$

Applying this construction with $\varepsilon=2^{-n}$ for each $n$ gives the required name. The rational endpoints and
rational complex values have finite numerical codes, so each approximant has the list code used by the name
transformer below. This proves that every $L^1$ element has a name; it does not supply a computable choice of a name
from an element given without any representation.
\end{proof}

\begin{lemma*}[\termdefineas{Locally uniform polynomial representation}{Locally uniform polynomial representation}]
Every function in $C(\R,\C)$ has a locally uniform name by rational complex polynomials. Two continuous functions
with the same name are equal.
\end{lemma*}

\begin{proof}[Proof]
Fix $g\in C(\R,\C)$, a positive integer $R$, and $\varepsilon>0$. Apply the real Weierstrass approximation theorem
separately to the real and imaginary parts of $g$ on $\ClosedInterval{-R}{R}$, with error less than $\varepsilon/4$ for
each part.
Combining the two real polynomials gives a complex polynomial $A$ satisfying
$$\sup_{\Abs{x}\le R}\Abs{A(x)-g(x)}<\varepsilon/2.$$
Take $N\ge1$ large enough to include all coefficients of $A$, and approximate each coefficient by a rational complex
number within
$$\delta:=\frac{\varepsilon}{2N(R+1)^N}.$$
Such approximations exist by the density of rational real and imaginary parts. For the resulting rational complex
polynomial $P$, the triangle inequality and $\Abs{x}^j\le(R+1)^N$ for $j<N$ give
$$\begin{aligned}
\sup_{\Abs{x}\le R}\Abs{P(x)-A(x)}&\le N\delta(R+1)^N=\varepsilon/2,\\
\sup_{\Abs{x}\le R}\Abs{P(x)-g(x)}&<\varepsilon.
\end{aligned}$$
Choosing such a polynomial with $\varepsilon=2^{-n}$ for each $R,n$ produces the required name. These choices prove
existence; no procedure for making them is assumed.

For uniqueness, suppose the same name represents $g$ and $h$, and fix $x\in\R$. Choose a positive integer
$R>\Abs{x}$. If $P_{R,n}$ is the polynomial supplied by that name, then
$$\Abs{g(x)-h(x)}\le\Abs{g(x)-P_{R,n}(x)}+\Abs{h(x)-P_{R,n}(x)}\le2\cdot2^{-n}.$$
Letting $n\to\infty$ proves $g(x)=h(x)$. Since $x$ was arbitrary, the two functions are equal.
\end{proof}

\begin{mathmeta}
  \define{ExponentialPartialSum,FourierSeriesCutoff,IntervalFourierPolynomial}
\end{mathmeta}

\begin{lemma*}[\termdefineas{Uniform truncation for interval Fourier transforms}{Uniform truncation for interval
Fourier transforms}]
Let $a\le b$, $\rho>0$, and let $M,n\in\NN$ satisfy $2\pi \rho\max(\Abs{a},\Abs{b})\le M$. Set
$$\FourierSeriesCutoff{M}{n}:=2M+2M^2+n+3$$
and, for $N\in\NN$, put
$$\IntervalFourierPolynomial{a}{b}{N}{\xi}:=
 \sum_{j<N}\frac{(-2\pi\mathrm i\xi)^j(b^{j+1}-a^{j+1})}{(j+1)!}.$$
Then, with $N=\FourierSeriesCutoff{M}{n}$,
$$\sup_{\Abs{\xi}\le \rho}\Abs{\int_a^b e^{-2\pi\mathrm i x\xi}\,dx
-\IntervalFourierPolynomial{a}{b}{N}{\xi}}\le(b-a)2^{-(n+2)}.$$
A closed numerical lambda term computes $\FourierSeriesCutoff{M}{n}$ from $M,n$. If $a,b$ are rational and $\rho$ is a
positive integer, a suitable $M$ can also be computed from their codes.
\end{lemma*}

\begin{proof}[Proof]
Write $\ExponentialPartialSum{N}{\zeta}:=\sum_{j<N}\zeta^j/j!$. For $r\ge0$, put $t_k=r^k/k!$. If $k+1\ge2r$, then
$$t_{k+1}=t_k\frac{r}{k+1}\le\frac{t_k}{2}.$$
Thus $t_{N+i}\le t_N2^{-i}$ whenever $N+1\ge2r$. Absolute convergence of the exponential series and the geometric
sum give, for $\Abs{\zeta}\le r$,
$$\Abs{e^\zeta-\ExponentialPartialSum{N}{\zeta}}\le\sum_{i=0}^{\infty}t_{N+i}\le2t_N.$$
To make the cutoff explicit, take $r=M\in\NN$. Since $M\le2^M$ and $(2M)!\ge1$,
$$t_{2M}\le M^{2M}\le2^{2M^2}.$$
Starting at $2M$, each further step halves the bound. For $N=\FourierSeriesCutoff{M}{n}$ there are $2M^2+n+3$ such
steps, so
$$\Abs{e^\zeta-\ExponentialPartialSum{N}{\zeta}}
 \le2\cdot2^{2M^2}2^{-(2M^2+n+3)}=2^{-(n+2)}.$$
This includes $M=0$, using the usual convention $M^0=1$.

For $x\in\ClosedInterval{a}{b}$ and $\Abs{\xi}\le \rho$, the exponent
$\zeta=-2\pi\mathrm i x\xi$ has modulus at most $M$.
Integrating the last
bound over $\ClosedInterval{a}{b}$ gives the required error. Indeed, integrating the finite sum term by term yields
$$\int_a^b\ExponentialPartialSum{N}{-2\pi\mathrm i x\xi}\,dx
 =\IntervalFourierPolynomial{a}{b}{N}{\xi}.$$
The construction uses no division by $\xi$ and works at $\xi=0$ as well. Its coefficients involve $\pi$; they will be
approximated by rational complex numbers below.

For the numerical construction, read $M,n$ by projections, compute $t=2M$, and then compute $t+tM+n+3$ using the
addition and multiplication terms. Their composition gives a closed term $D$ with
$$D\ChurchNumeral{\NatPair{M}{n}}\to_\beta^*\ChurchNumeral{\FourierSeriesCutoff{M}{n}}.$$
To choose $M$, suppose the endpoint codes are $\RationalCode{p_a}{q_a}{d_a}$ and
$\RationalCode{p_b}{q_b}{d_b}$. Their values have absolute values at most $p_a+q_a$ and $p_b+q_b$. Thus
$$M:=8\rho(p_a+q_a+p_b+q_b)$$
suffices because $\pi\le4$. The numerical projections, addition, and multiplication also compute this bound by a
closed term. Neither construction requires a search or a test for equality of real numbers.
\end{proof}

\begin{mathmeta}
  \define{IntervalFourierCoefficient,FourierCoefficientSensitivity}
\end{mathmeta}

\begin{lemma*}[\termdefineas{Computable coefficients of interval Fourier transforms}{Computable coefficients of interval
Fourier transforms}]
For rational endpoints $a,b$ and $j\in\NN$, let
$$\IntervalFourierCoefficient{a}{b}{j}:=
 \frac{(-2\pi\mathrm i)^j(b^{j+1}-a^{j+1})}{(j+1)!}.$$
One closed numerical lambda term, given codes for $a,b$ and integers $j,m\in\NN$, returns a rational complex number
$\widetilde c_j$ satisfying
$$\Abs{\widetilde c_j-\IntervalFourierCoefficient{a}{b}{j}}\le2^{-(m+3)}.$$
\end{lemma*}

\begin{proof}[Proof]
Suppose the endpoint codes are $\RationalCode{p_a}{q_a}{d_a}$ and $\RationalCode{p_b}{q_b}{d_b}$. Set
$$S:=p_a+q_a+p_b+q_b+1,\qquad
 \FourierCoefficientSensitivity{j}{S}:=4j10^jS^{j+1}.$$
Then $S\ge1$ and $\Abs{a},\Abs{b}\le S$. Put $k:=m+\FourierCoefficientSensitivity{j}{S}$, and compute a rational
approximation $q$ to $\pi$ by the construction in §{sec:tte-real-examples}, so that
$$\Abs{q-\pi}\le2^{-(k+3)}.$$
Define
$$\widetilde c_j:=\mathrm i^j\frac{(-2q)^j(b^{j+1}-a^{j+1})}{(j+1)!}.$$
This is rational complex, including at degree zero.

First check the error. Since $\Abs{q-\pi}\le1$ and $\pi\le4$, we have $\Abs{q}\le5$, and hence
$\Abs{-2q},\Abs{-2\pi}\le10$.
Induction using
$$\zeta^{j+1}-\theta^{j+1}=\zeta^j(\zeta-\theta)+\theta(\zeta^j-\theta^j)$$
shows that, for $\Abs{\zeta},\Abs{\theta}\le10$,
$$\Abs{\zeta^j-\theta^j}\le j10^j\Abs{\zeta-\theta}.$$
Also $\Abs{b^{j+1}-a^{j+1}}\le2S^{j+1}$, $\Abs{\mathrm i^j}=1$, and $(j+1)!\ge1$. Therefore
$$\Abs{\widetilde c_j-\IntervalFourierCoefficient{a}{b}{j}}
 \le\FourierCoefficientSensitivity{j}{S}\Abs{q-\pi}.$$
Writing $H=\FourierCoefficientSensitivity{j}{S}$ and using $H\le2^H$ gives
$$\Abs{\widetilde c_j-\IntervalFourierCoefficient{a}{b}{j}}
 \le H2^{-(m+H+3)}\le2^{-(m+3)}.$$
There is no exception at $j=0$: both coefficients equal $b-a$ and $H=0$.

It remains to describe the closed term producing this rational complex number. Multiplication of two rational codes
is implemented by
$$\begin{aligned}
&\Pair{\RationalCode{p}{q}{d}}{\RationalCode{u}{v}{e}}\\
 &\longmapsto\RationalCode{pu+qv}{pv+qu}{(d+1)(e+1)-1}.
\end{aligned}$$
The denominator is positive, so the displayed subtraction is ordinary subtraction. The projections, natural addition
and multiplication, predecessor, and pairing implement this formula. Swapping the two numerator components negates a
rational code; combine this with rational addition to subtract. Starting from $\RationalCode{1}{0}{0}$ and repeatedly
multiplying by a retained base computes its powers. The same recursion with natural multiplication computes the powers
in $H$. Factorial recursion followed by pairing produces $\RationalCode{1}{0}{(j+1)!-1}$, the reciprocal of the positive
factorial. These operations compute the real scalar in the formula for $\widetilde c_j$ exactly.

Represent a rational complex number by the pair of its real and imaginary rational codes. On rational values,
iterate $\Pair{\alpha}{\beta}\mapsto\Pair{-\beta}{\alpha}$ starting at $\Pair{1}{0}$.
The corresponding code operations compute $\mathrm i^j$. Multiply its two components by the
real scalar just computed. All recursions have a numerical iteration count and retain the endpoint and precision
parameters. If $c_a,c_b$ are the input endpoint codes, put
$$z:=\NatPair{c_a}{\NatPair{c_b}{\NatPair{j}{m}}}.$$
The resulting closed term $C$ satisfies
$$C\ChurchNumeral{z}\to_\beta^*\ChurchNumeral{\NatPair{u}{v}},\qquad
 \widetilde c_j=\RationalValue{u}+\mathrm i\RationalValue{v}.$$
Induction on the arithmetic recursions proves these reductions, and the preceding estimates give the required error.
\end{proof}

\begin{proposition*}[\termdefineas{computable Fourier transform on L1}{Computability of the Fourier transform on $L^1$}]
With the preceding representations, the operator
$$f\longmapsto\FourierTransform{f}:L^1(\R,\C)\longrightarrow C(\R,\C)$$
is computable. Its basic error bound is
$$\sup_{\xi\in\R}\Abs{\FourierTransform{f}(\xi)-\FourierTransform{g}(\xi)}
 \le\LpNorm{1}{f-g}.$$
\end{proposition*}

\begin{proof}[Proof]
Since $\Abs{e^{-2\pi\mathrm i x\xi}}=1$, multiplying an integrable function by this kernel preserves integrability.
Linearity and the norm inequality for the integral therefore give
$$\begin{aligned}
\Abs{\FourierTransform{f}(\xi)-\FourierTransform{g}(\xi)}
 &=\Abs{\int_{\R}(f(x)-g(x))e^{-2\pi\mathrm i x\xi}\,dx}\\
 &\le\int_{\R}\Abs{f(x)-g(x)}\,dx=\LpNorm{1}{f-g}.
\end{aligned}$$
The bound is independent of the frequency. Almost-everywhere equal representatives have the same integral, so this
estimate is well defined on $L^1$. Dominated convergence, with integrable majorant $\Abs{f}$, also proves that
$\FourierTransform{f}$ is continuous.

Fix an output window $\ClosedInterval{-R}{R}$ and precision $n$, and take the input approximant $s_{n+2}$. Write it as a
finite sum
of interval indicators with rational complex coefficients $v_\ell$ and rational endpoints $a_\ell\le b_\ell$, for
$\ell<L$. Every summand is integrable, since its support is bounded and its value is constant on the interval.
Multiplication by the kernel commutes with the finite sum. Integrating each indicator over the real line restricts
the integral to its interval, so
$$\FourierTransform{s_{n+2}}(\xi)=\sum_{\ell<L}v_\ell
 \int_{a_\ell}^{b_\ell}e^{-2\pi\mathrm i x\xi}\,dx.$$
This identity connects the finite interval computations to the Fourier transform of the supplied step function.

Here are explicit integer bounds computable from the finite input. For a rational code
$c=\RationalCode{p}{q}{d}$, put $h(c):=p+q$, so that $\Abs{\RationalValue{c}}\le h(c)$. Write
$$a_\ell=\RationalValue{c^a_\ell},\quad b_\ell=\RationalValue{c^b_\ell},\quad
 v_\ell=\RationalValue{u_\ell}+\mathrm i\RationalValue{w_\ell}.$$
Set
$$\begin{aligned}
 E_\ell&:=h(c^a_\ell)+h(c^b_\ell),& W_\ell&:=h(u_\ell)+h(w_\ell),\\
 M&:=8R\sum_{\ell<L}E_\ell,& A&:=\sum_{\ell<L}W_\ell E_\ell,\\
 V&:=\sum_{\ell<L}W_\ell.
\end{aligned}$$
The endpoint estimate and $\pi\le4$ show that $M$ satisfies the
\termuseas{Uniform truncation for interval Fourier transforms}{uniform truncation lemma} for every interval.
Moreover, $b_\ell-a_\ell\le E_\ell$ and $\Abs{v_\ell}\le W_\ell$, so
$$\sum_{\ell<L}\Abs{v_\ell}(b_\ell-a_\ell)\le A,\qquad \sum_{\ell<L}\Abs{v_\ell}\le V.$$
These are bounded sums of natural numbers; the empty list gives $M=A=V=0$. Set
$$N:=\FourierSeriesCutoff{M}{n+A},\qquad
 B(\xi):=\sum_{\ell<L}v_\ell\IntervalFourierPolynomial{a_\ell}{b_\ell}{N}{\xi}.$$
Linearity of the integral and the triangle inequality give
$$\begin{aligned}
\sup_{\Abs{\xi}\le R}\Abs{\FourierTransform{s_{n+2}}(\xi)-B(\xi)}
 &\le A2^{-(n+A+2)}\\
 &\le2^{-(n+2)},
\end{aligned}$$
where the last inequality uses $A\le2^A$.

Put
$$Q:=N(R+1)^N,\qquad m:=n+V+Q,\qquad \delta:=\frac{2^{-(n+2)}}{Q}.$$
Apply the preceding coefficient lemma at precision $m$ to every interval and degree $j<N$. Multiply the resulting
rational complex approximations by $v_\ell$ and add them exactly. The error of each coefficient of $B$ is at most
$$V2^{-(m+3)}\le2^{-(n+Q+3)}\le\delta,$$
because $V\le2^V$ and $Q\le2^Q$. Include zero coefficients to form a list of length $N$, and let $P$ be the resulting
rational complex polynomial. Since $R\ge1$ and $N\ge1$,
$$\sup_{\Abs{\xi}\le R}\Abs{B(\xi)-P(\xi)}\le\sum_{j<N}\delta R^j\le2^{-(n+2)}.$$

We now assemble the finite coefficient list by closed terms. Encode row $\ell$ by
$$d_\ell:=\NatPair{c^a_\ell}{\NatPair{c^b_\ell}{\NatPair{u_\ell}{w_\ell}}},\qquad
 c:=\LambdaListCode{[d_\ell]_{\ell<L}}.$$
For fixed $m,j$, retain $c,m,j$ as the recursion parameter. At stage $\ell<L$, read the row with
$\LambdaListGet$, project its entries, and apply the coefficient term $C$ to the endpoint codes and $j,m$.
Multiply the result by the row's rational complex weight and add it to the accumulator, initially zero.
The required complex arithmetic uses rational arithmetic on the two components:
$$\begin{aligned}
 \Pair{\alpha}{\beta}+\Pair{\gamma}{\delta}&=\Pair{\alpha+\gamma}{\beta+\delta},\\
 \Pair{\alpha}{\beta}\Pair{\gamma}{\delta}&=\Pair{\alpha\gamma-\beta\delta}{\alpha\delta+\beta\gamma}.
\end{aligned}$$
Induction on the number of processed rows shows that the accumulator denotes the sum of their weighted approximate
coefficients. An empty row list returns zero. This gives a closed term $F$ computing the coefficient code
$\gamma(c,m,j)$ on input $\NatPair{\NatPair{c}{m}}{j}$. Use $\LambdaListTabulate{F}$ with parameter $\NatPair{c}{m}$
and length $N$ to append these codes in increasing degree. Its output is exactly
$$\LambdaListCode{[\gamma(c,m,0),\ldots,\gamma(c,m,N-1)]}.$$
The index $N-1$ is defined because $N\ge1$. This list denotes $P$; no test for a zero coefficient is needed.

The bounds $M,A,V$ are also computed by bounded recursions over the same row list. The cutoff term and natural
power term then compute $N,Q,m$. Composing these operations with the tabulation gives a closed numerical term $K$
which, on input $\NatPair{c}{\NatPair{R}{n}}$, returns the code $k(c,R,n)$ of $P$. All recursion lengths are
computed natural numbers. Every rational code has a positive denominator, so the numerical program terminates on
all inputs; ordered endpoints are needed for the integral estimate, not for termination.

Combining the input error, the series tail, and the coefficient error gives
$$\sup_{\Abs{\xi}\le R}\Abs{\FourierTransform{f}(\xi)-P(\xi)}\le3\cdot2^{-(n+2)}<2^{-n}.$$
To obtain a single term acting on names, let $p(t)$ be the code of $s_t$ and encode the output request by
$z=\NatPair{R}{n}$. Let $U$ compute $z\mapsto n+2$. First lift $U$ to a program that ignores its name argument,
then query the input at the returned index. Pair this answer with the unchanged output request and apply $K$.
The query, pairing, and output-composition constructions give a closed term $\Phi$. After the elementary beta
reductions that expose these compositions, its computation is
$$\Phi\,o\,\ChurchNumeral{z}\to_\beta^*
 K\bigl(\LambdaNumericPair\,(o\,(U\ChurchNumeral{z}))\,\ChurchNumeral{z}\bigr).$$
The numerical computation of $U$ returns $n+2$, one query returns $p(n+2)$, and pairing followed by $K$ gives
$$\LambdaInputSteps{p}{\Phi\,o\,\ChurchNumeral{z}}{\ChurchNumeral{k(p(n+2),R,n)}}.$$
The construction works for every valid input name, including noncomputable names. The preceding estimate proves
that the output is a name of the Fourier transform, and confluence excludes other numeral outputs.
\end{proof}

\begin{example*}[An explicit Fourier transform]
For $f(x)=e^{-\Abs{x}}$, both an $L^1$-name and the Fourier transform can be computed. With our normalization,
$$\FourierTransform{f}(\xi)=\frac{2}{1+4\pi^2\xi^2}.$$
\end{example*}

\begin{proof}[Proof]
Put $f(x):=e^{-\Abs{x}}$. On the negative half-line it equals $e^x$, and on the positive half-line it equals $e^{-x}$.
The two improper integrals converge, so $f\in L^1(\R,\C)$. For every positive integer $R$,
$$\int_{\SetDifference{\R}{\RightClosedInterval{-R}{R}}}\Abs{f(x)}\,dx
 =\int_{-\infty}^{-R}e^x\,dx+\int_R^\infty e^{-x}\,dx
 =2e^{-R}\le2\cdot2^{-R}.$$
The last inequality follows from $e\ge2$.

The function is Lipschitz with constant one. Indeed, if $0\le a\le b$, then
$$0\le e^{-a}-e^{-b}=e^{-a}(1-e^{a-b})\le b-a,$$
using $e^{-a}\le1$ and $e^{a-b}\ge1+a-b$. Apply this estimate to $\Abs{x},\Abs{y}$ in increasing order and use
$\Abs{\Abs{x}-\Abs{y}}\le\Abs{x-y}$ to obtain $\Abs{f(x)-f(y)}\le\Abs{x-y}$.

For precision $n$, choose the integer parameters and grid
$$\begin{aligned}
R&:=n+3,& L&:=2R^2\cdot2^{n+4},& m&:=n+R+2,\\
a_i&:=-R+\frac{2Ri}{L}\quad(0\le i\le L),&
h&:=\frac{2R}{L}=\frac{2^{-(n+4)}}{R}.
\end{aligned}$$
The intervals $\RightClosedInterval{a_i}{a_{i+1}}$ for $i<L$ partition $\RightClosedInterval{-R}{R}$.

Set $K:=\FourierSeriesCutoff{R}{m}$ and take the rational values
$$\nu_i:=\ExponentialPartialSum{K}{-\Abs{a_i}}
 =\sum_{j<K}\frac{(-\Abs{a_i})^j}{j!}\qquad(i<L).$$
Since $\Abs{a_i}\le R$, the exponential-series estimate proved in the uniform truncation lemma gives
$$\Abs{f(a_i)-\nu_i}\le2^{-(m+2)}
 =2^{-(n+4)}2^{-R}\le\frac{2^{-(n+4)}}{R}=h,$$
where the last inequality uses $R\le2^R$. These values are computed by closed terms: compare the two unsigned
numerator parts of the rational code to form the code of $-\Abs{a_i}$, compute successive powers and factorials, and sum
the first $K$ rational terms with an accumulator initially zero. The cutoff and every summand use only the numerical
arithmetic and recursors already constructed.

Let $s_n$ take value $\nu_i$ on $\RightClosedInterval{a_i}{a_{i+1}}$ and zero outside $\RightClosedInterval{-R}{R}$. For
$x$ in its $i$th interval,
$$\Abs{f(x)-s_n(x)}\le\Abs{f(x)-f(a_i)}+\Abs{f(a_i)-\nu_i}\le h+h=2h.$$
Integrating over the window and adding the tail gives
$$\begin{aligned}
\LpNorm{1}{f-s_n}&\le2\cdot2^{-R}+2R\cdot2h\\
 &=2^{-(n+2)}+2^{-(n+2)}=2^{-(n+1)}\le2^{-n}.
\end{aligned}$$
Thus the sequence satisfies the required $L^1$ error bound.

To produce the name as a finite list, use the endpoint codes
$$c_i:=\RationalCode{2Ri}{RL}{L-1}\qquad(0\le i\le L),$$
where $L\ge1$ ensures that $L-1$ is defined. Let $w_i$ be the rational complex code for $\nu_i$ returned by the series
computation. Retain $\NatPair{R}{\NatPair{L}{m}}$ as a parameter. A closed row term $G$ takes this parameter and $i$
and returns
$$d_i:=\NatPair{c_i}{\NatPair{c_{i+1}}{w_i}}.$$
The finite tabulation term $\LambdaListTabulate{G}$ lists these rows for $i<L$. Composing it with the calculation
of $R,L,m$ gives a closed term $A$ satisfying
$$A\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{\LambdaListCode{[d_i]_{i<L}}}.$$
The decoded step function is exactly $s_n$, so this is a computable $L^1$-name, with no unspecified choices.

Finally, split the Fourier integral at zero. On each half-line, multiply the exponential kernel by the corresponding
expression for $f$ and integrate the resulting decaying exponential. This gives
$$\FourierTransform{f}(\xi)=\frac{1}{1+2\pi\mathrm i\xi}+\frac{1}{1-2\pi\mathrm i\xi}
=\frac{2}{1+4\pi^2\xi^2}.$$
The real denominator is at least one. To compute a locally uniform name of the entire transform, apply the closed
name transformer $\Phi$ from the preceding proposition to $A$. Substitution of a computable input name, proved in
§{sec:lambda-input-composition}, replaces each query by an ordinary beta computation. Thus $\Phi A$ is a closed
numerical term computing the output polynomial codes, and the proposition proves that
they approximate this Fourier transform.
\end{proof}

### Why the Input Representation Matters {#sec:tte-representation-strength}

\begin{mathmeta}
  \define{BernsteinBasis,BernsteinApproximation}
  \vars{R}{Nat}
  \vars{s}{Nat}
  \vars{t}{Real}
  \vars{n}{Nat}
\end{mathmeta}

\begin{lemma*}[\termdefineas{Quantitative Bernstein approximation}{Quantitative Bernstein approximation}]
Let $g:\ClosedInterval{0}{1}\to\R$ satisfy $\Abs{g(u)-g(v)}\le L\Abs{u-v}$ for some $L\ge0$.
For an integer $d\ge1$, define the \termdefine{Bernstein polynomial} by
$$\begin{aligned}
 \BernsteinBasis{d}{j}{t}&:=\binom dj t^j(1-t)^{d-j},\\
 \BernsteinApproximation{d}{g}{t}&:=\sum_{j=0}^{d}g(j/d)\BernsteinBasis{d}{j}{t}.
\end{aligned}$$
Then, for every $t\in\ClosedInterval{0}{1}$,
$$\Abs{\BernsteinApproximation{d}{g}{t}-g(t)}\le\frac{L}{2\sqrt d}.$$
\end{lemma*}

\begin{proof}[Proof]
The binomial theorem and its first two derivatives give
$$\sum_{j=0}^{d}\BernsteinBasis{d}{j}{t}=1,\qquad
 \sum_{j=0}^{d}(t-j/d)^2\BernsteinBasis{d}{j}{t}=\frac{t(1-t)}d.$$
The weights are nonnegative. Put
$$D:=\sum_{j=0}^{d}\Abs{t-j/d}\BernsteinBasis{d}{j}{t}.$$
The finite Cauchy--Schwarz inequality gives
$$\begin{aligned}
 D^2&\le\left(\sum_{j=0}^{d}\BernsteinBasis{d}{j}{t}\right)
       \left(\sum_{j=0}^{d}(t-j/d)^2\BernsteinBasis{d}{j}{t}\right)\\
 &=\frac{t(1-t)}d\le\frac1{4d}.
\end{aligned}$$
Since $D\ge0$, it follows that $D\le1/(2\sqrt d)$.

Subtract $g(t)$ using the fact that the weights sum to one, and apply the Lipschitz bound:
$$\begin{aligned}
 \Abs{\BernsteinApproximation{d}{g}{t}-g(t)}
 &\le\sum_{j=0}^{d}\BernsteinBasis{d}{j}{t}\Abs{g(j/d)-g(t)}\\
 &\le LD\le\frac{L}{2\sqrt d}.
\end{aligned}$$
\end{proof}

\begin{example*}[A computable integrable function with a noncomputable integral]
Pointwise computation, even with effective uniform approximation on every compact interval, does not supply an
$L^1$-name. There is a nonnegative computable continuous integrable function $f$ with
$$\FourierTransform{f}(0)=\int_{\R}f(x)\,dx=\HaltingReal.$$
Thus its Fourier transform is not a computable continuous function.
\end{example*}

\begin{proof}[Proof]
Use the increasing rational approximation $a_s\uparrow\HaltingReal$ from §{sec:tte-real-examples}. Put
$$c_0:=a_0,\qquad c_{s+1}:=a_{s+1}-a_s\quad(s\in\NN).$$
These are computable nonnegative rationals, and their partial sums telescope:
$$\sum_{s=0}^{N}c_s=a_N,\qquad
 \sum_{s=0}^{\infty}c_s=\HaltingReal
 \le\sum_{e=0}^{\infty}4^{-(e+1)}=\frac13.$$
A closed term computes a code for $c_s$: at zero use the code for $a_0$; at a positive index compute the two
successive approximants and subtract them using rational arithmetic.

Define the triangular bump and the function by
$$\tau(x):=\max(1-\Abs{x},0),\qquad
 f(x):=\sum_{s=0}^{\infty}c_s\tau(x-3s).$$
The function is nonnegative. For an integer $R\ge0$, if $\Abs{x}\le R$ and $s\ge R+1$, then
$$3s-x\ge3(R+1)-R\ge1,\qquad \tau(x-3s)=0.$$
Consequently,
$$f(x)=\sum_{s=0}^{R}c_s\tau(x-3s)\qquad(\Abs{x}\le R).$$
This is an exact finite description on the whole interval, including its endpoints. Each summand is continuous,
and every point has a neighborhood in some such interval, so $f$ is continuous.

There is also a global Lipschitz bound. Taking the maximum with zero does not increase distances, and
$\Abs{\Abs{u}-\Abs{v}}\le\Abs{u-v}$, so $\Abs{\tau(u)-\tau(v)}\le\Abs{u-v}$.
For any $x,y$, choose an integer $R$ containing both in the preceding window. Then
$$\begin{aligned}
\Abs{f(x)-f(y)}&\le\sum_{s=0}^{R}c_s\Abs{\tau(x-3s)-\tau(y-3s)}\\
 &\le a_R\Abs{x-y}\le\Abs{x-y}.
\end{aligned}$$

To evaluate at a rational input with code $i=\RationalCode{u}{v}{w}$, take $R=u+v$, which bounds $\Abs{q_i}$.
For each $s\le R$, compute $c_s$, subtract $3s$ from $q_i$, take the absolute value, subtract it from one, and
replace the result by zero if it is negative. Multiply it by $c_s$ and add the terms using a finite recursion
that retains $i$ as its parameter. All these operations use the closed rational programs already constructed.
Thus a closed term $E$ computes a numerical function $g$ with
$$E\ChurchNumeral{i}\to_\beta^*\ChurchNumeral{g(i)},\qquad q_{g(i)}=f(q_i).$$

If $p$ is a Cauchy name of $x$, set $F(p)(n):=g(p(n))$. The closed term
$$P:=\lambdaab{o}{\lambdaab{n}{E(on)}}$$
computes this transformation by one input query followed by exact rational evaluation. For $m\ge n$,
$$\Abs{q_{F(p)(n)}-q_{F(p)(m)}}
 =\Abs{f(q_{p(n)})-f(q_{p(m)})}\le\Abs{q_{p(n)}-q_{p(m)}}\le2^{-n}.$$
Continuity gives $q_{F(p)(n)}\to f(x)$, so the output is a Cauchy name of $f(x)$.
This proves that $f$ is computable as a map on represented real numbers.

We now construct a locally uniform polynomial name. Given integers $R\ge1$ and $n\ge0$, put
$$g_R(t):=f(2Rt-R),\qquad d:=(R2^n)^2.$$
The Lipschitz constant of $g_R$ is at most $2R$.
The \termuseas{Quantitative Bernstein approximation}{quantitative Bernstein lemma} therefore gives
$$\Abs{\BernsteinApproximation{d}{g_R}{t}-g_R(t)}
 \le\frac{2R}{2\sqrt d}=2^{-n}\qquad(0\le t\le1).$$
Consequently, the rational polynomial
$$Q_{R,n}(x):=\BernsteinApproximation{d}{g_R}{(x+R)/(2R)}$$
approximates $f$ uniformly on $\ClosedInterval{-R}{R}$ with error at most $2^{-n}$.

The coefficient list of $Q_{R,n}$ can be generated using closed terms. For $0\le j\le d$, compute the rational sample
$$v_j:=f(-R+2Rj/d)=g_R(j/d)$$
by applying $E$ to the grid-point code $\RationalCode{2Rj}{Rd}{d-1}$; here $d\ge1$.
Compute the binomial coefficient as the rational number
$$\binom dj=\frac{d!}{j!(d-j)!},$$
using the factorial and reciprocal-factorial programs. The natural-number differences $d-1$ and $d-j$ are nonnegative.
The two affine polynomials
$$\ell_+(x):=\frac12+\frac{x}{2R},\qquad
 \ell_-(x):=\frac12-\frac{x}{2R}$$
have explicit two-entry coefficient lists. The required polynomial is
$$Q_{R,n}(x)=\sum_{j=0}^{d}v_j\binom dj\ell_+(x)^j\ell_-(x)^{d-j}.$$

For completeness, polynomial arithmetic on these lists is also explicit. If the input lists have lengths $m$ and $r$,
interpret coefficients outside the lists as zero. Tabulate $m+r$ coefficients. Addition uses $a_k+b_k$, while
multiplication uses
$$c_k:=\sum_{i=0}^{k}a_i b_{k-i}\qquad(0\le k<m+r).$$
The finite sum retains both lists and $k$ as parameters; its indices satisfy $i\le k$, so $k-i$ is nonnegative.
The convolution formula proves that the decoded output is the product polynomial. Trailing zeros are harmless.

Starting with the constant polynomial one, iterate multiplication to form each power of $\ell_+$ and $\ell_-$.
Multiply their product by the constant $v_j\binom dj$, and add the resulting polynomial lists for $0\le j\le d$,
starting with the empty list for zero. Parameterized recursion retains $R,d$ throughout. Composing these closed terms
with the calculation of $d$ gives a closed numerical term $T$ with
$$T\ChurchNumeral{\NatPair{R}{n}}\to_\beta^*\ChurchNumeral{q(\NatPair{R}{n})},$$
where $q(\NatPair{R}{n})$ decodes to the coefficient list of $Q_{R,n}$. The preceding error estimate proves that
$q$ is a computable locally uniform polynomial name of $f$. The name condition only tests $R\ge1$; at $R=0$ the
program may return any fixed polynomial code.

Finally, splitting the triangle at zero gives
$$\int_{\R}\tau(x)\,dx
 =\int_{-1}^{0}(1+x)\,dx+\int_{0}^{1}(1-x)\,dx=1.$$
Translation preserves the integral, so the $s$th summand has integral $c_s$. Monotone convergence for the nonnegative
partial sums now gives
$$\int_{\R}f(x)\,dx=\sum_{s=0}^{\infty}c_s=\HaltingReal<\infty.$$
Thus $f$ is integrable, and the Fourier kernel at zero is identically one, giving
$\FourierTransform{f}(0)=\HaltingReal$.

A computable locally uniform polynomial name of the Fourier transform would give computable rational approximations
to this value: request precision $n$ on $\ClosedInterval{-1}{1}$ and read the real part of the constant coefficient.
Evaluation at zero
makes all positive powers vanish, and the uniform error bound gives error at most $2^{-n}$. This contradicts the
noncomputability of $\HaltingReal$. A computable $L^1$-name of $f$ would produce precisely such a polynomial name under
the preceding Fourier realizer, so no computable $L^1$-name exists either. The missing information is effective
control of the integral in the tails.
\end{proof}

<!-- formalization: skip (cited external L2 Fourier-transform computability theorem) -->
The norm used in the representation also determines what an output approximation means. In the standard $L^2(\R,\C)$
Cauchy representation, the Fourier transform with the same normalization extends to a computable unitary operator, and
its inverse is computable as well; see [@Kunkle2004] for the operator-theoretic development. Here the guarantee is an
$L^2$-norm error bound. It is not a guarantee of pointwise values: elements of this space are equivalence classes modulo
equality almost everywhere. The $L^1$ argument above instead produces a continuous function together with effective
uniform approximations on compact intervals.

