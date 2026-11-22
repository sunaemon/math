# Concrete Models of Cantor and Baire Space {#sec:concrete-cantor-baire-models}

<!-- formalization: skip (chapter overview, not a proof obligation) -->

§{sec:cantor-baire-space} studied $\CantorSpace$ and $\BaireSpace$ using cylinders, trees, and topological
characterizations.
This chapter constructs explicit homeomorphisms with concrete spaces: the middle-thirds Cantor set and
$\PowerSet{\omega}$ for Cantor space, and the irrational line and the space of infinite subsets of $\omega$ for Baire
space. Continued fractions, Stern--Brocot paths, and gaps between successive elements describe these homeomorphisms
in terms of finite prefixes. We also realize Baire space as a subspace of Cantor space.

## Cantor-Space Models {#sec:concrete-cantor-models}

\begin{mathmeta}
  \vars{J,j,n}{Nat}
  \vars{s}{Seq}
  \vars{x}{Name}
\end{mathmeta}
\index{Cantor space!concrete models}

<!-- formalization: skip (section lead-in) -->
We first describe the three models by their convergent sequences. All three spaces are metrizable, so these
convergence criteria determine their topologies. The homeomorphisms and clopen bases are constructed after the list.

\begin{enumerate}
\item \emph{Binary sequences.} In $\CantorSpace$, a sequence $\Sequence{x_j}{j\in\omega}$ converges to $x$ exactly when
each
coordinate eventually agrees with that of $x$:
$$\forall n\in\omega\;\exists J\in\omega\;\forall j\ge J,\quad x_j(n)=x(n).$$
The index $J$ may depend on $n$. Equivalently, any fixed finite initial segment eventually agrees with that of the
limit; the whole infinite sequence need not agree at any one stage.

\item \emph{Power set.} Give $\PowerSet{\omega}$ the topology transported from binary sequences by characteristic
functions, as constructed below. A sequence $\Sequence{E_j}{j\in\omega}$ converges to $E$ exactly when membership of
each fixed
natural number eventually agrees with membership in $E$:
$$\forall n\in\omega\;\exists J\in\omega\;\forall j\ge J,\quad (n\in E_j\Longleftrightarrow n\in E).$$
Thus, on any fixed finite set of natural numbers, the subsets eventually agree with the limit.

\item \emph{Middle-thirds Cantor set.} Let $C\IncludedIn\ClosedInterval{0}{1}$ be the set of reals with a ternary
expansion using only
the digits $0$ and $2$.
Give $C$ the subspace topology inherited from $\R$. For $z_j,z\in C$, convergence $z_j\to z$ means ordinary
convergence of real numbers:
$$\forall\varepsilon>0\;\exists J\in\omega\;\forall j\ge J,\quad \Abs{z_j-z}<\varepsilon.$$
\end{enumerate}

<!-- formalization: structural -->
**Cylinders and characteristic functions.**

For $s\in\finseq{2}$, the usual cylinder in $\CantorSpace$ is
$\cyl{s}=\{x\in\CantorSpace:s\prefixOf x\}$. These cylinders split into two immediate
subcylinders at each node and form the standard clopen basis.
A sequence converges to a point exactly when it eventually belongs to every cylinder containing that point.
This is the finite-prefix criterion above; it is equivalent to coordinatewise eventual agreement because one can
take the maximum of the finitely many indices needed for a given prefix.

Identify a subset $E\IncludedIn\omega$ with its characteristic function:
$$
\chi:\PowerSet{\omega}\longrightarrow 2^\omega,
\qquad
\chi(E)(n)=
\begin{cases}
1,&n\in E,\\
0,&n\notin E.
\end{cases}
$$
The inverse sends $x\in2^\omega$ to $\{n\in\omega:x(n)=1\}$. Equip $\PowerSet{\omega}$ with the topology
that makes this bijection $\chi$ a homeomorphism onto $2^\omega$ with its product topology.
The inverse image of a cylinder is
$$
\chi^{-1}(\cyl{s})=
\left\{E\IncludedIn\omega:\forall n<\Length{s},\quad
\begin{aligned}
s(n)=1&\implies n\in E,\\
s(n)=0&\implies n\notin E
\end{aligned}
\right\}.
$$
These inverse images form a clopen basis.

More generally, a \termuse{cylinder} is a set obtained by prescribing values at finitely many positions of a sequence.
Under the characteristic-function identification, for finite sets $F,G\IncludedIn\omega$, define the cylinder
$$
\relax[F;G]:=
\left\{E\IncludedIn\omega:\forall n\in\omega,\quad
\begin{aligned}
n\in F&\implies n\in E,\\
n\in G&\implies n\notin E
\end{aligned}
\right\}.
$$

The inverse image $\chi^{-1}(\cyl{s})$ is $[F_s;G_s]$, where
$F_s=\{n<\Length{s}:s(n)=1\}$ and $G_s=\{n<\Length{s}:s(n)=0\}$.
Conversely, choose $k$ such that $F\cup G\IncludedIn\{0,\ldots,k-1\}$.
Then
$$
\relax[F;G]=\bigcup\left\{\chi^{-1}(\cyl{s}):
s\in\funcspace{k}{2},\;F\IncludedIn F_s,\;G\IncludedIn G_s\right\}.
$$
The right-hand side is a finite union, so the sets $[F;G]$ also form a clopen basis.
If $F\cap G\ne\emptyset$, then $[F;G]=\emptyset$.

<!-- formalization: skip (applications of the power-set presentation) -->
This model is natural for almost inclusion, almost disjointness, ultrafilters, Cohen forcing, and fair-coin measure.

<!-- formalization: structural -->
**The ternary map.**

Define
$$
h:2^\omega\longrightarrow C,
\qquad
h(x)=\sum_{n=0}^{\infty}\frac{2x_n}{3^{n+1}}
$$
by reading a binary sequence as ternary digits $2x_0,2x_1,\ldots$. This map is onto by the definition of $C$.
If two sequences first differ at position $k$, the contribution $2/3^{k+1}$ there exceeds the sum
$1/3^{k+1}$ of all possible later differences, so their images differ. If they agree at the first $k$ positions,
their images differ by at most $3^{-k}$, proving continuity. Thus $h$ is a continuous bijection from a compact
space to a Hausdorff space, and hence a homeomorphism.
For a word $s$ of length $k$, put
$$t_s:=\sum_{i<k}\frac{2s_i}{3^{i+1}},\qquad I_s:=\ClosedInterval{t_s}{t_s+3^{-k}}.$$
The interval $I_s$ is the corresponding stage-$k$ interval of the middle-third construction, and
$$h(\cyl{s})=C\cap I_s.$$
Indeed, the remaining ternary digits contribute a number between $0$ and $3^{-k}$, and the stage-$k$
intervals for distinct words are disjoint.

In particular, for $z_j=h(x_j)$ and $z=h(x)$, real convergence $z_j\to z$ is equivalent to eventual agreement of
each binary coordinate. In the ternary expansions using only $0$ and $2$, each fixed digit therefore eventually
agrees with the corresponding digit of the limit.

<!-- formalization: skip (illustrative remark; the finite-alphabet homeomorphism and Brouwer's characterization
  are treated in §{sec:cantor-baire-space}) -->
Finite alphabets give the same space in different coordinates.
For every $2\le n<\omega$, the product $n^\omega$ is homeomorphic to $\CantorSpace$, as noted in
§{sec:cantor-baire-space}.
This is a change of finite prefix codes, not a change of the underlying compact zero-dimensional topology.
Brouwer's characterization in §{sec:clopen-scheme-characterizations} explains why all nonempty perfect compact
zero-dimensional metric presentations are homeomorphic to this same binary model.

## Baire-Space Models {#sec:baire-concrete-models}

\begin{mathmeta}
  \vars{s}{Seq}
  \vars{x}{Name}
\end{mathmeta}
\index{Baire space!concrete models}

\begin{mathmeta}
  \define{infiniteSubsets}
\end{mathmeta}

<!-- formalization: skip (section lead-in) -->
The section begins with the following explicit presentations.

\begin{enumerate}
\item \emph{Baire-space cylinders.} The reference model is $\BaireSpace$ with its usual cylinders
$\cyl{s}=\{x\in\BaireSpace:s\prefixOf x\}$ for $s\in\finseq{\omega}$. Each cylinder splits into countably many
immediate subcylinders $\cyl{s\concat(n)}$, giving the standard coding tree for open and closed subsets of
$\BaireSpace$.

\item \emph{Irrational line.} The space $\SetDifference{\R}{\QQ}$ is homeomorphic to $\BaireSpace$ by the
Alexandrov--Urysohn characterization in §{sec:clopen-scheme-characterizations}: it is Polish, zero-dimensional,
perfect, and nowhere locally compact. The next subsection gives a more explicit and more useful homeomorphism by
continued-fraction coordinates; in that presentation, basic clopen sets are cylinders that fix finitely many
partial quotients.

\item \emph{Infinite subsets.} The \termdefineas{infinite subset of omega}{space of infinite subsets of $\omega$}
is the subspace
$$
\infiniteSubsets{\omega}:=\{A\IncludedIn\omega:A\text{ is infinite}\}
$$
of $\PowerSet{\omega}\cong\CantorSpace$. If $A=\{a_0<a_1<a_2<\cdots\}$, the \termforward{gap map} sends
$$
A\longmapsto\Tuple{a_0,\;a_1-a_0-1,\;a_2-a_1-1,\ldots}\in\BaireSpace
$$
and has inverse
$$
\Tuple{g_0,g_1,g_2,\ldots}\longmapsto\{g_0,\;g_0+g_1+1,\;g_0+g_1+g_2+2,\ldots\}.
$$

Thus finite Baire prefixes are exactly finite initial-gap data for infinite subsets of $\omega$.

\end{enumerate}

<!-- formalization: skip (motivational transition) -->
These models explain how the abstract Polish-space definition turns into explicit finite data before the Borel hierarchy
begins in §{sec:fsigma-gdelta-sets}. The detailed constructions below introduce the additional coding devices only when
the required notation is in place.

### Simple Continued Fractions {#sec:simple-continued-fractions}

\begin{mathmeta}
  \vars{k,p}{Int}
  \vars{n,q}{Nat}
  \vars{a_*,b_*,p_*,q_*}{Nat}
  \vars{a_0,b_0}{Int}
  \vars{x}{Real}
\end{mathmeta}

\begin{theorem*}[Simple continued fraction expansion theorem]
Every irrational $\alpha \in \R$ admits a unique \termdefineas{continued fraction}{simple continued fraction expansion}
$$\alpha \;=\; a_0 + \cfrac{1}{a_1 + \cfrac{1}{a_2 + \cfrac{1}{a_3 + \cdots}}}, \qquad a_0 \in \ZZ,\;\; a_n \in
\RestrictedSet{\NN}{\ge 1} \text{ for } n \ge 1,$$
written $\alpha = [a_0; a_1, a_2, a_3, \ldots]$. Conversely, every infinite expression of this form converges to an
irrational real.
\end{theorem*}

\begin{proof}

<!-- formalization: skip (standard floor/fractional-part definitions; mathlib Int.floor/Int.fract) -->
We write $\Floor{x} := \max\{k \in \ZZ : k \le x\}$ for the
\termdefine{floor} of $x$ and
$\{x\} := x - \Floor{x} \in \LeftClosedInterval{0}{1}$ for its \termdefine{fractional part}.

\emph{Existence.} Set $a_0 := \Floor{\alpha}$ and $\alpha_0 := \{\alpha\}$, and for $n \ge 0$ define $a_{n+1}
:= \Floor{1/\alpha_n}$ and $\alpha_{n+1} := \{1/\alpha_n\}$. The fractional part of any irrational is itself
irrational and lies in $\OpenInterval{0}{1}$, so $\alpha_0 \in \SetDifference{\OpenInterval{0}{1}}{\QQ}$; inductively,
if $\alpha_n \in
\SetDifference{\OpenInterval{0}{1}}{\QQ}$ then $1/\alpha_n$ is irrational and greater than $1$, giving $a_{n+1} \in
\RestrictedSet{\NN}{\ge 1}$ and
$\alpha_{n+1} \in \SetDifference{\OpenInterval{0}{1}}{\QQ}$. Define $p_n, q_n$ by the seed values $\Pair{p_0}{q_0} :=
\Pair{1}{0}$ and $\Pair{p_1}{
q_1} := \Pair{0}{1}$ and the recurrence
\begin{equation*}
\begin{aligned}
p_{n+1} &\;:=\; a_n p_n + p_{n-1}, \\
q_{n+1} &\;:=\; a_n q_n + q_{n-1}
\end{aligned}
\quad (n \ge 1). \tag{$*$}
\end{equation*}

We claim that for $n \ge 1$,
$$[0; a_1, \ldots, a_n] \;=\; \frac{p_{n+1}}{q_{n+1}};$$
call $p_{n+1}/q_{n+1}$ the $n$-th \termdefine{convergent} of $\alpha_0$. Direct induction on this fails: the
inductive step needs the last slot of the continued fraction to range over the reals, not just
$\RestrictedSet{\NN}{\ge 1}$:

For any positive real $x$ and $n \ge 0$,
\begin{equation*}
\relax[0; a_1, \ldots, a_n, x] \;=\; \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}. \tag{i}
\end{equation*}
\emph{Base $n = 0$:} $[0; x] = 1/x = (x \cdot p_1 + p_0)/(x \cdot q_1 + q_0)$, from the seed values.
\emph{Inductive step at $n \ge 1$:}
$$\begin{aligned}
\relax[0; a_1, \ldots, a_n, x]
&\;=\; [0; a_1, \ldots, a_{n-1}, a_n + 1/x] \\
&\;\overset{\text{(i)}}{=}\; \frac{(a_n + 1/x) p_n + p_{n-1}}{(a_n + 1/x) q_n + q_{n-1}} \\
&\;=\; \frac{x(a_n p_n + p_{n-1}) + p_n}{x(a_n q_n + q_{n-1}) + q_n} \\
&\;\overset{(*)}{=}\; \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}.
\end{aligned}$$
Setting $x = a_n$ in (i) at level $n - 1$ and applying $(*)$, for $n \ge 1$:
$$[0; a_1, \ldots, a_n] \;\overset{\text{(i)}}{=}\; \frac{a_n p_n + p_{n-1}}{a_n q_n + q_{n-1}}
\;\overset{(*)}{=}\; \frac{p_{n+1}}{q_{n+1}}.$$
We will also need:

For $n \ge 0$,
\begin{equation*}
p_{n+1} q_n - p_n q_{n+1} = (-1)^{n+1}. \tag{ii}
\end{equation*}
\emph{Base $n = 0$:} $p_1 q_0 - p_0 q_1 = -1$, from the seed values. \emph{Inductive step:}
$$\begin{aligned}
p_{n+2} q_{n+1} - p_{n+1} q_{n+2}
&\;\overset{(*)}{=}\; (a_{n+1} p_{n+1} + p_n) q_{n+1} - p_{n+1} (a_{n+1} q_{n+1} + q_n) \\
&\;=\; -(p_{n+1} q_n - p_n q_{n+1}) \\
&\;\overset{\text{(ii)}}{=}\; (-1)^{n+2}.
\end{aligned}$$

The \termdefine{tail formula}
$$\alpha_0 \;=\; \frac{p_{n+1} + \alpha_n p_n}{q_{n+1} + \alpha_n q_n}$$
holds for $n \ge 0$. At $n = 0$ it reduces to the tautology $\alpha_0 = (p_1 + \alpha_0 p_0)/(q_1 + \alpha_0 q_0) =
\alpha_0$. \emph{Inductive step at $n \ge 1$:} substitute $\alpha_{n-1} = 1/(a_n + \alpha_n)$ into the formula at level
$n - 1$ and clear:

$$\begin{aligned}
\alpha_0
&\;=\; \frac{p_n + \alpha_{n-1} p_{n-1}}{q_n + \alpha_{n-1} q_{n-1}} \\
&\;=\; \frac{(a_n + \alpha_n) p_n + p_{n-1}}{(a_n + \alpha_n) q_n + q_{n-1}} \\
&\;\overset{(*)}{=}\; \frac{p_{n+1} + \alpha_n p_n}{q_{n+1} + \alpha_n q_n}.
\end{aligned}$$

Combining the tail formula at level $n + 1$ with (ii):
$$\begin{aligned}
\Abs{\alpha_0 - \frac{p_{n+1}}{q_{n+1}}}
&\;\overset{\text{tail}}{=}\; \Abs{
\frac{p_{n+2} + \alpha_{n+1} p_{n+1}}{q_{n+2} + \alpha_{n+1} q_{n+1}}
- \frac{p_{n+1}}{q_{n+1}}
} \\
&\;=\; \frac{\Abs{p_{n+2} q_{n+1} - p_{n+1} q_{n+2}}}{q_{n+1}(q_{n+2} + \alpha_{n+1} q_{n+1})} \\
&\;\overset{\text{(ii)}}{=}\; \frac{1}{q_{n+1}(q_{n+2} + \alpha_{n+1} q_{n+1})} \\
&\;<\; \frac{1}{q_{n+1} q_{n+2}}.
\end{aligned}$$

Since each $a_n \ge 1$ for $n \ge 1$, $(*)$ gives $q_{n+1} \ge q_n + q_{n-1}$ for $n \ge 1$, with $q_1 = 1$ and $q_2 \ge
1$, so $q_n$ grows at least at the Fibonacci rate; in particular $q_{n+1} \to \infty$ and
$p_{n+1}/q_{n+1} \to \alpha_0$. Hence $\alpha = a_0 + \alpha_0 = [a_0; a_1, a_2, \ldots]$.

\emph{Converse.} Fix any $a_0 \in \ZZ$ and any sequence $a_n \in \RestrictedSet{\NN}{\ge 1}$ for $n \ge 1$, and define
$p_n,q_n$ by the same seeds and recurrence. The Fibonacci-rate growth above depends only on the positivity of the
partial quotients, so $q_n \to \infty$. Put $c_n:=p_{n+1}/q_{n+1}$. The determinant identity gives
$$c_{n+1}-c_n
=\frac{p_{n+2}q_{n+1}-p_{n+1}q_{n+2}}{q_{n+1}q_{n+2}}
=\frac{(-1)^n}{q_{n+1}q_{n+2}}.$$
Moreover,
$$c_{n+2}-c_n
=\frac{a_{n+2}}{q_{n+1}q_{n+3}}(p_{n+2}q_{n+1}-p_{n+1}q_{n+2})
=\frac{a_{n+2}(-1)^n}{q_{n+1}q_{n+3}}.$$
Thus $c_{n+2}$ lies strictly between $c_n$ and $c_{n+1}$. Let $I_n$ be the closed interval with endpoints $c_n$
and $c_{n+1}$. Then $I_{n+1}\IncludedIn I_n$, and $I_{n+2}\IncludedIn\operatorname{int}I_n$: both $c_{n+2}$ and
$c_{n+3}$ lie strictly between the endpoints of $I_n$. The lengths $1/(q_{n+1}q_{n+2})$ tend to $0$, so the
intervals have a unique common point $\beta$, and $c_n\to\beta$. Moreover,
$\beta\in I_{n+2}\IncludedIn\operatorname{int}I_n$ for every $n$. For $n\ge1$, the $c_n$ are the finite convergents
$[0;a_1,\ldots,a_n]$. Since $c_0=0$ and $c_1=1/a_1\le1$, it follows that $\beta\in\OpenInterval{0}{1}$.

The limit is moreover irrational. If $\beta=p/q$ with $q \ge 1$, then $\beta$ lies strictly between $c_n$ and $c_{n+1}$
for every $n$, so
$$\Abs{\frac{p}{q}-\frac{p_{n+1}}{q_{n+1}}}<\Abs{c_{n+1}-c_n}=\frac{1}{q_{n+1}q_{n+2}}.$$
On the other hand, $p/q\ne p_{n+1}/q_{n+1}$, so
$$\Abs{\frac{p}{q}-\frac{p_{n+1}}{q_{n+1}}}
=\frac{\Abs{p q_{n+1}-q p_{n+1}}}{q q_{n+1}}
\ge \frac{1}{q q_{n+1}}.$$
Hence $q_{n+2}<q$ for every $n$, contradicting $q_n \to \infty$. Thus every infinite expression $[a_0; a_1, a_2,
\ldots]$ converges to the irrational real $a_0+\beta$.

\emph{Uniqueness.} Suppose $\alpha = [a_0; a_1, a_2, \ldots] = [b_0; b_1, b_2, \ldots]$ with $a_0, b_0 \in \ZZ$ and
$a_n, b_n \in \RestrictedSet{\NN}{\ge 1}$ for $n \ge 1$. By the converse, $\alpha - a_0 = [0; a_1, a_2, \ldots] \in
\OpenInterval{0}{
1}$ and $\alpha - b_0 = [0; b_1, b_2, \ldots] \in \OpenInterval{0}{1}$, forcing $a_0 = b_0 = \Floor{\alpha}$ and
equating the
tails. For finite truncations,
$$[0;a_1,\ldots,a_n]^{-1}=[a_1;\ldots,a_n],$$
and continuity of reciprocation at the positive limit lets this identity pass to the limit. Hence
$$\frac{1}{\alpha - a_0} = [a_1; a_2, \ldots] = [b_1; b_2, \ldots],$$
and the same argument applied to this value yields $a_1 = b_1$. Inductively $a_n = b_n$ for all $n$.
\end{proof}

For $n \ge 1$, the recurrence gives $p_{n+1}, q_{n+1} \in \RestrictedSet{\NN}{\ge 1}$. By (ii), any common divisor of
$p_{n+1}$ and $q_{n+1}$ divides $\pm 1$, so $p_{n+1}/q_{n+1}$ is in lowest terms.

<!-- formalization: skip (transition to the topological-form fact) -->
The topological form of the same theorem is another standard fact.

\begin{fact*}[Continued-fraction coordinate homeomorphism]
The continued-fraction coordinate map is a homeomorphism
$$\begin{aligned}
\theta : \SetDifference{\R}{\QQ} &\;\xrightarrow{\;\;\sim\;\;}\; \ZZ \times
\funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}}, \\
\alpha &\;\mapsto\; \Pair{a_0}{\Tuple{a_1, a_2, \ldots}}.
\end{aligned}$$
Composing $\theta$ with coordinatewise bijections $\ZZ \cong \omega$ and $\RestrictedSet{\NN}{\ge 1}\cong\omega$, and
then with the standard homeomorphism $\omega\times\BaireSpace\cong\BaireSpace$, gives a homeomorphism
$\SetDifference{\R}{\QQ}
\cong \BaireSpace$.

For each $a_0\in\ZZ$, let
$\theta_{a_0}:=\pi_2\circ\theta\big|_{\SetDifference{\OpenInterval{a_0}{a_0+1}}{\QQ}}$. Then
$$\begin{aligned}
\theta_{a_0} : \SetDifference{\OpenInterval{a_0}{a_0+1}}{\QQ} &\;\xrightarrow{\;\;\sim\;\;}\;
\funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}}, \\
\alpha &\;\mapsto\; \Tuple{a_1,a_2,\ldots}
\end{aligned}$$
is the fractional-part homeomorphism.
\end{fact*}

\begin{proof}
The expansion theorem makes $\theta$ and every $\theta_{a_0}$ bijective.
The integer-part component $\alpha \mapsto a_0$ is locally constant on the clopen partition
$$
\SetDifference{\R}{\QQ}
=
\InternalDisjointUnion_{k \in \ZZ} (\SetDifference{\OpenInterval{k}{k+1}}{\QQ}).
$$
It has value $k$ on the $k$-th piece, hence is continuous to $\ZZ$ with the
discrete topology.
To compute a basic cylinder, fix $a_1, \ldots, a_n$ and let the remaining tail vary. Formula (i) gives, for the next
complete quotient $x \in \SetDifference{\OpenInterval{1}{\infty}}{\QQ}$,
$$\alpha
\;=\;
a_0 + \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}.$$
The derivative of this fractional-linear function has the sign of
$$p_{n+1} q_n - p_n q_{n+1} = (-1)^{n+1},$$
by (ii), so it is decreasing when $n$ is even and increasing when $n$ is odd. As $x$ ranges over
$\SetDifference{\OpenInterval{1}{\infty}}{\QQ}$, the two endpoint limits are obtained at $x \to \infty$ and $x \to 1^+$,
giving
$p_{n+1}/q_{n+1}$ and
$(p_{n+1}+p_n)/(q_{n+1}+q_n)$. Hence
$$
\theta_{a_0}^{-1}\!\left(\cyl{\Tuple{a_1, \ldots, a_n}}\right)
\;=\;
\begin{cases}
\SetDifference{\OpenInterval{a_0 + \dfrac{p_{n+1}}{q_{n+1}}}{a_0 + \dfrac{p_{n+1} + p_n}{q_{n+1} + q_n}}}{\QQ}, & n
\text{ even},
\\[1.2em]
\SetDifference{\OpenInterval{a_0 + \dfrac{p_{n+1} + p_n}{q_{n+1} + q_n}}{a_0 + \dfrac{p_{n+1}}{q_{n+1}}}}{\QQ},
& n \text{ odd},
\end{cases}
$$
an open subinterval of $\SetDifference{\OpenInterval{a_0}{a_0+1}}{\QQ}$, so $\theta_{a_0}$ is continuous. For the
inverse, the
determinant identity shows that these subintervals have length
$1/(q_{n+1}(q_{n+1}+q_n))\le 1/q_{n+1}^2\to0$, so they form a neighborhood base for the subspace
topology. Hence $\theta_{a_0}^{-1}$ is continuous. The clopen partition into intervals between consecutive integers
then shows that $\theta$ is a
homeomorphism.

The final identification with $\BaireSpace$ uses that $\ZZ$, $\RestrictedSet{\NN}{\ge 1}$, and $\omega$ are countable
discrete spaces: code $a_0$ into coordinate $0$ via a bijection $\ZZ \cong \omega$, code the tail coordinates via a
bijection $\RestrictedSet{\NN}{\ge 1} \cong \omega$, and then prepend the first coordinate to the recoded tail.
\end{proof}

Under the homeomorphism $\theta_0$, the shift on
$\funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}}$ corresponds to the \termdefine{Gauss map}
$T(x):=\{1/x\}$ on $\SetDifference{\OpenInterval{0}{1}}{\QQ}$. This is the iteration
$\alpha_n\mapsto\alpha_{n+1}$ of fractional remainders used above. The corresponding complete quotient is
$1/\alpha_n=[a_{n+1};a_{n+2},\ldots]$. Thus shifting the partial quotients describes the Gauss map.

The coordinates also prove directly that the irrationals are Polish. Alternatively, they are a $\Gdelta$
subset of $\R$, so Alexandrov's theorem in §{sec:alexandrov-theorem} shows that they are Polish.

<!-- formalization: skip-begin (interchangeability remark, Stern-Brocot section intro, and the
  positive-rational continued-fraction convention; illustrative setup) -->
This is the standard reason "the irrationals" and "the Baire space" are used interchangeably in descriptive set theory.

### The Stern--Brocot Tree {#sec:stern-brocot-tree}

\begin{mathmeta}
  \vars{a}{Nat}
  \vars{a_*}{Nat}
\end{mathmeta}

We now restrict to the positive half-line, so $a_0\in\NN$. We label continued-fraction cylinders by positive
rationals and then arrange these labels in the binary Stern--Brocot tree using finite L/R words. This changes the
parent-child relation: the continued-fraction prefix tree is countably branching, whereas an edge in the binary tree
adds one letter, which may extend the current run rather than start a new partial quotient.

<!-- formalization: skip-end -->

Every positive rational has a finite continued-fraction expression; except for the one-term integer expressions, the two
standard finite expressions are related by splitting the last partial quotient:
$$[a_0; a_1,\ldots,a_n]
\;=\;
[a_0; a_1,\ldots,a_{n-1},a_n-1,1]
\qquad (a_n \ge 2).$$
The standard convention is to use the left-hand expression, whose last partial quotient is at least $2$. In this section
we instead use the right-hand expression, the one terminating in $1$:
$$r = [a_0; a_1,\ldots,a_{n-1},1].$$
For positive integers this means writing $m = [m-1;1]$.


The \termdefine{mediant} of two fractions is
$$\frac{a}{b} \oplus \frac{c}{d} \;:=\; \frac{a+c}{b+d}.$$

#### Cylinder geometry {#sec:stern-brocot-cylinder-geometry}

\begin{mathmeta}
  \vars{s}{Seq}
\end{mathmeta}

For a nonempty prefix $s = \Tuple{a_1,\ldots,a_n}$, let
$$\frac{p_{n+1}}{q_{n+1}} := [0; a_1,\ldots,a_n],
\qquad
\frac{p_n}{q_n} := [0; a_1,\ldots,a_{n-1}]$$
be the last two convergents computed from this prefix, and write
$$F_s(x) \;:=\; \frac{x p_{n+1} + p_n}{x q_{n+1} + q_n}.$$

The two rational boundary points of the fractional cylinder $\theta_0^{-1}(\cyl{s})$ are:
$$\begin{aligned}
F_s(\infty)
&= \frac{p_{n+1}}{q_{n+1}}, \\
F_s(1)
&= \frac{p_{n+1} + p_n}{q_{n+1} + q_n}
 = \frac{p_{n+1}}{q_{n+1}} \oplus \frac{p_n}{q_n}.
\end{aligned}$$
Thus, in the integer cell $\OpenInterval{a_0}{a_0+1}$, the continued-fraction interval formula above becomes
$$
\theta_{a_0}^{-1}(\cyl{s})
\;=\;
\begin{cases}
\SetDifference{\OpenInterval{a_0 + F_s(\infty)}{a_0 + F_s(1)}}{\QQ}, & n \text{ even}, \\[0.8em]
\SetDifference{\OpenInterval{a_0 + F_s(1)}{a_0 + F_s(\infty)}}{\QQ}, & n \text{ odd}.
\end{cases}
$$

Subdividing the cylinder by the next partial quotient gives
$$\theta_{a_0}^{-1}(\cyl{s}) \;=\; \InternalDisjointUnion_{k \ge 1}
\theta_{a_0}^{-1}(\cyl{s \concat (k)}).$$

The cut points are the \termdefineas{semiconvergent}{semiconvergents}
$$F_s(k) \;=\; \frac{k p_{n+1} + p_n}{k q_{n+1} + q_n} \qquad (k \ge 1),$$
and each child is the interval between two adjacent translated cut points:

$$
\theta_{a_0}^{-1}(\cyl{s \concat (k)})
\;=\;
\begin{cases}
\SetDifference{\OpenInterval{a_0 + F_s(k+1)}{a_0 + F_s(k)}}{\QQ}, & n \text{ even}, \\[0.8em]
\SetDifference{\OpenInterval{a_0 + F_s(k)}{a_0 + F_s(k+1)}}{\QQ}, & n \text{ odd}.
\end{cases}
$$

Pairs $\tfrac{a}{b}, \tfrac{c}{d}$ with $\Abs{bc - ad} = 1$ are \termdefineas{Farey neighbor}{Farey neighbors}. The
determinant identity $\Abs{p_{n+1} q_n - p_n q_{n+1}} = 1$ implies
$$\Abs{p_{n+1}(k q_{n+1} + q_n) - q_{n+1}(k p_{n+1} + p_n)} = 1,$$
so every semiconvergent $F_s(k)$ is Farey-adjacent to $\tfrac{p_{n+1}}{q_{n+1}}$ and is therefore in lowest terms.

Adjacent semiconvergents $F_s(k)$ and $F_s(k+1)$ are Farey neighbors for the same determinant reason.

#### Labeling cylinders by rationals {#sec:stern-brocot-rational-labels}

\begin{mathmeta}
  \vars{a}{Nat}
  \vars{s}{Seq}
  \vars{a_*}{Nat}
\end{mathmeta}

The mediant endpoint gives each continued-fraction cylinder its rational label. The node
$\theta_{a_0}^{-1}(\cyl{s})$ has label
$$[a_0; a_1,\ldots,a_n,1],
\qquad \text{where } s=\Tuple{a_1,\ldots,a_n},\;\; a_0 \in \NN.$$

By the determinant calculation above, each label is in lowest terms.

This labeling is a bijection from positive continued-fraction cylinders to $\RestrictedSet{\QQ}{>0}$. Surjectivity is
exactly the terminating expansion convention: if
$$r = [a_0; a_1,\ldots,a_{n-1},1],$$
then $r$ is the label of $\theta_{a_0}^{-1}(\cyl{\Tuple{a_1,\ldots,a_{n-1}}})$, with the empty prefix covering the
integer
case $m=[m-1;1]$. Injectivity follows from uniqueness of the chosen terminating expansion.

Here is an elementary justification of that convention. For existence, use the subtractive Euclidean algorithm
on $r=p/q>0$ with positive integers $p,q$. If $p=q$, then $r=1=[0;1]$. If $p>q$, reduce to
$(p-q)/q$ and recover $r$ by adding $1$. If $p<q$, reduce to $t=p/(q-p)$ and recover
$r=t/(t+1)$. The sum of numerator and denominator decreases at each reduction. Both recovery operations
preserve finite expansions ending in $1$: adding $1$ increases the integer part, while
$t/(t+1)=1/(1+1/t)$ inserts an initial reciprocal and combines the adjacent integer terms when needed.
Thus induction gives the required expansion for every positive rational.

For uniqueness, an empty positive prefix has value $a_0+1$, while a nonempty one has value strictly between
$a_0$ and $a_0+1$. Hence an integer has only the displayed empty-prefix expansion. For a noninteger, the floor
recovers $a_0$; subtracting it and taking the reciprocal recovers the remaining terminating expression.
Repeating this step determines all the positive entries, including the final $1$ convention.

#### Run-length words and the tree {#sec:stern-brocot-run-lengths}

\begin{mathmeta}
  \vars{a}{Nat}
  \vars{s}{Seq}
  \vars{a_*}{Nat}
\end{mathmeta}

Assign to the same cylinder $\theta_{a_0}^{-1}(\cyl{\Tuple{a_1,\ldots,a_n}})$ a finite L/R word by run-length coding the
label
$[a_0; a_1,\ldots,a_n,1]$ and omitting the final $1$-block. For $n \ge 1$, this word is
$$
\wordRepeat{R}{a_0}\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\cdots\wordRepeat{D_n}{a_n},
\qquad
D_n =
\begin{cases}
R, & n \text{ even}, \\
L, & n \text{ odd}.
\end{cases}
$$
For $s=\emptyset$ this gives $\wordRepeat{R}{a_0}$; in particular $1=[0;1]$ gets the empty word. Thus $\tfrac{1}{2} =
[0;1,1]$ has word $L$, and $\tfrac{5}{2} = [2;1,1]$ has word $RRL$.

Every finite L/R word has a unique decomposition into alternating runs, allowing the initial R-run to have length
zero. Thus the rational labels correspond bijectively to finite L/R words. Order them by extension of these words,
not by inclusion of the original continued-fraction cylinders. The resulting binary tree is the
\termdefine{Stern--Brocot tree}:

\begin{center}
\begin{tikzpicture}[
  level distance=1.0cm,
  sibling distance=3.4cm,
  every node/.style={align=center, inner sep=1pt},
  level 2/.style={sibling distance=1.7cm}
]
\node {$\emptyset:\ \tfrac{1}{1}$}
  child { node {$L:\ \tfrac{1}{2}$}
    child { node {$LL:\ \tfrac{1}{3}$} }
    child { node {$LR:\ \tfrac{2}{3}$} }
  }
  child { node {$R:\ \tfrac{2}{1}$}
    child { node {$RL:\ \tfrac{3}{2}$} }
    child { node {$RR:\ \tfrac{3}{1}$} }
  };
\end{tikzpicture}
\end{center}

The L-subtree, rooted at $\tfrac{1}{2}$, is the \termdefine{Farey tree}; its nodes are the rationals in
$\OpenInterval{0}{1}$ in
lowest terms.

\begin{mathmeta}
  \define{ContinuedFractionCylinderCode,ContinuedFractionPrefixCode}
\end{mathmeta}

\begin{remark*}[Cylinder codes]
The cylinder-code Galois connection from §{sec:closed-sets-trees} transports through the continued-fraction
coordinates. Fix $a_0\in\NN$ and put $I_{a_0}:=\SetDifference{\OpenInterval{a_0}{a_0+1}}{\QQ}$. For prefix up-sets
$A\in\PrefixUpSets{\RestrictedSet{\NN}{\ge 1}}$ and open sets $V\in\OpenSets{I_{a_0}}$, define
$$
\begin{aligned}
\ContinuedFractionCylinderCode{a_0}{A}&:=\bigcup_{s\in A}\theta_{a_0}^{-1}(\cyl{s}),\\
\ContinuedFractionPrefixCode{a_0}{V}
&:=\{s\in\finseq{\RestrictedSet{\NN}{\ge 1}}:\theta_{a_0}^{-1}(\cyl{s})\IncludedIn V\}.
\end{aligned}
$$
Then
$$
\ContinuedFractionCylinderCode{a_0}{A}\IncludedIn V
\quad\Longleftrightarrow\quad
A\IncludedIn\ContinuedFractionPrefixCode{a_0}{V}.
$$
Thus the finite continued-fraction cylinders are the basic nodes of the transported prefix tree.
\end{remark*}

#### Boundary and the mediant-limit map {#sec:boundary-mediant-limit-map}

\begin{mathmeta}
  \vars{a}{Nat}
  \vars{s}{Seq}
  \vars{n}{Nat}
  \vars{m}{Real}
  \vars{b}{Seq}
  \vars{a_*}{Nat}
\end{mathmeta}

The boundary of the binary tree is the Cantor space $\CantorSpace$ of infinite L/R words. The eventually-constant
branches are those of the form $b \concat \wordRepeat{L}{\omega}$ or $b \concat \wordRepeat{R}{\omega}$ for some $b \in
\finseq{2}$. The \termdefine{non-eventually-constant branches} are their complement
$$S \;:=\; \SetDifference{\CantorSpace}{\{b \concat \wordRepeat{L}{\omega},\; b \concat \wordRepeat{R}{\omega} : b \in
\finseq{2}\}}.$$

Branches in $S$ use the same run-length coding as finite rational nodes: an irrational
$$\alpha = [a_0; a_1,a_2,\ldots]$$
corresponds to
$$\wordRepeat{R}{a_0}\,\wordRepeat{L}{a_1}\,\wordRepeat{R}{a_2}\,\wordRepeat{L}{a_3}\,\cdots,$$
with $\wordRepeat{R}{0}$ the empty word, so numbers in $\OpenInterval{0}{1}$ correspond to branches of the L-subtree.

Associate to each finite L/R word $w$ a closed interval $J_w$ in $\ClosedInterval{0}{\infty}$. Start with
$J_{\emptySeq}=\ClosedInterval{0/1}{1/0}=\ClosedInterval{0}{\infty}$, where $1/0$ denotes the endpoint $\infty$.
If $J_w=\ClosedInterval{a/b}{c/d}$, put $m=(a+c)/(b+d)$ and define
$$J_{w\concat(L)}=\ClosedInterval{a/b}{m},\qquad J_{w\concat(R)}=\ClosedInterval{m}{c/d}.$$
The mediant $m$ is the label of the node $w$. Indeed, successive L moves replace the upper endpoint by
$(c+ka)/(d+kb)$, and successive R moves replace the lower endpoint by $(a+kc)/(b+kd)$. Substitution in the
continued-fraction recurrence $(*)$ gives the run-length labels above.

\begin{lemma*}[\termdefineas{completed-run cylinder lemma}{Completed runs and continued-fraction cylinders}]
Fix $a_0\in\NN$ and a finite sequence $s=\Tuple{a_1,\ldots,a_n}$ of positive integers, allowing $n=0$.
Put $D_j=R$ for even $j$ and $D_j=L$ for odd $j$, and set
$$v_n=\wordRepeat{R}{a_0}\wordRepeat{L}{a_1}\cdots\wordRepeat{D_n}{a_n},
\qquad w_n=v_n\concat(D_{n+1}),$$
where $v_0=\wordRepeat{R}{a_0}$. Then
$$J_{w_n}=\overline{\theta_{a_0}^{-1}(\cyl{s})},$$
where the closure is taken in $\R$.
\end{lemma*}

\begin{proof}
Use the convergent recurrence $(*)$ for $s$, and put $P_j=a_0q_j+p_j$.
Before appending $D_{n+1}$, the endpoints of $J_{v_n}$, in increasing order, are
$$
\begin{cases}
\Pair{P_{n+1}/q_{n+1}}{P_n/q_n},&n\text{ even},\\
\Pair{P_n/q_n}{P_{n+1}/q_{n+1}},&n\text{ odd}.
\end{cases}
$$
For $n=0$ these are $a_0/1$ and $1/0$. To pass from $n$ to $n+1$, repeat the next direction $a_{n+1}$ times.
The endpoint that changes becomes
$$\Pair{P_{n+2}}{q_{n+2}}=a_{n+1}\Pair{P_{n+1}}{q_{n+1}}+\Pair{P_n}{q_n},$$
while the other endpoint stays fixed. This proves the endpoint formula by induction.
Appending the single opposite letter $D_{n+1}$ to $v_n$ keeps $P_{n+1}/q_{n+1}$ and replaces the other endpoint
by $(P_{n+1}+P_n)/(q_{n+1}+q_n)$. These are exactly the two endpoints of the continued-fraction cylinder computed
in §{sec:stern-brocot-cylinder-geometry}. The same formula for the empty prefix gives $\ClosedInterval{a_0}{a_0+1}$.
Taking the closure fills the rational points and both endpoints, proving the equality.
\end{proof}

\begin{lemma*}[Nested mediant intervals]
For every infinite L/R word $z$, the intersection $\bigcap_n J_{\restrict{z}{n}}$ consists of exactly one point
of $\ClosedInterval{0}{\infty}$.
\end{lemma*}

\begin{proof}
The endpoint fractions satisfy $bc-ad=1$, initially and after either subdivision. In particular, they remain in
lowest terms. The increasing homeomorphism $u(t)=t/(1+t)$, with $u(\infty)=1$, sends $J_w$ to a closed interval
of length
$$u(c/d)-u(a/b)=\frac{1}{(a+b)(c+d)}.$$
This formula also holds for the endpoint $1/0$. Put $A=a+b$ and $B=c+d$. Initially $A=B=1$, and each subdivision
replaces one of $A,B$ by $A+B$. Thus $A+B\ge \Length{w}+2$, and
$$AB\ge A+B-1\ge \Length{w}+1.$$
Along every branch, the image intervals are nonempty, nested, and have lengths tending to zero. Their intersection
in $\ClosedInterval{0}{1}$ is a singleton, and applying $u^{-1}$ proves the claim.
\end{proof}

\begin{mathmeta}
  \define{MediantLimitMap}
\end{mathmeta}

Define the \termdefine{mediant-limit map}
$$\MediantLimitMap : \CantorSpace \longrightarrow \ClosedInterval{0}{\infty}$$
by taking $\MediantLimitMap(z)$ to be the unique point of $\bigcap_n J_{\restrict{z}{n}}$.

The constant branches satisfy $\MediantLimitMap(\wordRepeat{L}{\omega})=0$ and
$\MediantLimitMap(\wordRepeat{R}{\omega})=\infty$, since their intervals retain the endpoint $0$ or $\infty$,
respectively.

On the nonconstant eventually constant branches in $\SetDifference{\CantorSpace}{S}$,
$\MediantLimitMap$ is $2$-to-$1$ onto
$\RestrictedSet{\QQ}{>0}$. The rational at finite node $b$ has the two endpoint branches
$b\concat(L)\concat\wordRepeat{R}{\omega}$ and $b\concat(R)\concat\wordRepeat{L}{\omega}$, analogous to the dyadic
ambiguity $0.0\overline{1}=0.1\overline{0}$.

To see this, let $r$ be the mediant at node $b$. After choosing L, retaining $r$ as an endpoint forces every later
choice to be R; after choosing R, every later choice must be L. Choosing the other child at any later step excludes
$r$ from the closed interval. At depth $\Length{b}$, $r$ lies in the interior of $J_b$, so a branch with limit $r$ must
first pass through $b$. These are therefore its only two preimages. Conversely, every nonconstant eventually-constant
branch has a last change of letter and hence has one of these two forms.

For a branch in $S$, completing each run by the first opposite letter fixes a continued-fraction prefix.
The \termuse{completed-run cylinder lemma} identifies the corresponding $J_w$ with the closure in $\R$ of that
cylinder. The unique intersection point is therefore the irrational with those partial
quotients. Hence $\MediantLimitMap$ is a bijection from $S$ onto the positive irrationals, given by
$$\wordRepeat{R}{a_0}\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\wordRepeat{L}{a_3}\cdots
\longleftrightarrow
\Tuple{a_0,a_1,a_2,\ldots} \in \NN \times \funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}},$$
with
$\MediantLimitMap(\wordRepeat{R}{a_0}\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\wordRepeat{L}{a_3}\cdots)
=[a_0;a_1,a_2,\ldots]$.

This run-length map
$$S \longrightarrow \NN \times \funcspace{\omega}{\RestrictedSet{\NN}{\ge 1}}$$
is a homeomorphism. Indeed, at a point of $S$, any finite list of run lengths is determined by a finite L/R prefix long
enough to include the next change of letter, so the coordinate maps are continuous. Conversely, the inverse image of a
binary cylinder under the inverse run-length map only asks for finitely many completed run lengths and possibly a finite
lower bound on the next run length; this is open in the product of discrete coordinate spaces. Composing with the
continued-fraction homeomorphism from §{sec:simple-continued-fractions} shows that $\MediantLimitMap$ restricts to a
homeomorphism $S \to \SetDifference{\RestrictedSet{\R}{>0}}{\QQ}$.

<!-- formalization: skip (closing summary of the illustrative Stern--Brocot incarnation) -->
Thus the \termuse{Stern--Brocot tree} describes positive irrationals by infinite L/R words with infinitely many
changes of letter. Completed runs specify continued-fraction cylinders, whose rational endpoints were computed above.

### Infinite Subsets of $\omega$ {#sec:infinite-subsets-omega}

\begin{mathmeta}
  \vars{n,p}{Nat}
\end{mathmeta}

<!-- formalization: skip (change-point reformulation lead-in) -->
The non-eventually-constant branches $S$ admit a clean reformulation in terms of where their bits flip.

Each $b \in S$
has infinitely many \termdefineas{change point}{change points}
$$
\Delta(b) := \{n \in \omega : b_n \ne b_{n+1}\},
$$
and $b$ is recovered from $b_0$ together with $\Delta(b)$ by flipping the bit exactly at those positions.

Thus the space
$\infiniteSubsets{\omega}$ introduced above is the change-point version of the binary realization. Splitting $S$ by the
initial bit $b_0$ reduces the comparison to the two halves $\{b \in S : b_0 = L\}$ and $\{b \in S : b_0 = R\}$. The
infinite-subset model is the Stern--Brocot boundary with run lengths re-encoded as switch positions.

For the topology, fix an initial letter $\varepsilon\in\{L,R\}$ and define
$$H_\varepsilon:\infiniteSubsets{\omega}\to\{b\in S:b_0=\varepsilon\}$$
by starting with $H_\varepsilon(A)_0=\varepsilon$ and flipping the letter between positions $n$ and $n+1$ exactly when
$n\in A$. Then $\Delta(H_\varepsilon(A))=A$, and $\Delta$ is the inverse of $H_\varepsilon$ on the $\varepsilon$-half of
$S$. The map $H_\varepsilon$ is continuous because the first $k$ bits of $H_\varepsilon(A)$ depend only on $A\cap k$.

The map $\Delta$ is continuous because membership of $n$ in $\Delta(b)$ depends only on the two coordinates $b_n$ and
$b_{n+1}$. Thus each half of $S$ is homeomorphic to $\infiniteSubsets{\omega}$, and the split by the clopen
first-coordinate halves gives $S\cong 2\times\infiniteSubsets{\omega}$.

The space $\infiniteSubsets{\omega}$ is a $\Gdelta$ subset of $\CantorSpace$:
$$
\infiniteSubsets{\omega}
\;=\;
\bigcap_{n \in \omega} \{A \IncludedIn \omega : \exists m \ge n,\; m \in A\}.
$$

Each set in the intersection is open: once some $m \ge n$ is known to lie in $A$, no later coordinates can destroy that
witness. Hence $\infiniteSubsets{\omega}$ is Polish by Alexandrov's theorem in §{sec:alexandrov-theorem}.

The concrete homeomorphism with Baire space sends an infinite set to the gaps between its successive elements. For $A
\in \infiniteSubsets{\omega}$ with increasing enumeration $a_0 < a_1 < a_2 < \cdots$, the \termdefine{gap map} is
$$A \;\longmapsto\; \Tuple{a_0,\; a_1 - a_0 - 1,\; a_2 - a_1 - 1, \ldots} \in \BaireSpace,$$
with inverse
$$\Tuple{g_0, g_1, g_2, \ldots} \;\longmapsto\; \{g_0,\; g_0 + g_1 + 1,\; g_0 + g_1 + g_2 + 2, \ldots\}.$$

For the inverse map, write
$$a_n=n+\sum_{i=0}^{n}g_i\ge n.$$
Given a bound $M$, choose $n$ with $a_n\ge M$. Fixing $g_0,\ldots,g_n$ fixes $a_0,\ldots,a_n$, and all later
enumerated elements exceed $a_n$. Thus these finitely many gap coordinates determine membership below $M$,
which proves continuity of the inverse. For the gap map itself,
continuity is local: if a basic cylinder in $\BaireSpace$ contains the gap sequence of $A$ and fixes its coordinates
$0,\ldots,k-1$, then for $k>0$ it is enough to know $A$ below $a_{k-1}+1$. The case $k=0$ is vacuous. Every nearby
infinite set with the same membership pattern below this finite bound has the same first $k$ selected elements and hence
the same first $k$ gap coordinates. Therefore the gap map is continuous, and
$\infiniteSubsets{\omega} \cong \BaireSpace$.

The gap map is the run-length encoding of §{sec:boundary-mediant-limit-map} in another guise. For $b \in S$, let $r_0,
r_1, r_2, \ldots$ denote its alternating run lengths starting at position $0$, each $r_i \ge 1$. Then $\Delta(b)$ has
$i$-th element $r_0 + r_1 + \cdots + r_i - 1$, so applying the gap map to $\Delta(b)$ recovers the run lengths shifted
down by one to land in $\NN$: $g_i = r_i - 1$.

\begin{mathmeta}
  \forward{alephNull}
\end{mathmeta}

### Comparison of the Models {#sec:concrete-pictures-bridges}

<!-- formalization: skip-begin (chapter summary, comparison tables, native-uses discussion, and the
  continued-fraction/Stern-Brocot comparison; motivational, not proof obligations) -->
The concrete models in this chapter separate into compact Cantor-space pictures and noncompact Baire-space pictures.
In every row, finite information indexes the basic clopen sets.

| Cantor-space picture | underlying space | finite information |
|----------------------|------------------|--------------------|
| cylinder base | $\CantorSpace$ | a finite binary prefix |
| middle-thirds Cantor set | $C\IncludedIn\ClosedInterval{0}{1}$ | finitely many ternary digits, each $0$ or $2$ |
| power set | $\PowerSet{\omega}$ | finitely many membership decisions |

| Baire-space picture | underlying space | finite information |
|---------------------|------------------|--------------------|
| cylinder base | $\BaireSpace$ | a finite sequence of natural numbers |
| irrational line | $\SetDifference{\R}{\QQ}$ | a finite continued-fraction prefix |
| infinite subsets | $\infiniteSubsets{\omega}\IncludedIn\PowerSet{\omega}$ | initial gaps, or switch positions |

The homeomorphisms constructed above relate the models as follows. Simple continued fractions give
$\BaireSpace\cong\SetDifference{\R}{\QQ}$. Run lengths give a homeomorphism between the positive irrationals and
$S\IncludedIn\CantorSpace$. The gap map gives $\infiniteSubsets{\omega}\cong\BaireSpace$, while characteristic
functions identify $\infiniteSubsets{\omega}$ with a subspace of $\PowerSet{\omega}\cong\CantorSpace$.
Thus Baire space is homeomorphic to these subspaces of Cantor space. It is not homeomorphic to the whole Cantor space,
since it is not compact.

The native uses are different. The cylinder base supports closed sets as pruned trees, analytic sets via the Suslin
operation, and Cauchy representations of Polish spaces. Continued fractions support Diophantine approximation by
convergents and the ergodic theory of the Gauss map. Stern--Brocot paths give a rational binary-tree visualization of
irrationals. Infinite subsets support almost inclusion $A \IncludedIn^* B$, almost disjointness
$\Card{A \cap B} < \alephNull$, Ramsey-theoretic partitions, and cardinal invariants of the continuum.

#### Continued fractions and Stern--Brocot {#sec:cf-stern-brocot-comparison}

\begin{mathmeta}
  \vars{L}{Seq}
  \vars{a_*}{Nat}
  \vars{a_0}{Int}
\end{mathmeta}

Continued fractions and Stern--Brocot paths encode the same arithmetic data. The following table lists their
correspondence for three ranges of irrational numbers:
<!-- formalization: skip-end -->

| space | continued fractions | Stern--Brocot |
|-------|---------------------|---------------|
| $\SetDifference{\OpenInterval{0}{1}}{\QQ}$ | $a_0 = 0$ | $S \cap \cyl{L}$ |
| $\SetDifference{\RestrictedSet{\R}{>0}}{\QQ}$ | $a_0 \in \NN$ | $S$ |
| $\SetDifference{\R}{\QQ}$ | $a_0 \in \ZZ$ | sign times $S$ applied to $\Abs{x}$ |

The \termuse{Gauss map} $T$ on $\SetDifference{\OpenInterval{0}{1}}{\QQ}$ is the left shift in continued-fraction
coordinates,
$$[0; a_1, a_2, a_3, \ldots] \longmapsto [0; a_2, a_3, \ldots],$$
and on Stern--Brocot boundary paths in the L-subtree it deletes the initial L-run and swaps L and R on the tail:

$$\wordRepeat{L}{a_1}\wordRepeat{R}{a_2}\wordRepeat{L}{a_3}\cdots \longmapsto
\wordRepeat{L}{a_2}\wordRepeat{R}{a_3}\wordRepeat{L}{a_4}\cdots.$$
