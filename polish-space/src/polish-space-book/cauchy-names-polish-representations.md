# Cauchy Names and Polish Representations {#sec:cauchy-representation-admissibility}
\index{admissibility}

<!-- formalization: skip-begin (chapter motivation, comparison with concrete models, and overview table) -->
§{sec:closed-sets-trees} above explained the prefix-and-tree coding role of $\BaireSpace$. A complementary
picture — the **\termforwardas{Cauchy representation}{Cauchy representation}** — exhibits this role in metric terms:
every Polish space is a continuous image of a closed subset of $\BaireSpace$.

This chapter is a toolkit chapter. Its purpose is not to survey all representation theory, but to establish the naming
facts used repeatedly later: closed domains of Cauchy names, universal continuous surjections from Baire space,
admissibility up to continuous translation, and the binary versus signed-digit example that later becomes a
computability test case.

This should be read as the naming counterpart to the concrete models above. The earlier models presented spaces
homeomorphic to $\BaireSpace$ itself: irrationals, Stern--Brocot boundary paths, and infinite subsets of $\omega$.
Continued fractions name an irrational by partial quotients; Stern--Brocot paths name it by nested rational intervals.
After fixing the initial L/R letter, infinite subsets record the path by switch positions and gap data. A Cauchy
representation uses the same path idea
for an arbitrary Polish space $X$: it carves out a \termdefine{Cauchy space of names}
$$\DomainOf{\rho_X} \IncludedIn \BaireSpace$$
whose points are fast approximation processes in a fixed countable dense set. The representation map then forgets the
particular approximation process and keeps only its limit:
$$\DomainOf{\rho_X} \IncludedIn \BaireSpace
\;\xrightarrow{\;\rho_X\;}\;
X.$$
Thus the corresponding object is not usually $X$ itself but the Cauchy space $\DomainOf{\rho_X}$ above $X$: finite Baire
prefixes become finite metric approximations; infinite names become points of $X$; and different names may represent the
same point. The topology on $X$ is recovered not by a homeomorphism with the Cauchy space, but by the continuous
surjection $\rho_X$ and, later, by \termforwardas{admissible representation of topological space}{admissibility}.

The comparison is:

| picture | path space | finite datum | limit named |
|---------|------------|--------------|-------------|
| continued fractions | integer with a positive sequence | partial-quotient prefix | irrational real |
| Stern--Brocot | non-eventually-constant L/R word | rational interval below prefix | positive irrational |
| infinite subsets | $\infiniteSubsets{\omega}$ | switch-position or gap prefix | L/R branch with a fixed initial
letter, hence a positive irrational |
| Cauchy representation | Cauchy space $\DomainOf{\rho_X}$ | dense-point prefix | point of $X$ |
<!-- formalization: skip-end -->

## Cauchy Names {#sec:cauchy-names}

\begin{mathmeta}
  \vars{p}{Name}
  \vars{n}{Nat}
\end{mathmeta}

Fix a nonempty Polish space $X$ with complete compatible metric $d$ and a countable dense subset
$D = \IndexedFamily{q_n}{n\in\omega}$.
Call $p \in \BaireSpace$ a **\termdefine{Cauchy name}** if, for all $m\ge n\ge0$,
$$d(q_{p(n)},\, q_{p(m)}) \;\le\; 2^{-n}.$$
Let $\DomainOf{\rho_X} \IncludedIn \BaireSpace$ be the set of Cauchy names. The
\termdefine{Cauchy representation} is the map
$$\rho_X : \DomainOf{\rho_X} \twoheadrightarrow X, \qquad \rho_X(p) \;=\; \lim_{n \to \infty} q_{p(n)},$$
where the limit exists because the Cauchy-name condition makes $(q_{p(n)})$ a $d$-Cauchy sequence and $X$ is complete.
Letting $m \to \infty$ in the defining inequality yields the workhorse bound
$$d(q_{p(n)},\, \rho_X(p)) \;\le\; 2^{-n},$$
used repeatedly below.

<!-- formalization: structural -->
Three structural features:

*   **Closed domain.** Each constraint $d(q_{p(n)},\, q_{p(m)}) \le 2^{-n}$ depends only on finitely many coordinates of
    $p$, so it cuts out a clopen subset of $\BaireSpace$. The domain is the countable intersection of these clopen sets,
    hence closed in $\BaireSpace$. By the closed-subspace result of §{sec:polish-key-properties}, the domain is itself
    Polish.
*   **Continuous.** If two Cauchy names $p, p'$ agree on the first $n+1$ coordinates (indices $0, \ldots, n$), then
    $p(n) = p'(n)$, and the workhorse bound puts both $\rho_X(p)$ and $\rho_X(p')$ within $2^{-n}$ of the common point
    $q_{p(n)}$, so $d(\rho_X(p), \rho_X(p')) \le 2 \cdot 2^{-n}$ by the triangle inequality. Thus agreement on a
    sufficiently long prefix forces the images to be arbitrarily close, and $\rho_X : \DomainOf{\rho_X} \to X$ is
    continuous. In fact, with the \termuse{standard sequence metric} on $\BaireSpace$, this gives uniform continuity on
    $\DomainOf{\rho_X}$.
*   **Surjective.** For every $x \in X$ pick $a_n \in D$ with $d(a_n, x) \le 2^{-(n+1)}$ (possible by density). Then for
    $m \ge n$ the triangle inequality gives $d(a_n, a_m) \le 2^{-(n+1)} + 2^{-(m+1)} \le 2^{-n}$. Writing $a_n =
    q_{p(n)}$ produces a Cauchy name $p$, and since $a_n \to x$, its represented limit is $\rho_X(p)=x$.

## Universal Continuous Surjection {#sec:universal-continuous-surjection}

\begin{mathmeta}
  \vars{s}{Seq}
  \vars{k,n}{Nat}
\end{mathmeta}

<!-- formalization: structural -->
These three features establish:

\begin{theorem*} Every nonempty Polish space is a continuous image of a closed subset of $\BaireSpace$. In fact, every
nonempty Polish space is a continuous image of $\BaireSpace$ itself.

\end{theorem*}

\begin{proof}[Proof] The first assertion is immediate from the Cauchy representation: $\DomainOf{\rho_X}$ is closed in
$\BaireSpace$, and $\rho_X : \DomainOf{\rho_X} \to X$ is continuous and surjective.

For the stronger assertion, it remains to see that every nonempty closed $F \IncludedIn \BaireSpace$ is a continuous
retract of $\BaireSpace$. Let
$$T_F := \{s \in \finseq{\omega} : \cyl{s} \cap F \ne \emptyset\}$$
be the tree of finite prefixes realized by points of $F$. Since $F$ is closed, $F = [T_F]$, the set of infinite branches
through $T_F$: if $x \notin F$, some basic cylinder around $x$ is disjoint from $F$, so some prefix of $x$ is not in
$T_F$. For each $s \in T_F$, choose once and for all a branch $b_s \in F \cap \cyl{s}$.

Define $r : \BaireSpace \to F$ as follows. If $x \in F$, set $r(x) = x$. Otherwise let $n$ be least such that
$\restrict{x}{n} \in T_F$ but $\restrict{x}{n+1} \notin T_F$, and set $r(x) = b_{\restrict{x}{n}}$. This is a retraction
because it fixes every point of $F$ and always lands in $F$.

It is continuous. If $x \notin F$, the same first failure of membership in $T_F$ occurs throughout the cylinder
$\cyl{\restrict{x}{n+1}}$, so $r$ is locally constant there. If $x \in F$ and a basic neighborhood
$\cyl{\restrict{x}{k}}$ of $r(x)=x$ is given, then every $y \in \cyl{\restrict{x}{k}}$ either belongs to $F$, in which
case $r(y)=y \in \cyl{\restrict{x}{k}}$, or first leaves $T_F$ at some stage $m \ge k$ (since $\restrict{y}{k} =
\restrict{x}{k} \in T_F$), in which case $r(y)=b_{\restrict{y}{m}} \in \cyl{\restrict{y}{m}} \IncludedIn
\cyl{\restrict{y}{k}} = \cyl{\restrict{x}{k}}$. Thus $r$ is continuous at every point. Therefore $\rho_X \circ r :
\BaireSpace \to X$ is a continuous surjection.
\end{proof}

<!-- formalization: skip-begin (contextual applications and forward pointer to computable analysis) -->
Two uses:

*   **Reduction principle.** A continuous surjection from a closed name space can transfer an argument only when the
    relevant conclusion is preserved by continuous images. The reduction to a closed subspace of $\BaireSpace$ in the
    proof of the Lusin–Suslin theorem in §{sec:lusin-souslin-proof} instead uses the later
    \termforwardas{closed presentation in Baire space}{closed-presentation theorem} of
    §{sec:closed-presentation-baire}. The \termuse{perfect set theorem} of §{sec:perfect-set-theorem} is proved directly
    for arbitrary perfect Polish spaces by a Cantor scheme.
*   **Computable analysis.** The same naming map becomes effective once the metric presentation is computable.
    §{sec:computable-polish-tte} returns to this point and adds lambda realizers, computable dense sequences, and
    effective names. The present chapter uses Cauchy names only as topological names.
<!-- formalization: skip-end -->

## Reducibility of Representations {#sec:reducibility-representations}

\begin{mathmeta}
  \define{ContinuouslyReducesTo,NotContinuouslyReducesTo,ContinuouslyEquivalentTo,NotContinuouslyEquivalentTo}
\end{mathmeta}

A \termdefine{representation} of a set $X$ is a partial function $\PartialFunctionMap{\delta}{\BaireSpace}{X}$
whose range is all of $X$. Its domain carries the subspace topology inherited from $\BaireSpace$.
The Cauchy representation is one example. Compare two representations $\PartialFunctionMap{\delta_1}{\BaireSpace}{X}$
and $\PartialFunctionMap{\delta_2}{\BaireSpace}{X}$ of the same set $X$ via continuous translation. Say that $\delta_1$
is
\termdefineas{continuous reducibility of representations}{continuously reducible} to $\delta_2$, written
$$\delta_1 \ContinuouslyReducesTo \delta_2,$$
if there exists a continuous $f : \DomainOf{\delta_1} \to \DomainOf{\delta_2}$ with $\delta_2 \circ f = \delta_1$.
Thus every $\delta_1$-name can be continuously translated into a $\delta_2$-name of the same point. Representations
reducible in both directions are \termdefineas{continuous equivalence of representations}{continuously equivalent},
written $\delta_1 \ContinuouslyEquivalentTo \delta_2$.
<!-- formalization: skip-begin (deferred to the chapter on computable presentations) -->
The computable analogue is postponed to
§{sec:computable-metric-presentations}, where the dense sequence and the translator are required to be effective.
<!-- formalization: skip-end -->

A representation $\rho$ of a topological space $X$ is
\termdefineas{admissible representation of topological space}{admissible} if it is continuous and every continuous
representation $\delta$ of $X$ satisfies $\delta \ContinuouslyReducesTo \rho$. Equivalently, $\rho$ is a greatest
element of the preorder of continuous representations ordered by $\ContinuouslyReducesTo$. Schröder's universal-property
formulation quantifies over every continuous partial map $\PartialFunctionMap{g}{\BaireSpace}{X}$ rather than only
representations. It is equivalent to the greatest-element formulation without any Polishness assumption. Given such a
map $g$, prefix its names by $0$ and prefix $\rho$-names by $1$ to combine $g$ and $\rho$ into a continuous
representation of $X$. A translator from this combined representation to $\rho$ restricts to a translator from $g$ to
$\rho$.

## Kreitz–Weihrauch Admissibility Theorem {#sec:kreitz-weihrauch-admissibility}

\begin{mathmeta}
  \vars{i,n}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

\begin{theorem*}[\termdefineas{Kreitz--Weihrauch admissibility theorem}{Kreitz–Weihrauch}]
On any nonempty Polish space $X$, the Cauchy representation $\rho_X$ is admissible. Two admissible representations of
the same Polish space are continuously equivalent. Hence "the admissible representation" is well-defined up to
$\ContinuouslyEquivalentTo$, and a representation of a Polish space is admissible iff it is continuously equivalent to
$\rho_X$.

\end{theorem*}

\begin{proof}[Proof] Let $\delta : E \to X$ be any
continuous representation, with $E \IncludedIn \BaireSpace$. We must continuously translate each $\delta$-name into a
Cauchy name for the same point.

Fix $n$. The sets
$$U_i^n := \delta^{-1}\big(\Ball{q_i}{2^{-(n+2)}}\big) \qquad (i \in \omega)$$
cover $E$, by density of $\{q_i\}$. Since $E$ is a subspace of the zero-dimensional space $\BaireSpace$, it has the
relative clopen cylinder base $\{E \cap \cyl{s} : s \in \finseq{\omega}\}$. Enumerate all pairs $\Pair{s}{i}$ such that
$$E \cap \cyl{s} \IncludedIn U_i^n.$$
These relative clopen sets cover $E$: for $p \in E$, continuity of $\delta$ gives a cylinder neighborhood of $p$ whose
$\delta$-image lies in some ball $\Ball{q_i}{2^{-(n+2)}}$. Disjointify the enumeration by replacing each listed $E \cap
\cyl{s_j}$ with
$$C_j^n := \SetDifference{(E \cap \cyl{s_j})}{\bigcup_{k<j} (E \cap \cyl{s_k})}.$$
The nonempty $C_j^n$ form a disjoint clopen partition of $E$. Define $h_n : E \to \omega$ by setting $h_n(p)=i_j$ on
$C_j^n$, where $\Pair{s_j}{i_j}$ is the $j$-th listed pair. Because the pieces are clopen, $h_n$ is continuous as a map
into
the discrete space $\omega$, and
$$d(q_{h_n(p)}, \delta(p)) < 2^{-(n+2)}.$$

Now define $f : E \to \BaireSpace$ by
$$f(p)(n) := h_n(p).$$
Each coordinate is continuous, hence $f$ is continuous into the product space $\BaireSpace$. For $m \ge n$,
$$
\begin{aligned}
d(q_{f(p)(n)}, q_{f(p)(m)})
&\le d(q_{f(p)(n)}, \delta(p)) + d(\delta(p), q_{f(p)(m)})\\
&< 2^{-(n+2)} + 2^{-(m+2)}\\
&\le 2^{-n},
\end{aligned}
$$
so $f(p)$ is a Cauchy name. Moreover $q_{f(p)(n)} \to \delta(p)$, so $\rho_X(f(p))=\delta(p)$. Thus
$\delta \ContinuouslyReducesTo \rho_X$, and since $\delta$ was arbitrary, $\rho_X$ is admissible.

If $\alpha$ and $\beta$ are admissible representations of the same space, applying admissibility first to $\beta$ and
then to $\alpha$ gives $\beta \ContinuouslyReducesTo \alpha$ and $\alpha \ContinuouslyReducesTo \beta$, so
$\alpha \ContinuouslyEquivalentTo \beta$. In particular, every admissible representation is equivalent to $\rho_X$.
Conversely, if $\delta \ContinuouslyEquivalentTo \rho_X$, then $\delta$ is continuous because
$\delta = \rho_X \circ f$ for a continuous translator $f$, and every continuous representation $\gamma$ satisfies
$\gamma \ContinuouslyReducesTo \rho_X \ContinuouslyReducesTo \delta$; hence $\delta$ is admissible.
\end{proof}

Changing the complete compatible metric or the countable dense sequence gives a continuously equivalent Cauchy
representation, since each such representation is admissible. No effectiveness of these choices is required here.

\begin{corollary*}[Recovery of the topology]
Let $X$ be a nonempty Polish space and $\rho$ an admissible representation of $X$.
A set $U\IncludedIn X$ is open in $X$ if and only if $\rho^{-1}(U)$ is open in $\DomainOf{\rho}$.
Thus $\rho$ is a \termdefine{quotient map}; in particular, the Cauchy representation recovers the topology of $X$.
\end{corollary*}

\begin{proof}
The forward implication follows from continuity of $\rho$. Suppose that $\rho^{-1}(U)$ is open but $U$ is not.
Since $X$ is metrizable, there are $x\in U$ and a sequence $\Sequence{x_n}{n\in\omega}$ in $\SetDifference{X}{U}$
converging to $x$.
In $\BaireSpace$, define
$$
e_\infty(k)=0,\qquad
 e_n(k)=\begin{cases}1&k=n,\\0&k\ne n.\end{cases}
$$
The subspace $E:=\{e_\infty\}\cup\{e_n:n\in\omega\}$ has isolated points $e_n$ and $e_n\to e_\infty$.
Hence the map $g:E\to X$ defined by $g(e_\infty)=x$ and $g(e_n)=x_n$ is continuous.
The partial-map form of admissibility gives a continuous $h:E\to\DomainOf{\rho}$ with $\rho\circ h=g$.
But then
$$
h^{-1}(\rho^{-1}(U))=g^{-1}(U)=\{e_\infty\}
$$
is open in $E$, contradicting $e_n\to e_\infty$. Thus $U$ is open.
\end{proof}

## Comparing Binary and Signed-Digit Names {#sec:binary-signed-digit-comparison}

<!-- formalization: skip-begin (orientation and reference to the later computational treatment) -->
The two representations below name the same interval but permit different continuous choices of names.
The binary expansion illustrates the obstruction at dyadic boundaries; signed digits allow overlapping choices.
We compare both with Cauchy names before returning to their computational content in §{sec:tte-binary-signed-digit}.
<!-- formalization: skip-end -->

### Binary Expansion {#sec:binary-expansion-example}

\begin{mathmeta}
  \vars{m,n}{Nat}
  \vars{x}{Real}
  \vars{N}{Nat}
\end{mathmeta}

The \termdefine{binary expansion} is the representation of $\ClosedInterval{0}{1}$
$$\rho_{\mathrm{bin}} : \CantorSpace \to \ClosedInterval{0}{1}, \qquad \rho_{\mathrm{bin}}(p) \;=\; \sum_{n \in \omega}
p(n) \cdot
2^{-(n+1)}.$$

Every $x\in\ClosedInterval{0}{1}$ has a binary name. Starting with $s_0=0$, choose $p(n)=1$ exactly when
$s_n+2^{-(n+1)}\le x$, and put $s_{n+1}=s_n+p(n)2^{-(n+1)}$. Inductively $0\le x-s_n\le2^{-n}$, so $s_n\to x$.

**Factoring through Cauchy.** Fix an enumeration $D = \IndexedFamily{q_n}{n\in\omega}$ of the dyadic rationals in
$\ClosedInterval{0}{
1}$, and
define $f : \CantorSpace \to \DomainOf{\rho_{\ClosedInterval{0}{1}}}$ by sending $p$ to the sequence of indices for the
partial sums
$\sum_{k < n} p(k) \cdot 2^{-(k+1)}$. For $m\ge n$, the digits added between the two truncation stages satisfy
$$
\Abs{\sum_{k<m}p(k)2^{-(k+1)}-\sum_{k<n}p(k)2^{-(k+1)}}
\le \sum_{n\le k<m}2^{-(k+1)}
=2^{-n}-2^{-m}
\le 2^{-n}.
$$
Thus the partial sums form a Cauchy name. The map $f$ is continuous, and
$\rho_{\ClosedInterval{0}{1}} \circ f = \rho_{\mathrm{bin}}$. Hence
$$\rho_{\mathrm{bin}} \ContinuouslyReducesTo \rho_{\ClosedInterval{0}{1}}.$$
This is exactly the formal sense in which "the binary expansion gives a Cauchy approximation by truncation" — truncation
is the translation map.

**The converse fails.** $\rho_{\ClosedInterval{0}{1}} \NotContinuouslyReducesTo \rho_{\mathrm{bin}}$, so
$\rho_{\mathrm{bin}}$ is not
admissible. By the \termuseas{Kreitz--Weihrauch admissibility theorem}{Kreitz–Weihrauch theorem}, this is equivalent to
$\rho_{\ClosedInterval{0}{1}} \NotContinuouslyEquivalentTo \rho_{\mathrm{bin}}$. The obstruction sits at the dyadic
rationals. Suppose
a continuous $f : \DomainOf{\rho_{\ClosedInterval{0}{1}}} \to \CantorSpace$ satisfied
$\rho_{\mathrm{bin}} \circ f = \rho_{\ClosedInterval{0}{1}}$. Any Cauchy name $p$ of
a point in $\RightClosedInterval{1/2}{1}$ would force the leading binary digit $f(p)(0) = 1$, and any Cauchy name of a
point in $\LeftClosedInterval{0}{1/2}$
would force the leading binary digit $f(p)(0) = 0$.

Let $p^*$ be the constant Cauchy name of $1/2$. Since $f(\cdot)(0)$ maps into the discrete space $\{0,1\}$ and is
continuous at $p^*$, some finite prefix $s=\restrict{p^*}{N}$ decides the value of $f(p)(0)$ for every Cauchy name $p$
extending $s$. Choose the dyadic rationals
$$x^\pm=\frac12\pm2^{-(N+3)}.$$
Extend $s$ to $p^\pm$ by using a fixed index of $x^\pm$ at every position from $N$ onwards.
For $m\ge n$, the distance between the two approximations is zero if both positions precede $N$ or both are at
least $N$. If $n<N\le m$, it is
$$\Abs{x^\pm-1/2}=2^{-(N+3)}\le2^{-n}.$$
Thus $p^\pm$ are Cauchy names of $x^\pm$. The prefix decision gives
$f(p^-)(0)=f(p^+)(0)$. Correctness of the translator gives $f(p^-)(0)=0$ because $x^-<1/2$, and $f(p^+)(0)=1$ because
$x^+>1/2$, a contradiction.

<!-- formalization: skip (computability preview of the binary-expansion obstruction) -->
The same obstruction later becomes a computability obstruction: binary notation forces an infinite-carry decision at
dyadic boundary points. §{sec:tte-binary-signed-digit} revisits this example after Type-Two lambda realizers have been
introduced.

### Signed-Digit Representation {#sec:signed-digit-representation}

\begin{mathmeta}
  \vars{m}{Nat}
  \vars{x}{Real}
\end{mathmeta}

The standard repair is the **\termdefine{signed-digit representation}**
$$\rho_{\mathrm{sd}} : \funcspace{\omega}{\{-1,0,1\}} \to \ClosedInterval{0}{1}, \qquad
\rho_{\mathrm{sd}}(a)
= \frac12 + \sum_{n \in \omega} a(n)\,2^{-(n+2)}.$$
Here $\funcspace{\omega}{\{-1,0,1\}}$ is a finite-alphabet sequence space, hence naturally homeomorphic to a closed
subspace of $\BaireSpace$ after coding $-1,0,1$ by natural numbers.
The centering at $1/2$ ensures that every value lies in $\ClosedInterval{0}{1}$, since
$$\sum_{n \in \omega}2^{-(n+2)}=\frac12$$
is the maximum displacement in either direction. The converse translation below constructs a signed-digit name for
every $x\in\ClosedInterval{0}{1}$, so the range is exactly $\ClosedInterval{0}{1}$.

**Equivalence with Cauchy.** First, $\rho_{\mathrm{sd}} \ContinuouslyReducesTo \rho_{\ClosedInterval{0}{1}}$. Given a
signed-digit name
$a$, send it to the Cauchy name whose $N$-th approximation is the dyadic partial sum
$$s_N := \frac12 + \sum_{n<N} a(n)\,2^{-(n+2)}.$$
The omitted tail has absolute value at most $2^{-(N+1)}$, so the partial sums form a fast Cauchy sequence and converge
to $\rho_{\mathrm{sd}}(a)$. Each $s_N$ depends only on the first $N$ digits, hence the translation from signed-digit
names to Cauchy names is continuous.

Conversely, $\rho_{\ClosedInterval{0}{1}} \ContinuouslyReducesTo \rho_{\mathrm{sd}}$. Let $p$ be a Cauchy name for $x
\in \ClosedInterval{0}{1}$. We
recursively choose signed digits $a(0),a(1),\ldots$. After $n$ digits, put
$$c_n := \frac12 + \sum_{k<n} a(k)\,2^{-(k+2)}, \qquad R_n := 2^{-(n+1)},$$
and maintain the invariant $\Abs{x-c_n} \le R_n$. It holds at $n=0$ because $c_0=1/2$ and $x \in \ClosedInterval{0}{1}$.

Set $h:=2^{-(n+2)}$, so $R_n=2h$ and $R_{n+1}=h$. The workhorse bound gives
$$\Abs{q_{p(n+4)}-x} \le 2^{-(n+4)} = h/4.$$
Let $r:=q_{p(n+4)}-c_n$, and choose
$$
a(n)=
\begin{cases}
-1, & r < -h/2,\\
1, & r > h/2,\\
0, & \Abs{r} \le h/2.
\end{cases}
$$
If $a(n)=-1$, then $x-c_n < -h/4$, while the induction hypothesis gives $x-c_n \ge -2h$, so
$$\Abs{x-(c_n-h)} \le h.$$
The case $a(n)=1$ is symmetric. If $a(n)=0$, then $\Abs{x-c_n} \le 3h/4 < h$. Thus in every case
$$\Abs{x-c_{n+1}} \le R_{n+1}, \qquad c_{n+1}=c_n+a(n)2^{-(n+2)}.$$
Therefore $c_n \to x$, and the produced signed-digit sequence names $x$.

The $n$-th output digit depends only on the finite tuple $p(0),\ldots,p(n+4)$ and the earlier output digits, so the
translation is continuous. Hence $\rho_{\mathrm{sd}} \ContinuouslyEquivalentTo \rho_{\ClosedInterval{0}{1}}$, so by the
\termuseas{Kreitz--Weihrauch admissibility theorem}{Kreitz–Weihrauch theorem} $\rho_{\mathrm{sd}}$ is admissible.

<!-- formalization: skip (affine-rescaling observation and qualitative pointer to the effective version) -->
The same construction works on any compact interval by affine rescaling. The redundant digit is what makes the final
translation continuous; ordinary binary digits fail exactly at the places where an infinite carry would force a
discontinuous choice. The effective version of this contrast appears in §{sec:tte-binary-signed-digit}.
