# Wadge Hierarchy {#sec:wadge}

<!-- formalization: skip-begin (chapter motivation, historical context, and proof scope) -->
The Borel hierarchy of §{sec:borel-hierarchy} stratifies pointclasses by countable Boolean operations on opens. The
**\termdefine{Wadge hierarchy}**, introduced by William Wadge in the early 1970s and developed fully in his 1983
Berkeley thesis, supplies a much finer stratification using continuous reductions. Under suitable determinacy, the Wadge
degrees of Borel sets are *almost-linearly ordered* and *well-founded*. They break each Borel class into ordinal-many
finer pieces and refine the hierarchy at the level of pointclasses.

We work throughout in zero-dimensional Polish spaces — typically $\BaireSpace$ or $\CantorSpace$ — where cylinder bases
supply the natural game-theoretic framework. The Borel-preserving refinements of §{sec:closed-presentation-baire} show
that every standard Borel space admits such a presentation. The Wadge degree itself still depends on the chosen
topology, because changing the topology changes which reductions are continuous.

This chapter introduces Wadge reducibility and Wadge games, proves Wadge's lemma, and develops the first Wadge degrees
and the Hausdorff difference hierarchy. It also proves the Martin--Monk theorem on well-foundedness of Borel
Wadge degrees by an explicit simultaneous-game construction. The broader projective and AD-level hierarchy is
surveyed using external results from Kechris §21 and Moschovakis.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Read the strategy definitions and the Borel determinacy statement in §{sec:determinacy}, together with the
cylinder topology in §{sec:cylinder-base} and Borel ranks in §{sec:borel-hierarchy}. The proof of Borel
determinacy may be deferred while its conclusion is used. Measure algebras and Polish-group actions are not
needed. First learn the reduction game and Wadge lemma, then test the first degrees against the difference
hierarchy. The simultaneous-game proof of well-foundedness is a second-pass destination. The chapter should
leave readers able to distinguish Borel rank from continuous reducibility and to explain why the topology
chosen for the code space matters.

<!-- formalization: skip-end -->

## Wadge Reducibility {#sec:wadge-reducibility}
\index{Wadge reducibility}

For $A \IncludedIn X$ and $B \IncludedIn Y$ with $X, Y$ zero-dimensional Polish, $A$
**\termdefineas{Wadge reducibility}{Wadge-reduces}** to $B$, written $A \le_W B$, if there exists a continuous map $f :
X \to Y$ with
$$A \;=\; f^{-1}(B).$$
Thus $A$ is "no harder than $B$ up to a continuous renaming of points." The relation is reflexive and transitive, hence
a quasi-order on subsets of zero-dimensional Polish spaces, with associated equivalence $A \equiv_W B$ and
\termdefine{Wadge degree} $[A]_W$.

*Compatibility with Borel classes.* If $A \le_W B$ via continuous $f$, then $A$ has Borel rank no greater than that
of $B$, since
continuous preimages of $\bSigma^0_\alpha$ sets remain $\bSigma^0_\alpha$. So each Borel pointclass $\bSigma^0_\alpha,
\bPi^0_\alpha, \bDelta^0_\alpha$ is **closed under $\le_W$** — Wadge reductions never escape upward in the Borel
hierarchy, and each of these pointclasses is downward closed in the Wadge ordering.

*Self-dual vs non-self-dual.* A Wadge degree $[A]_W$ is \termdefine{self-dual} if $A \equiv_W \SetDifference{X}{A}$,
otherwise
\termdefine{non-self-dual}. For nonempty $X$, the trivial degrees $[\emptyset]_W$ and $[X]_W$ are non-self-dual and
mutually dual. A
self-dual degree is one on which a continuous self-map can swap "in" and "out" of $A$. Typical examples are
nonempty proper clopen sets <!--
formalization: skip-begin (引用・背景説明・読書案内:
自明な2次数の非自己双対性、自己双対性と補集合への連続還元の同値、および非自明clopenの例はWadgeHierarchyへ接続した。
残るself-dual joinは局所証明を展開しない例示であり、後続の補題としては使用しない。)
--> and, more generally, self-dual joins of a set with its complement.<!--
formalization: skip-end
-->

For a pointclass $\Gamma$, write $\check\Gamma := \{\SetDifference{X}{A} : A \in \Gamma\}$ for the
**\termdefine{dual class}**. Wadge degrees come paired with their duals; <!--
formalization: skip-begin (引用・背景説明・読書案内:
dual classの集合像による定義とWadge同値が補集合で保たれることは接続済み。
残る文はnon-self-dualという用語の解釈を述べる概説で、新しい局所的な構成・証明ではない。)
--> the non-self-dual ones enforce the asymmetry
between $\Gamma$ and $\check\Gamma$ at every level.<!--
formalization: skip-end
-->

## Wadge Games {#sec:wadge-games}

\begin{mathmeta}
  \vars{y}{Name}
  \vars{s}{Seq}
\end{mathmeta}

Wadge degrees are computed by games. For $A, B \IncludedIn \BaireSpace$, the \termdefine{Wadge game} $G_W(A, B)$ is
played as follows. At round $n$, Player I plays a natural number $a_n$, and Player II replies with a natural number
or a *pass*. Every finite sequence of such moves is allowed. II must make infinitely many non-pass moves to win:
II may wait any finite number of rounds for the next output coordinate, but must eventually produce every coordinate.
A play satisfying this output condition produces
$$x \;:=\; \Tuple{a_0, a_1, \ldots} \in \BaireSpace, \qquad y \;:=\; (\text{II's genuine moves in order}) \in
\BaireSpace.$$
*II wins* iff
$$x \in A \;\Longleftrightarrow\; y \in B.$$
The pass option is the technical mechanism that lets II observe enough of $x$ before committing to coordinates of $y$.
Plays with only finitely many genuine moves are losses for II.

\begin{lemma*}[\termdefineas{Wadge strategy correspondence}{Strategy correspondence}] In $G_W(A, B)$:

\begin{enumerate}
\item II has a winning strategy iff $A \le_W B$.
\item If I has a winning strategy, then $B \le_W \SetDifference{\BaireSpace}{A}$. Consequently, if the game is
determined and
$A\not\le_W B$, then I has a winning strategy and hence $B \le_W \SetDifference{\BaireSpace}{A}$.
\end{enumerate}

\end{lemma*}

\begin{proof}[Proof]
For (1, $\Rightarrow$), fix a winning strategy $\sigma$ of II. Prescribe I's input $x$ and let II follow
$\sigma$. The resulting play exists and is unique by the lemma on the play of two strategies in §{sec:determinacy}.
If two inputs agree on their first $N$ coordinates, induction over the first $N$ rounds shows that the entire
histories through those rounds agree: I supplies the same move, and II applies the same strategy to the same history.

Because $\sigma$ wins, it produces infinitely many genuine moves against every $x$. Let $f_\sigma(x)$ be its
output after deleting passes, and let $j_k(x)$ be the round at which its $k$-th genuine move is played.
Agreement of the input through that round fixes this output coordinate:
$$
\restrict{x'}{j_k(x)+1}=\restrict{x}{j_k(x)+1}
\quad\Longrightarrow\quad f_\sigma(x')(k)=f_\sigma(x)(k).
$$
Thus each coordinate is locally constant, and $f_\sigma$ is continuous. The winning condition gives
$$x\in A\quad\Longleftrightarrow\quad f_\sigma(x)\in B,$$
so $A=f_\sigma^{-1}(B)$.

For (1, $\Leftarrow$), suppose $A=f^{-1}(B)$ with $f$ continuous. For a finite input word $s$, let
$\widehat{s}$ extend $s$ by zeros, and write
$$K_f(s,k)\quad\Longleftrightarrow\quad
\forall z\in\cyl{s}\quad f(z)(k)=f(\widehat{s})(k).$$
This condition says that the next requested value is already determined on the whole cylinder.
Use code $0$ for a pass and code $m+1$ for a genuine move $m$. After I has supplied $x(0),\ldots,x(n)$,
put $s_n:=\restrict{x}{n+1}$. Start with $k_0:=0$ and apply the rule
$$
\Pair{c_n}{k_{n+1}}:=
\begin{cases}
\Pair{f(\widehat{s_n})(k_n)+1}{k_n+1},&K_f(s_n,k_n),\\
\Pair{0}{k_n},&\text{otherwise}.
\end{cases}
$$
Here $c_n$ is II's next coded move, and $k_n$ is the number of genuine moves already made. The count and all
previous responses can be reconstructed from the finite input word, so this is a strategy on finite histories.
Whenever a genuine move is made, its decoded value is $f(x)(k_n)$, since $x\in\cyl{s_n}$.

It remains to prove that the strategy produces every coordinate. For fixed $x$ and $k$, continuity of the
$k$-th coordinate of $f$ gives a cylinder containing $x$ on which that coordinate is constant.
Every sufficiently long input prefix determines a subcylinder of it, so $K_f(s_n,k)$ holds for all sufficiently
large $n$. The counts $k_n$ are nondecreasing. If at least $k$ values have been emitted, then either the next
one has already been emitted or the count is still $k$; in the latter case it increases as soon as a sufficiently
long prefix has been read. Induction on $k$ proves that arbitrarily many values are emitted.
Thus the play has infinitely many genuine moves, its output is exactly $f(x)$, and $A=f^{-1}(B)$ makes the
strategy winning for II.

For (2), fix a winning strategy $\tau$ of I. Given $y\in\BaireSpace$, make II never pass and supply the codes
$y(n)+1$. Keeping the full coded history, define
$$
\begin{aligned}
p_0&:=\emptySeq,& a_n&:=\tau(p_n),\\
p_{n+1}&:=p_n\concat\Pair{a_n}{y(n)+1},& g(y)(n)&:=a_n.
\end{aligned}
$$
If two inputs $y$ agree before coordinate $n$, induction gives the same $p_n$ and hence the same $a_n$.
Therefore every coordinate of $g$ depends on a finite prefix, and $g$ is continuous. II's genuine output in
this play is $y$. Since I follows $\tau$ and wins against this opponent who never passes,
$$g(y)\in A\quad\Longleftrightarrow\quad y\notin B.$$
Equivalently,
$$y\in B\quad\Longleftrightarrow\quad g(y)\in\SetDifference{\BaireSpace}{A}.$$
Hence $B=g^{-1}(\SetDifference{\BaireSpace}{A})$, as required.

Finally, under determinacy one player has a winning strategy. If $A\not\le_W B$, the implication already
proved for II excludes a winning strategy for II. Thus I has one, and (2) gives the second reduction.
\end{proof}

## Wadge's Lemma {#sec:wadge-lemma}

\begin{mathmeta}
  \vars{p}{Nat}
\end{mathmeta}

\begin{lemma*}[\termdefineas{Wadge lemma}{Wadge}] If $G_W(A, B)$ is determined, then either
$$A \le_W B \qquad \text{or} \qquad B \le_W \SetDifference{\BaireSpace}{A}.$$
\end{lemma*}

\begin{proof}[Proof]
This is immediate from the previous lemma: under determinacy one of I, II has a winning strategy, supplying one of the
two reductions.
\end{proof}

\begin{lemma*}[\termdefineas{Borelness of Wadge payoffs}{Borelness of Wadge payoffs}]
The payoff sets for both players in $G_W(A,B)$ are Borel whenever $A$ and $B$ are Borel, including the
convention that II loses if only finitely many genuine moves are made.
\end{lemma*}

\begin{proof}[Proof]
Encode a pass by $0$ and a genuine move $k$ by $k+1$. The space of round-by-round plays is
$$P:=\seqPower{(\omega\times\omega)}{\omega},\qquad p=\Tuple{\Pair{a_0}{c_0},\Pair{a_1}{c_1},\ldots}.$$
All coordinates have the discrete topology. The plays on which II produces infinitely many genuine moves form
$$L:=\bigcap_{N\in\omega}\bigcup_{n\ge N}\{p\in P:c_n\ne0\}.$$
Each set in braces is a countable union of basic cylinders, hence open.
Thus $L$ is a $\Gdelta$ subset of $P$, in particular a Borel subset.

For $p\in L$, list the positions of its genuine moves by
$$
\begin{aligned}
j_0(p)&:=\min\{n:c_n\ne0\},\\
j_{r+1}(p)&:=\min\{n>j_r(p):c_n\ne0\}.
\end{aligned}
$$
The output condition makes every minimum exist. The indices increase strictly and exhaust the genuine moves,
because each step chooses the first remaining position. Define
$$\pi_I(p)(n):=a_n,\qquad \pi_{II}(p)(r):=c_{j_r(p)}-1.$$
The latter subtraction is applied only to positive codes. Both maps have domain $L$ and codomain $\BaireSpace$.
The first is a coordinate projection. For the second, if $q\in L$ agrees with $p$ through round $j_r(p)$,
induction over the successive minima gives
$$j_r(q)=j_r(p),\qquad \pi_{II}(q)(r)=\pi_{II}(p)(r).$$
This fixes each output coordinate on a cylinder neighborhood relative to $L$, proving continuity.

Inside $L$, the matching-membership condition is the set
$$
E:=\bigl(\pi_I^{-1}(A)\cap\pi_{II}^{-1}(B)\bigr)
\cup
\bigl(\pi_I^{-1}(\SetDifference{\BaireSpace}{A})\cap
\pi_{II}^{-1}(\SetDifference{\BaireSpace}{B})\bigr).
$$
It is Borel in $L$ by continuity. Let $\iota:L\hookrightarrow P$ be inclusion. The actual payoff for II in the
whole play space is $W_{II}:=\iota[E]$. Since $L$ is Borel in $P$, every relatively Borel subset of $L$ is Borel
in $P$, so $W_{II}$ is Borel. Its complement $\SetDifference{P}{W_{II}}$ is I's payoff and is Borel as well.
In particular, every play outside $L$ is a loss for II.

Finally, pass to the alternating integer presentation. The map
$$\rho:\BaireSpace\to P,\qquad \rho(z)(n):=\Pair{z(2n)}{z(2n+1)}$$
is continuous and bijective; its inverse interleaves the two coordinates of each round.
I's integer payoff is $\rho^{-1}(\SetDifference{P}{W_{II}})$, which is Borel by continuity.
This is the ordinary integer game to which Borel determinacy applies.
\end{proof}

Hence Borel determinacy from §{sec:martin-borel-det} supplies the determinacy hypothesis in ZFC. For arbitrary subsets
of $\BaireSpace$, the same conclusion holds under AD.

\begin{corollary*}[Semi-linear ordering principle] For any two Borel subsets $A, B \IncludedIn \BaireSpace$, either $A
\le_W B$ or $B \le_W \SetDifference{\BaireSpace}{A}$. Thus any two degrees become comparable after possibly replacing
one of their sets by its complement.
\end{corollary*}

<!-- formalization: skip-begin (context on failures without determinacy) -->
The "almost-linearity" — every two degrees compare, possibly after replacing one by its complement — is the structural
payoff of determinacy. Without suitable determinacy, semi-linearity can fail: two sets may remain incomparable even
after
complementation. Such failures occur among projective sets in $L$. Incomparability of a non-self-dual set
with its own complement, by contrast, is already allowed by semi-linearity.
<!-- formalization: skip-end -->

## The First Wadge Degrees {#sec:first-wadge-degrees}

\begin{mathmeta}
  \vars{p}{Name}
  \vars{k,n}{Nat}
  \vars{\psi}{Fun(Name,Name)}
\end{mathmeta}

<!-- formalization: skip-begin (overview table for the explicit degree calculations below) -->
The Borel hierarchy starts at $\bSigma^0_1$, the open sets. There is no $\bSigma^0_0$ level in the convention of
§{sec:borel-hierarchy}. In the Wadge hierarchy, however, there is a genuine bottom layer before openness becomes
relevant: the two trivial sets $\emptyset$ and $X$. They form the first non-self-dual pair.

The next few degrees explain the meaning of Wadge reducibility more concretely:

| Wadge behavior | Borel class | membership test |
|---|---|---|
| trivial | $\emptyset$, $X$ | no test is performed |
| clopen | $\bDelta^0_1$ | membership and nonmembership are both decided by finite information |
| open / closed | $\bSigma^0_1$, $\bPi^0_1$ | one side is semidecidable by a finite witness |
| $\Fsigma$ / $\Gdelta$ | $\bSigma^0_2$, $\bPi^0_2$ | one side is a countable disjunction of closed tests |
| ambiguous second level | $\bDelta^0_2$ | membership follows first-entry parity in an increasing open approximation |

The rows through $\bSigma^0_2/\bPi^0_2$ have standard degrees or complete representatives under continuous reductions.
The ambiguous class $\bDelta^0_2$ has no single Wadge-complete set; its internal scale is instead the difference
hierarchy developed in §{sec:hausdorff-difference-hierarchy}.
<!-- formalization: skip-end -->

\begin{proposition*}[trivial and clopen degrees] Let $X$ be a nonempty zero-dimensional Polish space.

\begin{enumerate}
\item If $A\IncludedIn X$ is empty or all of $X$, then $A$ belongs to one of the two trivial Wadge degrees.
\item Every nonempty proper clopen subset of $X$ is Wadge-equivalent to every other nonempty proper clopen subset of a
zero-dimensional Polish space with at least two points.
\item The nonempty proper clopen degree is self-dual.
\end{enumerate}

\end{proposition*}

\begin{proof}[Proof] The first claim is immediate: the only continuous preimage of $\emptyset$ is $\emptyset$, and the
only continuous preimage of a full space is a full space.

For the second claim, let $C\IncludedIn X$ and $D\IncludedIn Y$ be nonempty proper clopen sets. Choose points $d_1\in D$
and
$d_0\in \SetDifference{Y}{D}$. The map
$$
f(x)=
\begin{cases}
d_1, & x\in C,\\
d_0, & x\notin C
\end{cases}
$$
is continuous because $C$ is clopen, and $C=f^{-1}(D)$. Thus $C\le_W D$. The reverse reduction is identical, so
$C\equiv_W D$.

For self-duality, apply the same argument with $D=\SetDifference{Y}{C}$ when $Y=X$. A nonempty proper clopen set and its
complement are Wadge-equivalent.
\end{proof}

Open sets form the first nontrivial non-self-dual Borel pointclass. A useful complete representative in $\CantorSpace$
is
$$
\mathsf O
:=
\{x\in\CantorSpace:\exists n\;x(n)=1\}.
$$
It is open, being the union of the clopen sets $\{x:x(n)=1\}$, and its complement is the singleton $\{0^\omega\}$.
To see that it is not closed, let $e_n$ have its only $1$ in coordinate $n$.
Then $e_n\in\mathsf O$ for every $n$, but $e_n\to0^\omega\notin\mathsf O$.

\begin{proposition*}[$\bSigma^0_1$-complete open set] The set $\mathsf O$ is $\bSigma^0_1$-complete under Wadge
reducibility among subsets of zero-dimensional Polish spaces: for every open $U\IncludedIn X$, where $X$ is
zero-dimensional Polish,
$$
U\le_W\mathsf O.
$$
Moreover, every proper open non-closed subset of a zero-dimensional Polish space is Wadge-equivalent to $\mathsf O$.

\end{proposition*}

\begin{proof}[Proof] Let $U\IncludedIn X$ be open. Choose a countable clopen basis $\Sequence{B_n}{n\in\omega}$.
Put $C_n=B_n$ when $B_n\IncludedIn U$, and put $C_n=\emptyset$ otherwise. The basis property gives
$$
U=\bigcup_{n\in\omega}C_n
$$
with each $C_n$ clopen. Define $f:X\to\CantorSpace$ by
$$
f(x)(n)=
\begin{cases}
1, & x\in C_n,\\
0, & x\notin C_n.
\end{cases}
$$
Each coordinate is continuous because $C_n$ is clopen, hence $f$ is continuous into the product space. By construction,
$$
x\in U
\quad\Longleftrightarrow\quad
\exists n\;f(x)(n)=1
\quad\Longleftrightarrow\quad
f(x)\in\mathsf O.
$$
Thus $U=f^{-1}(\mathsf O)$.

Now let $V\IncludedIn Y$ be proper open and not closed. We already have $V\le_W\mathsf O$ by the first part. For the
converse, choose $y_\infty\in\SetDifference{\Closure{V}}{V}$, and choose a sequence $\Sequence{y_n}{n\in\omega}$ in $V$
converging to
$y_\infty$. Define $g:\CantorSpace\to Y$ by
$$
g(x)=
\begin{cases}
y_n, & n\text{ is the least coordinate with }x(n)=1,\\
y_\infty, & x=0^\omega.
\end{cases}
$$
The map is continuous away from $0^\omega$: if the first $1$ occurs in coordinate $n$, then its value is fixed
on the cylinder determined by the first $n+1$ coordinates. To check continuity at $0^\omega$, let $H$ be an open
neighborhood of $y_\infty$ and choose $N$ such that $y_n\in H$ for all $n\ge N$. If the first $N$ coordinates
of $x$ are zero, then either $x=0^\omega$ or its first $1$ occurs in a coordinate $n\ge N$.
In either case $g(x)\in H$. Finally,
$$
x\in\mathsf O
\quad\Longleftrightarrow\quad
g(x)\in V,
$$
so $\mathsf O\le_W V$.
\end{proof}

By complementation, the dual complete closed set is
$$
\mathsf C:=\SetDifference{\CantorSpace}{\mathsf O}=\{0^\omega\}.
$$
Thus proper closed non-open sets form the dual $\bPi^0_1$ degree. The open and closed complete degrees are not
equivalent: if $\mathsf O\le_W\mathsf C$, then $\mathsf O$ would be closed, because continuous preimages of closed sets
are closed.

At the next Borel level, the useful normal form is not merely "countable union of closed sets" but "there exists a row
satisfying a closed condition." Fix a recursive pairing of $\omega\times\omega$ with $\omega$ and define
$$
\mathsf S_2
:=
\{p\in\CantorSpace:\exists n\;\forall k\; p(\NatPair{n}{k})=0\}.
$$
Equivalently, some row of the binary matrix coded by $p$ is constantly zero. This is an $\Fsigma$ set, since
$$
\mathsf S_2
=
\bigcup_{n\in\omega}
\bigcap_{k\in\omega}
\{p:p(\NatPair{n}{k})=0\},
$$
a countable union of closed sets.

\begin{lemma*}[\termdefine{clopen approximation lemma}] Let $X$ be a zero-dimensional second-countable metrizable space.
If $F\IncludedIn O\IncludedIn X$, with $F$ closed and $O$ open, then there is a clopen set $V$ such that
$$
F\IncludedIn V\IncludedIn O.
$$

\end{lemma*}

\begin{proof}[Proof] The two open sets $O$ and $\SetDifference{X}{F}$ cover $X$. Since clopen sets form a base, every
point has a clopen neighborhood contained in one of these two sets. Second countability gives Lindelöfness, so choose a
countable clopen cover $\Sequence{E_k}{k\in\omega}$ of this form. Assign $E_k$ to $O$ whenever $E_k\IncludedIn O$,
and otherwise to $\SetDifference{X}{F}$.
Disjointify the cover by putting
$$
W_k:=\SetDifference{E_k}{\bigcup_{j<k}E_j}.
$$
Each $W_k$ is clopen because it is a finite Boolean combination of clopen sets. Every point belongs to the unique
$W_k$ indexed by the least $k$ for which it belongs to $E_k$, so these sets partition $X$. Define
$$
V:=\bigcup_{\{k:E_k\IncludedIn O\}}W_k,\qquad
\SetDifference{X}{V}=\bigcup_{\{k:\neg(E_k\IncludedIn O)\}}W_k.
$$
Both unions are open, so $V$ is clopen. A point of $F$ cannot first occur in an $E_k$ assigned to
$\SetDifference{X}{F}$, while every selected $W_k$ lies in $O$. Therefore $F\IncludedIn V\IncludedIn O$.
\end{proof}

\begin{proposition*}[$\bSigma^0_2$-complete set] The set $\mathsf S_2$ is $\bSigma^0_2$-complete under Wadge
reducibility among subsets of zero-dimensional Polish spaces: if $A\in\bSigma^0_2(X)$, then
$$
A\le_W\mathsf S_2.
$$

\end{proposition*}

\begin{proof}[Proof] Write $A=\bigcup_n F_n$ with each $F_n$ closed, and fix a compatible metric $d$ on $X$. For each
$n,k\in\omega$, put
$$
O_{n,k}:=\bigcup_{z\in F_n}\MetricBall{d}{z}{2^{-k}}.
$$
This is an open set containing $F_n$. The clopen approximation lemma gives a clopen set $V_{n,k}$ with
$$
F_n\IncludedIn V_{n,k}\IncludedIn O_{n,k}.
$$
This also handles $F_n=\emptyset$: then $O_{n,k}=\emptyset$ and hence $V_{n,k}=\emptyset$.

These choices satisfy
$$
\bigcap_{k\in\omega}V_{n,k}=F_n.
$$
The inclusion from right to left holds by construction. If $x\notin F_n$, closedness gives $\varepsilon>0$ such that
$\MetricBall{d}{x}{\varepsilon}\cap F_n=\emptyset$. Choose $k$ with $2^{-k}<\varepsilon$. A point of $F_n$ at
distance less than $2^{-k}$ from $x$ would contradict this choice of ball, so $x\notin O_{n,k}$ and hence
$x\notin V_{n,k}$. This proves the other inclusion.

Define $f:X\to\CantorSpace$ by
$$
f(x)(\NatPair{n}{k})=
\begin{cases}
0, & x\in V_{n,k},\\
1, & x\notin V_{n,k}.
\end{cases}
$$
The pairing is a bijection, so this prescribes exactly one value at every coordinate. Each coordinate is continuous
because $V_{n,k}$ is clopen, so $f$ is continuous. For fixed $n$,
$$
\forall k\; f(x)(\NatPair{n}{k})=0
\quad\Longleftrightarrow\quad
x\in\bigcap_kV_{n,k}
\quad\Longleftrightarrow\quad
x\in F_n.
$$
Therefore
$$
x\in A
\quad\Longleftrightarrow\quad
\exists n\;\forall k\;f(x)(\NatPair{n}{k})=0
\quad\Longleftrightarrow\quad
f(x)\in\mathsf S_2.
$$
Hence $A=f^{-1}(\mathsf S_2)$.
\end{proof}

The dual complete $\bPi^0_2$ set is
$$
\mathsf P_2
:=
\SetDifference{\CantorSpace}{\mathsf S_2}
=
\{p:\forall n\;\exists k\;p(\NatPair{n}{k})=1\}.
$$
<!--
formalization: skip-begin (引用・背景説明・読書案内:
Pi02完全集合の行列条件はWadgeSecondLevel.pi2_eqへ接続済み。
残る文は元からformalization:skipで明示した解釈上の類例。段落内のskip指定で通常本文と同じ単位になっているが、
追加の証明は主張していない。)
--> <!-- formalization: skip (interpretive reading of the dual complete set) -->
It says that every row eventually displays a positive witness. This is the same logical shape as many recurrence
properties: for every requirement, some finite evidence eventually appears.<!--
formalization: skip-end
-->

\begin{corollary*} The set $\mathsf P_2$ is $\bPi^0_2$-complete. In particular, in $\CantorSpace$, $\mathsf
S_2\notin\bPi^0_2$ and $\mathsf P_2\notin\bSigma^0_2$.

\end{corollary*}

\begin{proof}[Proof]
Complementing the preceding proposition gives the required reductions to $\mathsf P_2$,
and $\mathsf P_2$ is a $\Gdelta$ set because $\mathsf S_2$ is $\Fsigma$.
For strictness, choose a set $T\IncludedIn\CantorSpace$ with
$$T\in\bSigma^0_2(\CantorSpace),\qquad T\notin\bPi^0_2(\CantorSpace),$$
as supplied by the diagonal argument in §{sec:borel-hierarchy}. The proposition provides a continuous map
$\psi:\CantorSpace\to\CantorSpace$ with $T=\psi^{-1}(\mathsf S_2)$. If $\mathsf S_2$ belonged to $\bPi^0_2$,
closure under continuous preimages would imply $T\in\bPi^0_2(\CantorSpace)$, a contradiction.
If $\mathsf P_2$ belonged to $\bSigma^0_2$, its complement $\mathsf S_2$ would belong to $\bPi^0_2$.
\end{proof}

<!-- formalization: skip (transition from complete second-level pointclasses to their ambiguous part) -->
The ambiguous class $\bDelta^0_2=\bSigma^0_2\cap\bPi^0_2$ is subtler. Its sets have both an $\Fsigma$ and a $\Gdelta$
description, but they need not be clopen and need not lie at any finite clopen stage. Hausdorff's difference hierarchy,
developed next, gives the missing internal scale: a $\bDelta^0_2$ set is one whose membership is decided by entering an
increasing open approximation at a first stage, with the answer determined by the parity of that first-entry stage.

## Hausdorff Difference Hierarchy {#sec:hausdorff-difference-hierarchy}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}
\index{Hausdorff difference hierarchy}
\index{difference hierarchy}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Hausdorff差分階層の導入と歴史的出典表示。具体的な定義、Delta02への包含、
Hausdorffの逆方向の定理・証明は後続で個別に対応済みで、この導入を独立した証明とは数えない。)
-->
The first refinement inside the Wadge hierarchy is already visible at the second Borel level. The class $\bDelta^0_2$ is
much larger than the clopen sets, but its members are still obtained by a controlled alternation of open approximations.
This is the **\termdefine{Hausdorff difference hierarchy}** [@Hausdorff1914].<!--
formalization: skip-end
-->

For an ordinal $\xi$, write $\xi=\lambda+n$ uniquely with $\lambda=0$ or $\lambda$ a limit ordinal and $n<\omega$. Call
$\xi$ *even* or *odd* according as $n$ is even or odd. If $\alpha<\omegaOneOrd$ and $(U_\xi)_{\xi<\alpha}$ is an
increasing sequence of open subsets of a metric space $X$, define
$$
D_\alpha((U_\xi)_{\xi<\alpha})
=
\left\{x\in X:
\begin{array}{l}
\text{there is a least }\xi<\alpha\text{ with }x\in U_\xi,\\
\text{and that }\xi\text{ has parity opposite to }\alpha
\end{array}
\right\}.
$$
The sets obtained in this way form the $\alpha$-th level $\mathsf D_\alpha(\bSigma^0_1)(X)$ of the hierarchy. Thus
$\mathsf D_1(\bSigma^0_1)$ consists of the open sets, $\mathsf D_2(\bSigma^0_1)$ consists of differences
$\SetDifference{U_1}{U_0}$ of open sets with $U_0\IncludedIn U_1$, and higher levels continue by alternating entry into
an increasing open
approximation. Within the union of the approximating opens, complementation reverses the selected parity.
The complement also contains every point that never enters the approximation. Thus reversing parity alone does
not give the full complement unless the open sets cover the space.

\begin{proposition*} For every countable $\alpha$,
$$
\mathsf D_\alpha(\bSigma^0_1)(X)\IncludedIn \bDelta^0_2(X).
$$

\end{proposition*}

\begin{proof}[Proof] Put
$$
S_\xi=\SetDifference{U_\xi}{\bigcup_{\eta<\xi}U_\eta}.
$$
The sets $S_\xi$ are pairwise disjoint: if $\xi<\eta$, membership in $S_\eta$ excludes membership in $U_\xi$.
Every point of $\bigcup_{\xi<\alpha}U_\xi$ has a least entry stage, so it belongs to exactly one $S_\xi$.
Thus $D_\alpha((U_\xi))$ is the union of those $S_\xi$ whose parity is opposite to that of $\alpha$. Each $S_\xi$ is the
intersection of an open set with the complement of an open set. In a metric space this is an $F_\sigma$ set, because
every open set is $F_\sigma$. Hence $D_\alpha((U_\xi))$ is $F_\sigma$, being a countable union of $F_\sigma$ sets.

Its complement is the union of the remaining $S_\xi$ together with
$$
\SetDifference{X}{\bigcup_{\xi<\alpha}U_\xi} ,
$$
which is closed. Hence the complement is also $F_\sigma$. Therefore the set is both $F_\sigma$ and $G_\delta$, so it
lies in $\bDelta^0_2(X)$.
\end{proof}

<!-- formalization: skip (transition to Hausdorff's converse) -->
The converse is Hausdorff's theorem: no $\bDelta^0_2$ set requires anything beyond countably many alternations of open
sets.

\begin{theorem*}[\termdefineas{Hausdorff theorem}{Hausdorff}] If $X$ is a Polish space, then
$$
\bDelta^0_2(X)
=
\bigcup_{\alpha<\omegaOneOrd}
\mathsf D_\alpha(\bSigma^0_1)(X).
$$

\end{theorem*}

\begin{proof}[Proof] Let $A\in\bDelta^0_2(X)$. Define a decreasing sequence of closed sets by transfinite recursion:
$$
F_0=X,\qquad
F_\lambda=\bigcap_{\xi<\lambda}F_\xi\quad(\lambda\text{ limit}),
$$
and
$$
F_{\xi+1}
=
\AmbientClosure{F_\xi}{A\cap F_\xi}
\cap
\AmbientClosure{F_\xi}{(\SetDifference{X}{A})\cap F_\xi}.
$$
The operation on the right is monotone in the closed set $F_\xi$ and takes values in $F_\xi$.
Consequently all stages are closed and the sequence is decreasing. Since $F_\xi$ is closed in $X$, the two
relative closures in the formula agree with their closures in $X$. Thus $F_{\xi+1}$ is the relative boundary,
inside $F_\xi$, between $A$ and its complement. Outside $F_{\xi+1}$, membership in $A$ is locally constant
relative to $F_\xi$.

This derivative reaches the empty set at a countable stage. To see first that some stage stabilizes, choose an
ordinal whose cardinality exceeds that of the power set of $X$. Two stages below it must agree; since the sequence
is decreasing, an adjacent pair must also agree. Let $\theta$ be the first ordinal with $F_{\theta+1}=F_\theta$.
Fix a countable basis $\Sequence{B_n}{n\in\omega}$ of $X$. For every $\xi<\theta$, choose $n(\xi)$ such that
$$
B_{n(\xi)}\cap F_\xi\ne\emptyset,
\qquad
B_{n(\xi)}\cap F_{\xi+1}=\emptyset.
$$
Such a basic open set exists because $F_{\xi+1}$ is a proper closed subset of $F_\xi$.
If $\xi<\eta<\theta$, then $F_\eta\IncludedIn F_{\xi+1}$, so $B_{n(\xi)}$ cannot meet $F_\eta$.
Therefore $n(\xi)\ne n(\eta)$. This injection into $\omega$ shows that $\theta$ is countable.

If the stabilized closed set $F_\theta$ were nonempty, then in the Polish space $F_\theta$ both $A\cap F_\theta$ and
$\SetDifference{F_\theta}{A}$ would be dense. Since $A\in\bDelta^0_2(X)$, both of these relative sets are $G_\delta$ in
$F_\theta$. Two disjoint dense $G_\delta$ subsets of a nonempty Polish space cannot exist, by the Baire category
theorem. Therefore $F_\theta=\emptyset$.

For each $\xi<\theta$, set
$$
P_\xi=\SetDifference{F_\xi}{F_{\xi+1}}.
$$
The sets $P_\xi$ partition $X$. Indeed, every point has a first stage at which it no longer belongs to $F_\xi$,
since $F_\theta=\emptyset$. This first loss cannot occur at a limit stage, where membership means membership in
all earlier stages; it therefore occurs at a successor. Decreasingness makes the layers disjoint.

The open sets representing the two sides of each layer can be given explicitly:
$$
\begin{aligned}
G_\xi&=\SetDifference{X}{\Closure{(\SetDifference{X}{A})\cap F_\xi}},\\
H_\xi&=\SetDifference{X}{\Closure{A\cap F_\xi}}.
\end{aligned}
$$
They satisfy
$$
G_\xi\cap F_\xi=A\cap P_\xi,
\qquad
H_\xi\cap F_\xi=\SetDifference{P_\xi}{A}.
$$
For example, a point of $A\cap F_\xi$ already belongs to $\Closure{A\cap F_\xi}$, so it leaves the next
stage precisely when it lies outside $\Closure{(\SetDifference{X}{A})\cap F_\xi}$.
Conversely, a point of $F_\xi$ outside this latter closure cannot belong to $\SetDifference{X}{A}$.
This proves the first identity; the second follows by exchanging the two sides.

Put $R_\xi=\SetDifference{X}{F_\xi}$. Then $R_\xi$ is open, the sequence $(R_\xi)_{\xi<\theta}$ is increasing, and
$$
R_{\xi+1}
=
R_\xi\cup G_\xi\cup H_\xi.
$$

Now form an increasing open approximation with two steps at stage $\xi$. Write $\alpha=2\cdot\theta$ for the
ordinal sum of $\theta$ many two-point blocks. Every $\eta<\alpha$ has a unique expression $\eta=2\cdot\xi+i$
with $\xi<\theta$ and $i\in\{0,1\}$. Define
$$
\begin{aligned}
V_{2\cdot\xi}&=R_\xi\cup H_\xi,\\
V_{2\cdot\xi+1}&=R_\xi\cup H_\xi\cup G_\xi=R_{\xi+1}.
\end{aligned}
$$
Each set is open. For $\xi<\zeta<\theta$,
$$
\begin{aligned}
R_\xi&\IncludedIn V_{2\cdot\xi}\IncludedIn V_{2\cdot\xi+1}=R_{\xi+1},\\
R_{\xi+1}&\IncludedIn R_\zeta\IncludedIn V_{2\cdot\zeta},
\end{aligned}
$$
so the entire sequence is increasing.

If $x\in P_\xi$, then $x\notin R_\xi$ and $x\in R_{\xi+1}$. Every earlier block lies in $R_\xi$, so $x$ has
not entered before stage $2\cdot\xi$. The identities for $G_\xi,H_\xi$ show that $x\in\SetDifference{P_\xi}{A}$
first enters at $2\cdot\xi$, while $x\in A\cap P_\xi$ first enters at $2\cdot\xi+1$.
These two indices have even and odd parity, respectively, and $\alpha=2\cdot\theta$ is even.
Since the layers partition $X$, selecting the odd first-entry stages gives exactly $A$:
$$
A=D_\alpha((V_\eta)_{\eta<\alpha}).
$$
The ordinal $\alpha$ is countable because it consists of countably many two-point blocks. The case $\theta=0$
is included: then $X=F_0=F_\theta=\emptyset$, and both $A$ and $D_0$ are empty.

Thus $A\in\mathsf D_\alpha(\bSigma^0_1)(X)$ for some countable $\alpha$. Together with the proposition, this proves the
theorem.
\end{proof}

<!-- formalization: skip (cited properness theorem and structural consequence) -->
The hierarchy is not merely a representation theorem. On every uncountable Polish space its levels are genuinely
distinct [@Kechris1995, §22.E], and in the Wadge hierarchy these alternating differences give the first infinite run of
nontrivial degrees below the higher Borel pointclasses.

## The Hierarchy of Borel Wadge Degrees {#sec:wadge-borel-hierarchy}

\begin{mathmeta}
  \vars{y,z}{Name}
  \vars{n}{Nat}
  \vars{s}{Seq}
  \vars{t}{Nat}
\end{mathmeta}

<!-- formalization: skip (transition to the cited global classification) -->
Under Borel determinacy, the Wadge degrees of Borel sets in $\BaireSpace$ admit a complete description.

It is cleaner to state the well-foundedness result on
**\termdefineas{coarse Wadge degree}{coarse Wadge degrees}**, where a set is identified with its complement:
$$A^\ast := [A]_W \cup [\SetDifference{\BaireSpace}{A}]_W.$$
Put $A^\ast \le_W^\ast B^\ast$ iff $A \le_W B$ or $A \le_W \SetDifference{\BaireSpace}{B}$.

\begin{lemma*}[\termdefineas{coarse Wadge order}{Coarse Wadge order}]
This relation is independent of representatives and is a partial order on coarse Wadge degrees.
For Borel sets it is linear by Wadge's lemma.
\end{lemma*}

\begin{proof}[Proof]
The same continuous map reduces complements whenever it reduces the original sets. Composing reductions and
using this complement law shows that the relation on representatives is reflexive and transitive.
Write $A\preceq B$ for this relation. We claim that $A\preceq B$ and $B\preceq A$ hold exactly when
$A\equiv_W B$ or $A\equiv_W\SetDifference{\BaireSpace}{B}$.
If the two reductions use the same complement parity, their composition gives the required mutual reductions
directly. If their parities differ, composition gives $A\le_W\SetDifference{\BaireSpace}{A}$ and
$B\le_W\SetDifference{\BaireSpace}{B}$. Complementing these reductions makes both sets self-dual,
so the complement choices can be removed and again yield mutual reductions. The converse is immediate.
Thus mutual coarse reducibility means precisely equality of coarse degrees. Transitivity now also shows that
replacing either representative within its coarse degree preserves the relation, and proves antisymmetry on
those degrees. No determinacy assumption is needed for these facts. Wadge's lemma supplies the remaining
comparability assertion for Borel sets.
\end{proof}

\begin{theorem*}[\termdefineas{Martin--Monk theorem}{Martin–Monk}] The order $\le_W^\ast$ on Borel coarse Wadge degrees
is well-founded. Equivalently, there is no sequence of Borel sets $A_0,A_1,\ldots$ such that
$$A_{n+1}^\ast <_W^\ast A_n^\ast \qquad\text{for every }n.$$

\end{theorem*}

\begin{proof}[Proof] Suppose toward a contradiction that such a descending sequence exists. For each $n$,
strictness implies
$$A_n \not\le_W A_{n+1}
\qquad\text{and}\qquad
A_n \not\le_W \SetDifference{\BaireSpace}{A_{n+1}}.$$
By the Wadge-game lemma in §{sec:wadge-games}, Player II cannot have a winning strategy in either of the two games
below. Their payoffs are Borel, so Borel determinacy gives Player I winning strategies in both games:
$$G_W(A_n,A_{n+1})
\qquad\text{and}\qquad
G_W(A_n,\SetDifference{\BaireSpace}{A_{n+1}}).$$
Fix such strategies and call them $\sigma^0_n$ and $\sigma^1_n$ respectively. For $i\in\{0,1\}$ and
$y\in\BaireSpace$, let $g^i_n(y)$ be I's output when I follows $\sigma^i_n$ and II supplies $y$ without passes.
At time $t$, I has seen only the first $t$ moves of II. Induction through these rounds therefore gives
$$
\restrict{y}{t}=\restrict{y'}{t}
\quad\Longrightarrow\quad g^i_n(y)(t)=g^i_n(y')(t).
$$
The winning conditions give
$$
\begin{aligned}
g^0_n(y)\in A_n&\quad\Longleftrightarrow\quad y\notin A_{n+1},\\
g^1_n(y)\in A_n&\quad\Longleftrightarrow\quad y\in A_{n+1}.
\end{aligned}
$$

For each binary sequence $z\in\CantorSpace$, play all games
$$G^z_n :=
\begin{cases}
G_W(A_n,A_{n+1}), & z(n)=0,\\
G_W(A_n,\SetDifference{\BaireSpace}{A_{n+1}}), & z(n)=1
\end{cases}
\qquad (n\in\omega)
$$
simultaneously, using no passes. Write $x^z_n$ for I's output on board $n$, and let II's output there be
$x^z_{n+1}$. To define the array without circularity, recurse on time $t$. Once all moves at earlier times
are known, put
$$
\begin{aligned}
y^z_{n,t}(k)&=
\begin{cases}
x^z_{n+1}(k),&k<t,\\
0,&k\ge t,
\end{cases}\\
x^z_n(t)&=g^{z(n)}_n(y^z_{n,t})(t).
\end{aligned}
$$
The temporary zeros do not affect the last value, since it depends only on coordinates before $t$.
Consequently the completed rows satisfy
$$x^z_n=g^{z(n)}_n(x^z_{n+1}).$$
Thus every board follows the chosen winning strategy, with II's output equal to $x^z_{n+1}$.

Induction on $t$ shows that $x^z_n(t)$ depends only on $z(n),\ldots,z(n+t)$: the current choice uses $z(n)$,
and a next-board move at time $k<t$ depends only on bits from $n+1$ through $n+1+k\le n+t$.
In particular, the whole row on board $n$ depends only on the tail starting at $n$.
Agreement on a sufficiently long finite prefix of $z$ fixes any prescribed finite prefix of that row,
so every map $z\mapsto x^z_n$ is continuous.

Define truth values
$$\varepsilon_n(z)=1 \quad\Longleftrightarrow\quad x^z_n\in A_n.$$
Since I wins every board, the displayed equivalences give
$$
\varepsilon_n(z)=
\begin{cases}
1-\varepsilon_{n+1}(z), & z(n)=0,\\
\varepsilon_{n+1}(z), & z(n)=1.
\end{cases}
$$

Set
$$D:=\{z\in\CantorSpace:\varepsilon_0(z)=1\}.$$
Since $D$ is the inverse image of the Borel set $A_0$ under the continuous map $z\mapsto x^z_0$,
it is Borel and therefore has the \termuse{Baire property}.

The set $D$ is a flip set. Indeed, if $z'$ is obtained from $z$ by changing only coordinate $n$, the tail dependence
leaves $x^z_{n+1}$ unchanged. The two recurrence clauses then give $\varepsilon_n(z')=1-\varepsilon_n(z)$.
For $m<n$, the reals $z$ and $z'$ have the same
$m$-th bit, so the recurrence propagates this change down to $\varepsilon_0(z')=1-\varepsilon_0(z)$. Thus the
homeomorphism $h_n$ that flips coordinate $n$ sends $D$ to its complement.

No flip set has the Baire property. If $D$ were meager, then $h_n[D]=\SetDifference{\CantorSpace}{D}$ would also be
meager, making the entire nonempty Baire space $\CantorSpace$ meager. Hence $D$ is non-meager.
By the Baire property, there are an open set $U$ and a meager set $M$ with $\SymmetricDifference{D}{U}\IncludedIn M$.
The set $U$ is nonempty, for otherwise $D\IncludedIn M$. Choose a nonempty basic cylinder $\cyl{s}\IncludedIn U$
and $n\ge \Length{s}$. Then $h_n$ preserves $\cyl{s}$, so
$$
\SetDifference{\cyl{s}}{D}\IncludedIn M,
\qquad
\cyl{s}\cap D\IncludedIn h_n[M].
$$
For the second inclusion, apply the first to $h_n(x)$ and use that $h_n$ is its own inverse and exchanges the two
sides of $D$. Thus $\cyl{s}\IncludedIn M\cup h_n[M]$, making this nonempty open cylinder meager,
contradicting the Baire category theorem. This proves that no strict descending sequence of Borel coarse Wadge degrees
exists.
\end{proof}

The preceding partial order and the Martin--Monk theorem make the Borel coarse degrees a well-order.
We use the zero-based convention: the Wadge rank $|A|_W$ is the order type of the strict initial segment
below $A^\ast$. Thus $|A|_W=0$ for the empty/full pair, complements have the same rank, and
$A^\ast<_W^\ast B^\ast$ exactly when $|A|_W<|B|_W$.

<!-- formalization: skip-begin (survey of the global Borel degree structure and its ordinal length) -->
The finer description of which levels are self-dual is an external structure theorem, not a consequence of
semi-linearity alone. The Steel--Van Wesep analysis gives alternating non-self-dual pairs and self-dual degrees
at successive levels. At nonzero limit positions, countable cofinality gives a self-dual degree and uncountable
cofinality gives a non-self-dual pair [@VanWesep1978, Theorem 3.1]. These positions refer to the zero-based
ordering just defined; shifting the rank convention would shift the descriptions of limit positions.
The first levels are:

| rank | degree | example |
|------|--------|---------|
| $0$ | non-self-dual pair | empty set, full space |
| $1$ | self-dual | a nontrivial proper clopen set |
| $2$ | non-self-dual pair | an open nonclosed set and its closed nonopen complement |

The open/closed level is identified in §{sec:first-wadge-degrees}. Further levels require the difference hierarchy
and self-dual joins; their ranks should not be identified with difference indices without a separate calculation.
The Hausdorff \termuseas{Hausdorff difference hierarchy}{difference hierarchy} already stratifies
$\bDelta^0_2$ into $\omegaOneOrd$-many distinct levels. The exact ordinal length of the full Borel Wadge
hierarchy is a further external classification, expressed using Veblen functions with base $\omegaOneOrd$;
we do not derive that computation here [@Kechris1995, §21].
<!-- formalization: skip-end -->

## Why Wadge {#sec:wadge-why}

<!-- formalization: skip (applications introduction) -->
The Wadge hierarchy organizes pointclasses by descriptive complexity:

\begin{mathmeta}
  \define{ADTheta}
\end{mathmeta}

*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    固定targetのWadge下方錐の連続逆像閉性は、同値類WadgeClassとは区別し、実際の連続写像の合成で狭く接続した。
    未リンクの残りはKechris §22.Eの差階層propernessによる細かさ、PD/ADでの全体構造・Thetaという外部分類、
    およびBorel reducibilityとの比較という用途の概説。
    ここでそれらの別証明やprojective/AD-levelのrank構成を提示してはいない。)
    --> **Sharper than Borel rank.** The class $\bDelta^0_2$ already contains sets at arbitrarily high
    countable levels of the Hausdorff difference hierarchy. Their Wadge ranks are unbounded within this
    class, although all these sets are both $\Fsigma$ and $\Gdelta$.<!--
    formalization: skip-end
    -->
*   **Wadge classes are closed pointclasses.** The collection of $A$ with $A \le_W B$ for fixed $B$ is closed under
    continuous preimages, making each Wadge class a Wadge-closed pointclass. This is the right setting for
    game-theoretic determinacy: $\Gamma$-determinacy is a property of the Wadge class $\Gamma$, not of any particular
    generating set.
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    固定targetのWadge下方錐の連続逆像閉性は、同値類WadgeClassとは区別し、実際の連続写像の合成で狭く接続した。
    未リンクの残りはKechris §22.Eの差階層propernessによる細かさ、PD/ADでの全体構造・Thetaという外部分類、
    およびBorel reducibilityとの比較という用途の概説。
    ここでそれらの別証明やprojective/AD-levelのrank構成を提示してはいない。)
    -->
    **Connection to determinacy.** The pattern of self-dual / non-self-dual alternation reflects the alternation between
    $\bSigma$ and $\bPi$ classes throughout the Borel and projective hierarchies. Well-foundedness of the Borel Wadge
    hierarchy is a theorem of ZFC. Under PD, the well-founded hierarchy extends through every projective level. Under
    AD, it extends to all subsets of $\BaireSpace$ and has overall length $\ADTheta$, the supremum of ordinals onto
    which $\R$ surjects.<!--
    formalization: skip-end
    -->
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    固定targetのWadge下方錐の連続逆像閉性は、同値類WadgeClassとは区別し、実際の連続写像の合成で狭く接続した。
    未リンクの残りはKechris §22.Eの差階層propernessによる細かさ、PD/ADでの全体構造・Thetaという外部分類、
    およびBorel reducibilityとの比較という用途の概説。
    ここでそれらの別証明やprojective/AD-levelのrank構成を提示してはいない。)
    --> **Connection to Borel reducibility.** The Wadge ordering on subsets is the topological cousin of the
    \termforward{Borel reducibility} ordering on equivalence relations developed in §{sec:borel-reducibility}. Where the
    equivalence-relation hierarchy is famously rich and intricate, the Wadge hierarchy on sets is, under determinacy,
    well-founded and almost-linear — the cleanest test bed for general theorems about pointclasses.<!--
    formalization: skip-end
    -->

<!-- formalization: skip-begin (references for the broader Wadge hierarchy) -->
A textbook treatment with full proofs is in [@Kechris1995, §21]; the broader survey including the projective and AD case
is in [@Moschovakis2009, Ch. 7].
<!-- formalization: skip-end -->
