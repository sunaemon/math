# Determinacy {#sec:determinacy}

\begin{mathmeta}
  \vars{b,x,x_*,y_*}{Name}
  \vars{s,t,s_*,t_*}{Seq}
  \vars{n}{Nat}
  \vars{r,\varepsilon,\delta}{Real}
\end{mathmeta}

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Use cylinders and trees from §{sec:closed-sets-trees}, analytic sets from §{sec:analytic-sets}, and
transfinite recursion from §{sec:ordinals-induction}. The category arguments use §{sec:baire-category}; the
measurability argument in §{sec:covering-game} additionally uses finite Borel measures and outer measure. Begin
with strategies and open/closed determinacy, then read the Borel determinacy statement before its
construction. The large-cardinal results at the end are cited background. Readers continuing to Wadge games
should understand how a winning strategy determines a continuous map; readers continuing to regularity should
follow the separate category, measure, and perfect-set games.

<!-- formalization: skip-end -->

<!-- formalization: skip (heuristic comparison between games and quantifier alternation) -->
A useful heuristic is that games describe successive choices made with knowledge of earlier moves.
For example, the $\varepsilon$--$\delta$ condition for continuity of $f:\mathbb R\to\mathbb R$ at
$r\in\mathbb R$ can be read as a one-round game. Player I chooses $\varepsilon>0$, and Player II chooses
$\delta>0$. II wins this round if every argument within $\delta$ of $r$ has value within $\varepsilon$ of
$f(r)$. II has a winning strategy exactly when $f$ is continuous at $r$. Infinite perfect-information games
extend this pattern to countably many moves; this analogy does not assign the payoff a level in a logical hierarchy.

The two players are called Player I and Player II. A
\termdefineas{perfect-information game}{two-player infinite perfect-information game} is a tuple $\Tuple{M,L,A}$, where
$M$ is
a set of moves, $L\IncludedIn\funcspace{\omega}{M}$ is the
set of allowed infinite plays, and $A\IncludedIn L$ is the payoff set for Player I. A finite sequence $s\in\finseq{M}$
is
a \termdefine{partial play} if it is an initial segment of some element of $L$. A move $a\in M$ is
\termdefine{legal after} $s$ if $s\concat(a)$ is a partial play. Player I chooses a legal move $a_0$ after $\emptyset$;
Player II then
chooses a legal move $a_1$ after seeing $(a_0)$; Player I chooses a legal move $a_2$ after seeing $\Pair{a_0}{a_1}$; and
so
on. Thus the players alternate, starting with I:
$$\underbrace{a_0}_{\mathrm{I}},\ \underbrace{a_1}_{\mathrm{II}},\ \underbrace{a_2}_{\mathrm{I}},\quad
\underbrace{a_3}_{\mathrm{II}},\ \ldots \qquad (a_n \in M).$$
The resulting infinite sequence is called a \termdefineas{game play}{play}, and it must lie in $L$. A play is a win for
Player I if it lies in $A$, and a win for Player II if it lies in $\SetDifference{L}{A}$.

A \termdefineas{game strategy}{strategy} for Player I is a function assigning I's next legal move after partial plays of
even length. A
strategy for Player II is a function assigning II's next legal move after partial plays of odd length. Player I
\termdefineas{follows a strategy}{follows} $\sigma$ in a play if $a_{2n}=\sigma(a_0,\ldots,a_{2n-1})$ for every $n$, and
Player II follows $\tau$ if $a_{2n+1}=\tau(a_0,\ldots,a_{2n})$ for every $n$. Equivalently, the play itself is said to
\termuseas{follows a strategy}{follow} the relevant strategy. A strategy is \termdefineas{winning strategy}{winning} if
every allowed play in which that player follows it is a win for that player. The game is
\termdefineas{determined game}{determined} if one of the two players has a winning strategy.

For infinite play, we require the legal finite positions to form a nonempty tree $T\IncludedIn\finseq{M}$
with no terminal nodes, and we take $L=\TreeBody{T}$. The next lemma shows that this agrees with the
branch-extension definition of a pruned tree in §{sec:cantor-baire-space}.

\begin{lemma*}[\termdefineas{branch extension for trees without terminal nodes}{Branch extension}]
Let $T\IncludedIn\finseq{M}$ be a nonempty tree. Every node has a legal one-step extension if and only if
every node extends to an infinite branch through $T$.
\end{lemma*}

\begin{proof}[Proof]
Suppose every node has a legal one-step extension. Choose a move $\chi(t)$ with
$t\concat(\chi(t))\in T$ for each $t\in T$. Starting at any $s\in T$, define
$$
t_0:=s,\qquad t_{n+1}:=t_n\concat(\chi(t_n)).
$$
Then $t_n\in T$, $\Length{t_n}=\Length{s}+n$, and each word extends its predecessor. These compatible words determine
an infinite sequence $z$ extending $s$. Every finite prefix of $z$ is a prefix of some $t_n$, hence belongs to
$T$ because $T$ is a tree. Thus $z\in\TreeBody{T}$. Conversely, the next coordinate of a branch extending a node
gives a legal one-step extension of that node.
\end{proof}

In particular, the nodes of $T$ are exactly the finite prefixes of allowed plays. The requirement
$L=\TreeBody{T}$ ensures that an infinite sequence of legal moves is itself allowed.

\begin{lemma*}[\termdefineas{play generated by two strategies}{The play of two strategies}]
Every pair of strategies, one for each player, has a unique allowed play following both.
Every strategy has at least one allowed play following it, and the two players cannot both have winning strategies.
\end{lemma*}

\begin{proof}[Proof]
Given strategies $\sigma$ for I and $\tau$ for II, define finite positions recursively by
$$
s_0:=\emptyset,\qquad
s_{n+1}:=
\begin{cases}
s_n\concat(\sigma(s_n)),&n\text{ even},\\
s_n\concat(\tau(s_n)),&n\text{ odd}.
\end{cases}
$$
Each position is legal and has length $n$. The compatible positions therefore determine a branch through $T$,
and this play follows both strategies. Conversely, induction on the length shows that any play following
both has $s_n$ as its prefix of length $n$. This proves uniqueness.

Pairing a fixed strategy with any legal strategy for the other player gives an allowed play following it.
Such a strategy for the other player exists by choosing a legal move at each of that player's positions.
If both strategies were winning, their common play would belong both to $A$ and to $\SetDifference{L}{A}$,
a contradiction.
\end{proof}

Examples clarify the definition. In the ordinary case $M=\omega$ and $L=\BaireSpace$. If
$$A=\{x\in\BaireSpace:x(0)=0\},$$
then Player I wins by playing $a_0=0$. If instead
$$A=\{x\in\BaireSpace:x(1)=0\},$$
then Player II wins by answering $a_1=1$, forcing the final play outside $A$.

The basic descriptive-set-theoretic case takes $M=\omega$ and allows every play in $\BaireSpace$.

For $A\IncludedIn\BaireSpace$, the corresponding game is denoted $G_A$. A pointclass here is a collection $\Gamma
\IncludedIn
\PowerSet{\BaireSpace}$, and $\Gamma$ is \termuseas{determined game}{determined} if every $A \in \Gamma$ is determined.

\begin{mathmeta}
  \forward{bethCard}
\end{mathmeta}

The theorem in §{sec:martin-borel-det} says that every Borel payoff is determined. The following construction
therefore produces a non-Borel payoff; its use of Choice is essential to the diagonalization.

\begin{theorem*}[\termdefineas{undetermined game under Choice}{An undetermined game under Choice}]
Assuming Choice, there is a set $A\IncludedIn\BaireSpace$ for which neither player has a winning strategy.
\end{theorem*}

\begin{proof}[Proof]
For each player, the set of finite histories at which that player moves is countably infinite.
A strategy is an arbitrary function from that set to $\omega$, so each strategy space has cardinality
$\alephNull^{\alephNull}=2^{\alephNull}=\bethCard{1}$.

A fixed strategy also has exactly $\bethCard{1}$ compatible plays. For an I-strategy $\sigma$, let the opponent
play any prescribed sequence $b\in\BaireSpace$, using $b(n)$ as the move at round $n$.
The play of these two strategies exists and is unique by the earlier lemma, and its odd coordinates are
exactly $b$. Distinct choices of $b$ therefore give distinct compatible plays. The upper bound holds because
all plays lie in $\BaireSpace$. For a II-strategy, prescribe the even coordinates in the same way.

Let $\kappa$ be the initial ordinal of cardinality $\bethCard{1}$. Choice gives enumerations
$$\Sequence{\sigma_\alpha}{\alpha<\kappa},\qquad\Sequence{\tau_\alpha}{\alpha<\kappa}$$
of the I-strategies and II-strategies. At each stage we choose a pair of plays $\Pair{x_\alpha}{y_\alpha}$.
The first will defeat $\sigma_\alpha$ by being outside the final payoff; the second will defeat $\tau_\alpha$
by being inside it.

Use the transfinite-recursion principle of Appendix §{sec:ordinals-induction}. Given the pairs chosen before
stage $\alpha$, put
$$P_\alpha:=\{y_\beta:\beta<\alpha\},\qquad N_\alpha:=\{x_\beta:\beta<\alpha\}.$$
Choose $x_\alpha$ following $\sigma_\alpha$ and then $y_\alpha$ following $\tau_\alpha$, subject to
$$
\begin{aligned}
x_\alpha&\notin P_\alpha\cup N_\alpha,\\
y_\alpha&\notin P_\alpha\cup N_\alpha\cup\{x_\alpha\}.
\end{aligned}
$$
At stage zero both earlier sets are empty. These definitions collect the earlier choices at successor
and limit stages alike.

To justify every choice, both earlier sets are images of the ordinal $\alpha$, so
$$\Card{P_\alpha},\Card{N_\alpha}\le\Card{\alpha}.$$
Because $\kappa$ is the initial ordinal of cardinality continuum, $\Card{\alpha}<2^{\alephNull}$.
Cardinal arithmetic for the infinite cardinal $2^{\alephNull}$ gives
$$
\begin{aligned}
\Card{P_\alpha\cup N_\alpha}
&\le \Card{P_\alpha\cup N_\alpha\cup\{x_\alpha\}}\\
&\le 2\Card{\alpha}+1<2^{\alephNull}.
\end{aligned}
$$
A compatible-play set has cardinality $2^{\alephNull}$, so it cannot be contained in either forbidden set.
This proves existence of both choices from any earlier history. Fixing a choice from each nonempty set of
admissible pairs makes the recursion clause a function, as required by transfinite recursion.
Only a finite union of small sets is used at each stage; no regularity assumption on the continuum is needed.

No $x_\alpha$ equals any $y_\beta$. If $\alpha<\beta$, then $x_\alpha\in N_\beta$ and the choice of $y_\beta$
excludes equality. If $\beta<\alpha$, then $y_\beta\in P_\alpha$ and the choice of $x_\alpha$ excludes equality.
At the same stage, $y_\alpha\ne x_\alpha$ by construction. Thus the two ranges of chosen plays are disjoint.

Define the final payoff by
$$A:=\{y_\alpha:\alpha<\kappa\}.$$
For every I-strategy $\sigma_\alpha$, the play $x_\alpha$ follows it and lies outside $A$.
For every II-strategy $\tau_\alpha$, the play $y_\alpha$ follows it and belongs to $A$.
Neither player can therefore have a winning strategy for this payoff.
\end{proof}

<!-- formalization: skip (conceptual synthesis and forward references) -->
The concept of \termdefine{determinacy} is the connecting tissue between descriptive complexity and regularity
properties: the more
classes one assumes determined, the more sets enjoy the regularity properties of §{sec:perfect-sets-standard-borel},
§{sec:fsigma-gdelta-sets}, and §{sec:regularity-independence}. The systematic treatment is [@Moschovakis2009, Chs. 6–7];
the Borel-\termuse{determinacy} proof in detail is in [@Kechris1995, §20].

<!-- formalization: skip-begin (chapter roadmap and formalization scope) -->
The chapter moves in layers. First we isolate the basic payoff games and the topological games that encode completeness.
Then Gale--Stewart gives the open/closed case, Martin's theorem gives the full Borel case, and large-cardinal hypotheses
explain what happens at the analytic and projective levels. The final sections translate determinacy into the three
regularity properties and then state AD, which pushes the same pattern to all sets of reals in a choice-free setting.

Proof scope: this chapter defines the elementary games and proves the Choice-based construction of an
undetermined game, Gale--Stewart determinacy, and the category and perfect-set game lemmas.
The converse strong-Choquet characterization and the
measure-theoretic game lemma are quoted from the literature. Martin's Borel determinacy is imported from Manthe's
checked Lean formalization. The chapter sketches its universally unravelable sets and proves the strategy
transport connecting that external theorem to our Baire games. Local covering and inverse-limit lemmas explain
the construction; the imported proof supplies the closed-set construction and the Borel induction.
Analytic determinacy, AD, and Martin--Steel are likewise
external results: the chapter states their exact role without reproducing inner-model or large-cardinal
machinery.
<!-- formalization: skip-end -->

## Topological Infinite Games {#sec:topological-infinite-games}

\begin{mathmeta}
  \vars{p}{Nat}
\end{mathmeta}

The \termdefine{strong Choquet game} on a topological space $X$ uses the same move set for both players:
$$M_X:=\{\Pair{x}{U}:x\in X,\ U\IncludedIn X\text{ is open},\ x\in U\}.$$
Let $L_X\IncludedIn\funcspace{\omega}{M_X}$ be the set of alternating sequences of pairs
$$
\Pair{x_0}{U_0},\ \Pair{x_0}{V_0},\ \Pair{x_1}{U_1},\ \Pair{x_1}{V_1},\ldots
$$
such that
$$x_n\in V_n\IncludedIn U_n
\qquad\text{and}\qquad
U_{n+1}\IncludedIn V_n$$
for every $n$. Let $A_X\IncludedIn L_X$ consist of those plays for which the open sets chosen by Player I have empty
intersection:
$$\bigcap_{n\in\omega} U_n=\emptyset.$$
The strong Choquet game is $\Tuple{M_X,L_X,A_X}$. Thus Player I wins exactly on $A_X$, and Player II wins otherwise,
equivalently when the nested play has a surviving point.

A topological space $X$ is \termdefine{strong Choquet} if Player II has a winning strategy in the strong Choquet game on
$X$.

For the empty space there is no first move. We declare Player II to win without a move, so the empty space
is strong Choquet. In the strategy formulation below, this holds because there are no plays to test.

A strategy for Player II can be specified by its response to the finite history of Player I's moves
and the current move. Its previous responses can be recovered from that history. The response to
$x\in U$ must be an open set $V$ with $x\in V\IncludedIn U$. A play following the strategy is legal when
each next open set chosen by Player I is contained in the preceding response. The strategy is winning
if every such infinite play has a point in all of Player I's open sets.

\begin{lemma*}[\termdefineas{transport of strong Choquet strategies}{Transport of strong Choquet strategies}]
If $f:X\to Y$ is an open embedding and $Y$ is strong Choquet, then $X$ is strong Choquet.
In particular, open subspaces inherit this property, and homeomorphisms preserve it.
\end{lemma*}

\begin{proof}[Proof]
Fix a winning strategy on $Y$. Send each move $\Pair{x}{U}$ in $X$ to $\Pair{f(x)}{f[U]}$ in $Y$;
the image is open because $f$ is an open embedding. Apply the fixed strategy to this image history.
If it returns $V$, respond in $X$ with $f^{-1}[V]$. Continuity makes this response open, and
injectivity together with $V\IncludedIn f[U]$ gives $f^{-1}[V]\IncludedIn U$. The response contains $x$.

A legal play in $X$ gives a legal image play in $Y$. Let $y$ belong to every open set in the image
play. The first of these sets is contained in $f[X]$, so $y=f(x)$ for a unique $x\in X$.
Injectivity implies that $x$ belongs to every original open set. This is a winning strategy on $X$.
Apply the result to the inclusion of an open subspace, or to a homeomorphism, for the two consequences.
\end{proof}

\begin{proposition*}[\termdefineas{metric strong Choquet strategy}{Metric strategy}]
Every completely metrizable space is strong Choquet. In particular, every Polish space is strong Choquet.
\end{proposition*}

\begin{proof}[Proof]
Fix a complete compatible metric $d$. When Player I plays $x_n\in U_n$, choose $\varepsilon_n>0$ with
$\Ball{x_n}{\varepsilon_n}\IncludedIn U_n$, and set
$$
r_n:=\min\{\varepsilon_n/2,2^{-n}/2\},\qquad V_n:=\Ball{x_n}{r_n}.
$$
Since $0<r_n<\varepsilon_n$, these open responses satisfy
$$
x_n\in V_n,\qquad \Closure{V_n}\IncludedIn U_n,\qquad
\Diameter{\Closure{V_n}}\le 2r_n\le 2^{-n}.
$$
The rule uses only the round number and the current point and open set, so it defines a strategy on every
finite history. All closures and diameters here are taken in $X$ with the chosen metric.

Consider a legal play following this strategy, and put $K_n:=\Closure{V_n}$. Legality gives
$$
K_{n+1}\IncludedIn U_{n+1}\IncludedIn V_n\IncludedIn K_n.
$$
Each $K_n$ is closed and bounded, and $x_n\in K_n$. For $m,k\ge n$, both $x_m$ and $x_k$ belong to $K_n$, so
$$
d(x_m,x_k)\le\Diameter{K_n}\le 2^{-n}.
$$
Thus the sequence of chosen points is Cauchy. Completeness gives a limit $x$. For every $n$, the closed set
$K_n$ contains the tail of this sequence, so $x\in K_n\IncludedIn U_n$. Hence every open set chosen by I
contains $x$, and the strategy is winning.
\end{proof}

\begin{claim*} A separable metrizable space is Polish iff it is strong Choquet.

\end{claim*}

\begin{proof}[Proof]
The forward implication follows from the \termuse{metric strong Choquet strategy} above.
For the converse, fix a compatible metric on the separable metrizable space $X$, embed it in its completion
$\widehat X$, and transport a winning strategy $\sigma$ to the image. We construct ambient open covers of $X$
tagged by finite histories following $\sigma$.

At level zero there is one node with empty history and region $\widehat X$, whose available set is $X$.
At later nodes the available set is the last strategy response. Suppose the regions at level $n$ cover $X$,
and the trace on $X$ of each region lies in its available set. For every node $i$ and
point $x$ in its trace, choose an ambient ball about $x$ contained in that region, with positive radius at most
$2^{-n}/2$. Its trace is a legal next move by Player I. The strategy responds with an open neighborhood of $x$
in $X$. Lift this response to an ambient open set and intersect it with the chosen ball, obtaining $W_{i,x}$.
These sets cover $X$. In their open union, take a locally finite open refinement indexed by the same pairs
$\Pair{i}{x}$, each member contained in $W_{i,x}$. Apply §{sec:appendix-metric-paracompactness} in this open metric
subspace. The refined members
are the next-level regions, tagged by the extended histories and their parent $i$. Let $G_n$ be the union of
the regions at level $n$. Each $G_n$ is open and contains $X$, each child region lies in its parent, and only
finitely many regions at a fixed level contain a given point of $G_n$.

Fix $y\in\bigcap_nG_n$. At each level the nodes whose regions contain $y$ form a finite nonempty set, and the
parent maps preserve these sets. \termuse{König's lemma} gives a coherent sequence of nodes through all levels.
Their stored histories determine a legal play following $\sigma$. Since the strategy wins, some $z\in X$
belongs to all of Player I's moves. At round $n$, both $y$ and $z$ lie in the ambient ball used for that move,
so $d(y,z)\le 2^{-n}$. Hence $y=z\in X$.

We have proved
$$X=\bigcap_{n\in\omega}G_n.$$
The completion $\widehat X$ is Polish because the original metric is separable. Thus $X$ is $\Gdelta$ in a
Polish space, and \termuse{Alexandrov's theorem} in §{sec:alexandrov-theorem} shows that $X$ is Polish.
\end{proof}

<!-- formalization: skip-begin (external input or explanatory background) -->
For Choquet's metrization theorem in this form, see [@Kechris1995, Theorem 8.18].
<!-- formalization: skip-end -->


<!-- formalization: skip (interpretation and forward reference to Gandy--Harrington games) -->
This is the topological-game version of the same completeness argument used earlier for Baire category.
In the Gandy--Harrington topology of §{sec:edst-gh-topology}, nonempty analytic sets play the role of small
neighborhoods. There, compatible finite prefixes of the point and its analytic witnesses supply the common point.

## Open and Closed Determinacy {#sec:gale-stewart}

\begin{mathmeta}
  \vars{s}{Seq}
\end{mathmeta}

A \termdefine{tree for play} is a nonempty tree $T\IncludedIn\finseq{M}$ with no terminal nodes,
where $M$ is a set of moves with the discrete topology. We allow arbitrary sets of moves in the auxiliary games
used in Martin's proof, even when the original game has moves in $\omega$. The game
$G(A,T)$, for $A\IncludedIn\TreeBody{T}$, uses the nodes of $T$ as its legal finite positions; Player I wins exactly
when
the resulting branch lies in $A$. The ordinary game on $\BaireSpace$ is the case $T=\finseq{\omega}$.

<!-- formalization: skip (historical attribution) -->
The open-and-closed game theorem is due to Gale and Stewart [@GaleStewart1953].

\begin{theorem*}[\termdefineas{Gale--Stewart theorem}{Gale–Stewart}] Let $T$ be a tree for play.
Every open and every closed subset of $\TreeBody{T}$ is determined in $G(A,T)$.

\end{theorem*}

\begin{proof}[Proof]
First take an open payoff $U\IncludedIn\TreeBody{T}$. Write
$$
U=\bigcup_{s\in S}\bigl(\cyl{s}\cap\TreeBody{T}\bigr)
$$
for some $S\IncludedIn T$. If a legal partial play has a prefix in $S$, then Player I has already won. We identify
Player I's winning partial plays by backtracking from these finite certificates.

Define, by transfinite recursion,
$$
\begin{aligned}
W_0&:=S,\\
W_{\alpha+1}&:=W_\alpha
  \cup\{s\in T: \Length{s}\text{ is even and }s\concat(a)\in W_\alpha\text{ for some legal }a\}\\
&\hspace{2.8em}\cup\{s\in T: \Length{s}\text{ is odd and }s\concat(a)\in W_\alpha\text{ for every legal }a\},\\
W_\lambda&:=\bigcup_{\alpha<\lambda}W_\alpha\quad\text{for limit }\lambda.
\end{aligned}
$$

This increasing sequence stabilizes. Indeed, its values are subsets of $T$. Choose an ordinal whose
cardinality exceeds that of $\PowerSet{T}$; two stages below it must have the same value. If
$\alpha<\beta$ and $W_\alpha=W_\beta$, then
$$
W_\alpha\IncludedIn W_{\alpha+1}\IncludedIn W_\beta=W_\alpha.
$$
Thus $W_{\alpha+1}=W_\alpha$. The successor rule and the union rule at limit stages imply that all later
stages have this same value. Write $W$ for the stable value; in particular, $S\IncludedIn W$.

For $s\in W$, let $r(s)$ be the least stage at which $s$ enters. If $s\notin S$, this stage is nonzero.
It cannot be a limit stage, since membership in a union already holds at an earlier stage. Hence
$r(s)=\beta+1$ for some $\beta$, and $s\notin W_\beta$. The successor rule now gives two possibilities:
at an I-turn there is a legal child in $W_\beta$, while at a II-turn every legal child lies in $W_\beta$.
In either case, the indicated children belong to $W$ and have entry stage strictly below $r(s)$.

At each I-position in $\SetDifference{W}{S}$, choose a legal child of smaller entry stage. At all other
I-positions, choose any legal move. A play starting in $W$ and following this strategy must reach $S$:
otherwise its entry stages would decrease strictly at every move. The set of these stages has a least element,
and the next move would have a still smaller stage, a contradiction. Thus every position of $W$ is winning
for I; in particular, $\emptyset\in W$ gives I a winning strategy for $U$.

If $\emptyset\notin W$, the fixed-point property gives the opposite strategy. At an II-position outside
$W$, some legal child must remain outside $W$, since otherwise the successor rule would put the position
in $W$. At an I-position outside $W$, every legal child remains outside $W$, since one child in $W$
would suffice to put the position in $W$. Player II chooses a child outside $W$ whenever possible and uses
an arbitrary legal move at other positions. Induction on the length of the play shows that all positions
stay outside $W$, hence outside $S$. No finite prefix then certifies membership in $U$, so II wins.

For a closed payoff $A\IncludedIn\TreeBody{T}$, apply the same construction with Player II as the player
trying to reach the open set $\SetDifference{\TreeBody{T}}{A}$. In the recursion, the existential predecessor
clause now applies at odd-length positions and the universal clause at even-length positions. If the root enters
the resulting winning region, II forces the open complement; otherwise I keeps the play outside that region and
wins in $A$. The turn order is unchanged throughout.
\end{proof}

## Borel Determinacy {#sec:martin-borel-det}

\begin{mathmeta}
  \vars{i,k,l,p}{Nat}
  \vars{n}{Nat}
\end{mathmeta}


<!-- formalization: skip-begin (external input or explanatory background) -->
Martin proved Borel determinacy in ZFC [@Martin1975].
<!-- formalization: skip-end -->

\begin{theorem*}[\termdefineas{Borel determinacy}{Martin}] \emph{Every Borel subset of $\BaireSpace$ is
determined.}
\end{theorem*}

<!-- formalization: skip-begin (external input or explanatory background) -->
This theorem is provable in ZFC. Friedman [@Friedman1971] showed that
\termuse{Borel determinacy} is not provable in Zermelo set theory with Choice, assuming that theory is consistent.
Martin's discussion in [@Martin1975] explains how stronger fragments of determinacy require higher iterates of
power sets. This is a lower bound on the set-theoretic resources needed for the theorem; it is not an equivalence
with the full Replacement scheme.

\begin{proof}[Proof from cited results]
We follow Manthe's formalization [@Manthe2025] of Martin's purely inductive proof
[@Martin1985]. It strengthens unravelability to universal unravelability and proceeds along the generation of
Borel sets, without an explicit induction on Borel ranks. A payoff is \termforwardas{unravels a payoff set}{unraveled}
when a covering pulls it back to a clopen payoff. Gale--Stewart then supplies a winning strategy upstairs.
The covering transfers that strategy to the original game. The external Lean development checks this entire
argument; the local connection to our strategy definitions is proved after this proof.
<!-- formalization: skip-end -->

\paragraph*{Games on Trees and Coverings}\label{sec:martin-games-coverings}

The \termuse{tree for play} convention above lets the unraveling architecture change the legal positions while retaining
the same game semantics.
The auxiliary move sets need not be countable: a single move may include an entire strategy or subtree.
Branch spaces carry the product topology of these discrete move sets.

For $k \in \omega$, write
$$T^{(k)} := \{s \in T : \Length{s}=k\}.$$
A strategy for a game on $T$ is a rule defined on legal positions of the appropriate parity. Let $S(T)$ be the class of
strategies for either player.

A \termdefineas{game-tree covering}{covering} of $T$ is a triple $\Tuple{\tilde T,\pi,\varphi}$ such that:

\begin{enumerate}
\item $\tilde T$ is a tree for play.
\item $\pi : [\tilde T] \to [T]$ is continuous.
\item $\varphi : S(\tilde T)\to S(T)$ sends strategies for I to strategies for I, and strategies for II to strategies
for II.
\item If $x\in [T]$ is a play following $\varphi(\sigma)$, then there is a play $\tilde x\in[\tilde T]$ following
$\sigma$ with $\pi(\tilde x)=x$.
\end{enumerate}

The covering \termdefineas{unravels a payoff set}{unravels} $A\IncludedIn[T]$ if $\pi^{-1}(A)$ is clopen in $[\tilde
T]$.

\begin{lemma*} If a covering of $T$ unravels $A\IncludedIn[T]$, then $G(A,T)$ is determined.

\end{lemma*}

\begin{proof}[Proof] Since $\pi^{-1}(A)$ is clopen, Gale--Stewart determines $G(\pi^{-1}(A),\tilde T)$. Let $\sigma$ be
a winning strategy there, say for Player I. We show that $\varphi(\sigma)$ wins $G(A,T)$. If $x$ follows
$\varphi(\sigma)$, condition (4) gives $\tilde x$ following $\sigma$ with $\pi(\tilde x)=x$. Since $\sigma$ wins,
$\tilde x\in\pi^{-1}(A)$, hence $x\in A$. The proof for a winning strategy for II is the same, replacing membership in
$A$ by nonmembership.
\end{proof}

Coverings compose. If $\Tuple{T_1,\pi_1,\varphi_1}$ covers $T_0$ and $\Tuple{T_2,\pi_2,\varphi_2}$ covers $T_1$, then
$$\Tuple{T_2,\pi_1\circ\pi_2,\varphi_1\circ\varphi_2}$$
covers $T_0$. Condition (4) is verified by lifting a play first through $\varphi_1$ and then through $\varphi_2$. Hence
a later unraveling may be composed with all earlier ones.

\paragraph*{Controlled Coverings}\label{sec:martin-controlled-coverings}

The induction needs coverings that do not disturb a fixed finite opening segment. A covering
$\Tuple{\tilde T,\pi,\varphi}$ of
$T$ is a \termdefineas{k-covering of a game tree}{$k$-covering} if:

1.  $\restrict{\pi(\tilde x)}{n}$ depends only on $\restrict{\tilde x}{n}$ for every $n$.

2.  $\varphi(\sigma)$ restricted to positions of length $<n$ depends only on $\sigma$ restricted to positions of length
    $<n$.

3.  For every $j\le k$, the prefix map induced by $\pi$ is a bijection $\tilde T^{(j)}\to T^{(j)}$. Under these
    identifications, $\varphi(\sigma)$ agrees with $\sigma$ at positions of length $<k$.

Thus a $k$-covering is invisible through level $k$: up to that level the original and auxiliary games have the same
positions. Composition preserves the relevant control: if $\Tuple{T_1,\pi_1,\varphi_1}$ is a $k$-covering of $T_0$ and
$\Tuple{T_2,\pi_2,\varphi_2}$ is a $k$-covering of $T_1$, then the composite is a $k$-covering of $T_0$.

We also use two elementary facts. First, if a $k$-covering unravels $A$, it also unravels $\SetDifference{[T]}{A}$,
because
clopen sets are closed under complement. Second, if $A$ belongs to a Borel pointclass $\Gamma$ and $\pi$ is continuous,
then $\pi^{-1}(A)$ belongs to the same pointclass. This is just the closure of Borel classes under continuous preimage.

\paragraph*{Unraveling One Closed Set}\label{sec:martin-closed-unraveling}

<!-- formalization: structural (proof roadmap only) -->
The central game construction in Martin's proof is the following.

<!-- formalization: skip-begin (external input or explanatory background) -->
\begin{lemma*} Let $C\IncludedIn[T]$ be closed and let $k\in\omega$. There is a $k$-covering of $T$ that unravels $C$.

\end{lemma*}

The closed-set lemma is the substantial auxiliary-game construction imported from [@Martin1985].
A \termdefine{I-quasi-strategy} below a position $p$ is a subtree containing $p$, closed under every legal
move by II, and having at least one legal extension at each of I's turns. A \termdefine{II-quasi-strategy}
is defined dually. Such subtrees are among the certificates used in auxiliary moves.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (finite control supplied by the imported closed-set construction) -->
For finite-level control it suffices to treat even $k$: when $k$ is odd, construct a $(k+1)$-covering,
which is also a $k$-covering. The construction preserves the first $k$ moves and then augments moves with
certificates. Its conclusion includes both the clopen preimage and strategy lifting for each player.
These properties are supplied by the cited construction; determinacy of the closed game alone does not establish
them. We use this lemma as an external input to the induction below.
<!-- formalization: skip-end -->

\paragraph*{Inverse Limits of Coverings}\label{sec:martin-inverse-limits}

<!-- formalization: structural (proof roadmap only) -->
The induction will produce one covering after another, one for each member of a countable union. We need a way to take
their limit without losing finite-level control.

\begin{lemma*} Suppose $\Tuple{T_{i+1},\pi_{i+1},\varphi_{i+1}}$ is a $(k+i)$-covering of $T_i$ for every $i\in\omega$.
Then
there is a tree $T_\infty$ and, for each $i$, maps $\rho_i:[T_\infty]\to[T_i]$ and $\psi_i:S(T_\infty)\to S(T_i)$ such
that $\Tuple{T_\infty,\rho_i,\psi_i}$ is a $(k+i)$-covering of $T_i$, and the system commutes with the given coverings.

\end{lemma*}

\begin{proof}[Proof] Because the covering from $T_{i+1}$ to $T_i$ is bijective through level $k+i$, we may identify the
trees through those levels. More explicitly, a level-$m$ node is represented by a coherent family
$\Sequence{s_i}{i\in\omega}$ of level-$m$ nodes: each bonding prefix map sends $s_{i+1}$ to $s_i$.
Evaluation at any stage $j$ with $m\le k+j$ is bijective. Earlier coordinates are finite projections,
and later coordinates are obtained by the unique inverses of the bijective bonding maps.
Truncation commutes with these maps. Use the coherent families as the levels of $T_\infty$, with
coordinatewise truncation as the prefix operation. This gives a tree on the product of the move sets:
a finite word records at each move the corresponding move in every $T_i$. We use actual coherent families,
so no literal equality of the different stage alphabets is required. Prefix closure follows from compatible truncation.
To extend a node of length $m$, choose a stage beyond
$m+1$, choose a legal child there, and recover its coherent family by finite projections and the unique later
inverse maps. The recovered family truncates to the original node. Thus this tree has no terminal nodes.

For a branch $x\in[T_\infty]$, define $\rho_i(x)$ by projecting through the finite composite
$$T_j\to T_{j-1}\to\cdots\to T_i$$
on each prefix, where $j$ is chosen so large that the prefix has length $<k+j$. The coherence of the finite composites
makes these prefix definitions compatible, hence determines a branch of $T_i$.

For a strategy $\sigma$ on $T_\infty$, define $\psi_i(\sigma)$ on positions of length $<k+j$ by applying the finite
composite of the strategy maps from level $j$ down to level $i$. To supply a full strategy at stage $j$, extend the
transported finite restriction by arbitrary legal moves beyond its opening. Causality makes the finite result
independent of this extension. The locality condition for $(k+j)$-coverings makes it independent of all larger $j$.
These compatible finite restrictions determine a full strategy $\psi_i(\sigma)$ for the same player as $\sigma$;
the strategy maps commute with the given coverings, and agreement on any finite opening is preserved.

To verify the lifting axiom, let $x_i$ follow $\psi_i(\sigma)$. Recursively choose $x_{j+1}$ following
$\psi_{j+1}(\sigma)$ with $\pi_{j+1}(x_{j+1})=x_j$, using
$\varphi_{j+1}(\psi_{j+1}(\sigma))=\psi_j(\sigma)$ and the lifting axiom of the given covering.
For each fixed prefix length, the prefixes of these branches agree under the level bijections
once $j$ is sufficiently large.
Their coherent families form a branch $x_\infty\in[T_\infty]$. Agreement of the strategy maps with the identity
through the controlled levels shows that this branch follows $\sigma$, and the projection construction gives
$\rho_i(x_\infty)=x_i$. The remaining locality and finite-level identities follow from the same stabilized
prefixes. Thus the limit has the required $k+i$ control.
\end{proof}

\paragraph*{The Induction}\label{sec:martin-borel-induction}

<!-- formalization: skip-begin (definitions and Borel induction imported from Manthe2025) -->
A payoff $A\IncludedIn[T]$ is \termdefine{universally unravelable} if, for every controlled covering
of $T$, its pulled-back payoff can be unraveled by an $l$-covering for every $l\in\omega$.
Here a controlled covering means one satisfying the causality conditions above, with no positive initial-level
control required. Taking the identity covering recovers ordinary unravelability.

\begin{theorem*}[Unraveling theorem]
\emph{For every tree for play $T$, the universally unravelable subsets of $[T]$ form a sigma-algebra
containing the open sets. Consequently every Borel payoff is universally unravelable.}
\end{theorem*}

\begin{proof}[Proof]
Continuous pullback preserves closed sets, so the closed-set construction applies after every covering.
Thus closed sets are universally unravelable. Complementing the clopen pullback proves closure under
complement and also treats open sets. The empty payoff is already clopen.
Universal unravelability is preserved by pullback along coverings: compose the covering being tested with
the original one. This observation permits successive changes of the underlying tree in the union step.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (universal quantification supplied by the imported Borel induction) -->
Let $A=\bigcup_{i\in\omega} A_i$, where each $A_i$ is universally unravelable.
To prove the same for $A$, first pull everything back along an arbitrary covering and fix $k$.
It suffices to construct a $k$-unraveling of this pulled-back union. Relabel this tree $T$ and its summands $A_i$.
The following tower argument supplies that unraveling.

Set $T_0:=T$. Choose a $k$-covering
$$\Tuple{T_1,\pi_1,\varphi_1}$$
of $T_0$ that unravels $A_0$. Having constructed $T_i$ and the composite projection
$$\rho_i:[T_i]\to[T],$$
choose a $(k+i)$-covering
$$\Tuple{T_{i+1},\pi_{i+1},\varphi_{i+1}}$$
of $T_i$ that unravels $\rho_i^{-1}(A_i)$. Universal unravelability supplies this step after the
composite covering $\rho_i$, even though the underlying tree has changed.

Apply the inverse-limit lemma to the sequence of coverings. We get a $k$-covering
$$\Tuple{T_\infty,\rho_0,\psi_0}$$
of $T$. For every $i$, the map from $T_\infty$ to $T_i$ factors through the covering that unraveled $\rho_i^{-1}(A_i)$,
so $\rho_0^{-1}(A_i)$ is clopen in $[T_\infty]$. Therefore
$$\rho_0^{-1}(A)=\bigcup_i \rho_0^{-1}(A_i)$$
is open.

By the open-set case already proved, there is a $k$-covering of $T_\infty$ that unravels this open set. Composing
it with $\Tuple{T_\infty,\rho_0,\psi_0}$ gives a $k$-covering of $T$ that unravels $A$.

Since the initial covering and $k$ were arbitrary, this proves closure under countable unions.
The sigma-algebra therefore contains the sigma-algebra generated by the open sets, which is the Borel sigma-algebra.
<!-- formalization: skip-end -->
\end{proof}

<!-- formalization: skip (conclusion of the imported unraveling proof) -->
Taking $T=\finseq{\omega}$ and $k=0$, every Borel $A\IncludedIn\BaireSpace$ has a covering that unravels it. The
covering lemma at the start of the argument then gives determinacy of $G_A$. This proves Martin's theorem from
the cited closed-set covering construction.
\end{proof}

<!-- formalization: skip-begin (provenance of the imported checked theorem) -->
The Lean dependency is Manthe's \texttt{BorelDet.Proof.borel\_determinacy}, fixed to the source revision recorded
with the vendored dependency and adapted to this book's Lean and mathlib versions. Its theorem is imported with
its proof. Manthe's inverse limit is constructed in the
category of trees; restriction to each finite level identifies its stabilized projections. The coherent-family
argument here explains the same finite-level mechanism.
<!-- formalization: skip-end -->

\begin{lemma*}[Strategy transport from the external game]
On the full tree $\finseq{\omega}$, a winning strategy in the imported game gives a winning strategy for the same
player in $G_A$, with exactly the same compatible plays.
\end{lemma*}

\begin{proof}[Proof]
Convert a history given as a function on a finite ordinal into the list of its values in increasing order.
For Player I this list has length $2n$; for Player II it has length $2n+1$. Apply the imported strategy at this
position and take its selected move. Every move is legal in the full tree. For an infinite play $x$, the list
obtained from its first $m$ coordinates is exactly its length-$m$ prefix. Thus the equations saying that $x$
follows the transported strategy are exactly the equations defining membership in the imported strategy tree.
The payoff upstairs is the inverse image of $A$ under the map forgetting the proof of being a branch.
This map is continuous, so a Borel $A$ gives a Borel payoff. The imported theorem supplies a winning strategy;
the equality of compatible plays transfers its winning property to $G_A$.
\end{proof}

<!-- formalization: skip-begin (external input or explanatory background) -->
Martin's original and later proofs supply the complete covering construction; see
[@Martin1975; @Martin1985; @Kechris1995, §20].

\begin{mathmeta}
  \forward{bethCard}
\end{mathmeta}

**Why Replacement.** The induction successively collects trees and strategy maps whose auxiliary move sets
can grow with the Borel rank. Replacement supports these transfinite constructions in ZFC.
Friedman's lower bound rules out proving all of Borel determinacy in Zermelo set theory with Choice
[@Friedman1971; @Martin1975]. The precise calibration of restricted determinacy principles requires specifying
the base theory and the available power-set iterations; we do not use such an equivalence here.
<!-- formalization: skip-end -->


## Analytic and Projective Determinacy {#sec:analytic-projective-det}

<!-- formalization: skip-begin (external inner-model and large-cardinal determinacy results) -->
\begin{theorem*}[\termdefineas{analytic determinacy}{Analytic determinacy}] $\bSigma^1_1$-Det is equivalent to the
assertion that $x^\#$ exists for every real $x$.
\end{theorem*}

Martin [@Martin1970] proved $\bSigma^1_1$-Det from a measurable cardinal, and his argument needs only $x^\#$ for every
real $x$, giving one direction of the displayed equivalence. Harrington [@Harrington1978] proved the converse. Here
$x^\#$ is the standard inner-model-theoretic sharp of $x$, a canonical real coding indiscernible structure for $L[x]$.
The text uses only the quoted equivalence, not the fine-structural definition of sharps.

So already at the analytic level, determinacy escapes ZFC: it is equivalent to the existence of sharps for all real
parameters. A measurable cardinal is a standard sufficient hypothesis for this statement, while projective determinacy
requires the stronger Woodin-cardinal machinery described below.

\termdefineas{projective determinacy}{Projective Determinacy (PD)} is the assertion that every projective set is
determined. Under PD the entire projective hierarchy enjoys the regularity properties below, with a uniform structure
theory: PD is the standard set-theoretic axiom for projective descriptive set theory.

The large-cardinal route to PD is the Martin--Steel theorem, stated at the end of this chapter after the regularity
consequences have been made explicit.
<!-- formalization: skip-end -->

## Determinacy Implies Regularity {#sec:det-implies-regularity}

<!-- formalization: skip-begin (regularity-game overview and proof-scope transition) -->
Determinacy yields regularity through auxiliary \termdefineas{regularity game}{regularity games}.
The consequences of a winning strategy depend on the game and on which player wins. For example, in the
perfect-set game below, I produces a Cantor subset and II gives a countability conclusion. The Baire-property
argument instead applies games on many open subspaces. To apply pointclass determinacy, one must also check that
the auxiliary payoffs remain in a determined class.

The Banach--Mazur argument below is proved locally. For the covering game, we quote only the lemma excluding
a winning strategy for I when the payoff has no positive-measure Borel subset. The payoff coding, strategy transfer,
covering estimate, and Borel hull argument are proved here. We also give the complete $*$-game argument for perfect
sets, due to Davis [@Davis1964].
<!-- formalization: skip-end -->

### Banach–Mazur Game and the Baire Property {#sec:banach-mazur-game}

\begin{mathmeta}
  \vars{i,n}{Nat}
\end{mathmeta}

Let $X$ be Polish, let $A \IncludedIn X$, and let $W \IncludedIn X$ be nonempty and open. The
\termdefineas{Banach--Mazur game}{Banach–Mazur game}
$G^{**}(A; W)$ is played as follows. Fix a compatible complete metric on $X$. Players alternate choosing nonempty open
subsets
$$W \supseteq U_0 \supseteq V_0 \supseteq U_1 \supseteq V_1 \supseteq \cdots,$$
with I playing the $U_n$ and II playing the $V_n$, subject to the additional rules
$$
\Closure{V_n}\IncludedIn U_n,\qquad
\Closure{U_{n+1}}\IncludedIn V_n,\qquad
\Diameter{V_n}\le 2^{-n}.
$$
A strategy for II assigns a legal response to the current open move and the finite history of I's earlier moves;
its own earlier responses are recovered from that history. Such a strategy always admits a legal infinite play.
Start with $U_0=W$. After each response $V_n$, choose a nonempty open ball $U_{n+1}$ with
$\Closure{U_{n+1}}\IncludedIn V_n$. The same small-ball construction used for the
\termuseas{metric strong Choquet strategy}{metric strong Choquet strategy} gives such a move at every round.

\begin{lemma*}[\termdefineas{Banach--Mazur outcome}{Unique outcome}]
Every legal play has a unique point $x$ in $\bigcap_n\Closure{V_n}$.
Moreover, $x\in V_n\IncludedIn U_n\IncludedIn W$ for every $n$.
\end{lemma*}

\begin{proof}[Proof]
Put $K_n:=\Closure{V_n}$ and choose $y_n\in V_n$. The rules give
$$
K_{n+1}\IncludedIn U_{n+1}\IncludedIn V_n\IncludedIn K_n,\qquad
\Diameter{K_n}=\Diameter{V_n}\le 2^{-n}.
$$
For $m,k\ge n$, both $y_m$ and $y_k$ lie in $K_n$, so $d(y_m,y_k)\le 2^{-n}$.
Thus $\Sequence{y_n}{n\in\omega}$ is Cauchy and converges to some $x$ by completeness. Each closed set $K_n$ contains
all sufficiently late terms, hence contains $x$. If $z$ also belongs to every $K_n$, then
$d(x,z)\le 2^{-n}$ for every $n$, so $x=z$. Finally, $x\in K_{n+1}\IncludedIn V_n$, and the remaining
inclusions follow from the rules.
\end{proof}

This point $x$ is the outcome of the play, and *I wins* iff $x\in A$.
Write $G^{**}(A):=G^{**}(A;X)$.

\begin{lemma*}[\termdefineas{disjoint response refinement}{Disjoint response refinement}]
Let $W$ be a nonempty open subset of a second-countable metric space. Enumerate the nonempty members $B_j$ of a
countable basis whose closures lie in $W$, allowing repetitions if there are only finitely many.
For each $j$, let $R_j\IncludedIn B_j$ be nonempty and open. Define
$$
C_j:=
\begin{cases}
R_j,& B_j\cap\bigcup_{i<j}C_i=\emptyset,\\
\emptyset,&\text{otherwise}.
\end{cases}
$$
Then the nonempty $C_j$ are pairwise disjoint, and their union is open and dense in $W$.
\end{lemma*}

\begin{proof}[Proof]
Every nonempty open $O\IncludedIn W$ contains some $B_j$ of this enumeration: choose a small open ball with
closure in $O$, and then a basic open set inside that ball. The nonempty sets $C_j$ are disjoint by construction.
To see that their union meets $O$, choose $B_j\IncludedIn O$. If the rule accepts $R_j$, then
$R_j\IncludedIn O$ is a nonempty part of the union. If the rule rejects it, then $B_j$ meets some earlier $C_i$,
so again $O$ meets the union. The union is open because all its nonempty pieces are open.
\end{proof}

\begin{theorem*}[\termdefineas{Banach--Mazur--Oxtoby theorem}{Banach–Mazur–Oxtoby}] Player II has a winning strategy in
$G^{**}(A; W)$ iff $A \cap W$ is meager in $W$.

\end{theorem*}

\begin{proof}[Proof] \emph{($\Leftarrow$).}
Choose sets $N_n\IncludedIn W$ that are nowhere dense in $W$ and cover $A\cap W$.
Regarded as subsets of $X$, they are still nowhere dense: a nonempty ambient open set contained in
$\Closure{N_n}$ would meet $W$ and yield a nonempty relatively open subset of the closure of $N_n$ in $W$.
All closures below are taken in $X$.

At round $n$, the set $O_n:=\SetDifference{U_n}{\Closure{N_n}}$ is nonempty and open.
Choose $a_n\in O_n$ and $\varepsilon_n>0$ with $\Ball{a_n}{\varepsilon_n}\IncludedIn O_n$, and set
$$
r_n:=\min\{\varepsilon_n/2,2^{-n}/2\},\qquad V_n:=\Ball{a_n}{r_n}.
$$
Then
$$
\Closure{V_n}\IncludedIn O_n\IncludedIn U_n,\qquad
\Diameter{V_n}\le 2r_n\le 2^{-n},\qquad
\Closure{V_n}\cap N_n=\emptyset.
$$
Fixing these choices for each round and each possible current open set defines II's strategy on all finite
histories. The outcome $x$ belongs to $W$ and to every $\Closure{V_n}$, hence avoids every $N_n$.
Since the $N_n$ cover $A\cap W$, we have $x\notin A$, so II wins.

\emph{Proof of $(\Rightarrow)$.} Let $\sigma$ be a winning strategy for II. We construct countable families
$\mathcal F_n$ of legal $\sigma$-positions after $n$ complete rounds. Start with
$\mathcal F_0=\{\emptySeq\}$, the empty history, and associate to it the current open set $W$.
For any other position $p$, write $V(p)$ for its last response; put $V(\emptySeq)=W$.

For each $p\in\mathcal F_n$, apply the \termuse{disjoint response refinement} lemma inside $V(p)$.
Use as $B_j$ the basic open sets with $\Closure{B_j}\IncludedIn V(p)$, and as $R_j$ the responses prescribed
by $\sigma$ when I plays $B_j$ after $p$. Keep the extended position $\Tuple{p,B_j,R_j}$ precisely when the rule
accepts $R_j$. Let $\mathcal F_{n+1}$ consist of all these extensions. Every extension is legal, and each
family is countable. The responses from one parent are disjoint by the lemma. Responses from different
parents lie inside disjoint parent responses, so induction shows that the sets $V(p)$, for
$p\in\mathcal F_n$, are pairwise disjoint at every level.

Put
$$D_n:=\bigcup_{p\in\mathcal F_n}V(p),\qquad D:=\bigcap_n D_n.$$
Here $D_0=W$, and every $D_n$ is open. Each parent's selected responses have dense union in that parent,
so $D_n\IncludedIn\Closure{D_{n+1}}$. Inductively, every $D_n$ is dense in $W$.
The Baire category theorem makes $D$ dense in $W$, and $D$ is a $\Gdelta$ set.
Moreover, each $\SetDifference{W}{D_n}$ is relatively closed and nowhere dense in $W$, so
$\SetDifference{W}{D}$ is meager in $W$.

If $x\in D$, disjointness gives a unique $p_n\in\mathcal F_n$ with $x\in V(p_n)$.
The current open set of the parent of $p_{n+1}$ also contains $x$, so uniqueness forces that parent to be $p_n$.
Thus these positions fit together into one infinite legal $\sigma$-play. Its response at round $n$ is
$V(p_{n+1})$, which contains $x$, so the unique outcome of this play is $x$.
Since $\sigma$ is winning, $x\notin A$. Hence $A\cap W\IncludedIn\SetDifference{W}{D}$ is meager in $W$.
\end{proof}

In the dual game $H^{**}(A;W)$, II opens with $V_0\IncludedIn W$, and I responds with $U_0$.
The subsequent moves satisfy
$$
\Closure{U_n}\IncludedIn V_n,\qquad
\Closure{V_{n+1}}\IncludedIn U_n,\qquad
\Diameter{U_n}\le 2^{-n}.
$$
I wins exactly when the outcome belongs to $A$. This is $G^{**}(\SetDifference{X}{A};W)$ with the player names
exchanged, so I has a winning strategy in $H^{**}(A;W)$ iff $A\cap W$ is comeager in $W$.
Here the diameter bound is imposed on I's responses. To compare this game with the play after I's initial move
in $G^{**}(A;W)$, we use small-ball refinements that preserve the outcome.

\begin{corollary*}[First-player criterion]
I has a winning strategy in $G^{**}(A;W)$ iff there is a nonempty open $V\IncludedIn W$ such that
$A\cap V$ is comeager in $V$.
\end{corollary*}

\begin{proof}[Proof]
Suppose first that $\tau$ is a winning strategy for I, with initial move $U_0$.
We construct a winning responder strategy in the auxiliary game $G^{**}(\SetDifference{X}{A};U_0)$.
When its opening player chooses $B_n$, choose a nonempty open ball $V_n$ such that
$$\Closure{V_n}\IncludedIn B_n,\qquad \Diameter{V_n}\le 2^{-n}.$$
Feed $V_n$ to $\tau$ as the next move of the original Player II, retaining the entire earlier simulated
history. Let $R_n$ be $\tau$'s response, namely the original move $U_{n+1}$. Then
$$
\Closure{R_n}\IncludedIn V_n\IncludedIn B_n,\qquad
\Diameter{R_n}\le\Diameter{V_n}\le 2^{-n},
$$
so $R_n$ is a legal response in the auxiliary game. Fixing the small-ball choices for each round and each
possible $B_n$ defines this strategy on every finite history.

Every legal auxiliary play produces a legal original play. At the first round,
$\Closure{V_0}\IncludedIn B_0\IncludedIn U_0$; at later rounds,
$$\Closure{V_{n+1}}\IncludedIn B_{n+1}\IncludedIn R_n=U_{n+1}.$$
If $x$ is the auxiliary outcome, then $x\in\Closure{R_n}\IncludedIn V_n$ for every $n$.
Thus it is also the unique original outcome. Since $\tau$ wins, $x\in A$, so the auxiliary responder avoids
$\SetDifference{X}{A}$. The Banach–Mazur–Oxtoby theorem gives that $A\cap U_0$ is comeager in $U_0$.
In particular, the first move of any winning I-strategy already supplies the required open set.

Conversely, suppose $A\cap V$ is comeager in a nonempty open $V\IncludedIn W$.
Choose a winning responder strategy $\rho$ for $G^{**}(\SetDifference{X}{A};V)$.
I starts with $V$. After the original II-move $V_n$, feed $V_n$ to $\rho$ as an opening move in the auxiliary
game, and use its response as $U_{n+1}$. The original rules ensure that these auxiliary opening moves are
legal. The auxiliary outcome belongs to every $\Closure{U_{n+1}}\IncludedIn V_n$, so it is also the original
outcome. It lies in $A$ because $\rho$ wins, proving that I wins the original game.
\end{proof}

To use games with natural-number moves, enumerate a countable basis of nonempty open sets as
$\Sequence{B_i}{i\in\omega}$,
allowing repetitions if the basis is finite. Every nonempty open $U$ has, for each $n$, a basic refinement satisfying
$$\Closure{B_i}\IncludedIn U,\qquad \Diameter{B_i}\le 2^{-n}.$$
Indeed, first choose a small open ball whose closure lies in $U$ and whose diameter is at most $2^{-n}$,
and then choose a nonempty basic open set inside that ball.

\begin{lemma*}[\termdefineas{Banach--Mazur code tree}{Legal code tree}]
Let $T\IncludedIn\finseq{\omega}$ consist of the finite code sequences that obey the rules of
$G^{**}(A;W)$: the code at position $2n$ represents I's move, the code at position $2n+1$ represents II's move,
the first basic open set lies in $W$, and all applicable closure and diameter conditions hold.
Then $T$ is a tree with no terminal nodes. Its body $\TreeBody{T}$ is a closed subset of $\BaireSpace$ and is Polish.
\end{lemma*}

\begin{proof}[Proof]
The empty sequence is legal, and every prefix of a legal sequence is legal because its conditions are among
those already checked. For the first move, choose a basic open set inside $W$. After any later finite position,
choose a basic refinement whose closure lies in the last open set. At an II-turn, also impose the current
bound $2^{-n}$ on its diameter. The refinement construction above supplies each of these moves, so every node
has a successor. The \termuseas{branch extension for trees without terminal nodes}{branch-extension lemma}
makes $T$ pruned.
By §{sec:closed-sets-trees}, its body is closed. Being closed in the Polish space $\BaireSpace$, the body is Polish.
\end{proof}

\begin{proposition*}[\termdefineas{Banach--Mazur outcome map}{Continuous outcome map}]
Every $p\in\TreeBody{T}$ has a unique outcome $\pi(p)$ determined by
$$\{\pi(p)\}=\bigcap_n\Closure{B_{p(2n+1)}}.$$
The map $\pi:\TreeBody{T}\to X$ is continuous and takes values in $W$. More precisely,
$$
\restrict{p}{2n+2}=\restrict{q}{2n+2}
\quad\Longrightarrow\quad
 d(\pi(p),\pi(q))\le 2^{-n}.
$$
\end{proposition*}

\begin{proof}[Proof]
Decoding a branch gives a legal open-set play. The nested-closure argument above supplies its unique outcome,
and $\pi(p)\in\Closure{B_{p(1)}}\IncludedIn B_{p(0)}\IncludedIn W$.
If two branches agree through position $2n+1$, their outcomes lie in the closure of the same II-response.
That closure has diameter at most $2^{-n}$, giving the displayed estimate. For any $\varepsilon>0$, choose $n$
with $2^{-n}<\varepsilon$. The cylinder fixing the first $2n+2$ codes, intersected with $\TreeBody{T}$,
is an open neighborhood on which outcomes lie within distance $\varepsilon$ of the given outcome.
This proves continuity.
\end{proof}

The coded payoff is exactly
$$A_T:=\pi^{-1}(A)=\pi^{-1}(A\cap W)\IncludedIn\TreeBody{T}.$$
Thus Borel payoffs remain Borel. More generally, any pointclass on Polish spaces closed under continuous
preimages contains $A_T$ whenever it contains $A$. Legality is already part of the domain $\TreeBody{T}$.
This defines the game $G(A_T,T)$ on natural-number moves.

\begin{proposition*}[\termdefineas{Banach--Mazur strategy refinement}{Refining open-set strategies}]
For either player, a winning strategy in $G^{**}(A;W)$ gives a winning strategy in the coded game $G(A_T,T)$.
\end{proposition*}

\begin{proof}[Proof]
For every nonempty open $U$ and every $n$, fix a code $\rho_n(U)$ such that
$$\Closure{B_{\rho_n(U)}}\IncludedIn U,\qquad \Diameter{B_{\rho_n(U)}}\le 2^{-n}.$$
These choices depend only on $U$ and $n$ and will be used throughout the simulation.

Suppose first that I has a winning strategy. When it prescribes an open move $U_n$, play the code
$\rho_0(U_n)$ instead. Feed II's actual basic responses $V_0,\ldots,V_n$ to the original strategy to obtain
its next prescribed move. This preserves the entire history of II's moves. Writing
$\widetilde U_n:=B_{\rho_0(U_n)}$, the relevant inclusions are
$$
\Closure{V_n}\IncludedIn\widetilde U_n\IncludedIn U_n,\qquad
\Closure{\widetilde U_{n+1}}\IncludedIn U_{n+1}\IncludedIn V_n.
$$
The initial refinement is contained in $W$, so the coded strategy is legal. The same II-responses form a
legal play against the original strategy. Both outcomes are the unique point of
$\bigcap_n\Closure{V_n}$, and hence belong to $A$.

Now suppose that II has a winning strategy. Decode I's basic moves $U_0,\ldots,U_n$, let the original
strategy prescribe $V_n$, and answer with the code $\rho_n(V_n)$. Put
$\widetilde V_n:=B_{\rho_n(V_n)}$. Then
$$
\Closure{\widetilde V_n}\IncludedIn V_n\IncludedIn U_n,\qquad
\Diameter{\widetilde V_n}\le 2^{-n},\qquad
\Closure{U_{n+1}}\IncludedIn\widetilde V_n\IncludedIn V_n.
$$
Thus the coded response is legal, and the decoded I-moves are legal against the original strategy.
The coded outcome $x$ lies in every $\Closure{\widetilde V_n}$ and therefore in every $\Closure{V_n}$.
Uniqueness of the original outcome identifies it with $x$, so $x\notin A$.
\end{proof}

\begin{proposition*}[\termdefineas{Banach--Mazur strategy lifting}{Lifting coded strategies}]
For either player, a winning strategy in $G(A_T,T)$ gives a winning strategy in $G^{**}(A;W)$.
\end{proposition*}

\begin{proof}[Proof]
Use the fixed refinements $\rho_n(U)$ from the preceding proof. Retain the entire simulated code history:
distinct codes may denote the same open set, and the coded strategy can distinguish them.

Suppose II has a winning coded strategy $\tau$. Start with $s_0:=\emptyset$. After I's arbitrary open move
$U_n$, set
$$
\begin{aligned}
a_n&:=\rho_n(U_n),& b_n&:=\tau(s_n\concat(a_n)),\\
V_n&:=B_{b_n},& s_{n+1}&:=s_n\concat\Pair{a_n}{b_n}.
\end{aligned}
$$
Thus $s_n$ records all earlier simulated moves. The first refined opening lies in $W$. At later rounds,
$$\Closure{B_{a_n}}\IncludedIn U_n\IncludedIn V_{n-1}=B_{b_{n-1}}\qquad(n>0).$$
Induction therefore makes the simulated opening legal. The coded response satisfies
$$\Closure{V_n}\IncludedIn B_{a_n}\IncludedIn U_n,\qquad \Diameter{V_n}\le 2^{-n},$$
so it is also a legal open response. The coded and open plays have exactly the same II-responses $V_n$,
hence the same unique outcome. Since $\tau$ wins, that outcome is outside $A$.

Suppose instead that I has a winning coded strategy $\sigma$. Play its initial code as an open set:
$$a_0:=\sigma(\emptyset),\qquad U_0:=B_{a_0},\qquad s_0:=(a_0).$$
After II's arbitrary open response $V_n$, put
$$
\begin{aligned}
b_n&:=\rho_n(V_n),& a_{n+1}&:=\sigma(s_n\concat(b_n)),\\
U_{n+1}&:=B_{a_{n+1}},& s_{n+1}&:=s_n\concat\Pair{b_n}{a_{n+1}}.
\end{aligned}
$$
Here $s_n$ ends with I's current code. The simulated II-response is legal because
$$\Closure{B_{b_n}}\IncludedIn V_n\IncludedIn U_n,\qquad \Diameter{B_{b_n}}\le 2^{-n}.$$
The prescribed next move satisfies
$$\Closure{U_{n+1}}\IncludedIn B_{b_n}\IncludedIn V_n,$$
so the actual open play is legal as well. The coded outcome $x$ lies in every
$\Closure{B_{b_n}}\IncludedIn V_n$, hence is the unique outcome of the actual open play. Since $\sigma$ wins,
$x\in A$. Both constructions use only the current move and the retained finite history, so they define strategies.
\end{proof}

\begin{corollary*}[\termdefineas{Banach--Mazur coding equivalence}{Coding equivalence}]
The coded game $G(A_T,T)$ and the open-set game $G^{**}(A;W)$ have the same winning players.
In particular, one is determined if and only if the other is determined.
\end{corollary*}

\begin{theorem*}[\termdefineas{determinacy implies the Baire property}{Baire regularity from determinacy}]
Suppose $\Gamma$ is a pointclass on Polish spaces closed under continuous preimages, and every game on a
pruned tree on $\omega$ with payoff in $\Gamma$ is determined. Then every $A\in\Gamma$ has the
\termuse{Baire property}.
\end{theorem*}

\begin{proof}[Proof]
Let $A\in\Gamma$. For every nonempty open $W$, the continuous outcome map gives $A_T=\pi^{-1}(A)\in\Gamma$.
The coded game is therefore determined. By the coding equivalence, so is $G^{**}(A;W)$.
Define
$$U^*:=\bigcup\{V\IncludedIn X:V\text{ open and }A\cap V\text{ is comeager in }V\}.$$
This set is open. For an open $V$, meagreness in $V$ and ambient meagreness agree for subsets of $V$.
Thus the defining condition says equivalently that $\SetDifference{V}{A}$ is meager in $X$.

Second countability gives a countable subfamily $V_n$ with the same union $U^*$. Hence
$$\SetDifference{U^*}{A}=\bigcup_n\SetDifference{V_n}{A}$$
is meager. This uses no regularity assumption on $A$.

Set $W:=\SetDifference{X}{\Closure{U^*}}$. If $W=\emptyset$, then $A\cap W$ is meager. Otherwise, I cannot win
$G^{**}(A;W)$: the first-player criterion would give a nonempty open $V\IncludedIn W$ on which $A\cap V$
is comeager, forcing $V\IncludedIn U^*$, contrary to the definition of $W$. Determinacy therefore gives
II a winning strategy on $W$. The Banach–Mazur–Oxtoby theorem makes $A\cap W$ meager in $W$, and hence in $X$.

The boundary $\SetDifference{\Closure{U^*}}{U^*}$ of the open set $U^*$ is closed with empty interior,
so it is nowhere dense. Since
$$
\SetDifference{A}{U^*}=(A\cap W)\cup
\bigl(A\cap\SetDifference{\Closure{U^*}}{U^*}\bigr),
$$
this difference is meager too. Thus $A\triangle U^*$ is meager and $U^*$ is open, proving the Baire property.
\end{proof}

<!-- formalization: skip-begin (standard pointclass closure and external determinacy consequences) -->
Closure under continuous preimages holds for the standard pointclasses:
Borel, $\bSigma^1_n$, $\bPi^1_n$, and the projective class as a whole.
Borel determinacy recorded in §{sec:martin-borel-det} therefore gives the Baire property for Borel sets in ZFC;
PD lifts this to all projective sets.
<!-- formalization: skip-end -->

### Covering Game and Lebesgue Measurability {#sec:covering-game}

\begin{mathmeta}
  \vars{m,n,p}{Nat}
\end{mathmeta}

Fix a finite Borel measure $\mu$ on $\CantorSpace$. We use the
\termdefine{Harrington covering game} from [@Moschovakis2009, 6A.17]. For $B\IncludedIn\CantorSpace$ and
$\varepsilon>0$, I plays bits, forming $x$, and II replies at round $n$ with a clopen set $G_n$ satisfying
$$\mu(G_n)\le\varepsilon 2^{-2n-2}.$$
Clopen sets are coded by integers. Player I wins precisely when
$$x\in\SetDifference{B}{\bigcup_n G_n}.$$
The empty clopen set is always a legal response.

For a fixed strategy $\sigma$ of II, let $G_\sigma(s)$ be its response after I has played the nonempty
binary string $s$. Earlier responses of II are determined by $s$, so this notation retains the whole relevant
history. The strategy is winning exactly when
$$\forall x\in B\ \exists n\in\omega\quad x\in G_\sigma(\restrict{x}{n+1}).$$

\begin{lemma*}[\termdefineas{covering-strategy estimate}{Covering-strategy estimate}]
A winning strategy $\sigma$ of II with budget $\varepsilon$ gives an open set $U_\sigma\supseteq B$
with $\mu(U_\sigma)\le\varepsilon$. If II wins for every positive budget, then $\mu^*(B)=0$.
\end{lemma*}

\begin{proof}[Proof]
Take the union over all possible bit histories:
$$U_\sigma:=\bigcup_{n\in\omega}\ \bigcup_{s\in 2^{n+1}}G_\sigma(s).$$
It is open because the responses are clopen. If $x\in B$, the winning condition gives
$x\in G_\sigma(\restrict{x}{n+1})$ for some $n$, hence $x\in U_\sigma$. At round $n$ there are
$2^{n+1}$ histories. Countable subadditivity and the response bounds give
$$
\begin{aligned}
\mu(U_\sigma)
&\le\sum_{n\in\omega}\ \sum_{s\in 2^{n+1}}\mu(G_\sigma(s))\\
&\le\sum_{n\in\omega}2^{n+1}\varepsilon 2^{-2n-2}\\
&=\varepsilon\sum_{n\in\omega}2^{-n-1}=\varepsilon.
\end{aligned}
$$
Thus $\mu^*(B)\le\varepsilon$. Applying this to every positive budget proves the last assertion.
\end{proof}

\begin{lemma*}[\termdefineas{Borel hull criterion for measurability}{Borel hull criterion}]
Let $A\IncludedIn\CantorSpace$. Suppose that for every Borel $H\supseteq A$ for which
$\SetDifference{H}{A}$ contains no Borel subset of positive measure, II wins the covering game for
$\SetDifference{H}{A}$ with every positive budget. Then $A$ is measurable for the completion of $\mu$.
\end{lemma*}

\begin{proof}[Proof]
Outer regularity gives open sets $U_n\supseteq A$ with
$$\mu(U_n)\le\mu^*(A)+2^{-n}.$$
Put $H:=\bigcap_n U_n$. This is a Borel set containing $A$, and
$$\mu^*(A)\le\mu(H)\le\mu^*(A)+2^{-n}\qquad(n\in\omega).$$
Letting $n\to\infty$ gives $\mu(H)=\mu^*(A)$.

Set $B:=\SetDifference{H}{A}$. If $C\IncludedIn B$ is Borel, then $A\IncludedIn\SetDifference{H}{C}$ and
$$
\begin{aligned}
\mu(H)&=\mu(\SetDifference{H}{C})+\mu(C),\\
\mu(H)&=\mu^*(A)\le\mu(\SetDifference{H}{C}).
\end{aligned}
$$
Finiteness of $\mu(H)$ forces $\mu(C)=0$. The hypothesis now supplies winning strategies for II on $B$,
and the covering-strategy estimate gives $\mu^*(B)=0$. The set $B$ is therefore measurable in the completion.
Since $A=\SetDifference{H}{B}$ and $H$ is Borel, $A$ is measurable in the completion as well.
\end{proof}

To make the payoff complexity explicit, let $\mathcal C$ be the clopen subsets of $\CantorSpace$.
This family is countable: every clopen set is compact and is therefore a finite union of basic cylinders.
Fix an injection $c:\mathcal C\to\omega$ and put $C:=c[\mathcal C]$.
Write $D_k:=c^{-1}(k)$ for $k\in C$, and put $D_k:=\emptyset$ otherwise.
Let $T_{\mu,\varepsilon}\IncludedIn\finseq{\omega}$ consist of the finite histories satisfying
$$
\begin{aligned}
s(2n)&\in2 &&\text{if }2n<\Length{s},\\
s(2n+1)&\in C,\quad
\mu(D_{s(2n+1)})\le\varepsilon 2^{-2n-2}
&&\text{if }2n+1<\Length{s}.
\end{aligned}
$$
These conditions are preserved by taking initial segments. Every legal history can be extended:
I can play $0$, and II can play $c(\emptyset)$. Thus $T_{\mu,\varepsilon}$ is pruned, and its branch space
$P:=\TreeBody{T_{\mu,\varepsilon}}$ is a closed subspace of $\BaireSpace$, hence Polish.
For a branch $a\in P$, recover I's target and II's responses by
$$\pi(a)(n):=a(2n),\qquad R_n(a):=D_{a(2n+1)}.$$

\begin{lemma*}[\termdefineas{covering-game payoff coding}{Covering-game payoff coding}]
The target map $\pi:P\to\CantorSpace$ is continuous. For each $n$, the set
$$E_n:=\{a\in P:\pi(a)\in R_n(a)\}$$
is open, so $F:=\bigcap_n(\SetDifference{P}{E_n})$ is closed in $P$.
The coded payoff for I is
$$B_{\mu,\varepsilon}:=\pi^{-1}(B)\cap F.$$
Consequently, if a pointclass $\Gamma$ contains the closed sets and is closed under continuous preimages
and finite intersections, then $B\in\Gamma$ implies $B_{\mu,\varepsilon}\in\Gamma$.
\end{lemma*}

\begin{proof}[Proof]
Each coordinate of $\pi$ is an even coordinate of $a$, so $\pi$ is continuous. Moreover,
$$E_n=\bigcup_{k\in\omega}\bigl(\{a\in P:a(2n+1)=k\}\cap\pi^{-1}(D_k)\bigr).$$
The coordinate condition defines an open cylinder, and $D_k$ is open. Every term in the union is therefore
open. Taking complements and intersections proves that $F$ is closed. Membership in $F$ means that the target
avoids every response, which gives the payoff formula. The stated closure properties give the last assertion.
\end{proof}

\begin{proposition*}[\termdefineas{covering-game strategy lifting}{Lifting a covering strategy}]
If II has a winning strategy in the coded game on $T_{\mu,\varepsilon}$ with payoff
$B_{\mu,\varepsilon}$, then II has a winning strategy in the covering game on $B$ with budget $\varepsilon$.
\end{proposition*}

\begin{proof}[Proof]
Let $\widehat{\tau}$ be the coded strategy. Retain the complete simulated code history, starting with
$q_0:=\emptySeq$. After I plays the current bit $x(n)$, set
$$
\begin{aligned}
k_n&:=\widehat{\tau}(q_n\concat(x(n))),& G_n&:=D_{k_n},\\
q_{n+1}&:=q_n\concat\Pair{x(n)}{k_n}.
\end{aligned}
$$
Inductively, $q_n$ is legal and has length $2n$. Appending I's bit is legal, and the strategy returns a legal
code $k_n\in C$ with $\mu(G_n)\le\varepsilon 2^{-2n-2}$. Thus the recurrence defines a budgeted strategy of II;
its response depends only on the bits played so far, since these determine the earlier simulated history.
For every $x$, the resulting code play follows $\widehat{\tau}$, and its target is $x$. If $x\in B$ avoided
every $G_n$, that play would belong to $B_{\mu,\varepsilon}$, contradicting that $\widehat{\tau}$ wins for II.
Thus every $x\in B$ is caught, as required.
\end{proof}

<!-- formalization: skip-begin (cited external exclusion of I in the covering game) -->
We use the following external game lemma: if $B$ contains no Borel subset of positive measure, I has no
winning strategy in the covering game [@Moschovakis2009, 6A.17]. This applies to the integer presentation
above: its legal histories record precisely the bits and clopen responses of that game.
<!-- formalization: skip-end -->

\begin{theorem*}[\termdefineas{Mycielski--Świerczkowski theorem}{Mycielski--Świerczkowski}]
Let $\Gamma$ be a pointclass on Polish spaces containing the Borel sets and closed under finite Boolean
operations and continuous preimages. Suppose every game on a pruned tree on $\omega$ with payoff in $\Gamma$
is determined. Then every $A\in\Gamma$ on $\CantorSpace$ is measurable for the completion of every finite
Borel measure $\mu$ on $\CantorSpace$.
\end{theorem*}

This form follows using the external game lemma above; the general determinacy-to-measurability theorem is due to
Mycielski and Świerczkowski [@MycielskiSwierczkowski1964; @Moschovakis2009, 6A.18].

\begin{proof}[Proof using the game lemma]
Let $H\supseteq A$ be Borel and suppose that $B:=\SetDifference{H}{A}$ contains no Borel subset of positive
measure. Closure under finite Boolean operations gives $B\in\Gamma$. For every $\varepsilon>0$, the payoff
formula gives $B_{\mu,\varepsilon}=\pi^{-1}(B)\cap F\in\Gamma$, since $F$ is closed. The coded game is therefore
determined. The external game lemma rules out a winning strategy for I, so II has a winning coded strategy.
Lifting it gives a winning covering strategy on $B$ with budget $\varepsilon$. This works for every positive
budget and every such $H$. The Borel hull criterion now gives the asserted measurability.
\end{proof}

<!-- formalization: skip (applications of cited determinacy principles) -->
Both the Borel pointclass and the class of all projective sets satisfy these closure assumptions.
Thus Borel determinacy gives the Borel case, PD gives universal measurability for projective sets, and AD gives
measurability for all sets of reals.

The standard Borel classification transfers the finite-measure statement
from Cantor space to arbitrary standard Borel spaces: use a Borel embedding and extend the transported measure
by zero outside its image. A countable exhaustion handles sigma-finite measures, including Lebesgue measure.

<!-- formalization: skip (illustrative warning about open approximation) -->
The Borel hull is essential here. A measurable set need not agree with an open set modulo a null set;
for example, a positive-measure closed nowhere dense set for the fair-coin measure has no nonempty open region
on which it has full measure.

### The $*$-Game and the Perfect Set Property {#sec:star-game}

\begin{mathmeta}
  \vars{b}{Name}
  \vars{k}{Nat}
  \vars{t,p_*,s_*,q_*}{Seq(Nat)}
  \vars{h,h_*}{Seq(Seq(Nat))}
  \vars{a,c,x,y}{Name}
  \vars{a_*}{Nat}
  \vars{\sigma}{Fun(Seq(Nat),Seq(Nat))}
  \vars{\widehat{\sigma},\widehat{\tau}}{Fun(Seq(Nat),Nat)}
  \vars{\iota}{Fun(Seq(Nat),Nat)}
  \vars{n}{Nat}
\end{mathmeta}

In the \termdefineas{star game}{$*$-game} Player I plays finite binary strings $s_0, s_1, \ldots$ and Player II plays
single bits $b_0, b_1,\ldots$; the play codes the real
$$x \;:=\; s_0 \concat (b_0) \concat s_1 \concat (b_1) \concat \cdots \;\in\; \CantorSpace.$$
Player I wins iff $x \in A$. The empty word is allowed, but every round adds at least the bit chosen by II,
so the output is always an infinite binary sequence.

A strategy of I can be written as $\sigma:\finseq{2}\to\finseq{2}$, with $\sigma(\restrict{b}{n})$ specifying
I's word at round $n$. For II we write $\tau(h,t)$, where $h\in\finseq{(\finseq{2})}$ is the history of I's previous
words and $t\in\finseq{2}$ is the current word. Each player retains the opponent's whole finite history;
the player's own earlier moves are already determined by that history and the strategy.

The following game theorem is due to Davis [@Davis1964].

\begin{theorem*}[\termdefineas{Davis perfect-set game theorem}{Davis}] For $A\IncludedIn\CantorSpace$, the $*$-game has
the following consequences.

\begin{enumerate}
\item If I has a winning strategy, then $A$ contains a Cantor set.
\item If II has a winning strategy, then $A$ is countable.
\end{enumerate}

\end{theorem*}

\begin{proof}[Proof]
Suppose first that I has a winning strategy $\sigma$. For each $b\in\CantorSpace$, let II play the bits of $b$.
Define I's words and the output prefixes by
$$
\begin{aligned}
p_0&:=\emptySeq,& s_n&:=\sigma(\restrict{b}{n}),\\
p_{n+1}&:=p_n\concat s_n\concat(b(n)).
\end{aligned}
$$
The prefixes extend one another and $\Length{p_n}\ge n$. Thus there is a unique $f(b)\in\CantorSpace$ extending
every $p_n$. This is the outcome of the play against $b$, so $f(b)\in A$.

If $b$ and $c$ agree on their first $n$ bits, their words and output prefixes in the first $n$ rounds agree as well.
Since $\Length{p_n}\ge n$, this gives
$$\restrict{b}{n}=\restrict{c}{n}\quad\Longrightarrow\quad
\restrict{f(b)}{n}=\restrict{f(c)}{n}.$$
Cylinder neighborhoods therefore show that $f$ is continuous. To prove injectivity, suppose $f(b)=f(c)$.
Inductively assume that $b$ and $c$ agree before round $n$. The current prefix $p_n$ and word $s_n$ are then the same
in both plays. At position $\Length{p_n}+\Length{s_n}$, the two outputs have bits $b(n)$ and $c(n)$, so these bits agree
too.
Induction gives $b=c$.

Since $\CantorSpace$ is compact and the codomain is Hausdorff, this continuous injection is a closed embedding.
Its image $f[\CantorSpace]\IncludedIn A$ is a Cantor set. This proves the first implication.

Now suppose that II has a winning strategy $\tau$. For a finite history $h$ of I's words, let $p_h$ be the output
already forced by $\tau$. Thus
$$p_{\emptySeq}=\emptySeq,\qquad
p_{h\concat(t)}=p_h\concat t\concat(\tau(h,t)).$$
Let $E_h$ consist of the reals $x$ extending $p_h$ for which every $t\in\finseq{2}$ satisfies
$$p_h\concat t\prefixOf x\quad\Longrightarrow\quad
\tau(h,t)\ne x(\Length{p_h}+\Length{t}).$$
These are precisely the targets for which the construction gets stuck at $h$.

For fixed $h$, the set $E_h$ has at most one member. The prefix $p_h$ is fixed, and any remaining tail $y$ must satisfy
$$y(k)=1-\tau(h,\restrict{y}{k})\qquad(k\in\omega).$$
The first bit is therefore determined; after the first $k$ bits have been determined, this equation determines
the next one. Induction proves uniqueness of the whole tail. Since finite histories form a countable set,
$$E:=\bigcup_{h\in\finseq{(\finseq{2})}}E_h$$
is countable.

Fix $x\notin E$. Starting with $h_0:=\emptySeq$, recursively choose the shortest finite word $t$ such that
$$p_{h_n}\concat t\prefixOf x,\qquad \tau(h_n,t)=x(\Length{p_{h_n}}+\Length{t}),$$
and put $s_n:=t$ and $h_{n+1}:=h_n\concat(s_n)$. Initially $p_{h_0}\prefixOf x$.
Whenever $p_{h_n}\prefixOf x$, the fact that $x\notin E_{h_n}$ guarantees such a word.
For each length there is only one candidate matching the target tail, so the shortest word is well defined.
Its matching response ensures $p_{h_{n+1}}\prefixOf x$. The recursion therefore continues for every round.
Moreover, $\Length{p_{h_n}}\ge n$, because every round adds one bit after I's word. The resulting infinite outcome is
exactly $x$.

II follows $\tau$ in this play, so $x\notin A$. We have proved that every $x\notin E$ is outside $A$.
Thus $A\IncludedIn E$, and $A$ is countable.
\end{proof}

\begin{corollary*}
If the $*$-game on $A\IncludedIn\CantorSpace$ is determined, then $A$ is countable or contains a Cantor set.
\end{corollary*}

To apply integer-game determinacy, fix an injective code $\iota:\finseq{2}\to\omega$ and let
$C:=\iota[\finseq{2}]$. Only codes in $C$ may be used at I's turns; II uses the integers $0$ and $1$.
Let $T\IncludedIn\finseq{\omega}$ consist of the finite sequences whose entries at even positions belong to $C$
and whose entries at odd positions belong to $2$. A branch $a\in\TreeBody{T}$ decodes to
$$s_n:=\iota^{-1}(a(2n)),\qquad b(n):=a(2n+1).$$
Let $\pi(a)$ be the resulting infinite concatenation of these words and bits.

\begin{lemma*}[\termdefineas{Davis code tree}{Integer coding of the $*$-game}]
The tree $T$ is pruned, its body $\TreeBody{T}$ is Polish, and the map
$\pi:\TreeBody{T}\to\CantorSpace$ is continuous. The coded payoff for $A$ is exactly $\pi^{-1}(A)$.
\end{lemma*}

\begin{proof}[Proof]
The coordinate conditions are preserved by taking prefixes. Every node has a legal successor: use
$\iota(\emptySeq)$ at an I-turn and $0$ at an II-turn. Thus $T$ is pruned, and its body is closed in $\BaireSpace$,
hence Polish. If two branches agree on their first $2n$ codes, their first $n$ words and bits agree.
The output after these rounds has length at least $n$, so
$$\restrict{a}{2n}=\restrict{a'}{2n}\quad\Longrightarrow\quad
\restrict{\pi(a)}{n}=\restrict{\pi(a')}{n}.$$
This proves continuity using cylinder neighborhoods. The payoff identity is the definition of I's win.
\end{proof}

\begin{proposition*}[\termdefineas{Davis strategy lifting}{Lifting coded $*$-game strategies}]
A winning strategy for either player in the game on $T$ with payoff $\pi^{-1}(A)$ gives a winning strategy
for the same player in the $*$-game on $A$.
\end{proposition*}

\begin{proof}[Proof]
First let $\widehat{\sigma}$ be a coded winning strategy for I. Keep the entire simulated code history $q_n$,
starting with $q_0:=\emptySeq$. After II's previous bits have been supplied, set
$$
\begin{aligned}
a_n&:=\widehat{\sigma}(q_n),& s_n&:=\iota^{-1}(a_n),\\
q_{n+1}&:=q_n\concat\Pair{a_n}{b(n)}.
\end{aligned}
$$
The history $q_n$ has length $2n$ and is legal. Therefore $a_n\in C$, and $s_n$ is well defined.
Appending the bit $b(n)$ preserves legality. The chosen word depends only on the preceding bit history,
so it defines a strategy for I. When that strategy is followed, the canonical code of $s_n$ is exactly $a_n$.
Thus the coded play follows $\widehat{\sigma}$ and has the same concatenated outcome as the original play.
Its outcome belongs to $A$.

Now let $\widehat{\tau}$ be a coded winning strategy for II. Again start with $q_0:=\emptySeq$ and retain the full
code history. When I supplies $s_n$, set
$$
\begin{aligned}
a_n&:=\iota(s_n),& b(n)&:=\widehat{\tau}(q_n\concat(a_n)),\\
q_{n+1}&:=q_n\concat\Pair{a_n}{b(n)}.
\end{aligned}
$$
Appending $a_n$ is legal, and the strategy supplies a legal bit $b(n)\in2$. Hence the histories remain legal.
This response depends only on I's previous words and current word, so it defines a strategy for II.
The coded play follows $\widehat{\tau}$, and decoding preserves its concatenated outcome. That outcome is outside
$A$, as required.
\end{proof}

\begin{theorem*}[\termdefineas{determinacy implies the perfect set property}{Perfect-set regularity from determinacy}]
Suppose $\Gamma$ is a pointclass on Polish spaces closed under continuous preimages, and every game on a pruned
tree on $\omega$ with payoff in $\Gamma$ is determined. Then every $A\in\Gamma$ on $\CantorSpace$ is countable
or contains a Cantor set.
\end{theorem*}

\begin{proof}[Proof]
The Polish branch space and continuous map above give $\pi^{-1}(A)\in\Gamma$. Thus the coded game is determined.
Lifting its winning strategy gives a winning strategy for the same player in the $*$-game on $A$.
Davis's theorem now gives the asserted alternative.
\end{proof}

<!-- formalization: skip-begin (external perfect-set consequences) -->
For closed sets,
§{sec:perfect-set-theorem} proves this in ZFC. The analytic extension is the standard ZFC perfect-set theorem for
analytic sets, recorded with the other regularity facts in §{sec:regularity-independence}. PD extends the same
conclusion to all projective sets.

The pattern is uniform: with the required closure under the auxiliary-game codings, determinacy in pointclass
$\Gamma$ delivers the three classical regularity properties for
$\Gamma$. This is why "the right axiom for projective DST is PD" — under PD, the projective hierarchy behaves like the
Borel hierarchy does in ZFC, with all regularity properties holding throughout.
<!-- formalization: skip-end -->

## The Axiom of Determinacy {#sec:axiom-of-determinacy}

The assertion covering all real payoffs is the \termdefineas{Axiom of Determinacy}{Axiom of Determinacy (AD)}: every
$A \IncludedIn \BaireSpace$ is determined.

**AD contradicts AC.** The construction of a non-determined payoff set in §{sec:determinacy} uses Choice to well-order
all strategies and diagonalize against them. Hence AD cannot be added to ZFC.

<!-- formalization: skip-begin (external AD and large-cardinal determinacy results) -->
The standard large-cardinal calibration is
usually stated for determinacy inside $L(\R)$ rather than as a bare equiconsistency slogan for full ZF + AD:

\begin{theorem*}[\termdefineas{Martin--Steel--Woodin theorem}{Martin--Steel--Woodin}] If there are infinitely many
Woodin cardinals with a measurable cardinal above them, then $L(\R)$ satisfies AD. Over ZFC, the assertion that
$L(\R)$ satisfies AD is equiconsistent with the existence of infinitely many Woodin cardinals. The measurable
cardinal above them is part of the sufficient hypothesis for the direct implication stated above; it is not
required for this equiconsistency.
\end{theorem*}

Under AD, every set of reals is Lebesgue measurable, has the Baire property, and has the perfect set property — the same
conclusion Solovay's model in §{sec:forcing-independence-regularity} reaches with forcing instead of determinacy. The
two routes give complementary choice-free theories of universal regularity: determinacy gives regularity through games,
while Solovay's model gives regularity through a forcing collapse of an inaccessible. The exact consistency-strength
bookkeeping belongs to inner model theory; the point needed here is only that AD and $L(\R)$-determinacy sit far beyond
ZFC and are measured by Woodin-cardinal hypotheses.

## Martin--Steel: Large Cardinals to PD {#sec:martin-steel-pd}
\index{Woodin cardinal}
\index{large cardinal!projective determinacy}

For the projective hierarchy, the decisive bridge from large cardinals to determinacy is the
\termforward{Martin--Steel theorem} [@MartinSteel1989].

\begin{theorem*}[\termdefineas{Martin--Steel theorem}{Martin--Steel}] \emph{If there are infinitely
many Woodin cardinals, then \termuse{projective determinacy} holds.}
\end{theorem*}

More precisely, the finite-level theorem says that enough Woodin cardinals, with a
measurable cardinal above them in the usual formulation, imply determinacy for the corresponding initial segment of the
projective hierarchy. Taking the finite-level result for every $n$ yields PD:
$$
\text{large cardinals}
\quad\Longrightarrow\quad
\bSigma^1_n\text{-Det and }\bPi^1_n\text{-Det for every }n
\quad\Longrightarrow\quad
\mathrm{PD}.
$$

The proof is not a game-by-game extension of Borel determinacy. Borel determinacy unravels a Borel code until the payoff
becomes clopen. At the projective levels the code contains alternating real quantifiers, and a winning strategy must be
stable through those quantifiers. Martin and Steel obtain that stability from inner models with Woodin cardinals. The
large cardinals supply iteration strategies for those models; the iteration strategies supply comparison and
absoluteness; and those absoluteness facts produce the winning strategies for projective games.\termref{absoluteness}

This is why PD is treated as the natural axiom for projective descriptive set theory. It is strong enough to give all
three regularity properties in §{sec:det-implies-regularity}, to organize projective Wadge degrees as in §{sec:wadge},
and to support their structural study. Related large-cardinal hypotheses also give projective absoluteness
for forcing, as discussed in §{sec:forcing-absoluteness}; that conclusion requires the hypotheses stated there.
PD is also calibrated
closely to large cardinals: the consistency strength of PD is captured by the finite Woodin-cardinal hierarchy, so the
theorem is not merely a sufficient-condition result but part of the standard scale measuring projective set
theory.\termref{absoluteness}

Further work studies the internal structure of determinacy models and its connection with generic
absoluteness. Sargsyan--Trang [@SargsyanTrang2024LSA] prove the Mouse Set Conjecture in the minimal model of
the Largest Suslin Axiom, abbreviated LSA; the stated scope is this model, not an unrestricted resolution of
the conjecture. Roughly, mouse capturing relates definability of reals to membership in iterable inner-model
approximations. Their work on Sealing [@SargsyanTrang2024Sealing] connects determinacy models to the
preservation under set forcing of the theory associated with universally Baire sets. It calibrates the
consistency strength of Sealing against the principle LSA-over-uB, over the background large-cardinal theory
specified there. These results extend the connection between determinacy and absoluteness discussed in
§{sec:forcing-absoluteness}; the inner-model constructions are beyond the present book.
<!-- formalization: skip-end -->
