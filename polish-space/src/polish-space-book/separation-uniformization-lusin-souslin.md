# Separation, Uniformization, and Lusin–Suslin {#sec:separation-uniformization-lusin-souslin}

<!-- formalization: skip-begin (chapter motivation and declaration of proof scope) -->
§{sec:analytic-sets-suslin-schemes} built the analytic class and its
\termuseas{Suslin-scheme representation theorem}{Suslin-scheme representation}.
This chapter first develops three analytic-side tools:
\termforwardas{Lusin separation theorem}{Lusin separation},
\termforwardas{Jankov--von Neumann uniformization theorem}{Jankov--von Neumann uniformization}, and the
\termforward{Lusin--Suslin theorem}. These results supply the working infrastructure for later chapters.
We then turn to the projective hierarchy, scales and Kondo uniformization, and the regularity boundary.

Proof scope: Lusin separation, Jankov--von Neumann uniformization, and the Lusin--Suslin prefix-separation argument
are proved here. The Kondo proof constructs a selector by successive minima and proves that its graph is coanalytic.
It uses the cited scale-existence, closure, and norm-comparison machinery. The full projective-scale theory and the
broader regularity boundary remain external background, with sources identified where used.
<!-- formalization: skip-end -->

## Lusin Separation and Uniformization {#sec:lusin-separation-uniformization}

<!-- formalization: skip (section lead-in) -->
Before proving Lusin--Suslin, we isolate two analytic-side tools that recur throughout the rest of the text. Each
replaces an analytic obstruction by something more tractable: a Borel separator from a disjoint analytic set, or a
definable choice of witnesses inside an analytic relation. The companion topological tool — Polish-topology
refinement — is collected separately in §{sec:polish-embeddings-refinements}.

### Lusin separation {#sec:lusin-separation}

\begin{mathmeta}
  \vars{s,t}{Seq(Nat)}
  \vars{p,p_*}{Name}
  \vars{n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
局所主張であるdisjoint analytic setsのBorel分離はlusinSeparationへ接続済み。
未リンク部分は前章の引用付きanalytic non-Borel例を振り返る導入で、ここで新たに非Borel性の証明を提示していない。)
--> \termforwardas{Lusin separation theorem}{Lusin separation} says that analytic sets need not be Borel, but<!--
formalization: skip-end
-->  two disjoint
analytic sets can still be pulled apart by a Borel set.

\begin{theorem*}[\termdefineas{Lusin separation theorem}{Lusin separation}] If $A_0,A_1\IncludedIn X$ are disjoint
analytic subsets of a Polish space, then there is a Borel set $B\IncludedIn X$ such that
$$A_0\IncludedIn B\IncludedIn \SetDifference{X}{A_1}.$$

\end{theorem*}

\begin{proof}[Proof] Put $C:=\SetDifference{X}{A_1}$. We construct a rank $\rho:C\to\omegaOneOrd$ whose initial segments
$$C_{\le\alpha}:=\{x\in C:\rho(x)\le\alpha\}$$
are Borel for countable $\alpha$, and then find one that contains $A_0$.

By the \termuse{closed-projection characterization of analytic sets}, choose a closed set
$F\IncludedIn X\times\BaireSpace$ whose projection is $A_1$, and fix a compatible metric on $X$.
Retain the empty root and define
$$
T_x:=\{\emptySeq\}\cup\left\{s\in\finseq{\omega}:F\cap
\left(\Ball{x}{2^{-\Length{s}}}\times\cyl{s}\right)\ne\emptyset\right\}.
$$
These are trees: passing to an initial segment enlarges both the ball and the cylinder. The added root creates no
infinite branch. For nonempty $s$, the membership set is open, since
$$
\{x:s\in T_x\}
=\bigcup_{\substack{\Pair{y}{p}\in F\\p\in\cyl{s}}}\Ball{y}{2^{-\Length{s}}}.
$$
For the empty word it is all of $X$. Thus the map sending $x$ to the indicator code of $T_x$ is Borel.

We have
$$x\in C\quad\Longleftrightarrow\quad T_x\text{ is well-founded}.$$
Indeed, a witness $\Pair{x}{p}\in F$ gives a branch through $T_x$. Conversely, from a branch $p$ choose, for $n\ge1$,
$$
\Pair{x_n}{p_n}\in F\cap\left(\Ball{x}{2^{-n}}\times\cyl{\restrict{p}{n}}\right).
$$
The first coordinates converge to $x$ because their distances are less than $2^{-n}$, and every coordinate of $p_n$
eventually agrees with that of $p$. Hence $\Pair{x_n}{p_n}\to\Pair{x}{p}$, and closedness of $F$ gives $\Pair{x}{p}\in
F$.

For $x\in C$, define $\rho(x)$ to be the rank of the root of $T_x$. This rank is countable: every ordinal below a node
rank occurs as the rank of some node, by induction using the defining supremum of successor ranks, and the tree has
only countably many nodes.

\begin{mathmeta}
  \define{OrdinalRankLayer}
\end{mathmeta}
To prove Borelness of the rank layers directly, let $E_x(t,s)$ mean that $s,t\in T_x$ and $s\properPrefixOf t$.
For each fixed pair of words, the edge event $E_{t,s}:=\{x:E_x(t,s)\}$ is Borel, because the two node-membership
conditions are open. Treat words outside the tree as isolated nodes of this relation. Define
$\OrdinalRankLayer{\alpha}{s}$ to consist of the $x$ for which the relation below $s$ is well founded and its rank at
$s$ is at most $\alpha$. Then
$$
\OrdinalRankLayer{\alpha}{s}
=\bigcap_{t\in\finseq{\omega}}\left(
E_{t,s}^{\complement}\cup\bigcup_{\beta<\alpha}\OrdinalRankLayer{\beta}{t}\right).
$$

For the forward inclusion, a predecessor in the relation has rank strictly below the rank at $s$, so its
rank itself supplies a bound $\beta<\alpha$. Conversely, if every predecessor has a well-founded relation below it,
then the same holds at $s$. If each predecessor rank is at most some $\beta<\alpha$, the successor ordinal of each
predecessor rank
is at most $\alpha$, so their supremum is at most $\alpha$. This proves the recursion, including $\alpha=0$, when the
inner union
is empty. Transfinite induction now makes every $\OrdinalRankLayer{\alpha}{s}$ Borel for countable $\alpha$: the set
of smaller ordinals and the set of words are both countable. In particular,
$$C_{\le\alpha}=\OrdinalRankLayer{\alpha}{\emptySeq}$$
is Borel. This argument uses no separation theorem.

If $D\IncludedIn C$ is analytic, the Borel-image characterization in §{sec:analytic-sets} makes the set of codes of
$\{T_x:x\in D\}$ analytic. These trees are well founded, so the
\termuse{boundedness theorem for well-founded trees}, proved in §{sec:edst-boundedness}, gives a countable ordinal
$\alpha$ bounding all their root ranks. Thus $D\IncludedIn C_{\le\alpha}$.

Finally, disjointness gives $A_0\IncludedIn C$. Apply this bound to the analytic set $A_0$ and set $B:=C_{\le\alpha}$.
Then $B$ is Borel, contains $A_0$, and is contained in $C=\SetDifference{X}{A_1}$.
\end{proof}

Equivalently, disjoint analytic sets are \termdefine{Borel separable}. <!--
formalization: skip-begin (引用・背景説明・読書案内:
Borel separableの定義は既存リンクで対応済み。残りは分離定理の有用性を述べる一般的な動機付けで、追加の定理や局所的証明を主張していない。)
--> This is one of the main reasons analytic sets
remain usable even when they are not themselves Borel: an analytic obstruction can often be replaced by a Borel
separator once it is disjoint from the object one wants to keep.<!--
formalization: skip-end
-->

The theorem supplies the separation step in the proof of \termuse{Suslin's theorem} from §{sec:analytic-sets}. If $A$
is both analytic and coanalytic, then $A$ and $\SetDifference{X}{A}$ are disjoint analytic sets; separating $A$ from
$\SetDifference{X}{A}$ gives a Borel set squeezed between them, hence exactly $A$.

<!-- formalization: skip (pointer to the later effective version) -->
In later effective arguments, especially §{sec:edst-coanalytic-ranks-silver}, the same proof is repeated with recursive
rank bounds attached. That is the form needed for Silver's dichotomy.

### Uniformization {#sec:uniformization}

\begin{mathmeta}
  \vars{i,j,n,p}{Nat}
\end{mathmeta}

Projection loses witnesses: from $x\in\pi_X(A)$ one knows only that some $y$ satisfies $\Pair{x}{y}\in A$. A
\termdefine{uniformization} restores witnesses by choosing one such $y$ for each $x$ in the projection.

For $A\IncludedIn X\times Y$, a map $u:\pi_X(A)\to Y$ uniformizes $A$ if
$$
\Pair{x}{u(x)}\in A \qquad (x\in\pi_X(A)).
$$

\begin{theorem*}[\termdefineas{Jankov--von Neumann uniformization theorem}{Jankov--von Neumann uniformization}] If
$A\IncludedIn X\times Y$ is analytic, where $X$ and $Y$ are Polish, then $A$ admits a uniformizing function
$$u:\pi_X(A)\to Y$$
whose graph is contained in $A$ and which is measurable with respect to the $\sigma$-algebra generated by analytic
subsets of $X$.

\end{theorem*}

<!-- formalization: skip (application guidance following the theorem statement) -->
In particular, after restricting to suitable Borel or analytic pieces in applications, the theorem supplies definable
partial choices.

\begin{proof}[Proof] Let $D:=\pi_X(A)$. By the
\termuse{closed-projection characterization of analytic sets}, there is a closed set
$$C\IncludedIn X\times Y\times\BaireSpace$$
whose projection to $X\times Y$ is $A$. Put $Z:=Y\times\BaireSpace$, with any complete compatible metric.
It is enough to choose, for each $x\in D$, a point $z=\Pair{y}{p}\in Z$ such that $\Pair{x}{z}\in C$; then $u(x):=y$
uniformizes
$A$.

Fix a countable basis $\{W_i:i\in\omega\}$ for $Z$. This basis has arbitrarily small refinements whose closures stay
inside a prescribed open set: given an open set $W$, a point $z\in W$, and $\epsilon>0$, choose $r>0$ such that
$\Ball{z}{2r}\IncludedIn W$ and $2r<\epsilon$. Choose $W_i$ with $z\in W_i\IncludedIn\Ball{z}{r}$. Then
$\Closure{W_i}\IncludedIn\Closure{\Ball{z}{r}}\IncludedIn\Ball{z}{2r}\IncludedIn W$ and
$\Diameter{W_i}\le 2r<\epsilon$. We build, for each $x\in D$, a nested sequence
$$
Z=U_0(x)\supseteq \Closure{U_1(x)}\supseteq U_1(x)\supseteq \Closure{U_2(x)}\supseteq\cdots
$$
with $\Diameter{U_n(x)}<2^{-n}$ for $n\ge 1$ and
$$C_x\cap U_n(x)\ne\emptyset,$$
where $C_x:=\{z\in Z:\Pair{x}{z}\in C\}$.

Assume $U_n(x)$ has been chosen. Let $i_{n+1}(x)$ be the least index $i$ such that
$$
\Closure{W_i}\IncludedIn U_n(x),\qquad
\Diameter{W_i}<2^{-(n+1)},\qquad
C_x\cap W_i\ne\emptyset,
$$
and put $U_{n+1}(x):=W_{i_{n+1}(x)}$. We record the index itself, since different indices may name the same basis
set.

Such a $W_i$ exists: choose $z^*\in C_x\cap U_n(x)$ and then use the refinement property to find an eligible $W_i$
containing $z^*$. The closures $\Closure{U_n(x)}$ are nested nonempty closed sets with diameters tending to $0$ in a
complete space, so their intersection is a singleton. Call it $z(x)$. To see that $z(x)\in C_x$, choose
$z_n\in C_x\cap U_n(x)$. The nesting and diameter bounds force $z_n\to z(x)$, and $C_x$ is closed.

It remains to check the promised measurability. Let
$$
E(O):=\{x\in X:C_x\cap O\ne\emptyset\},
$$
where $O\IncludedIn Z$ is open. Each $E(O)$ is analytic, because it is the projection to $X$ of the Borel set
$C\cap(X\times O)$.

For $n\ge 1$ and $i\in\omega$, put
$$D_{n,i}:=\{x\in D:i_n(x)=i\}.$$
We prove by induction on $n$ that these decision sets belong to the $\sigma$-algebra generated by analytic subsets of
$X$. Let $P_{n,i}\IncludedIn D$ be the set of points for which index $i$ is eligible at stage $n$. Initially,
$P_{1,i}=E(W_i)$ if $\Diameter{W_i}<2^{-1}$, and $P_{1,i}=\emptyset$ otherwise. Thus all the initial eligibility sets
are measurable. At later stages,
$$
P_{n+1,i}=E(W_i)\cap
\bigcup_{\substack{j\in\omega\\\Closure{W_i}\IncludedIn W_j\\\Diameter{W_i}<2^{-(n+1)}}}D_{n,j}.
$$
This is a countable union of measurable sets intersected with an analytic set, so it is measurable whenever the
previous decision sets are. At every stage, the least-index rule gives the finite exclusion formula
$$
D_{n,i}=\SetDifference{P_{n,i}}{\bigcup_{k<i}P_{n,k}}.
$$
This proves the induction. For a finite history $s=\Tuple{j_1,\ldots,j_n}$, the set
$$D_s:=\{x\in D:i_1(x)=j_1,\ldots,i_n(x)=j_n\}=\bigcap_{k=1}^n D_{k,j_k}$$
is therefore measurable as well; the empty history gives $D_\emptyset=D$, which is analytic.

For an open set $O\IncludedIn Z$,
$$
z^{-1}(O)=\bigcup\{\,D_{n,i}: n\ge 1,\ i\in\omega,\ \Closure{W_i}\IncludedIn O\,\}.
$$
The inclusion from right to left follows from $z(x)\in\Closure{U_n(x)}$. Conversely, if $z(x)\in O$, then some ball
around $z(x)$ is contained in $O$; for all sufficiently large $n$, the nested closed set $\Closure{U_n(x)}$ has diameter
small enough and contains $z(x)$, so $\Closure{U_n(x)}\IncludedIn O$. The right-hand side is a countable union of the
measurable decision sets $D_{n,i}$, so $z$ is measurable for the analytic-generated $\sigma$-algebra on $D$. Composing
$z(x)=\Pair{y(x)}{p(x)}$ with the first projection gives the required uniformizing function $u(x)=y(x)$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Borel構造が同じなら固定した写像の可測性が同値になる局所的主張はmeasurable_iff_of_borel_eqへ狭く接続した。
未リンク部分はJvNのanalytic-generated measurabilityとBorel selectorの一般的な適用範囲、
および分離定理との比較で、新しい具体的反例や選択構成の証明を提示していない。)
--> The theorem does not in general give a Borel selector on the whole projection; additional hypotheses on the relation
and its sections are needed.<!--
formalization: skip-end
-->  In particular, a Borel-preserving topology refinement cannot turn a non-Borel selector
into a Borel map, since it leaves the Borel sets unchanged. <!--
formalization: skip-begin (引用・背景説明・読書案内:
Borel構造が同じなら固定した写像の可測性が同値になる局所的主張はmeasurable_iff_of_borel_eqへ狭く接続した。
未リンク部分はJvNのanalytic-generated measurabilityとBorel selectorの一般的な適用範囲、
および分離定理との比較で、新しい具体的反例や選択構成の証明を提示していない。)
--> Lusin separation gives Borel separators for disjoint
analytic sets, but does not by itself upgrade the measurability of the selector.<!--
formalization: skip-end
-->

<!-- formalization: skip (transition to the countable-section theorem) -->
For Borel relations, countability of the sections gives Borel choices that enumerate every section. This is used
later in Feldman--Moore's representation theorem for countable Borel equivalence relations.

<!-- formalization: skip (countable-section decomposition quoted from Kechris; local deductions remain in scope) -->
\begin{theorem*}[\termdefineas{Lusin--Novikov uniformization theorem}{Lusin--Novikov uniformization}] Let $X,Y$ be
standard Borel spaces and let $A\IncludedIn X\times Y$ be Borel. If every vertical section
$$A_x:=\{y\in Y:\Pair{x}{y}\in A\}$$
is countable, then there are partial Borel functions
$$\PartialFunctionMap{f_n}{X}{Y}\qquad(n\in\omega)$$
whose graphs are contained in $A$ and such that
$$A=\bigcup_{n\in\omega}\mathrm{graph}(f_n).$$
Equivalently, every Borel relation with countable vertical sections admits a Borel enumeration of its sections, allowing
repetitions or undefined values where the section is finite.

\end{theorem*}

\begin{proof}[Proof from the decomposition lemma] Reduce first to the case $X,Y$ are Polish spaces with their
Borel $\sigma$-algebras,
by the definition of a standard Borel space in §{sec:standard-borel-spaces}. The nontrivial step
is the Lusin--Novikov decomposition lemma: a Borel set $B\IncludedIn X\times Y$ with countable vertical sections can be
split into countably many Borel pieces, each having at most one point in every vertical section. Equivalently, $B$ is a
countable union of graphs of partial Borel functions.

<!-- formalization: skip-begin (external input or explanatory background) -->
The decomposition lemma is an imported theorem here; its proof is given in [@Kechris1995, §18]. It is stronger
than ordinary one-point selection. A Jankov--von Neumann selector need not be Borel, and repeatedly choosing unused
points need not exhaust an infinite countable section. Countability of a section also does not imply that its points
can be isolated by basic open neighborhoods. The decomposition lemma supplies Borel pieces with singleton sections
without making that topological assumption.
<!-- formalization: skip-end -->


Applying this decomposition lemma to $A$ gives Borel sets $G_n\IncludedIn A$ whose vertical sections have size at most
one and whose union is $A$. For each $n$, let
$$D_n:=\pi_X(G_n).$$
The first projection is injective on $G_n$. The Lusin--Suslin theorem in §{sec:lusin-souslin-theorem} therefore makes
$D_n$ Borel and the inverse $D_n\to G_n$ Borel. Composing that inverse with the second projection gives the unique
Borel map $f_n:D_n\to Y$ with graph $G_n$. Since the pieces cover $A$, these partial Borel functions satisfy
$$A=\bigcup_n \mathrm{graph}(f_n).$$
\end{proof}

<!-- formalization: skip-begin (comparison with one-point uniformization and transition to Lusin--Suslin) -->
The theorem is stronger than ordinary uniformization: it does not merely choose one witness from each nonempty section,
but enumerates all witnesses in a Borel-uniform way. This is why it is the correct input for countable Borel equivalence
relations in §{sec:countable-borel-er-hyperfinite}: a countable class can be covered by countably many Borel partial
maps.

In the proof of Lusin--Suslin below, injectivity supplies a different kind of uniformity: the witness in the source is
unique once the image point is known. The proof exploits that uniqueness by using the
\termuse{Lusin separation theorem} to build Borel tests for the finite prefixes of that source witness.
<!-- formalization: skip-end -->

## The Lusin–Suslin Theorem {#sec:lusin-souslin-theorem}

<!-- formalization: skip-begin (theorem motivation and spelling convention) -->
The analytic class gives one half of a sharp dichotomy: the continuous (or Borel) image of a Borel set is in general
only analytic, and analytic sets that are not Borel genuinely exist in every uncountable Polish space. The
\termforwardas{Lusin--Suslin theorem}{Lusin–Suslin theorem} supplies the other half: *injectivity* is
a sufficient hypothesis for the image to be Borel.

The theorem is also commonly spelled **Lusin–Souslin** in the literature. We use Lusin–Suslin throughout, matching
the spelling used for Suslin schemes and Suslin's theorem above.
<!-- formalization: skip-end -->

### Statement {#sec:lusin-souslin-statement}

\begin{theorem*}[\termdefineas{Lusin--Suslin theorem}{Lusin–Suslin}] Let $X$ and $Y$ be Polish spaces and
$f : X \to Y$ a Borel-measurable map. If $f$ is injective on a Borel set $B \IncludedIn X$, then $f(B)$ is Borel in
$Y$, and the restriction $f|_B : B \to f(B)$ is a Borel isomorphism.
\end{theorem*}

\begin{corollary*}[Continuous form] A continuous injection from a Polish space into a Polish space has Borel image and
is a Borel isomorphism onto that image.
\end{corollary*}

### Why It Matters {#sec:lusin-souslin-why-matters}

<!-- formalization: skip (applications introduction) -->
This single theorem underwrites a remarkable amount of standard practice:

*   It is the engine of the *Borel Schröder–Bernstein theorem* used in the proof of Kuratowski's isomorphism theorem
    in §{sec:kuratowski-isomorphism}: the two Borel injections produced there have Borel images precisely by
    Lusin–Suslin.
*   A *Borel section* of a Borel map between standard Borel spaces has Borel range: as a right inverse,
    it is injective, so Lusin--Suslin applies. The chosen representatives therefore form a standard Borel subspace.
*   It is the reason a *Borel bijection* between Polish spaces is automatically a Borel isomorphism — its inverse is
    Borel for free, with no need to construct it explicitly.

### Proof {#sec:lusin-souslin-proof}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{j,k}{Nat}
  \vars{s,t,s_*}{Seq(Nat)}
  \vars{x,x_*}{Name}
  \vars{F}{Set(Name)}
  \vars{\iota}{Fun(Seq(Nat),Nat)}
\end{mathmeta}

<!-- formalization: structural (proof roadmap only) -->
\begin{proof}[Proof]
The proof has two halves: a reduction to the case of a continuous injection on a closed subspace of $\BaireSpace$, and a
separated-prefix construction within that case.

\paragraph*{Reduction}

The following changes of presentation preserve the relevant Borel structures, and Borelness of the image is
invariant under such changes. The topology-refinement results are those developed in
§{sec:polish-embeddings-refinements}.

Given $f:X\to Y$ Borel and injective on the Borel set $B\IncludedIn X$, choose a countable open base
$\Sequence{V_n}{n\in\omega}$ of $Y$. Apply \termuse{Kuratowski's refinement theorem} to the Borel family
$$C_0:=B,\qquad C_{n+1}:=f^{-1}(V_n)\quad(n\in\omega).$$
In the refined Polish topology, $B$ is clopen and $f$ is continuous, because the inverse images of the basic open
sets are open. Restricting to $B$ therefore gives a continuous injection on a Polish space.

By \termuse{closed presentation in Baire space} in §{sec:closed-presentation-baire}, there are a closed set
$F\IncludedIn\BaireSpace$ and a continuous Borel isomorphism $e:F\to B$. Compose the restricted map with $e$.
Refinement preserves the Borel $\sigma$-algebra of the source, and $e$ preserves both the image and injectivity.
It therefore suffices to prove the image assertion for a closed set $F\IncludedIn\BaireSpace$ and a continuous
injection $f:F\to Y$.

\paragraph*{Separated prefix tests}

If $F=\emptyset$, then both the image and inverse claims are immediate. Otherwise, take $F\IncludedIn\BaireSpace$
closed and nonempty, let $f:F\to Y$ be continuous and injective, and fix a compatible metric $d_Y$ on $Y$. For each
finite sequence $s\in\finseq{\omega}$ put
$$
A_s := f(F\cap\cyl{s}).
$$
Each $A_s$ is analytic. For a fixed length $k\ge 1$, the family $\{A_s:s\in\funcspace{k}{\omega}\}$ is pairwise
disjoint, because the cylinders of length $k$ are disjoint and $f$ is injective.

Fix an injective numbering $\iota:\finseq{\omega}\to\omega$ of finite sequences. For each $s$, the union
$$\bigcup_{\substack{\Length{t}=\Length{s}\\t\ne s}}A_t$$
is analytic: countable unions of analytic sets are analytic, as one sees by presenting each summand as a continuous
image of a Polish space and taking their countable disjoint sum. This union is disjoint from $A_s$.
The \termuse{Lusin separation theorem} therefore gives a Borel set $C_s$ containing $A_s$ and disjoint from every
$A_t$ with $\Length{t}=\Length{s}$ and $t\ne s$.

For $\Length{s}=k\ge1$, put
$$B_s^k:=\SetDifference{C_s}{\bigcup_{\substack{\Length{t}=k\\\iota(t)<\iota(s)}}C_t}.$$
Only finitely many terms occur in this union, since $\iota$ is injective. No removed set meets $A_s$, so
$A_s\IncludedIn B_s^k$. The sets $B_s^k$ are pairwise disjoint at each fixed level: if
$\iota(s)<\iota(t)$, then $B_t^k$ misses $C_s$, which contains $B_s^k$. All these sets are Borel.

Make the tests compatible along prefixes by setting, for $\Length{s}=k\ge 1$,
$$
H_s := \bigcap_{1\le j\le k} B_{\restrict{s}{j}}^j.
$$
Then $A_s\IncludedIn H_s$, the sets $H_s$ at a fixed level are pairwise disjoint, and $t\extendsPrefix s$ implies
$H_t\IncludedIn H_s$. Finally put
$$
O_s := \bigcup_{x\in F\cap\cyl{s}}\Ball{f(x)}{2^{-\Length{s}}}.
$$
This is an open neighborhood of $A_s$ in $Y$.

\paragraph*{The image is Borel}

We claim
\begin{equation*}
f(F)
\;=\;
\bigcap_{k\ge 1}\,
\bigcup_{s\in\funcspace{k}{\omega}}
\left(H_s\cap O_s\right).
\tag{$\dagger$}
\end{equation*}
The right-hand side is Borel because it is a countable intersection of countable unions of Borel sets.

\emph{($\IncludedIn$).} If $y=f(x)$ with $x\in F$, then for each $k\ge 1$ the prefix $s=\restrict{x}{k}$ satisfies $y\in
A_s\IncludedIn H_s\cap O_s$. Thus $y$ lies in the right-hand side of $(\dagger)$.

\emph{($\supseteq$).} Let $y$ lie in the right-hand side. For each $k\ge 1$, choose $s_k\in\funcspace{k}{\omega}$ with
$y\in H_{s_k}\cap O_{s_k}$. The prefix tests make this sequence unique and compatible. Indeed, the sets $H_s$ at level
$k$ are pairwise disjoint, so there is at most one such $s_k$; and since $H_{s_{k+1}}\IncludedIn
H_{\restrict{s_{k+1}}{k}}$, disjointness at level $k$ forces $s_k=\restrict{s_{k+1}}{k}$.

Let $x:=\bigcup_k s_k\in\BaireSpace$. Since $y\in O_{s_k}$, choose $x_k\in F\cap\cyl{s_k}$ with
$$
d_Y(f(x_k),y)<2^{-k}.
$$
The compatibility of the prefixes gives $x_k\to x$ in $\BaireSpace$, and closedness of $F$ gives $x\in F$. Continuity
gives $f(x_k)\to f(x)$, while the displayed inequality gives $f(x_k)\to y$. Limits are unique in the metric space $Y$,
so $y=f(x)$. This proves $(\dagger)$, and consequently $f(F)$ is Borel.

\paragraph*{Borelness of the inverse}

<!-- formalization: structural (proof goal only) -->
We show $f^{-1} : f(F) \to F$ is Borel by showing that the preimage of each open set in $F$ is Borel in $f(F)$.

It suffices to handle a basic clopen $\cyl{t} \cap F$ with $t \in \finseq{\omega}$. The set $F \cap \cyl{t}$ is closed
in $\BaireSpace$, and the restriction
$$
f|_{F\cap\cyl{t}}:F\cap\cyl{t}\to Y
$$
is again continuous and injective. Applying the image part of the closed-subspace case just proved to this restriction
shows that $f(F\cap\cyl{t})$ is Borel in $Y$. Since
$$
(f^{-1})^{-1}(\cyl{t} \cap F)=f(F\cap\cyl{t}),
$$
the preimage of every basic clopen of $F$ under $f^{-1}$ is Borel. The basic clopens generate the Borel $\sigma$-algebra
of $F$, so $f^{-1}$ is Borel.

Returning to the original Borel domain $B$, every Borel subset of $B$ is Borel in $X$. Apply the image conclusion
to each such subset. Since its image is the inverse image of that subset under $(f|_B)^{-1}$, the inverse on $f(B)$
is Borel. Thus $f|_B$ is a Borel isomorphism.
\end{proof}

### Sharpness {#sec:lusin-souslin-sharpness}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
分離可能距離化可能な余域への拡張、密着位相の恒等単射による反例、standard Borel sourceで十分という局所的主張を、
それぞれ実際の埋め込み・Borel sigma algebra・Polish presentationの証明へ狭く接続した。
未リンク部分は既存のanalytic
representationによる非Borel像の注意とKechris/Moschovakisへの文献案内のみで、新しい局所的構成を置いていない。)
--> Injectivity is sharp: there is a continuous surjection $\BaireSpace\twoheadrightarrow A$ onto any analytic non-Borel
set $A$.<!--
formalization: skip-end
-->  The codomain hypothesis can be relaxed from Polish to separable metrizable by embedding the codomain into a
Polish space. For arbitrary topological codomains, however, the conclusion can fail even though Borelness remains
well-defined. For example, give an uncountable Polish space $X$ the indiscrete topology in the codomain. The identity
from the original Polish $X$ to this codomain is Borel and injective, but the image of a nontrivial Borel subset of $X$
is not Borel in the indiscrete codomain. What the proof fundamentally uses on the source side is its standard Borel
structure. <!--
formalization: skip-begin (引用・背景説明・読書案内:
分離可能距離化可能な余域への拡張、密着位相の恒等単射による反例、standard Borel sourceで十分という局所的主張を、
それぞれ実際の埋め込み・Borel sigma algebra・Polish presentationの証明へ狭く接続した。
未リンク部分は既存のanalytic
representationによる非Borel像の注意とKechris/Moschovakisへの文献案内のみで、新しい局所的構成を置いていない。)
--> A non-effective textbook proof is given in [@Kechris1995, §15], and a development together with the broader
machinery of effective descriptive set theory is in [@Moschovakis2009, §2E].<!--
formalization: skip-end
-->

<!-- formalization: skip (first-pass route after Lusin--Suslin) -->
For a first pass through standard Borel theory, continue now to
§{sec:standard-borel-classification-closed-sets}. The separation, uniformization, and Lusin--Suslin results
above supply its analytic-side prerequisites. The remaining sections develop the projective hierarchy, scales,
and stronger uniformization results; return to them for the determinacy and regularity route.

## The Projective Hierarchy {#sec:projective-hierarchy}

<!-- formalization: skip-begin (orientation definition and classical strictness theorem cited to the literature) -->
Iterating projection and complementation yields the **\termdefine{projective hierarchy}**, defined recursively for $n
\ge 1$:

*   $\bSigma^1_1(X)$ = analytic sets.
*   $\bPi^1_n(X)$ = complements of $\bSigma^1_n(X)$ sets.
*   $\bSigma^1_{n+1}(X)$ = projections to $X$ of $\bPi^1_n(X \times \BaireSpace)$ sets.
*   $\bDelta^1_n(X) = \bSigma^1_n(X) \cap \bPi^1_n(X)$.

A set is \termdefineas{projective set}{projective} if it lies in $\bigcup_{n\ge 1} \bSigma^1_n(X)$. As with the Borel
hierarchy, this stratification is strict in any uncountable Polish space: each new level contains genuinely new sets
[@Kechris1995, §37].
<!-- formalization: skip-end -->

## Scales and $\bPi^1_1$ Uniformization {#sec:scales-pi11-uniformization}

\begin{mathmeta}
  \vars{n,p}{Nat}
\end{mathmeta}


<!-- formalization: skip-begin (external input or explanatory background) -->
Projection creates witnesses, and complementation hides them.
\termforwardas{descriptive-set-theoretic scale}{Scales} are the standard device for recovering enough ordinal structure
from a projective set to run recursive choices, comparison arguments, and
\termuse{uniformization}.

Let $A\IncludedIn X$ be a subset of a Polish space. A \termdefineas{descriptive-set-theoretic scale}{scale} on $A$ is a
sequence of norms
$$\varphi_n:A\to\mathrm{Ord}\qquad(n\in\omega)$$
with a closure property: whenever $x_k\in A$ converges to $x\in X$ and each sequence $\varphi_n(x_k)$ is eventually
constant, then $x\in A$ and
$$\varphi_n(x)\le\lim_k\varphi_n(x_k)$$
for every $n$. In practice the norms are required to be definable in the pointclass under discussion, so that
comparisons such as
$$\varphi_n(x)\le\varphi_n(y)$$
remain projectively controlled.

The basic example is coanalytic. If $A\IncludedIn X$ is $\bPi^1_1$, reduce membership in $A$ to well-foundedness of a
tree:
$$
x\in A
\quad\Longleftrightarrow\quad
T_x\text{ is well-founded}.
$$
The ordinal rank of $T_x$ gives a coanalytic norm. Refining the reduction over finite approximations gives a sequence of
such norms, hence a $\bPi^1_1$ scale on $A$. This is the boldface ancestor of the coanalytic ranks used effectively in
§{sec:edst-coanalytic-ranks-silver}.

Scales are not just bookkeeping. They allow one to choose least witnesses without leaving the definability class. The
central theorem at the first coanalytic level is
\termforwardas{Kondo uniformization theorem}{Kondo's uniformization theorem}.
<!-- formalization: skip-end -->

\begin{theorem*}[\termdefineas{Kondo uniformization theorem}{Kondo}] Let $A\IncludedIn X\times Y$ be $\bPi^1_1$, where
$X$ and $Y$ are Polish spaces. Then there is a $\bPi^1_1$ set $G\IncludedIn A$ such that $G$ is the graph of a partial
function and
$$
\DomainOf{G}=\pi_X(A).
$$
Equivalently, every nonempty vertical section $A_x$ has a chosen point $u(x)\in A_x$, and the graph of $u$ is
coanalytic.

\end{theorem*}

\begin{proof}[Proof] First use §{sec:closed-presentation-baire} to replace $Y$ by a closed subspace $F$ of
$\BaireSpace$ through a Borel isomorphism. Analytic and coanalytic sets are preserved under Borel isomorphisms:
analyticity is preserved under Borel images, and bijections commute with complements. Thus we may transfer both the
relation and the eventual uniformizing graph between the two presentations. In this presentation the coordinates
$y(n)$ are defined, and a coordinatewise limit remains in $F$ because $F$ is closed.

Use the cited scale-existence theorem to put a $\bPi^1_1$ scale $\Sequence{\varphi_n}{n\in\omega}$ on $A$.
For fixed $x\in\pi_X(A)$, interleave the ordinal ranks and the natural coordinates as keys
$$h_{2n}(x,y):=\varphi_n(x,y),\qquad h_{2n+1}(x,y):=y(n).$$
View natural numbers as finite ordinals. Starting with $S_0=A_x$, let $a_i$ be the least value of $h_i(x,\cdot)$ on
$S_i$, and put $S_{i+1}:=\{y\in S_i:h_i(x,y)=a_i\}$. Every $S_i$ is nonempty, since a nonempty set of ordinals has a
least member. Choose $q_k\in S_{2k+2}$ for each $k$. Then $q_k(n)$ is constant for $k\ge n$, and
$\varphi_n(x,q_k)=a_{2n}$ for $k\ge n$. The points $q_k$ converge coordinatewise to a point $y\in F$.
The scale closure property gives $\Pair{x}{y}\in A$ and $\varphi_n(x,y)\le a_{2n}$ for every $n$.
Induction on $i$ now proves $h_i(x,y)=a_i$: the coordinate equalities follow from convergence, while at a rank step
the preceding equalities put $y$ in $S_i$, so minimality gives the reverse inequality. Thus $y$ realizes every
successive minimum. Two points realizing every successive minimum have equal keys by induction and hence equal
coordinates, so this point is unique.

We verify the complexity of this construction rather than assuming that the graph of successive minima has the
required complexity. The cited norm-comparison machinery supplies analytic relations $L_n$ and coanalytic relations
$P_n$ such that, whenever $\Pair{x}{y}\in A$,
$$\begin{aligned}
L_n(x,z,y)&\Longleftrightarrow
 \Pair{x}{z}\in A\ \land\ \varphi_n(x,z)\le\varphi_n(x,y)\\
&\Longleftrightarrow P_n(x,z,y).
\end{aligned}$$
For points in the same section of $A$, equality of the $n$th ranks is expressed analytically by
$L_n(x,z,y)\land L_n(x,y,z)$, and strict inequality by
$L_n(x,z,y)\land\neg P_n(x,y,z)$. Coordinate equality and strict inequality are Borel.
For each $i$, let $B_i$ consist of the triples $\Tuple{x,y,z}$ satisfying $L_0(x,z,y)$, equality of the keys before $i$
through these tests, and strict inequality of the $i$th key. Each $B_i$ is analytic.
For $\Pair{x}{y}\in A$, its witnesses are exactly the points $z\in A_x$ with the same earlier keys and a smaller $i$th
key:
the $L_0$ condition ensures membership in $A_x$, and it is automatic for such a competitor, either by the smaller
zeroth key or by equality of that key. Hence
$$G:=\SetDifference{A}{\bigcup_{i\in\omega}\{\Pair{x}{y}:\exists z\ \Tuple{x,y,z}\in B_i\}}$$
is coanalytic. Its points are precisely those realizing every successive minimum. The existence and uniqueness
already proved show that $G$ is a graph contained in $A$ with domain $\pi_X(A)$.
Only scale existence, its closure property, and the analytic/coanalytic norm comparisons are imported inputs.
\end{proof}

<!-- formalization: skip-begin (external input or explanatory background) -->
Full proofs of that imported scale machinery appear in [@Kechris1995, §35; @Moschovakis2009, Ch. 4].

This should be compared with Jankov--von Neumann uniformization in §{sec:uniformization}. Jankov--von Neumann starts
with an analytic relation and gives a selector measurable for the analytic-generated $\sigma$-algebra. Kondo starts with
a coanalytic relation and gives a coanalytic graph. This is the point of \termdefine{coanalytic uniformization}:
coanalytic ranks supply enough ordinal control to make the choice definable at the same projective level.
<!-- formalization: skip-end -->


## Regularity and Independence {#sec:regularity-independence}

Let $A$ be a subset of a topological space $X$. The set $A$ has the \termdefine{Baire property} if there is an open set
$U\IncludedIn X$ such that
$$
(\SetDifference{A}{U})\cup(\SetDifference{U}{A})
$$
is \termuseas{meager set}{meager}. Equivalently, $A$ differs from an open set by a meager set.

<!-- formalization: skip-begin (classical regularity and independence survey, cited to the literature and determinacy
  chapter) -->
Analytic sets enjoy strong regularity properties, all provable in ZFC:

*   **Lebesgue measurability**: every analytic subset of $\seqPower{\R}{n}$ is Lebesgue measurable.
*   **Baire property**: every analytic set has the \termuse{Baire property}.
*   **Perfect set property**: every uncountable analytic set contains a perfect subset, hence has cardinality
    $2^{\alephNull}$. This extends the \termuseas{cardinality dichotomy}{Cantor–Bendixson dichotomy} from closed sets
    to analytic sets.

Coanalytic sets also have the Baire property and, in Euclidean spaces, are Lebesgue measurable: both properties
are preserved under complements. The perfect set property does not follow by complementation. At higher projective
levels, ZFC no longer guarantees all these regularity properties; the precise boundaries depend on the property.
For example, relative to the consistency of ZFC with an inaccessible cardinal, the statement that every projective
set of reals is Lebesgue measurable is independent of ZFC. In the constructible universe there are nonmeasurable
projective sets, whereas Solovay's construction from an inaccessible cardinal gives a model of ZFC in which all
projective sets are measurable [@Solovay1970, Theorem 2]. This is an application of a
\termforwardas{large cardinal axiom}{large-cardinal} assumption.
Solovay also obtains a model of ZF with dependent choice in which every set of reals is Lebesgue measurable
[@Solovay1970, Theorem 1]. This latter model does not satisfy the full axiom of choice, which implies the existence
of nonmeasurable sets. The systematic treatment of projective regularity under determinacy hypotheses is in
[@Moschovakis2009, Chs. 6–7]; the basic statements and the regularity-via-determinacy mechanism are recorded in
§{sec:determinacy} below.
<!-- formalization: skip-end -->
