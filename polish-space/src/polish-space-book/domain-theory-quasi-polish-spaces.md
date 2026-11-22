# Domain Theory and Quasi-Polish Spaces {#sec:domain-theory-quasi-polish}
\index{quasi-Polish space}

<!-- formalization: skip-begin (chapter synthesis) -->
Domain theory gives a second native language for finite information. TTE names approximate points by streams; domains
approximate points by directed systems of finite observations. The comparison through admissible representations shows
that these are two presentations of the same topological content at the level of represented spaces.

The chapter also widens the scope of descriptive set theory beyond Hausdorff spaces. Many computational spaces are
naturally $T_0$ rather than metrizable in the classical sense, because nontermination and partial information should not
be separated from every completed value by open tests. Quasi-Polish spaces preserve enough of the Polish-space hierarchy
to keep Borel, analytic, and representation-theoretic arguments available in that setting.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter motivation and proof scope) -->
Polish spaces are the topological setting for analysis and probability — Hausdorff, separable, completely metrizable.
\termdefineas{domain theory}{Domain theory}, developed by Dana Scott from 1969 onward as the mathematical
foundation for the denotational semantics of programming languages, is the topological setting for *computation*:
directed-complete partial orders equipped with the \termforward{Scott topology}, where opens encode finitely observable
properties of computational processes. The two appear initially incompatible — Scott topologies on a
typical domain are only $T_0$, while Polish spaces are $T_2$ with trivial specialization order — but they unify
cleanly
through de Brecht's \termforwardas{quasi-Polish space}{quasi-Polish spaces}, a class which carries both classical
descriptive set theory and the computational content of domain theory.

Proof scope: this chapter combines proofs of local results with discussion of external theorems. It develops enough
dcpo, Scott-topological, quasi-Polish,
and representation-theoretic machinery to connect Polish spaces, TTE, and realizability, while the full domain-theoretic
classification theorems and quasi-Polish representation theory remain external references.

The chapter begins with the semantic motivation in §{sec:domains-motivation}, then introduces the order and Scott
topology in §{sec:domains-scott}. The interval domain in §{sec:interval-domain} gives a concrete model of real-number
approximation before §{sec:quasi-polish-spaces} places domains and Polish spaces in a common class. Finally,
§{sec:domains-tte-equivalence} constructs the comparison with TTE through admissible basis-chain names.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Use admissible representations from §{sec:kreitz-weihrauch-admissibility}. For the computational comparison,
read represented maps and name operations in §{sec:type-two-lambda-realizers} and
§{sec:tte-represented-constructions}; compactness, Fourier analysis, and randomness are optional. The
vocabulary of categories and functors is collected in §{sec:cat-basics}, with equivalences in
§{sec:cat-equivalences}; topos logic is not needed yet. Follow the Scott-open examples and interval domain
before the general representation comparison. The goal is to translate finite observations between names and
ordered approximations, and to identify which separation assumptions are relaxed in the quasi-Polish setting.

<!-- formalization: skip-end -->

## Motivation: Denotational Semantics {#sec:domains-motivation}

\begin{mathmeta}
  \forward{DirectedSup,FlatNaturals}
\end{mathmeta}

<!-- formalization: skip-begin (denotational-semantics motivation and external reference) -->
Domain theory was introduced to give recursive programs a mathematical meaning. The denotational semantics of a
programming language assigns to each well-typed term an element of a domain, with three guiding correspondences:

*   **Types as domains.** A type like $\mathtt{Int} \to \mathtt{Int}$ becomes the domain of Scott-continuous functions
    $\FlatNaturals \to \FlatNaturals$, where $\FlatNaturals = \NN \cup \{\bot\}$ is the flat domain encoding "either a
    natural number
    or non-termination."
*   **Recursion as least fixed points.** A recursive definition $f = F(f)$ is solved by the directed supremum
    $\DirectedSup_n F^n(\bot)$, which exists by directed-completeness and is the least fixed point of $F$ when $F$ is
    Scott-continuous.
*   **Approximation as way-below.** $a \ll b$ formalizes "$a$ is a finitely-observable approximation of $b$" — the
    computationally accessible piece of information.

This makes \termuse{domain theory} the standard framework for the semantics of functional programming languages (PCF,
Haskell, ML), and its topological side connects directly to computable analysis [@AbramskyJung1994].
<!-- formalization: skip-end -->

## Domains and the Scott Topology {#sec:domains-scott}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{a,s}{Seq}
\end{mathmeta}
\index{domain}
\index{Scott topology}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
情報の近似順序として領域理論を導入する意味論上の読み方と動機付け。新しい数学的定義・構成・証明ではなく、
有向性・dcpo・way-belowの厳密な定義は直後の別単位でLeanへ接続済み。)
--> \termuseas{domain theory}{Domain theory} is the study of partially ordered spaces of information, ordered by
approximation. The order relation
is read
$$a\sqsubseteq b$$
as "$a$ contains no more information than $b$" or "$b$ refines $a$." A computation is then modeled not as a sequence
converging in a symmetric metric, but as an increasing process that reveals more information over time.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{DirectedSup}
\end{mathmeta}

A subset $S\IncludedIn D$ of a poset $\Pair{D}{\sqsubseteq}$ is \termdefine{directed} if it is nonempty and every finite
subset
has an upper bound in $S$; equivalently, $S$ is nonempty and for every $s,t\in S$ there is $u\in S$ with
$s\sqsubseteq u$ and $t\sqsubseteq
u$. A \termdefine{directed-complete partial order} (dcpo) is a poset in which every directed subset $S$ has a supremum,
written
$$\DirectedSup S.$$
This is the standard domain-theoretic notation for directed suprema, not a disjoint-union notation. The supremum is the
idealized result of accumulating all finite information in $S$.

A dcpo usually carries a least element $\bot$, representing "no information," "undefined," or "non-terminating." The
\termdefine{way-below relation} formalizes finite approximation:
$$
a\ll b
\quad\Longleftrightarrow\quad
\text{for every directed }S,\; b\sqsubseteq\DirectedSup S
\text{ implies }(\exists s\in S)\; a\sqsubseteq s.
$$
Thus $a\ll b$ means that whenever a directed computation eventually reaches enough information to cover $b$, it must
already reach enough information to cover $a$ at some finite stage.

A dcpo $D$ is \termdefineas{continuous dcpo}{continuous} if, for every $b\in D$, the set
$$\{a\in D:a\ll b\}$$
is directed and has supremum $b$. It is \termdefineas{omega-continuous}{$\omega$-continuous} if there is a countable
subset $B\IncludedIn D$ such that, for every $b\in D$, the set $\{a\in B:a\ll b\}$ is directed with supremum $b$. Such a
$B$ is a \termdefineas{domain-theoretic basis}{basis}. In this chapter, a \termdefineas{domain-theoretic domain}{domain}
means a continuous dcpo, and an \termdefineas{omega-continuous domain}{$\omega$-continuous domain} means a continuous
dcpo with a countable basis.

The \termdefine{Scott topology} declares $U \IncludedIn D$ open iff $U$ is upward-closed and inaccessible under directed
suprema:
$$
\DirectedSup S \in U
\;\Longrightarrow\;
S \cap U \ne \emptyset
\quad \text{for every directed } S \IncludedIn D.
$$
Equivalently, a Scott-open set is an observable property: once it holds of a completed value, it must already hold at
some finite approximation.

A function $f:D\to E$ between dcpos is \termdefine{Scott-continuous} if it is monotone and preserves directed suprema:
$$
f(\DirectedSup S)=\DirectedSup f[S]
\qquad(S\IncludedIn D\text{ directed}).
$$
\begin{theorem*}[Scott continuity and topological continuity]
A map between dcpos is Scott-continuous if and only if it is continuous for their Scott topologies.
\end{theorem*}

\begin{proof}
Suppose $f:D\to E$ is monotone and preserves directed suprema. If $U\IncludedIn E$ is Scott-open, then
$f^{-1}[U]$ is upward-closed. If $S\IncludedIn D$ is directed and $f(\DirectedSup S)\in U$, then
$\DirectedSup f[S]\in U$. Since $f[S]$ is directed, some $s\in S$ satisfies $f(s)\in U$.
Thus $f^{-1}[U]$ is Scott-open.

Conversely, suppose $f$ is continuous for the Scott topologies. For any $a\in D$, the principal down-set
$\mathord{\downarrow}a:=\{z\in D:z\sqsubseteq a\}$ is Scott-closed: it is downward-closed, and the supremum of a
directed subset bounded above by $a$ is still below $a$. Consequently, with $U$ ranging over Scott-open sets,
$$
a\sqsubseteq b
\quad\Longleftrightarrow\quad
\forall U,\quad a\in U\Longrightarrow b\in U.
$$
The forward implication uses upward closure; for the converse, if $a\not\sqsubseteq b$, the complement of
$\mathord{\downarrow}b$ is an open set containing $a$ but not $b$. Applying this characterization to inverse images
of opens shows that $f$ is monotone.

Let $S\IncludedIn D$ be directed. Monotonicity makes $f(\DirectedSup S)$ an upper bound of $f[S]$.
If $y\in E$ is any other upper bound, the closed set $f^{-1}[\mathord{\downarrow}y]$ contains $S$ and therefore
contains $\DirectedSup S$. Hence $f(\DirectedSup S)\sqsubseteq y$. This proves that
$f(\DirectedSup S)$ is the least upper bound of $f[S]$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後の有限観測性の説明を導入する案内文「The slogan is:」のみ。
有限観測性の数学的内容はdomain_scott_observableへ別途接続済み。)
--> The slogan is:<!--
formalization: skip-end
-->

*   *Open sets are finitely observable properties.* If a directed supremum has a Scott-open property,
    some member of the directed family already has that property. This is a topological condition; no effective
    enumeration of observations is part of its definition.

Scott topologies are $T_0$. For a nontrivial dcpo with a least element, $\bot$ lies in the closure of every nonempty
subset. Such a space is not $T_1$, and hence is not Hausdorff.

\begin{mathmeta}
  \define{FlatNaturals,PrincipalUp}
\end{mathmeta}
The flat domain $\FlatNaturals := \NN \cup \{\bot\}$ has order
$\bot \sqsubseteq n$ for every $n \in \NN$, with distinct natural numbers incomparable.
Every directed subset has a greatest element. Indeed, if it contains $n\in\NN$, a common upper bound of $n$ and
any other member must be $n$ itself. Otherwise its only member is $\bot$.
Thus the flat domain is a dcpo, and every upward-closed set is Scott-open: a directed supremum already belongs to
the directed set. Its Scott-open sets are exactly the subsets of $\NN$ together with $\FlatNaturals$ itself.
Observing membership in a nontrivial Scott-open set therefore means seeing a completed numerical value; no finite
observation distinguishes nontermination $\bot$ from a computation that has merely not halted yet.

\begin{example*}[\termdefine{Baire prefix domain}]
Let
$$
D_\omega:=\finseq{\omega}\cup\BaireSpace
$$
and order $D_\omega$ by prefix extension:
$$
a\sqsubseteq b\quad\Longleftrightarrow\quad a\prefixOf b.
$$
The empty sequence is the bottom element. We verify directed completeness, the finite-approximation structure,
and the topology on maximal elements explicitly.

Let $S\IncludedIn D_\omega$ be directed. If two members have a value at the same position, their common extension
in $S$ forces those values to agree. Define their union $u$ by giving it a value at a position exactly when some
member has a value there. The positions so defined form an initial segment: a value at a position also supplies
values at all preceding positions. Thus $u$ is a finite or infinite sequence. Every member of $S$ is a prefix of
$u$, and any common extension must contain all its entries. Hence $u=\DirectedSup S$.
If $S$ contains an infinite branch, that branch is its greatest element. Otherwise, a common finite bound on the
lengths makes $u$ finite, whereas unbounded lengths give a value at every position and make $u$ infinite.

For a finite sequence $s$ and any $x\in D_\omega$,
$$
s\ll x\quad\Longleftrightarrow\quad s\prefixOf x.
$$
The forward implication follows by testing the singleton directed family $\{x\}$.
For the reverse implication, suppose $s\prefixOf x\sqsubseteq\DirectedSup S$. Each of the finitely many entries
of $s$ occurs in some member of $S$. Finitely many applications of directedness give a single member containing
them all, and that member extends $s$. If $s$ is empty, any member of the nonempty family suffices.

The finite prefixes of any $x\in D_\omega$ form an increasing family with union $x$.
They are precisely the finite sequences way below $x$, so the finite sequences form a countable domain-theoretic
basis. Moreover, applying the definition of way-below to this family shows that every element way below $x$ lies
below a finite prefix and is itself finite. Thus the family of all approximants is already this directed family of
finite prefixes, and $D_\omega$ is an $\omega$-continuous domain.

The maximal elements are exactly the infinite branches. A finite word has a proper extension, for example by
appending $0$, so it is not maximal. An infinite branch already specifies every entry; any extension must equal it.
Thus the total, or maximal, elements are identified with $\BaireSpace$.

For a finite prefix $s$, the principal upper set
$$
\PrincipalUp{s}:=\{x\in D_\omega:s\prefixOf x\}
$$
is Scott-open. It is upward-closed, and the finite-entry argument above shows that a directed supremum can extend
$s$ only if some member already extends $s$.
These sets form a basis of the Scott topology. Indeed, if a Scott-open set $U$ contains $x$, apply inaccessibility
to the directed family of finite prefixes of $x$. Some finite prefix $s$ belongs to $U$, and upward closure gives
$x\in\PrincipalUp{s}\IncludedIn U$.

On the maximal elements,
$$
\PrincipalUp{s}\cap\BaireSpace=\cyl{s}.
$$
The Scott basis therefore restricts to exactly the cylinder basis of Baire space. The inclusion of $\BaireSpace$
into $D_\omega$ is a homeomorphism onto the subspace of maximal elements. Finite prefixes are thus the same
finite observations in the domain and in the usual topology of Baire space.
\end{example*}

## The Interval Domain {#sec:interval-domain}

\begin{mathmeta}
  \define{IntervalDomain,IntervalBox}
  \vars{a,b,u,v}{Rat}
  \vars{y}{Real}
  \vars{c,d,x}{Real}
\end{mathmeta}
The cleanest case study is the \termdefine{interval domain} $\IntervalDomain$:
$$\IntervalDomain \;=\; \{\ClosedInterval{a}{b} \IncludedIn \R : a \le b\} \cup \{\bot\}, \qquad
\ClosedInterval{a}{b} \sqsubseteq \ClosedInterval{c}{d} \;\iff\; \ClosedInterval{c}{d}
\IncludedIn \ClosedInterval{a}{b}.$$
Elements are nonempty closed bounded intervals ordered by *reverse inclusion*; the bottom element $\bot$ sits below
every interval and represents "no information."

\begin{proposition*}[Directed completeness of the interval domain]
The poset $\IntervalDomain$ is a dcpo. If a directed set $S$ contains an interval, its supremum is
$$
\DirectedSup S=\bigcap\{I\in S:I\ne\bot\}.
$$
The directed set $\{\bot\}$ has supremum $\bot$.
\end{proposition*}

\begin{proof}
Suppose $S$ contains an interval $I_0$. The interval members have the finite intersection property, since any finitely
many have a common refinement in $S$, which is a nonempty interval. Intersecting each member with $I_0$ gives closed
subsets of the compact interval $I_0$ with the finite intersection property. Hence the intersection $K$ of all interval
members is nonempty. The set $K$ is compact and contains every point between any two of its points, so
$K=\ClosedInterval{\min K}{\max K}$. Reverse inclusion now makes $K$ the least upper bound of $S$.
If $S$ contains no interval, nonemptiness gives $S=\{\bot\}$.
Notice that a directed family need not be a nested sequence; the argument uses common refinements of finite
subfamilies.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のinterval domainの性質一覧を導入する「Properties:」のみ。
極大元・位相・可算基底の数学的内容は一覧の各部分で別途対応させる。)
--> Properties:<!--
formalization: skip-end
-->

*   The maximal (= total) elements are precisely the singletons $\{x\} = \ClosedInterval{x}{x}$, and identifying
    $\ClosedInterval{x}{x}$ with $x$
    recovers $\R$ as a subspace of $\IntervalDomain$.
*   The Scott topology, restricted to the maximal elements, is exactly the standard topology on $\R$.
*   $\IntervalDomain$ is an $\omega$-continuous dcpo with countable basis
    $\{\bot\}\cup\{\ClosedInterval{a}{b} : a, b \in \QQ,\ a\le b\}$<!--
    formalization: skip-begin (引用・背景説明・読書案内:
    未リンク部分は「hence quasi-Polish」のみ。極大元の同定と実数への同相、
    および具体的な有理区間基底をもつω連続dcpoであることはLeanへ接続済み。準Polish性は後段で外部定理として掲げるde
    Brechtの特徴付けとω連続dcpoの包含からの帰結であり、この章の局所証明とは扱わない。)
    --> , hence quasi-Polish.<!--
    formalization: skip-end
    -->

Computationally, an element $\ClosedInterval{a}{b} \in \IntervalDomain$ represents "the real $x$ is known to within
precision
$\Abs{b-a}$."
A directed family $\ClosedInterval{a_n}{b_n}$ refining toward $\ClosedInterval{x}{x}$ is the domain-theoretic analogue
of a
\termuse{Cauchy name}. The maximal-element presentation induced by $\IntervalDomain$ gives a domain model of $\R$.
To obtain names in the sense of TTE, use countable rational-interval chains converging to a singleton.
Their supremum map gives a representation equivalent to the \termuse{Cauchy representation}, as explained below.

\begin{proposition*}[Topology on maximal intervals]
The maximal elements of $\IntervalDomain$ are exactly the singleton intervals, and the map
$x\mapsto\ClosedInterval{x}{x}$ is a
homeomorphism from $\R$ to this subspace with its relative Scott topology.
\end{proposition*}

\begin{proof}
Every interval is refined by the singleton interval of any of its points, and a singleton interval has no proper
refinement. The bottom element is not maximal. This proves the assertion about maximal elements.

For a rational open interval $\OpenInterval{u}{v}$, put
$$\IntervalBox{u}{v}:=\{I\in\IntervalDomain:I\ne\bot,\ I\IncludedIn\OpenInterval{u}{v}\}.$$
This is upward-closed. Suppose the intersection of the interval members of a directed family lies in
$\OpenInterval{u}{v}$.
If no member lies entirely in $\OpenInterval{u}{v}$, their intersections with the closed set
$\SetDifference{\R}{\OpenInterval{u}{v}}$ have the
finite
intersection property. Compactness inside any fixed interval member then gives a point of their common
intersection outside $\OpenInterval{u}{v}$, a contradiction. Thus $\IntervalBox{u}{v}$ is Scott-open. Its trace on
singleton
intervals is exactly $\OpenInterval{u}{v}$, so the relative Scott topology contains the usual topology of $\R$.

For the other inclusion, let $V$ be Scott-open with $\ClosedInterval{x}{x}\in V$. The family
$$\{\ClosedInterval{a}{b}:a<x<b\}$$
is directed under reverse inclusion: intersect two such intervals to obtain a common refinement still containing
$x$ in its interior. Its intersection is $\{x\}$, since every other point is excluded by some sufficiently small
interval about $x$. Thus its supremum is $\ClosedInterval{x}{x}$. Scott openness gives some $\ClosedInterval{a}{b}\in V$
with $a<x<b$.
For every $y\in\OpenInterval{a}{b}$, upward closure then gives $\ClosedInterval{y}{y}\in V$. Hence the trace of $V$ on
singleton intervals is
open in the usual topology.
\end{proof}

\begin{proposition*}[Approximation and a rational basis]
For interval elements, the way-below relation is given by
$$
\ClosedInterval{a}{b}\ll\ClosedInterval{c}{d}\quad\Longleftrightarrow\quad a<c\ \text{ and }\ d<b.
$$
Moreover, $\bot\ll I$ for every $I\in\IntervalDomain$, and $I\ll\bot$ holds exactly when $I=\bot$.
The countable set
$$
B:=\{\bot\}\cup\{\ClosedInterval{u}{v}:u,v\in\QQ,\ u\le v\}
$$
is a domain-theoretic basis of $\IntervalDomain$. In particular, the interval domain is $\omega$-continuous.
\end{proposition*}

\begin{proof}
Fix $J=\ClosedInterval{c}{d}$ and consider its rational enlargements
$$
R_J:=\{\ClosedInterval{u}{v}:u,v\in\QQ,\ u<c,\ d<v\}.
$$
This family is nonempty by density of $\QQ$ in $\R$. It is directed under reverse inclusion: the intersection of two
members has rational endpoints and still contains $J$ in its interior. Its intersection is exactly $J$.
Indeed, a point smaller than $c$ can be excluded by choosing a rational left endpoint between that point and $c$;
a point larger than $d$ can be excluded similarly on the right. Hence $\DirectedSup R_J=J$.

If $\ClosedInterval{a}{b}\ll J$, applying the definition to $R_J$ gives $\ClosedInterval{u}{v}\in R_J$ with
$\ClosedInterval{a}{b}\sqsubseteq\ClosedInterval{u}{v}$. Therefore $a\le u<c$ and $d<v\le b$, proving the strict
inequalities.
Conversely, suppose $a<c$ and $d<b$, and let $S$ be directed with $J\sqsubseteq\DirectedSup S$.
The intersection of the interval members of $S$ is contained in $J$, hence in $\OpenInterval{a}{b}$.
The compactness argument in the preceding proof gives some interval member $K\IncludedIn\OpenInterval{a}{b}$.
Then $\ClosedInterval{a}{b}\sqsubseteq K$, as required.

The bottom element is way below every element because a directed set is nonempty and all its members lie above
$\bot$. Also, $I\ll\bot$ implies $I\sqsubseteq\bot$ by applying the definition to the singleton directed set
$\{\bot\}$, so $I=\bot$.

The set $B$ is countable because $\QQ^2$ is countable. For an interval element $J$, the characterization just proved
gives
$$
\{I\in B:I\ll J\}=\{\bot\}\cup R_J.
$$
This set is directed with supremum $J$. For the bottom element, the corresponding set is just $\{\bot\}$.
These are precisely the basis conditions. They also give continuity: every element way below $J$ lies below some
member of the directed basis family, by the definition of way-below. Thus any two such approximants have a common
upper bound in that family. All approximants are below $J$, and they include the basis family with supremum $J$,
so their supremum is $J$ as well.
\end{proof}

\begin{corollary*}[Interpolation through rational intervals]
If $I\ll J$ in $\IntervalDomain$, there is $K\in B$ such that $I\ll K\ll J$.
\end{corollary*}

\begin{proof}
If $I=\bot$, take $K=\bot$. Otherwise write $I=\ClosedInterval{a}{b}$ and $J=\ClosedInterval{c}{d}$; the bottom case for
$J$ is impossible.
Choose rational numbers $u,v$ with
$$
a<u<c\le d<v<b.
$$
Then $K=\ClosedInterval{u}{v}$ has the required properties by the strict endpoint characterization.
\end{proof}

## Quasi-Polish Spaces {#sec:quasi-polish-spaces}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
de Brecht 2013を引用し、準Polish空間をPolish空間とω連続domainの共通一般化として位置付ける導入。
包含・特徴付けは章で外部理論として明示され、ここで新しい局所証明は提示しない。)
-->
The class of \termuseas{quasi-Polish space}{quasi-Polish spaces}, introduced by de Brecht in 2013 [@deBrecht2013], is
the natural common generalization of Polish spaces and $\omega$-continuous domains.<!--
formalization: skip-end
-->

A \termdefine{quasi-metric} on a set $X$ is a function
$$d:X\times X\to\LeftClosedInterval{0}{\infty}$$
such that:

1.  $d(x,x)=0$ for every $x$;
2.  $d(x,z)\le d(x,y)+d(y,z)$ for all $x,y,z$;
3.  $d(x,y)=d(y,x)=0$ implies $x=y$.

Symmetry is not required. The open balls
$$\Ball{x}{\varepsilon}=\{y:d(x,y)<\varepsilon\}$$
generate a $T_0$ topology. The asymmetry is intentional: $d(x,y)$ measures how much information is needed to refine $x$
into $y$, so the cost from $x$ to $y$ need not match the cost from $y$ to $x$.

A sequence $\Sequence{x_n}{n\in\omega}$ is \termdefine{left K-Cauchy} if, for every $\varepsilon>0$, there is $N$ such
that
$$d(x_n,x_m)<\varepsilon\qquad(N\le n\le m).$$
A quasi-metric is \termdefineas{complete quasi-metric}{complete} in the quasi-Polish sense if every left K-Cauchy
sequence converges with respect to the associated metric
$$
\widehat d(x,y):=\max\{d(x,y),d(y,x)\}.
$$
This is the sequential form of Smyth completeness: the Cauchy condition is oriented, but its limit must retain the
information visible in both directions.

\begin{definition*} A topological space is \termdefineas{quasi-Polish space}{quasi-Polish} if it is countably based,
$T_0$, and its topology is induced by some complete quasi-metric.
\end{definition*}

\begin{example*}[\termdefineas{Scott topology on Pomega}{Scott topology on $\PowerSet{\omega}$}]
Order $\PowerSet{\omega}$ by inclusion. Directed suprema are unions. For arbitrary $F,A\IncludedIn\omega$,
$$
F\ll A
\quad\Longleftrightarrow\quad
F\text{ is finite and }F\IncludedIn A.
$$
To see this, suppose first that $F$ is finite and contained in the union of a directed family.
Choose a member containing each element of $F$, and use directedness finitely many times to obtain one member
containing all of $F$. If $F$ is empty, any member suffices. This proves the reverse implication.
For the forward implication, the finite subsets of $A$ form a nonempty directed family with union $A$.
Applying $F\ll A$ to this family puts $F$ inside one finite subset of $A$.

The finite subsets of $\omega$ thus form a countable domain-theoretic basis. The basic Scott-open neighborhoods are
$$
\PrincipalUp{F}:=\{A\IncludedIn\omega:F\IncludedIn A\},
\qquad F\IncludedIn\omega\text{ finite}.
$$
Each is Scott-open by the finite argument above. Conversely, if a Scott-open set $U$ contains $A$, apply
inaccessibility to the directed family of finite subsets of $A$. Some finite $F\IncludedIn A$ belongs to $U$,
and upward closure gives $\PrincipalUp{F}\IncludedIn U$.
Thus every Scott-open neighborhood is witnessed by finite positive information: every element of $F$ has appeared
in $A$. There is no corresponding finite negative evidence for $n\notin A$ in this topology.

This space is quasi-Polish. The definition in §{sec:quasi-polish-spaces} can be checked directly with
$$d(A,B):=\sup\bigl(\{0\}\cup\{2^{-i}:i\in\SetDifference{A}{B}\}\bigr).$$
This is nonnegative, and $d(A,B)=0$ exactly when $A\IncludedIn B$. The triangle inequality holds because every
element lost from $A$ to $C$ is lost either from $A$ to $B$ or from $B$ to $C$.

If $B$ contains every element of $A$ below $N$, then $d(A,B)\le 2^{-N}$.
Conversely, $d(A,B)<2^{-i}$ prevents the loss of any given $i\in A$.
These two observations show that the forward balls induce exactly the finite-positive-information Scott topology.
Its countable basis is given by the finite sets $F$ above, and $d(A,B)=d(B,A)=0$ implies $A=B$, so it is $T_0$.

For Smyth completeness, let $\Sequence{A_n}{n\in\omega}$ be left K-Cauchy.
For each $i$, applying the Cauchy condition with $2^{-i}$ gives a stage after which membership of $i$ can never
change from present to absent. Thus membership of each natural number eventually stabilizes. Let $A$ contain exactly
the numbers that are eventually present. Given $\varepsilon>0$, choose $N$ with $2^{-N}<\varepsilon$, then wait until
membership of every natural number below $N$ has stabilized. Both $d(A_n,A)$ and $d(A,A_n)$ are at most $2^{-N}$
thereafter, proving convergence for the
symmetrized metric. Thus this compatible quasi-metric is complete.

The space is not Polish. Indeed, if $A\StrictlyIncludedIn B$,
then every
Scott-open neighborhood of $A$ also contains $B$, because Scott opens are upward-closed. Hence the topology is $T_0$ but
not $T_1$, and therefore not Hausdorff.
\end{example*}

On the nonmetrizable spaces in this chapter, $\bSigma^0_2$ and $\bPi^0_2$ refer to de Brecht's generalized Borel
hierarchy [@deBrecht2013]. At level two, $\bSigma^0_2(X)$ consists of the sets
$$
\bigcup_n\SetDifference{U_n}{V_n},
$$
where every $U_n$ and $V_n$ is open in $X$. Its dual class is
$$
\bPi^0_2(X):=\{\SetDifference{X}{A}:A\in\bSigma^0_2(X)\}.
$$
Equivalently, a generalized $\bPi^0_2$ set has the form
$$
\bigcap_n\bigl(\SetDifference{X}{U_n}\cup V_n\bigr)
$$
for open $U_n,V_n$.

On metrizable spaces this agrees with the classical Borel hierarchy used in §{sec:borel-hierarchy}.

<!-- formalization: skip-begin (external de Brecht characterizations, closure theorems, and survey consequences) -->
\begin{theorem*}[de Brecht characterizations] For a nonempty countably based space $X$, the following are equivalent:

\begin{enumerate}
\item $X$ is quasi-Polish.
\item $X$ is homeomorphic to a generalized $\bPi^0_2$ subspace of $\PowerSet{\omega}$ with the Scott topology.
\item $X$ is homeomorphic to a generalized $\bPi^0_2$ subspace of some $\omega$-continuous domain.
\item $X$ is $T_0$ and is a continuous open image of $\BaireSpace$.
\end{enumerate}
\end{theorem*}

The class is closed under countable products and $\bPi^0_2$-subspaces — the analogue of Alexandrov's theorem from
§{sec:alexandrov-theorem}. It includes:

*   Every Polish space (a complete metric is in particular a complete quasi-metric).
*   Every $\omega$-continuous dcpo with the Scott topology.
*   Every $\bPi^0_2$ subspace of any quasi-Polish space.

A summary table:

| Class | Sep. | Order | Computability |
|-------|------|-------|---------|
| Polish | $T_2$ | discrete | TTE / Cauchy |
| $\omega$-cont. domain | $T_0$ | dcpo | Scott domains |
| **Quasi-Polish** | $T_0$ | mixed | unified |

The generalized Borel hierarchy and the Hausdorff--Kuratowski difference theorem extend to quasi-Polish
spaces [@deBrecht2013]. Conclusions about embedded Cantor sets need separate hypotheses.
<!-- formalization: skip-end -->

For example, the chain $\ClosedInterval{0}{1}$ with its Scott topology is an uncountable $\omega$-continuous dcpo, but
it has no
subspace homeomorphic to Cantor space: any two distinct points are comparable in the specialization order,
so no subspace with two or more points is $T_1$. Thus the Cantor-subspace conclusion of the classical perfect
set theorem does not transfer unchanged.

## Admissible Domain Representations and TTE {#sec:domains-tte-equivalence}

\begin{mathmeta}
  \vars{i,j,k,n,k_*}{Nat}
  \vars{s_*}{Seq(Nat)}
  \vars{p,q}{Name}
\end{mathmeta}

The two computational frameworks meet through representations by increasing chains of finite domain information.

<!-- formalization: skip (external admissible-representation theorem of Schröder and de Brecht) -->
\begin{theorem*}[\termdefineas{admissible domain representation theorem}{Admissible domain representation}]
Every quasi-Polish space $X$ admits an admissible partial surjection from $\BaireSpace$ whose domain is $\bPi^0_2$.
More concretely, after realizing $X$ as a generalized $\bPi^0_2$ subspace of an $\omega$-continuous domain $D$, names
may be taken to be way-below-increasing basis chains whose supremum lies in the designated subspace $X$.
\end{theorem*}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Schröder 2002とde Brecht 2013からの外部表現定理の出典を示す一文のみ。
具体的な基底鎖による表現構成・名前域・admissibilityは後続の局所証明として別途監査する。)
--> This form combines the representation theorems in [@Schroder2002; @deBrecht2013].<!--
formalization: skip-end
-->

The word "designated" matters. The points of $X$ need not be the maximal elements of $D$: every maximal-point subspace
is $T_1$<!--
formalization: skip-begin (引用・背景説明・読書案内:
未リンク部分は冪集合Scott空間を準Polish空間の例として扱う接続句のみ。極大点部分空間のT₁性はdomain_maximal_t1へ、
冪集合Scott位相の非T₁性はpowerset_scott_not_t1へ接続した。冪集合が準Polishであるという分類は直前で引用するde
Brechtの外部特徴付けによるもので、ここで新たな局所証明は提示していない。)
--> , whereas quasi-Polish spaces such as<!--
formalization: skip-end
-->  $\PowerSet{\omega}$ need not be $T_1$.

\begin{lemma*}[\termdefineas{domain interpolation lemma}{Interpolation through a domain basis}]
Let $B$ be a basis of a continuous dcpo $D$. If $a\ll x$, there is $b\in B$ with
$$a\ll b\ll x.$$
Moreover, the sets
$$W_b:=\{y\in D:b\ll y\},\qquad b\in B,$$
form a basis of the Scott topology.
\end{lemma*}

\begin{proof}
The definition of way-below directly gives the implication
$$a\sqsubseteq u\ll v\sqsubseteq x\quad\Longrightarrow\quad a\ll x.$$
Write
$$B_x:=\{b\in B:b\ll x\},\qquad T_x:=\bigcup_{b\in B_x}B_b.$$
The set $T_x$ is nonempty, since every set of basis approximants is nonempty. It is also directed.
Indeed, take $u\in B_b$ and $v\in B_c$ with $b,c\in B_x$, and choose a common upper bound $e\in B_x$ of $b,c$.
Then $u\ll e$ and $v\ll e$. Applying these two relations to the directed family $B_e$ gives members of $B_e$
above $u$ and $v$, respectively. A common upper bound of those members in $B_e$ belongs to $T_x$ and is above both
$u$ and $v$.

Every member of $T_x$ is below $x$. Conversely, an upper bound $y$ of $T_x$ bounds every $B_b$ for $b\in B_x$,
so it bounds each $b=\DirectedSup B_b$ and then $x=\DirectedSup B_x$. Thus $\DirectedSup T_x=x$.
Apply $a\ll x$ to this directed family. There are $u\in B_b$ and $b\in B_x$ with $a\sqsubseteq u$.
It follows that $a\ll b\ll x$, proving interpolation through the chosen basis.

For any $a\in D$, the set $W_a$ is upward-closed. If $a\ll\DirectedSup S$, interpolate to obtain
$a\ll b\ll\DirectedSup S$. Some $d\in S$ satisfies $b\sqsubseteq d$, whence $a\ll d$.
Thus $W_a$ is Scott-open. Finally, let $U$ be Scott-open with $x\in U$. Since $\DirectedSup B_x=x$, some
$b\in B_x$ belongs to $U$. Upward closure gives
$$x\in W_b\IncludedIn U,$$
which proves the basis assertion.
\end{proof}

\begin{lemma*}[\termdefineas{cofinal basis chain lemma}{Cofinal basis chains}]
Let $B$ be a countable basis of a continuous dcpo $D$. For every $x\in D$, there is a sequence
$\Sequence{c_n}{n\in\omega}$ of elements of $B_x:=\{b\in B:b\ll x\}$ such that
$$
c_n\ll c_{n+1},\qquad
\forall b\in B_x\;\exists n\; b\sqsubseteq c_n,\qquad
\DirectedSup_n c_n=x.
$$
\end{lemma*}

\begin{proof}
Enumerate the nonempty countable set $B_x$ as a sequence $\Sequence{r_n}{n\in\omega}$, allowing repetitions, and set
$c_0=r_0$.
Given $c_n$, choose $u_n\in B_x$ above both $c_n$ and $r_{n+1}$. The
\termuseas{domain interpolation lemma}{interpolation lemma} gives $c_{n+1}\in B$ with
$$u_n\ll c_{n+1}\ll x.$$
Then $c_n\ll c_{n+1}$ and $r_{n+1}\sqsubseteq c_{n+1}$. Inductively, the chain is increasing and each term
dominates all earlier enumerated approximants. Every member of $B_x$ is therefore below some $c_n$.
All $c_n$ are below $x$, and any upper bound of the chain bounds $B_x$, whose supremum is $x$.
Hence $\DirectedSup_n c_n=x$.
\end{proof}

\begin{mathmeta}
  \define{DomainRepresentation}
\end{mathmeta}

Here is the chain construction behind the theorem. Fix an embedding $X\IncludedIn D$ as a generalized $\bPi^0_2$
subspace and a countable basis $\IndexedFamily{b_n}{n\in\omega}$ of $D$. Define
$\PartialFunctionMap{\DomainRepresentation{X}}{\BaireSpace}{X}$ by declaring that $p$ is a name when
$$
b_{p(0)}\ll b_{p(1)}\ll b_{p(2)}\ll\cdots
\qquad\text{and}\qquad
\DirectedSup_n b_{p(n)}\in X,
$$
and then setting
$$
\DomainRepresentation{X}(p):=\DirectedSup_n b_{p(n)}.
$$

The chain condition is closed, since a failure is witnessed by two adjacent coordinates. On this closed space of
names, the supremum map into $D$ is continuous for the Scott topology. Indeed, for any Scott-open set $U$,
$$
\DirectedSup_n b_{p(n)}\in U\quad\Longleftrightarrow\quad
\exists n\; b_{p(n)}\in U.
$$
The forward implication is inaccessibility, and the reverse implication is upward closure. Each condition on the right
depends on a single coordinate of the name, so its truth is determined by a finite prefix.
The remaining requirement that the supremum belong to $X$ is the inverse image of a generalized $\bPi^0_2$ set.
Closure of that class under continuous preimages, followed by passage from the closed name space to the ambient
Baire space, shows that the domain of names is $\bPi^0_2$.

Here are the two closure steps used in this argument. If $f:Y\to Z$ is continuous, then
$$
f^{-1}\!\left[\bigcap_n\bigl(\SetDifference{Z}{U_n}\cup V_n\bigr)\right]
=\bigcap_n\bigl(\SetDifference{Y}{f^{-1}[U_n]}\cup f^{-1}[V_n]\bigr),
$$
and the inverse images of the open sets remain open. Next, let $C$ be closed in $Y$ and let
$A\IncludedIn C$ be generalized $\bPi^0_2$ in the subspace topology. Write its defining relatively open sets as
$C\cap O_n$ and $C\cap P_n$, where $O_n,P_n$ are open in $Y$. Viewed as a subset of $Y$, it has the following
description:
$$
A=C\cap\bigcap_n\bigl(\SetDifference{Y}{O_n}\cup P_n\bigr)
$$
This still has the required form: use $\SetDifference{Y}{C}$ and $\varnothing$ as the two open sets in the zeroth
condition, then use $O_n$ and $P_n$ in condition $n+1$. Apply these observations to the closed space of chain names
and its continuous supremum map.

For surjectivity, fix $x\in X$ and apply the \termuse{cofinal basis chain lemma} to the chosen countable basis.
It gives $c_n\ll c_{n+1}\ll x$ with $\DirectedSup_n c_n=x$. Choose indices $p(n)$ so that $b_{p(n)}=c_n$.
Then $p$ is a name and $\DomainRepresentation{X}(p)=x$.

\begin{lemma*}[\termdefineas{continuous choice from an open cover}{Continuous choice from an open cover}]
Let $E\IncludedIn\BaireSpace$, and let $U_j$, for $j\in\omega$, be relatively open sets covering $E$.
There is a continuous map $h:E\to\omega$ such that $q\in U_{h(q)}$ for every $q\in E$.
\end{lemma*}

\begin{proof}
If $E$ is empty, use the empty map. Otherwise enumerate all pairs $\Pair{s_i}{k_i}$ such that
$$V_i:=E\cap\cyl{s_i}\IncludedIn U_{k_i}.$$
These relative cylinders cover $E$, since cylinders form a basis of Baire space. They are relatively clopen.
For each $q\in E$, let $\iota(q)$ be the least index with $q\in V_{\iota(q)}$, and put $h(q)=k_{\iota(q)}$.
The nonempty sets
$$C_i:=\SetDifference{V_i}{\bigcup_{j<i}V_j}$$
form a relatively clopen partition of $E$. On each $C_i$, the chosen index is constantly $i$ and $h$ is constantly
$k_i$. Thus $h$ is continuous and makes the required choice.
\end{proof}

\begin{proposition*}[\termdefineas{admissibility of basis-chain names}{Admissibility of basis-chain names}]
Let $D$ be a continuous dcpo with countable basis $\IndexedFamily{b_n}{n\in\omega}$, and give a subspace
$X\IncludedIn D$ the relative Scott topology. The chain representation $\DomainRepresentation{X}$ is admissible.
If $X$ is generalized $\bPi^0_2$ in $D$, its domain of names is $\bPi^0_2$ in Baire space.
\end{proposition*}

\begin{proof}
The continuity and surjectivity arguments above apply to any subspace; the additional complexity assertion was also
proved above. We establish the universal property from §{sec:cauchy-representation-admissibility}.
Let $\delta:E\to X$ be any continuous partial map with $E\IncludedIn\BaireSpace$.
For empty $E$ the translator is the empty map, so assume $E$ is nonempty. Write
$$W_{b_j}=\{x\in D:b_j\ll x\}.$$
These sets are Scott-open by the \termuse{domain interpolation lemma}. Fix an enumeration of all pairs
$\Pair{s_i}{k_i}$ satisfying
$$V_i:=E\cap\cyl{s_i}\IncludedIn\delta^{-1}[W_{b_{k_i}}].$$
Each $V_i$ is relatively clopen. Moreover, whenever $b_k\ll\delta(q)$, relative openness gives a cylinder certificate
with $q\in V_i$ and $k_i=k$.

We recursively construct continuous maps $h_n:E\to\omega$. The relatively open sets
$\delta^{-1}[W_{b_j}]$ cover $E$, since the basis approximants below each point are nonempty.
The \termuse{continuous choice from an open cover} therefore gives $h_0$ with
$$b_{h_0(q)}\ll\delta(q).$$
Suppose $h_n$ has been chosen with $b_{h_n(q)}\ll\delta(q)$ for all $q$. For each $j$, let $U_j^n$ consist of the
points $q\in E$ satisfying
$$
\begin{aligned}
b_j&\ll\delta(q),\qquad b_{h_n(q)}\ll b_j,\\
\forall i\le n\;&\bigl(q\in V_i\Longrightarrow b_{k_i}\sqsubseteq b_j\bigr).
\end{aligned}
$$
These sets are relatively open. The first condition is open by continuity of $\delta$; the second is locally constant
because $h_n$ is continuous into the discrete space $\omega$. Each of the finitely many remaining conditions is either
vacuous or the relatively clopen condition $q\notin V_i$.

They also cover $E$. At a given $q$, directedness supplies a basis approximant above both $b_{h_n(q)}$ and all
$b_{k_i}$ with $i\le n$ and $q\in V_i$. Interpolation then gives a basis element way above this common bound and
way below $\delta(q)$, providing a suitable index $j$.
Apply \termuse{continuous choice from an open cover} once more to choose $h_{n+1}$ continuously with
$q\in U_{h_{n+1}(q)}^n$. This ensures
$$
b_{h_n(q)}\ll b_{h_{n+1}(q)}\ll\delta(q),\qquad
q\in V_i\Longrightarrow b_{k_i}\sqsubseteq b_{h_{i+1}(q)}.
$$
Thus every certificate that applies to the input is absorbed at a finite stage.

Set $g(q)(n):=h_n(q)$. Each coordinate is continuous, so $g:E\to\BaireSpace$ is continuous.
For every $b_k\ll\delta(q)$ there is a certificate with $k_i=k$ and $q\in V_i$; the displayed inequality puts
$b_k$ below a member of the output chain. Hence this chain is cofinal among the basis approximants of $\delta(q)$,
and
$$
\DomainRepresentation{X}(g(q))=\DirectedSup_n b_{h_n(q)}=\delta(q).
$$
In particular, $g(q)$ is a valid name whose supremum lies in $X$. This proves the required lifting property and hence
admissibility. All cylinder enumerations, basis relations, and choices here are fixed topological data; they are not
assumed to be computable.
\end{proof}

When $X$ is Polish, both $\DomainRepresentation{X}$ and the standard \termuse{Cauchy representation} $\rho_X$ are
admissible. The Kreitz--Weihrauch theorem in §{sec:kreitz-weihrauch-admissibility} therefore gives
$$
\DomainRepresentation{X}\ContinuouslyEquivalentTo\rho_X.
$$

Thus domain chains and TTE names are alternative presentations of the same approximation process. The
$\IntervalDomain$ presentation corresponds to the standard Cauchy representation of $\R$. The associated TTE
function-space representation represents all continuous functions on $\R$, with its computable elements corresponding
to the computable continuous functions. <!--
formalization: skip-begin (引用・背景説明・読書案内:
未リンク部分はrealizabilityとの広い圏論的比較をeffective-topos章へ送る案内文のみ。
実数の区間鎖とCauchy表現の連続同値、通常の連続実関数全体への関数空間表現の全射性、および計算可能な名前とType-Two
lambda実現子の同値は具体的なLean構成へ接続済み。)
--> The broader categorical comparison with realizability is taken up in
§{sec:effective-topos}.<!--
formalization: skip-end
-->
