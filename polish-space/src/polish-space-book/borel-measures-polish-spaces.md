# Borel Measures on Polish Spaces {#sec:borel-measures}
\index{Borel measure}

\begin{mathmeta}
  \forward{ProbMeasures,EventualEqualityER}
\end{mathmeta}

<!-- formalization: skip-begin (chapter motivation) -->

This chapter is not a replacement for measure theory; it isolates the measure facts that become especially clean on
Polish and standard Borel spaces.
\termforwardas{Ulam theorem}{Ulam regularity} says finite Borel measures are controlled by
compact and open approximation. The weak topology on $\ProbMeasures{X}$ and
\termforward{Prokhorov's theorem} make measures
themselves into Polish-space objects, so the coding and compactness tools of the earlier chapters can be applied to
laws, not only to points. \termforwardas{Lusin theorem}{Lusin's theorem} explains why Borel maps are continuous on large
compact pieces, and disintegration supplies regular conditional probabilities as families of probability measures
that depend Borel measurably on the parameter, rather than merely as almost-everywhere scalar identities.

The \termforwardas{zero-one law}{zero-one laws} and \termforwardas{Maharam theorem}{Maharam uniqueness}
connect this regular
measure theory back to the rest of the book. Tail events in product spaces give the measure-side analogue of
Baire-category genericity, while the classification of non-atomic standard probability spaces identifies the
measure algebra behind
\termforward{random forcing}. In short, Polish spaces make measure theory regular, codable, and compatible with the
descriptive-set-theoretic machinery used in determinacy, forcing, and classification.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter overview, scope, and reference) -->
The standard Borel structure of §{sec:standard-borel-spaces} captures the measurable scaffolding of a Polish space.
Equipping that scaffolding with measures is what makes Polish spaces the standard setting for analysis and probability:
regularity, approximation, and disintegration theorems that fail in general topological measure theory all hold for
\termforwardas{Borel measure}{Borel measures} on Polish spaces. This chapter records the measure-theoretic facts the
rest of the text uses — regularity of finite Borel measures, the Polish topology on the space of probability measures,
Prokhorov's compactness criterion, Lusin's continuity theorem, disintegration, zero-one laws, and measure-algebra
uniqueness — and supplies the measure theory that the random forcing of §{sec:random-forcing-detail} will use. The
standard descriptive-set-theoretic reference is [@Kechris1995, Ch. 17].

Proof scope: this chapter proves the measure facts used later. It proves the Polish-space
regularity, compactness, zero-one, and measure-algebra statements in the forms used by the forcing and classification
chapters. It records the Prokhorov–Varadarajan and Portmanteau theorems with citations because they are standard weak-
convergence infrastructure. For disintegration, it uses conditional expectation and its measurable factorization
as standard measure-theoretic inputs, then constructs Borel conditional measures and proves their concentration
on fibers and uniqueness.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

The prerequisites are the definition of a standard Borel space in §{sec:standard-borel-spaces}, the refinement
tools in §{sec:polish-topology-refinement}, and the measure theory listed in §{sec:expected-reader}. For
disintegration, use conditional expectation and its measurable factorization as stated inputs; their proofs
are outside this chapter. First follow regularity, weak convergence, and the statements of disintegration and
the zero-one laws. Return to the conditional-measure construction for the dependence on the parameter. The
goal is to recognize which operations on measures can be expressed as Borel maps and why null ideals and zero-one
arguments support random forcing and nonsmoothness. Games, Wadge ranks, and effective DST are not prerequisites.

<!-- formalization: skip-end -->

## Finite Borel Measures Are Radon {#sec:borel-measures-radon}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}
\index{Radon measure}

A \termdefine{Borel measure} on a Polish space $X$ is a measure on the Borel $\sigma$-algebra $\mathcal B(X)$. We focus
on \termdefineas{finite Borel measure}{finite} Borel measures and especially
\termdefineas{probability measure}{probability measures}: those with $\mu(X) = 1$. The space of all probability measures
is denoted
\begin{mathmeta}
  \define{ProbMeasures}
\end{mathmeta}
$$\ProbMeasures{X} := \{\mu : \mathcal B(X) \to \ClosedInterval{0}{1} : \mu \text{ a probability measure}\}.$$

\begin{lemma*}[Closed-set regularity]
Let $\mu$ be a finite Borel measure on a metric space $X$. For every Borel $B \IncludedIn X$ and every $\varepsilon>0$
there are a closed $F$ and an open $U$ such that
$$F\IncludedIn B\IncludedIn U,
\qquad \mu(\SetDifference{U}{F})<\varepsilon.$$
\end{lemma*}

\begin{proof}[Proof]
Let $\mathcal R$ consist of the Borel sets with the displayed two-sided approximation property. Every open set belongs
to $\mathcal R$: it is an increasing union of closed sets in a metric space, so continuity from below and finite total
mass give the inner approximation, while the set itself gives the outer approximation. Taking complements exchanges
the inner and outer approximants: if $F\IncludedIn B\IncludedIn U$, then
$$U^c\IncludedIn B^c\IncludedIn F^c,
\qquad \SetDifference{F^c}{U^c}=\SetDifference{U}{F}.$$
Thus $\mathcal R$ is closed under complements.

For countable unions, let $A=\bigcup_n A_n$ with $A_n\in\mathcal R$. Choose closed $F_n$ and open $U_n$ with
$$F_n\IncludedIn A_n\IncludedIn U_n,
\qquad \mu(\SetDifference{U_n}{F_n})<\varepsilon 2^{-(n+2)}.$$
Continuity from below gives $N$ such that, writing $A_N^*=\bigcup_{n\le N}A_n$,
$$\mu(\SetDifference{A}{A_N^*})<\varepsilon/2.$$
The set $F=\bigcup_{n\le N}F_n$ is closed, $U=\bigcup_n U_n$ is open, and $F\IncludedIn A\IncludedIn U$.
Moreover,
$$\SetDifference{U}{F}
\IncludedIn\bigcup_n\SetDifference{U_n}{F_n}\;\cup\;\SetDifference{A}{A_N^*}.$$
To check this inclusion, a point of $U$ outside all the gaps $\SetDifference{U_n}{F_n}$ lies in some $F_n$, hence in
$A$. If it also lies in $A_N^*$, it belongs to some $U_j$ with $j\le N$, hence to $F_j$ and therefore to $F$.
Consequently,
$$\mu(\SetDifference{U}{F})
\le\sum_{n=0}^{\infty}\mu(\SetDifference{U_n}{F_n})+\mu(\SetDifference{A}{A_N^*})
<\varepsilon/2+\varepsilon/2=\varepsilon.$$
Thus $\mathcal R$ is a $\sigma$-algebra containing the open sets, so it contains every Borel set.
\end{proof}

\begin{theorem*}[\termdefineas{Ulam theorem}{Ulam}] Every finite Borel measure $\mu$ on a Polish space $X$ is
\termdefine{inner regular by compact sets}:
$$\mu(B) = \sup\{\mu(K) : K \IncludedIn B,\, K \text{ compact}\} \qquad (B \in \mathcal B(X)).$$

\end{theorem*}

\begin{proof}[Proof] It suffices to find compact $K \IncludedIn X$ with $\mu(\SetDifference{X}{K}) < \varepsilon$ for
every
$\varepsilon > 0$. Indeed, apply closed-set regularity inside a given Borel set with error $\varepsilon/2$, apply this
compact-concentration claim with the same error, and intersect the two approximants.

If $X=\emptyset$, take $K=\emptyset$. Otherwise, fix a complete compatible metric $d$ and a countable dense set
$\IndexedFamily{q_n}{n\in\omega}$. For each $k\ge1$, the closures of the balls $\Ball{q_n}{1/k}$ cover $X$.
Continuity from below therefore gives $N_k$ such that
$$C_k:=\bigcup_{n\le N_k}\Closure{\Ball{q_n}{1/k}},
\qquad \mu(\SetDifference{X}{C_k})<\varepsilon 2^{-k}.$$
Set $K:=\bigcap_{k\ge1}C_k$. Each $C_k$ is closed, so $K$ is closed, and
$$\mu(\SetDifference{X}{K})
\le\sum_{k=1}^{\infty}\mu(\SetDifference{X}{C_k})
<\sum_{k=1}^{\infty}\varepsilon 2^{-k}=\varepsilon.$$
The strict inequality follows by retaining the strict bound for $k=1$ and using the non-strict bounds for $k\ge2$;
the geometric series is finite. The set $K$ is totally bounded: for any $r>0$, choose $k$ with $2/k<r$. Then
$$K\IncludedIn C_k\IncludedIn\bigcup_{n\le N_k}\Ball{q_n}{2/k}
\IncludedIn\bigcup_{n\le N_k}\Ball{q_n}{r}.$$
A closed totally bounded subset of a complete metric space is compact. Indeed, total boundedness produces a Cauchy
subsequence of every sequence, completeness supplies its limit, and closedness keeps that limit in the set.
\end{proof}

A measure that is inner regular by compacts and outer regular by opens is \termdefineas{Radon measure}{Radon}. Thus
every finite Borel measure on a Polish space is Radon, and the descriptive and analytic notions of "well-behaved
measure" coincide.

## The Polish Space of Probability Measures {#sec:prob-measure-space}
\index{probability measure}

The \termdefine{weak topology} on $\ProbMeasures{X}$ — also called the weak* topology — is generated by the maps $\mu
\mapsto \int f \, d\mu$ for bounded continuous $f : X \to \R$.

\begin{theorem*}[\termdefineas{Prokhorov--Varadarajan theorem}{Prokhorov–Varadarajan}]
<!-- formalization: skip-begin (Polishness and Levy--Prokhorov metric quoted from Kechris;
compactness remains linked) -->
Let $X$ be Polish and fix a complete compatible metric $d$ on $X$. Then $\ProbMeasures{X}$ is Polish in the weak
topology.
A compatible complete metric is the Lévy–Prokhorov metric
$$
d_{\mathrm{LP}}(\mu, \nu)
:= \inf\left\{\varepsilon > 0 :
\begin{array}{l}
\mu(A) \le \nu(A^\varepsilon) + \varepsilon,\\
\nu(A) \le \mu(A^\varepsilon) + \varepsilon
\end{array}
\text{ for every } A \in \mathcal B(X)\right\},
$$
where $A^\varepsilon := \{x : d(x, A) < \varepsilon\}$.
<!-- formalization: skip-end -->
 If $X$ is compact, then $\ProbMeasures{X}$ is compact.

\end{theorem*}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
確率測度空間の標準定理についてKechrisの番号を示す書誌的な文。局所的な数学の主張・証明ではない。)
--> These facts are collected in [@Kechris1995, Theorems 17.19 and 17.23--17.25].<!--
formalization: skip-end
-->

<!-- formalization: skip (expository consequence of the cited Prokhorov–Varadarajan theorem) -->
The Polish-on-Polish closure of $\ProbMeasures{\cdot}$ is what makes probability theory on Polish spaces self-contained:
a
sequence of \termuseas{probability measure}{probability measures} has a Polish space of weak limits, and the
descriptive-set-theoretic structure of the previous chapters becomes available again at the level of measures.

<!-- formalization: skip (cited external weak-convergence infrastructure) -->
\begin{lemma*}[Portmanteau theorem]
If $\lambda_i\to\lambda$ weakly in $\ProbMeasures{X}$, then
$$
\lambda(F)\ge\limsup_i\lambda_i(F) \quad(F\text{ closed}),
\qquad
\lambda(U)\le\liminf_i\lambda_i(U) \quad(U\text{ open}).
$$
Conversely, either family of inequalities for all closed sets or for all open sets characterizes weak convergence of
probability measures.
\end{lemma*}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前のPortmanteau定理のKechris Theorem 17.20への出典表示。本文が明示する引用入力の書誌情報である。)
--> For the Portmanteau theorem in this form, see [@Kechris1995, Theorem 17.20].<!--
formalization: skip-end
-->

## Prokhorov's Theorem {#sec:prokhorov}

\begin{mathmeta}
  \vars{m,p}{Nat}
\end{mathmeta}

A family $\Gamma \IncludedIn \ProbMeasures{X}$ is \termdefineas{tight family of measures}{tight} if for every
$\varepsilon
>
0$ there is a compact $K \IncludedIn X$ with $\mu(\SetDifference{X}{K}) < \varepsilon$ for every $\mu \in \Gamma$ —
uniformly
compactly concentrated, in the same sense \termuseas{Ulam theorem}{Ulam's theorem} gives for a single measure.

\begin{theorem*}[\termdefineas{Prokhorov's theorem}{Prokhorov}]
For $X$ Polish and $\Gamma \IncludedIn \ProbMeasures{X}$,
$$\Gamma \text{ is relatively compact in } \ProbMeasures{X}
\quad\Longleftrightarrow\quad
\Gamma \text{ is tight}.$$

\end{theorem*}

\begin{proof}[Proof]
If $\Gamma=\emptyset$, both assertions hold trivially, so assume $\Gamma\ne\emptyset$.
By §{sec:hilbert-cube-embedding}, identify $X$ with a $\Gdelta$ subspace of the Hilbert cube
$H=\ClosedInterval{0}{1}^\omega$. Extend each $\mu\in\ProbMeasures{X}$ to $H$ by
$$\hat\mu(B):=\mu(B\cap X).$$
The map $\mu\mapsto\hat\mu$ is injective and continuous for the weak topologies: bounded continuous functions
on $H$ restrict to bounded continuous functions on $X$. To prove continuity of its inverse on the image,
it suffices to check sequences, since both weak topologies are metrizable by §{sec:prob-measure-space}.
Suppose $\hat\mu_i\to\hat\mu$. For an open $O\IncludedIn X$, choose an open $U\IncludedIn H$ with $O=X\cap U$.
The Portmanteau inequality gives
$$\mu(O)=\hat\mu(U)\le\liminf_i\hat\mu_i(U)=\liminf_i\mu_i(O).$$
Its converse gives $\mu_i\to\mu$, so the extension map is a topological embedding.

Its image consists exactly of the probabilities $\nu$ on $H$ with $\nu(X)=1$.
Indeed, $X$ is Borel in $H$, and restricting such a measure to the Borel subspace $X$ gives a probability measure
whose extension is $\nu$. The equality follows because the complement of $X$ has measure zero.

Assume that $\Gamma$ is tight, and put $\widehat\Gamma:=\{\hat\mu:\mu\in\Gamma\}$.
The space $\ProbMeasures{H}$ is compact by §{sec:prob-measure-space}.
For every $\delta>0$, choose a compact $K_\delta\IncludedIn X$ with
$$\mu(\SetDifference{X}{K_\delta})\le\delta\qquad(\mu\in\Gamma).$$
Viewed in $H$, this set is still compact and hence closed. Portmanteau implies that the set
$$\{\nu\in\ProbMeasures{H}:\nu(K_\delta)\ge1-\delta\}$$
is closed. It contains $\widehat\Gamma$, and therefore also its closure.
Every $\nu\in\Closure{\widehat\Gamma}$ consequently satisfies
$$\nu(X)\ge\nu(K_\delta)\ge1-\delta.$$
Since $\delta>0$ was arbitrary, $\nu(X)=1$. Thus the compact set $\Closure{\widehat\Gamma}$ lies in the image
of the extension map. Pulling it back gives a compact set containing $\Gamma$, so $\Closure{\Gamma}$ is compact.

Conversely, let $C:=\Closure{\Gamma}$ be compact. Write
$$X=\bigcap_{n\in\omega}G_n$$
with each $G_n$ open in $H$, and fix $\varepsilon>0$. First let $G\IncludedIn H$ be open with
$\hat\mu(G)=1$ for every $\mu\in C$. We claim that there is a compact $L\IncludedIn G$ such that
$$\hat\mu(L)>1-\varepsilon\qquad(\mu\in C).$$
For each $\mu\in C$, inner regularity gives a compact $L_\mu\IncludedIn G$ with
$\hat\mu(L_\mu)>1-\varepsilon$. Choose an open $V_\mu$ with
$$L_\mu\IncludedIn V_\mu\IncludedIn\Closure{V_\mu}\IncludedIn G.$$
By the open-set clause of Portmanteau, evaluation on $V_\mu$ is lower semicontinuous, so
$$\{\lambda\in C:\hat\lambda(V_\mu)>1-\varepsilon\}$$
is open in $C$. These neighborhoods cover $C$. Choose a finite subcover indexed by $\mu_0,\ldots,\mu_r$ and put
$$L:=\bigcup_{j\le r}\Closure{V_{\mu_j}}.$$
Then $L$ is compact, is contained in $G$, and has $\hat\lambda(L)>1-\varepsilon$ for every $\lambda\in C$.

Apply the claim to $G_n$ with error $\varepsilon 2^{-(n+1)}$. This gives compact $L_n\IncludedIn G_n$ with
$$\hat\mu(\SetDifference{H}{L_n})<\varepsilon 2^{-(n+1)}\qquad(\mu\in C).$$
Set
$$K:=\bigcap_{n\in\omega}L_n.$$
This is a closed subset of the compact space $H$ and lies in $\bigcap_nG_n=X$, so it is compact in $X$.
For every $\mu\in C$,
$$\begin{aligned}
\mu(\SetDifference{X}{K})
&=\hat\mu(\SetDifference{H}{K})\\
&\le\sum_{n\in\omega}\hat\mu(\SetDifference{H}{L_n})<\varepsilon.
\end{aligned}$$
The final inequality follows by retaining the strict bound at $n=0$ and using the non-strict bounds for the other
terms; the bounding geometric series has finite sum $\varepsilon$.
Thus $C$ is tight, and its subset $\Gamma$ is tight as well.
\end{proof}

<!-- formalization: skip (applications of Prokhorov compactness outside the chapter's proof obligations) -->
The implication "tight $\Rightarrow$ relatively compact" is the working direction. It supplies subsequential limits in
stochastic-process arguments, existence of stationary measures for Markov chains, existence of invariant measures for
group actions, and central-limit-style weak convergence proofs. The reverse direction uses
\termuseas{Ulam theorem}{Ulam's theorem} to extract uniform tightness from compactness of the closure.

## Lusin's Theorem {#sec:lusin-measurable-continuous}

\begin{mathmeta}
  \vars{C,F}{Nat}
\end{mathmeta}

Borel measurable functions are not in general continuous, but they are continuous after removing a small set:

\begin{theorem*}[\termdefineas{Lusin theorem}{Lusin}] Let $X, Y$ be Polish, $\mu \in \ProbMeasures{X}$, and $f : X \to
Y$
Borel-measurable. For every $\varepsilon > 0$ there is a closed $F \IncludedIn X$ with $\mu(\SetDifference{X}{F}) <
\varepsilon$
such that $\restrict{f}{F}$ is continuous.

\end{theorem*}

\begin{proof}[Proof] In fact, $F$ can be chosen compact. Apply \termuse{Borel maps become continuous} in
§{sec:polish-topology-refinement} to refine $\tau_X$ to a Polish topology $\tau'\supseteq\tau_X$ in which $f$ is
continuous, with the same Borel $\sigma$-algebra. Thus $\mu$ is still a finite Borel measure on $\Pair{X}{\tau'}$.
By \termuseas{Ulam theorem}{Ulam's theorem} applied to this topology, choose a $\tau'$-compact $F$ with
$\mu(\SetDifference{X}{F})<\varepsilon$. The identity map from $\Pair{X}{\tau'}$ to $\Pair{X}{\tau_X}$ is continuous, so
$F$ is
also $\tau_X$-compact and hence closed. Its restriction $\Pair{F}{\tau'}\to\Pair{F}{\tau_X}$ is a continuous bijection
from a
compact space to a Hausdorff space, hence a homeomorphism. Composing its inverse with the $\tau'$-continuous
restriction of $f$ shows that $\restrict{f}{F}$ is continuous for the original topology.
\end{proof}

For the category analogue, let $\{V_n\}$ be a countable base for $Y$. Each Borel set $f^{-1}(V_n)$ has the Baire
property, so choose an open $U_n\IncludedIn X$ with $f^{-1}(V_n)\mathbin{\triangle}U_n$ meager. Set
$$M:=\bigcup_n\bigl(f^{-1}(V_n)\mathbin{\triangle}U_n\bigr).$$
Then $M$ is meager, and for every $n$,
$$f^{-1}(V_n)\cap\SetDifference{X}{M}=U_n\cap\SetDifference{X}{M}.$$
These sets are relatively open in $\SetDifference{X}{M}$, so the basis criterion for continuity shows that $f$ is
continuous on this comeager set. Intersecting it with the closed set $F$ in
\termuseas{Lusin theorem}{Lusin's theorem} makes $f$ continuous outside $M\cup(\SetDifference{X}{F})$, where
$M$ is meager and the open set $\SetDifference{X}{F}$ has measure less than $\varepsilon$.

The measure-small exceptional set cannot in general be replaced by a null set. Let $\lambda$ be Lebesgue measure on
$X=\ClosedInterval{0}{1}$. To obtain a closed nowhere dense set of positive measure, take a dense sequence $q_n$ and use
closed-set
regularity and $\lambda(\{q_n\})=0$ to choose relatively open neighborhoods $W_n$ with
$$q_n\in W_n,\qquad \lambda(W_n)<2^{-(n+2)}.$$
Then $O:=\bigcup_n W_n$ is open and dense, while
$$\lambda(O)\le\sum_{n=0}^{\infty}\lambda(W_n)\le\frac12.$$
Thus $K:=\SetDifference{X}{O}$ is closed and nowhere dense, with $\lambda(K)\ge1/2$. Let $g$ be its indicator:
$g=1$ on $K$ and $g=0$ on $\SetDifference{X}{K}$. For any conull $C\IncludedIn X$, the set $K\cap C$ is nonempty,
because $K$ has positive measure. Also $C$ is dense: every nonempty relatively open subset of the interval has positive
Lebesgue measure. Since $\SetDifference{X}{K}$ is open and dense, $C\cap\SetDifference{X}{K}$ is dense in $X$, and
hence dense in $C$. If $\restrict{g}{C}$ were continuous, its value $0$ on this dense subset would force it to be
identically $0$ on $C$, contradicting its value $1$ at a point of $K\cap C$.

## Disintegration {#sec:disintegration}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}
\index{disintegration}
\index{Markov kernel}
\index{regular conditional probability}

The most consequential measure-theoretic fact about Polish/standard Borel spaces is that conditional measures can always
be chosen Borel-measurably:

A \termdefine{Markov kernel} from a standard Borel space $Y$ to a standard Borel space $X$ is a map
$$K : Y \times \mathcal B(X) \to \ClosedInterval{0}{1}$$
such that:

1.  for each $y \in Y$, the set function $B \mapsto K(y,B)$ is a probability measure on $X$;
2.  for each Borel $B \IncludedIn X$, the function $y \mapsto K(y,B)$ is Borel.

Equivalently, after identifying $\ProbMeasures{X}$ with its standard Borel structure from §{sec:prob-measure-space}, a
kernel is a Borel map
$$Y \to \ProbMeasures{X}, \qquad y \mapsto K_y.$$
<!--
formalization: skip-begin (引用・背景説明・読書案内:
核を確率測度空間へのBorel写像と見る同値はProbabilityMeasureBorel.standardBorel_measurable_iff
に接続済み。残部はその可測性を積分・核の合成・押し出しで使えるという標準測度論上の用途説明で、この段落で新しい合成公式やその証明を展開しない。
一般の核合成定理をこのリンクが証明したとは扱わない。)
-->
The word "Borel" here is not cosmetic. It says that conditional measures may be used as ordinary measurable data: one
may integrate $y \mapsto K_y(B)$, compose kernels, and form pushforwards without leaving the standard-Borel category.
<!--
formalization: skip-end
-->

\begin{lemma*}[Measurable families of probability measures]
Let $X$ be Polish, let $Y$ be any measurable space, and let $k:Y\to\ProbMeasures{X}$ be a map.
Then $k$ is measurable for the Borel structure of the weak topology if and only if
$y\mapsto k(y)(B)$ is measurable for every Borel set $B\IncludedIn X$.
Consequently, this Borel structure depends only on the Borel structure of $X$ and transports along
Borel isomorphisms. The same characterization therefore defines the standard Borel structure on
$\ProbMeasures{X}$ when $X$ is a standard Borel space.
\end{lemma*}

\begin{proof}[Proof]
For an open set $U\IncludedIn X$, the evaluation $\mu\mapsto\mu(U)$ is lower semicontinuous by
the Portmanteau theorem. The Borel sets whose evaluations are Borel form a Dynkin system:
evaluation at the whole space is constant, complements use $\mu(B^c)=1-\mu(B)$, and disjoint
countable unions use sums of nonnegative measurable functions. Open sets form a generating
$\pi$-system, so the $\pi$–$\lambda$ theorem makes every Borel evaluation measurable.
This proves the forward implication.

First prove the converse for the Hilbert cube $H=\HilbertCube$. Choose a countable generating
$\pi$-system $\Sequence{C_n}{n\in\omega}$ containing $H$, by taking finite intersections of a
countable Borel generating family together with $H$. The evaluation map
$$E:\ProbMeasures{H}\to\HilbertCube,\qquad E(\mu)(n)=\mu(C_n)$$
is Borel by the preceding argument and injective by uniqueness of finite measures on a generating
$\pi$-system. The weak space $\ProbMeasures{H}$ is compact metrizable, hence Polish.
Lusin–Suslin therefore makes $E$ a Borel isomorphism onto its Borel image. If all evaluations of
$k$ are measurable, then $E\circ k$ is measurable, and composing with this inverse proves that $k$ is measurable.

For general Polish $X$, choose a topological embedding $f:X\to H$ with Borel image.
The pushforward map $f_*:\ProbMeasures{X}\to\ProbMeasures{H}$ is a topological embedding, as in
the Hilbert-cube argument for Prokhorov's theorem. Its image is
$$\{\nu\in\ProbMeasures{H}:\nu(f(X))=1\},$$
which is Borel by the first paragraph. Thus $\ProbMeasures{X}$ has a standard Borel structure.
If every evaluation of $k$ is measurable, then every evaluation of $f_*\circ k$ is measurable,
since $(f_*k(y))(C)=k(y)(f^{-1}(C))$. The compact case makes $f_*\circ k$ measurable, and the
inverse of the topological embedding on its image makes $k$ measurable.

The characterization says precisely that the weak Borel structure is generated by all Borel
evaluations. For a Borel isomorphism $g:X\to X'$, the identity
$(g_*\mu)(B)=\mu(g^{-1}(B))$ shows that pushforward and its inverse are measurable.
Choosing any compatible Polish topology on a standard Borel space therefore gives the same
measurable structure on its probability measures.
\end{proof}

\begin{lemma*}[\termdefineas{clopen probability extension}{Clopen probability extension}]
Let $\mathcal C$ be the algebra of clopen subsets of $\CantorSpace$, and let $Y$ be a standard Borel space.
For each $C\in\mathcal C$, suppose that $g_C:Y\to\ClosedInterval{0}{1}$ is Borel and that, for every $y\in Y$,
$$g_\emptyset(y)=0,\qquad g_\CantorSpace(y)=1,\qquad
g_{C\internalDisjointUnion E}(y)=g_C(y)+g_E(y)
$$
whenever $C,E\in\mathcal C$ are disjoint. There is a unique family of probability measures $\lambda_y$ on
$\CantorSpace$ satisfying $\lambda_y(C)=g_C(y)$ for all $y\in Y$ and $C\in\mathcal C$.
The map $y\mapsto\lambda_y$ is Borel for the weak topology on $\ProbMeasures{\CantorSpace}$, and
$y\mapsto\lambda_y(B)$ is Borel for every Borel $B\IncludedIn\CantorSpace$.
\end{lemma*}

\begin{proof}[Proof]
Fix $y$. If pairwise disjoint clopens $C_n$ have a clopen union $C$, compactness of $C$ gives a finite
$J\IncludedIn\omega$ such that $C=\bigcup_{n\in J}C_n$. Disjointness forces $C_n=\emptyset$ for $n\notin J$.
Finite additivity therefore gives
$$g_C(y)=\sum_{n\in J}g_{C_n}(y)=\sum_{n\in\omega}g_{C_n}(y).$$
Thus $C\mapsto g_C(y)$ is a premeasure. The clopens form an algebra generating the Borel sets, so
Carathéodory extension gives a probability measure $\lambda_y$. Uniqueness of finite measures on a generating
algebra shows that this extension is unique.

To check measurability of all Borel evaluations, let $\mathcal D$ consist of the Borel sets $B$ for which
$y\mapsto\lambda_y(B)$ is Borel. It contains $\mathcal C$ and is a Dynkin system: complements and disjoint
countable unions are handled by
$$\lambda_y(B^c)=1-\lambda_y(B),\qquad
\lambda_y\!\left(\bigcup_n B_n\right)=\sum_n\lambda_y(B_n).
$$
Since $\mathcal C$ is closed under intersections, the $\pi$--$\lambda$ theorem gives
$\mathcal D=\mathcal B(\CantorSpace)$. Hence the family is a Markov kernel.

It remains to verify Borel measurability into the weak topology. The algebra $\mathcal C$ is countable:
every clopen is a finite union of basic cylinders, by compactness. Consider
$$E:\ProbMeasures{\CantorSpace}\longrightarrow\ClosedInterval{0}{1}^{\mathcal C},\qquad
E(\lambda)=(C\mapsto\lambda(C)).
$$
For each clopen $C$, its indicator is continuous, so $\lambda\mapsto\lambda(C)=\int1_C\,d\lambda$ is
continuous in the weak topology. Thus $E$ is continuous; uniqueness on the generating algebra makes it injective.
By §{sec:prob-measure-space}, $\ProbMeasures{\CantorSpace}$ is compact. The target is Hausdorff, so $E$ is a
homeomorphism onto its closed image. The Borel structure of the countable product $\ClosedInterval{0}{1}^{\mathcal C}$
is
generated by its coordinates. Consequently, the clopen evaluations generate the Borel structure of
$\ProbMeasures{\CantorSpace}$. Since their compositions with $y\mapsto\lambda_y$ are exactly the Borel functions
$g_C$, this map is Borel.
\end{proof}

\begin{theorem*}[\termdefineas{disintegration theorem}{Disintegration}] Let $X, Y$ be standard Borel spaces, $\pi : X
\to Y$ Borel-measurable, and $\mu \in \ProbMeasures{X}$. Set $\nu := \pi_*\mu \in \ProbMeasures{Y}$. Then there is a
Borel
family $\IndexedFamily{\mu_y}{y\in Y}$ of probability measures on $X$, called a \termdefine{disintegration} of $\mu$
along $\pi$,
such that

\begin{enumerate}
\item $\mu_y(\pi^{-1}(\{y\})) = 1$ for $\nu$-almost every $y$;
\item $\mu(B) = \int_Y \mu_y(B) \, d\nu(y)$ for every Borel $B \IncludedIn X$.
\end{enumerate}

The disintegration is unique modulo $\nu$-null sets.

\end{theorem*}

Here $\mu_y$ is a conditional law of the original point $x \in X$ given the observed value $\pi(x)=y$. The support
condition says that, for almost every observed $y$, the conditional measure lives on the fiber above $y$; the integral
formula says that the original measure is recovered by first choosing $y$ according to $\nu$ and then choosing $x$
according to $\mu_y$.

<!-- formalization: structural (proof roadmap only) -->
\begin{proof}[Proof] We first obtain scalar conditional expectations, then extend their values on a
countable clopen algebra to probability measures. Measurability follows from the evaluation maps on that algebra.

Use the classification theorem in §{sec:standard-borel-classification} to realize $X$ as a Borel subset of
$\CantorSpace$. Let $\mathcal C$ be the countable Boolean algebra of clopen subsets of $\CantorSpace$.
Since $\mu$ is a probability measure, $X$ is nonempty; fix $x_0\in X$ for the null-set modifications below.

For each $C\in\mathcal C$, choose a $\pi^{-1}\mathcal B(Y)$-measurable representative of the
conditional expectation of $1_{C\cap X}$. Measurable factorization through $\pi$ gives a Borel function
$g_C:Y\to\mathbb R$ satisfying
$$g_C(\pi(x))=\mathbb E_\mu(1_{C\cap X}\mid\pi^{-1}\mathcal B(Y))(x).$$
This representative is integrable with respect to $\nu$. For every Borel $D\IncludedIn Y$, the change-of-variables
formula and the defining property of conditional expectation give
$$\begin{aligned}
\int_D g_C\,d\nu
&=\int_{\pi^{-1}(D)}g_C\circ\pi\,d\mu\\
&=\int_{\pi^{-1}(D)}1_{C\cap X}\,d\mu\\
&=\mu(C\cap X\cap\pi^{-1}(D)).
\end{aligned}$$

Positivity, preservation of constants, and additivity of conditional expectation imply, separately for each
clopen or disjoint pair of clopens,
$$\begin{gathered}
0\le g_C(y)\le1,\qquad g_\emptyset(y)=0,\qquad g_\CantorSpace(y)=1,\\
g_{C\internalDisjointUnion E}(y)=g_C(y)+g_E(y).
\end{gathered}$$
Each assertion holds for $\nu$-almost every $y$: its pullback holds $\mu$-almost everywhere, and
$\nu=\pi_*\mu$. Let $H\IncludedIn Y$ be the set where all these assertions hold simultaneously, for all
$C\in\mathcal C$ and all disjoint $C,E\in\mathcal C$. Each equality or inequality defines a Borel set.
Since $\mathcal C$ and $\mathcal C\times\mathcal C$ are countable, $H$ is Borel and $\nu(H)=1$.

Define the corrected functions by
$$\widehat g_C(y)=
\begin{cases}
g_C(y),&y\in H,\\
1_C(x_0),&y\notin H.
\end{cases}$$
They are Borel. On $H$ the probability identities already hold; outside $H$ they are the identities for the
point mass at $x_0$. Thus $C\mapsto\widehat g_C(y)$ is a finitely additive probability on $\mathcal C$ for
every $y$. Also $\widehat g_C=g_C$ almost everywhere, so every integral over $D$ above is unchanged.
By \termuse{clopen probability extension}, there is a unique probability measure $\tilde\mu_y$ on
$\CantorSpace$ satisfying $\tilde\mu_y(C)=\widehat g_C(y)$ for all $C\in\mathcal C$.
The map $y\mapsto\tilde\mu_y$ is Borel into $\ProbMeasures{\CantorSpace}$, and every Borel evaluation is Borel.
In particular, this Markov kernel satisfies
$$\int_D\tilde\mu_y(C)\,d\nu(y)=\mu(C\cap X\cap\pi^{-1}(D))$$
for every $C\in\mathcal C$ and every Borel $D\IncludedIn Y$.

Fix a Borel set $D\IncludedIn Y$. On the ambient Cantor space define
$$\begin{aligned}
Q_D(B)&=\int_D\tilde\mu_y(B)\,d\nu(y),\\
R_D(B)&=\mu(B\cap X\cap\pi^{-1}(D)).
\end{aligned}$$
These are finite measures. Countable additivity of $Q_D$ follows from countable additivity of each
$\tilde\mu_y$ and monotone convergence. The measure $R_D$ is the pushforward, under the inclusion of $X$,
of the restriction of $\mu$ to $\pi^{-1}(D)$. Both measures have total mass $\nu(D)$, which may be zero.
The preceding identity gives $Q_D(C)=R_D(C)$ for every $C\in\mathcal C$. Since the clopen algebra is a
$\pi$-system generating the Borel sets, uniqueness of finite measures gives $Q_D=R_D$. Consequently,
$$\int_D\tilde\mu_y(B)\,d\nu(y)=\mu(B\cap X\cap\pi^{-1}(D))$$
for every Borel $B\IncludedIn\CantorSpace$ and every Borel $D\IncludedIn Y$.

Apply this identity with $B=X^c$ and $D=Y$, where the complement is taken in the ambient Cantor space.
Since $X^c\cap X=\emptyset$,
$$\int_Y\tilde\mu_y(X^c)\,d\nu(y)=0.$$
The integrand is nonnegative and Borel, so $\tilde\mu_y(X^c)=0$ almost everywhere. Equivalently,
$\tilde\mu_y(X)=1$ almost everywhere. Thus
$$H_X=\{y\in Y:\tilde\mu_y(X)=1\}$$
is Borel and has $\nu$-measure $1$.

Make a second null-set modification by setting
$$\lambda_y=
\begin{cases}
\tilde\mu_y,&y\in H_X,\\
\delta_{x_0},&y\notin H_X.
\end{cases}$$
This remains a Borel probability family on the ambient space, and now $\lambda_y(X)=1$ for every $y$.
Every Borel subset $A$ of $X$ is also Borel in the ambient space, since $X$ is Borel. Define
$$\mu_y(A)=\lambda_y(A).$$
This gives a probability measure on $X$ for every $y$, and $y\mapsto\mu_y(A)$ is Borel for every such $A$.
The modification affects only a fixed $\nu$-null set, so for every Borel $A\IncludedIn X$ and
$D\IncludedIn Y$,
$$\int_D\mu_y(A)\,d\nu(y)=\mu(A\cap\pi^{-1}(D)).$$
Taking $D=Y$ gives the integral formula in the theorem.

Choose a countable family $\Sequence{G_n}{n\in\omega}$ generating $\mathcal B(Y)$ and separating points.
For each $n$ and every Borel $D\IncludedIn Y$, the extended identity gives
$$\begin{aligned}
\int_D\mu_y(\pi^{-1}(G_n))\,d\nu(y)
&=\mu(\pi^{-1}(G_n)\cap\pi^{-1}(D))\\
&=\nu(G_n\cap D)=\int_D1_{G_n}(y)\,d\nu(y).
\end{aligned}$$
Uniqueness of measurable densities therefore gives
$\mu_y(\pi^{-1}(G_n))=1_{G_n}(y)$ almost everywhere. Countability lets us remove one common null set
so that these identities hold for all $n$ simultaneously. For any remaining $y$, put
$$V_n(y)=
\begin{cases}
\pi^{-1}(G_n),&y\in G_n,\\
\SetDifference{X}{\pi^{-1}(G_n)},&y\notin G_n.
\end{cases}$$
Each $V_n(y)$ has $\mu_y$-measure $1$, including the second case because the excluded set has measure zero.
Their countable intersection also has measure $1$. Moreover,
$$\begin{aligned}
x\in\bigcap_n V_n(y)
&\iff \forall n\;(\pi(x)\in G_n\iff y\in G_n)\\
&\iff \pi(x)=y,
\end{aligned}$$
since the family separates points. Hence $\mu_y(\pi^{-1}(\{y\}))=1$ for $\nu$-almost every $y$.

For uniqueness, first recover the full conditional identity from the two conditions in the theorem.
For any probability family satisfying them, its fiber condition implies, outside one null set,
$$\mu_y(A\cap\pi^{-1}(D))=1_D(y)\mu_y(A)$$
for Borel $A\IncludedIn X$ and $D\IncludedIn Y$. Indeed, on the fiber over $y$, membership in
$\pi^{-1}(D)$ is constant and equals membership of $y$ in $D$; the complement of the fiber has measure zero.
Apply the theorem's integral formula to $A\cap\pi^{-1}(D)$ to obtain
$$\int_D\mu_y(A)\,d\nu(y)=\mu(A\cap\pi^{-1}(D)).$$

Let $(\mu_y)$ and $(\rho_y)$ be two such families. Choose a countable generating family
$\Sequence{A_n}{n\in\omega}$ for $\mathcal B(X)$. For every finite $F\IncludedIn\omega$, set
$$A_F=\bigcap_{n\in F}A_n,\qquad A_\emptyset=X.$$
These sets form a countable $\pi$-system generating $\mathcal B(X)$: intersections correspond to unions of
finite index sets, and singletons among the index sets recover the original generators.
For each $F$, the recovered conditional identity shows that
$$\int_D\mu_y(A_F)\,d\nu(y)=\int_D\rho_y(A_F)\,d\nu(y)$$
for every Borel $D\IncludedIn Y$. Uniqueness of measurable densities gives
$\mu_y(A_F)=\rho_y(A_F)$ almost everywhere. There are only countably many finite $F$, so outside one common
null set the two probability measures agree on the whole generating $\pi$-system. Uniqueness of finite
measures now gives $\mu_y=\rho_y$ there. Thus the exceptional null set is independent of the Borel set being
evaluated, as required.
\end{proof}

<!-- formalization: skip (illustrative specialization of disintegration) -->
\begin{example*}[Product measures]
If $X=Y\times Z$, $\pi(y,z)=y$, and $\mu=\nu\times\lambda$, then the disintegration is
constant across fibers: after identifying each fiber $\{y\}\times Z$ with $Z$, its conditional measure is $\lambda$.
As a measure on $X$, the family varies with $y$ and is given by
$$\mu_y=\delta_y\times\lambda.$$
The theorem is the non-product generalization: even when the fibers twist measurably and no topological bundle structure
is present, standard Borelness still supplies a measurable family of fiber measures.
\end{example*}

\begin{example*}[Conditional distributions]
If $X$ and $Y$ are random variables on a probability space with values in standard Borel spaces $S$ and $T$,
apply the theorem to the joint law on $S\times T$ and the projection to $T$.
Push each conditional measure on the product forward to the first coordinate, and denote the resulting law by
$\mu_y$. The kernel
$$y \mapsto \mathbb P(X\in\cdot\mid Y=y)$$
is a regular conditional distribution. Ordinary conditional expectation is recovered by integration:
$$\mathbb E[f(X)\mid Y=y]=\int f(x)\,d\mu_y(x)$$
for bounded Borel $f$.
\end{example*}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
regular conditional
probabilityの定義はBorelMeasureProse.IsRegularConditionalProbabilityに接続した。
残る一般可測空間での非存在と諸分野での用途は、具体例の構成・証明を提示しない背景説明で、後続の局所補題にも用いない。
標準Borel空間上の存在はDisintegrationFibersとConditionalDistributionsで別に対応済み。)
--> The standard-Borel hypothesis is essential: the same statement fails for general measurable spaces, where regular
conditional probabilities need not exist.<!--
formalization: skip-end
-->  More explicitly, let $\Tuple{\Omega,\mathcal F,\mathbb P}$ be a probability space
and let $\mathcal G\IncludedIn\mathcal F$ be a sub-$\sigma$-algebra. A
\termdefineas{regular conditional probability}{regular conditional probability} $\mathbb P(\mathord\cdot\mid\mathcal G)$
is a $\mathcal G$-measurable family $\omega\mapsto\mathbb P_\omega$ of probability measures such that
$\omega\mapsto\mathbb P_\omega(A)$ is a version of $\mathbb E(1_A\mid\mathcal G)$ for every $A\in\mathcal F$.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
regular conditional
probabilityの定義はBorelMeasureProse.IsRegularConditionalProbabilityに接続した。
残る一般可測空間での非存在と諸分野での用途は、具体例の構成・証明を提示しない背景説明で、後続の局所補題にも用いない。
標準Borel空間上の存在はDisintegrationFibersとConditionalDistributionsで別に対応済み。)
--> Disintegration supplies such families on Polish and standard Borel state spaces; they can fail on general measurable
spaces. It is the descriptive backbone of Markov kernels, conditional expectations, Bayesian inverses, and the
measure-theoretic version of fiber bundles. Most modern probability texts assume Polish state spaces precisely so that
this theorem is available without further qualification.<!--
formalization: skip-end
-->

## Zero-One Laws {#sec:zero-one-laws}

\begin{mathmeta}
  \vars{p}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
この節で扱う2種類の確率0-1則とBaireカテゴリーの類似を予告する導入。3つの定理と局所証明自体は後続でそれぞれ対応している。)
-->
On product Polish spaces, two classical \termdefineas{zero-one law}{zero-one laws} force certain Borel events to have
trivial probability, and a topological analogue does the same for Baire category. They are the measure-theoretic
backbone of ergodicity arguments throughout the rest of the text.<!--
formalization: skip-end
-->

For a product space $X = \prod_n X_n$ with product probability measure $\mu = \prod_n \mu_n$, the
\termdefineas{tail sigma-algebra}{tail $\sigma$-algebra} is
$$\mathcal T \;:=\; \bigcap_{N \in \omega}\, \sigma(\pi_n : n \ge N),$$
the Borel events whose membership is unaffected by altering any finite prefix. <!--
formalization: skip-begin (引用・背景説明・読書案内:
tail σ代数の定義と有限prefix不変性の同値はTopologicalTail.tail_measurable_iffに接続した。
残る3例は証明を展開しない例示であり、この章の後続の証明に依存する局所補題ではない。)
--> Examples in $\CantorSpace$: "$x$ has
infinitely many $1$'s," "$\sum_n x_n / 2^{n+1}$ is rational," and "$x \in N$" for any Borel null set $N$ saturated
under the eventual-agreement relation $\EventualEqualityER$ of §{sec:e0-glimm-effros}.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefineas{Dynkin pi-lambda theorem}{Dynkin's $\pi$-$\lambda$ theorem}]
If $\mathcal P$ is a $\pi$-system and $\mathcal D$ is a Dynkin system containing $\mathcal P$, then
$\sigma(\mathcal P)\IncludedIn\mathcal D$.
\end{lemma*}

\begin{proof}[Proof]
Let $\mathcal D_0$ be the smallest Dynkin system containing $\mathcal P$.
For any $A\in\mathcal D_0$, consider
$$\mathcal D_A:=\{B:A\cap B\in\mathcal D_0\}.$$
This is a Dynkin system. It contains $\emptyset$. For complementation, use
$$A\cap B^c=\SetDifference{A}{A\cap B}.$$
A Dynkin system is closed under differences of nested members: if $E\IncludedIn A$ and both sets belong to it,
then $\SetDifference{A}{E}=(E\cup A^c)^c$ belongs to it, since $E$ and $A^c$ are disjoint.
Intersections with $A$ distribute over countable unions and preserve disjointness, giving the remaining closure.

First fix $A\in\mathcal P$. The $\pi$-system property implies $\mathcal P\IncludedIn\mathcal D_A$,
so minimality gives $\mathcal D_0\IncludedIn\mathcal D_A$.
Thus $A\cap B\in\mathcal D_0$ whenever $A\in\mathcal P$ and $B\in\mathcal D_0$.
Now fix $B\in\mathcal D_0$. By this conclusion and commutativity of intersection,
$\mathcal P\IncludedIn\mathcal D_B$, so minimality gives $\mathcal D_0\IncludedIn\mathcal D_B$.
Hence $\mathcal D_0$ is closed under binary intersections.

It is therefore closed under finite unions and differences as well. For any sequence $E_n\in\mathcal D_0$,
put
$$E'_n:=\SetDifference{E_n}{\bigcup_{i<n}E_i}.$$
These sets belong to $\mathcal D_0$, are pairwise disjoint, and have the same union as the $E_n$.
The Dynkin closure now gives $\bigcup_nE_n\in\mathcal D_0$.
Thus $\mathcal D_0$ is a $\sigma$-algebra containing $\mathcal P$, and
$\sigma(\mathcal P)\IncludedIn\mathcal D_0\IncludedIn\mathcal D$.
\end{proof}

\begin{theorem*}[\termdefine{Kolmogorov 0-1 law}] Let $\mu = \prod_n \mu_n$ be a product probability measure on a
product of standard Borel spaces. Every tail event $A \in \mathcal T$ has $\mu(A) \in \{0, 1\}$.

\end{theorem*}

\begin{proof}[Proof] For each $N$, write $\mathcal A_N := \sigma(\pi_0, \ldots, \pi_{N-1})$ for the prefix
$\sigma$-algebra and $\mathcal B_N := \sigma(\pi_n : n \ge N)$ for the tail-from-$N$ $\sigma$-algebra. Independence of
coordinates under the product measure gives
$$\mu(B \cap C) = \mu(B)\mu(C) \qquad (B \in \mathcal A_N,\, C \in \mathcal B_N).$$
Let $A \in \mathcal T$. Then $A \in \mathcal B_N$ for every $N$, so for every $B \in \mathcal A_\infty := \bigcup_N
\mathcal A_N$,
\begin{equation*}
\mu(A \cap B) = \mu(A)\mu(B). \tag{$\dagger$}
\end{equation*}

The prefix $\sigma$-algebras increase with $N$. If $B\in\mathcal A_N$ and $C\in\mathcal A_M$, then
$B\cap C\in\mathcal A_{\max\{N,M\}}$, and $B^c\in\mathcal A_N$. Thus $\mathcal A_\infty$ is an algebra,
in particular a $\pi$-system. It generates the full Borel $\sigma$-algebra of $X$, since it contains every
coordinate \termuse{cylinder} and is contained in the product $\sigma$-algebra.

Now put
$$\mathcal D := \{B \in \mathrm{Borel}(X) : \mu(A \cap B) = \mu(A)\mu(B)\}.$$
This class contains $X$. If $B\in\mathcal D$, then
$$
\begin{aligned}
\mu(A\cap B^c)
&=\mu(A)-\mu(A\cap B)\\
&=\mu(A)(1-\mu(B))\\
&=\mu(A)\mu(B^c),
\end{aligned}
$$
so $B^c\in\mathcal D$.

If $B_n\in\mathcal D$ are pairwise disjoint, countable additivity gives
$$
\begin{aligned}
\mu\Bigl(A\cap\bigcup_n B_n\Bigr)
&=\sum_n\mu(A\cap B_n)\\
&=\mu(A)\sum_n\mu(B_n)\\
&=\mu(A)\mu\Bigl(\bigcup_n B_n\Bigr).
\end{aligned}
$$
Hence $\bigcup_n B_n\in\mathcal D$, and $\mathcal D$ is a Dynkin system containing $\mathcal A_\infty$.

By \termuseas{Dynkin pi-lambda theorem}{Dynkin's $\pi$-$\lambda$ theorem},
$\mathcal D \supseteq \sigma(\mathcal A_\infty) = \mathrm{Borel}(X)$. Setting $B := A$ in $(\dagger)$ yields
$\mu(A) = \mu(A)^2$, so $\mu(A) \in \{0, 1\}$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のHewitt–Savage定理への導入で、Cesàro極限とE0飽和集合を証明なしに例示する。
有限置換不変性を仮定した定理とその局所証明は別に対応済み。)
--> The strengthening to permutation-invariance covers events like the Cesàro-mean limit and any
$\EventualEqualityER$-saturated set:<!--
formalization: skip-end
-->

\begin{mathmeta}
  \forward{SymmetricDifference}
\end{mathmeta}

\begin{lemma*}[\termdefineas{approximation by a generating algebra}{Approximation by a generating algebra}]
Let $\mathcal A$ be an algebra generating a $\sigma$-algebra $\mathcal F$, and let $\mu$ be a probability measure on
$\mathcal F$. For every $E\in\mathcal F$ and every $\varepsilon>0$, some $B\in\mathcal A$ satisfies
$$\mu(E\mathbin{\triangle} B)<\varepsilon.$$
\end{lemma*}

\begin{proof}[Proof]
Let $\mathcal R$ be the class of sets in $\mathcal F$ with the approximation property.
It contains $\mathcal A$. Taking complements preserves the symmetric difference, so $\mathcal R$ is closed
under complements.

Let $E_n\in\mathcal R$ be pairwise disjoint and fix $\varepsilon>0$.
Choose numbers $\delta_n>0$ with $\sum_n\delta_n<\varepsilon/2$, and choose $B_n\in\mathcal A$ such that
$$\mu(\SymmetricDifference{E_n}{B_n})<\delta_n.$$
Continuity from above for the decreasing tails gives $N$ with
$$\mu\!\left(\bigcup_{n\ge N}E_n\right)<\varepsilon/2.$$
Put $B:=\bigcup_{n<N}B_n\in\mathcal A$. The symmetric difference between $B$ and $\bigcup_nE_n$ is contained
in the union of the first $N$ approximation errors and the remaining tail. Hence
$$\begin{aligned}
\mu\!\left(\SymmetricDifference{B}{\bigcup_nE_n}\right)
&\le\sum_{n<N}\mu(\SymmetricDifference{B_n}{E_n})
  +\mu\!\left(\bigcup_{n\ge N}E_n\right)\\
&<\varepsilon/2+\varepsilon/2=\varepsilon.
\end{aligned}$$
Thus $\mathcal R$ is a Dynkin system containing the algebra $\mathcal A$, which is a $\pi$-system.
The \termuseas{Dynkin pi-lambda theorem}{Dynkin $\pi$--$\lambda$ theorem} gives
$\mathcal F=\sigma(\mathcal A)\IncludedIn\mathcal R$.
\end{proof}

\begin{theorem*}[\termdefine{Hewitt--Savage 0-1 law}] Let $\mu = \nu^\omega$ be the i.i.d. product of a probability
measure $\nu$ on a standard Borel space $X_0$. Every Borel event $A \IncludedIn \seqPower{X_0}{\omega}$ invariant under
every finite-support permutation of $\omega$ has $\mu(A) \in \{0, 1\}$.

\end{theorem*}

\begin{proof}[Proof] Apply the generating-algebra approximation lemma to $\mathcal A_\infty$. For every
$\varepsilon > 0$ there exist $N$ and $B \in \mathcal A_N$ with $\mu(A \triangle B) < \varepsilon$.

Let $\sigma$ be the permutation of $\omega$ swapping the blocks $\{0, 1, \ldots, N-1\}$ and $\{N, N+1, \ldots, 2N-1\}$
and fixing all other coordinates. Define the Borel automorphism $\sigma^* : \seqPower{X_0}{\omega} \to
\seqPower{X_0}{\omega}$ by $\sigma^*(x)_n = x_{\sigma(n)}$. Since $\mu$ is i.i.d., $\sigma^*$ is measure-preserving.
Since $A$ is permutation-invariant, $\sigma^*(A) = A$.

Apply $\sigma^*$ to the approximation:
$$\mu(A \triangle \sigma^*(B)) = \mu(\sigma^*(A) \triangle \sigma^*(B)) = \mu(\sigma^*(A \triangle B)) = \mu(A \triangle
B) < \varepsilon.$$

Now $B \in \mathcal A_N$ depends on coordinates $0, \ldots, N-1$, while $\sigma^*(B)$ depends on coordinates $N, \ldots,
2N-1$. These two coordinate blocks are independent under the i.i.d. product, so
$$\mu(B \cap \sigma^*(B)) = \mu(B)\mu(\sigma^*(B)) = \mu(B)^2.$$

Combine the two approximations using $A = A \cap A$ and
$$
(S\cap T)\mathbin{\triangle}(S'\cap T')
\IncludedIn (S\mathbin{\triangle} S')\cup(T\mathbin{\triangle} T')
$$
with $S=T=A$, $S'=B$, and $T'=\sigma^*(B)$:
$$
\begin{aligned}
\Abs{\mu(A) - \mu(B \cap \sigma^*(B))}
&= \Abs{\mu(A \cap A) - \mu(B \cap \sigma^*(B))}\\
&\le \mu(A \triangle B) + \mu(A \triangle \sigma^*(B))\\
&< 2\varepsilon.
\end{aligned}
$$

Also $\Abs{\mu(A) - \mu(B)} < \varepsilon$, hence $\Abs{\mu(A)^2 - \mu(B)^2} < 2\varepsilon$ since both are in
$\ClosedInterval{0}{1}$.
Therefore
$$\Abs{\mu(A) - \mu(A)^2} \;\le\; \Abs{\mu(A) - \mu(B)^2} + \Abs{\mu(B)^2 - \mu(A)^2} \;<\; 2\varepsilon + 2\varepsilon
= 4\varepsilon.$$
Letting $\varepsilon \to 0$ gives $\mu(A) = \mu(A)^2$, so $\mu(A) \in \{0, 1\}$. 
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後に引用するKuratowski–Ulamと位相的0-1則への案内。ここで独立した構成や証明を提示する文ではない。)
--> The Baire-category analogue replaces "null" with "meager," and Fubini-style independence with the following standard
category theorem.<!--
formalization: skip-end
-->

<!-- formalization: skip (classical Kuratowski--Ulam theorem cited as external category infrastructure) -->
\begin{fact*}[\termdefineas{Kuratowski--Ulam theorem}{Kuratowski--Ulam}]
Let $P$ and $Y$ be Polish spaces, and let $M\IncludedIn P\times Y$ be Borel. Then $M$ is meager iff the section
$M_p:=\{y:\Pair{p}{y}\in M\}$ is meager for comeagerly many $p\in P$.
\end{fact*}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Kuratowski–UlamのKechris Theorem 8.41への出典表示。外部入力の文献情報を局所的な証明として数えない。)
--> This is [@Kechris1995, Theorem 8.41].<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefineas{Kuratowski--Ulam rectangle lemma}{Kuratowski--Ulam rectangle consequence}]
Let $P$ and $Y$ be Polish spaces, let $W\IncludedIn P$ be non-meager, and let $B\IncludedIn Y$ be arbitrary.
Then $W\times B$ is meager in $P\times Y$ iff $B$ is meager in $Y$.
In particular, if $P$ is nonempty, this applies with $W=P$.
\end{lemma*}

\begin{proof}[Proof]
For the forward direction, cover $W\times B$ by closed nowhere-dense sets $F_n$.
Choose a countable base of nonempty open sets $U_m$ in $P$, and put
$$D_{n,m}:=\{y\in Y:U_m\times\{y\}\IncludedIn F_n\}.$$
Each $D_{n,m}$ is closed, since it is the intersection, over $p\in U_m$, of the inverse images of $F_n$
under the continuous maps $y\mapsto\Pair{p}{y}$. If $D_{n,m}$ contained a nonempty open set $V$, then
$U_m\times V$ would be a nonempty open subset of $F_n$, contrary to nowhere density.
Thus every $D_{n,m}$ is nowhere dense.

For $y\in B$, the closed sections $\{p\in P:\Pair{p}{y}\in F_n\}$ cover $W$.
Since $W$ is not meager, at least one section has nonempty interior and hence contains some $U_m$.
Consequently $y\in D_{n,m}$, and
$$B\IncludedIn\bigcup_{n,m}D_{n,m}.$$
This proves that $B$ is meager. Conversely, the product with $P$ of any nowhere-dense subset of $Y$ is nowhere dense
in $P\times Y$. Applying this to a countable nowhere-dense cover of $B$ shows that $P\times B$, and hence
$W\times B$, is meager.
\end{proof}

For an arbitrary subset $A\IncludedIn\prod_nX_n$, say that $A$ is a \termdefine{tail set} if changing finitely many
coordinates does not change membership in $A$. For Borel $A$, this is equivalent to $A\in\mathcal T$.
Indeed, tail invariance writes $A$ as the inverse image, under restriction to the remaining coordinates, of its
Borel section at any fixed finite prefix. Thus $A\in\sigma(\pi_n:n\ge N)$ for every $N$.
Conversely, a member of $\sigma(\pi_n:n\ge N)$ cannot distinguish points that agree at all coordinates $n\ge N$.
Membership in $\mathcal T$ therefore implies tail invariance.

\begin{theorem*}[\termdefine{Topological 0-1 law}] Let $X = \prod_n X_n$ be a countable product of nonempty Polish
spaces. Every tail set in $X$ with the Baire property is either meager or comeager.

\end{theorem*}

\begin{proof}[Proof] Let $A \IncludedIn X$ be a tail set with the Baire property, and suppose $A$ is non-meager. We
show that $A$ is
comeager.

By the BP, $A = U \triangle M$ for some open $U$ and meager $M$. Non-meagerness of $A$ forces $U$ to be nonempty, so $U$
contains some basic open box
$$V \;=\; \prod_{n < N} V_n \;\times\; \prod_{n \ge N} X_n$$
with each $V_n \IncludedIn X_n$ a nonempty open set. Since $V \IncludedIn U$,
$$\SetDifference{V}{A} \;\IncludedIn\; M,$$
which is meager. Hence $A$ is comeager in $V$.

Set $P_N := \prod_{n < N} X_n$ and $Y_N := \prod_{n \ge N} X_n$. Tail-invariance gives a set-theoretic decomposition:
there is a set $A_N \IncludedIn Y_N$ such that
$$A = P_N \times A_N, \qquad V \cap A = \prod_{n < N} V_n \times A_N.$$
Indeed, put $y \in A_N$ iff $\Pair{p}{y} \in A$ for some, equivalently every, $p \in P_N$. No Borel or Baire-property
claim
about $A_N$ is needed.

Compute
$$\SetDifference{V}{A} \;=\; \prod_{n < N} V_n \;\times\; \Big(\SetDifference{\prod_{n \ge N} X_n}{A_N}\Big).$$
The first factor $\prod_{n<N}V_n$ is a nonempty open subset of $P_N$, so the Baire category theorem says that it is
not meager in $P_N$. Apply the \termuseas{Kuratowski--Ulam rectangle lemma}{rectangle lemma} in $P_N\times Y_N$.
It follows that $\SetDifference{\prod_{n \ge N} X_n}{A_N}$ is meager, or equivalently that $A_N$ is comeager in the
tail factor.

Now expand the global complement:
$$\SetDifference{X}{A} \;=\; \prod_{n < N} X_n \;\times\; \Big(\SetDifference{\prod_{n \ge N} X_n}{A_N}\Big).$$
The same rectangle consequence shows the complement is meager, since the right factor is meager. Therefore $A$ is
comeager.
\end{proof}

These three theorems explain several facts used elsewhere in the text. The non-smoothness of $\EventualEqualityER$
in §{sec:e0-glimm-effros} reduces to \termuseas{Hewitt--Savage 0-1 law}{Hewitt--Savage}: every
$\EventualEqualityER$-invariant Borel set is invariant under finite-support permutations for the fair-coin product.
Hence any $\EventualEqualityER$-invariant Borel function with values in a standard Borel space is
$\mu$-almost everywhere constant. To see this, take a countable point-separating Borel family in the target and
intersect the full-measure side of each inverse image; all points in this conull intersection have the same value.

<!-- formalization: skip-begin (forward comparison with the later forcing characterizations) -->
The \termforward{Cohen forcing} / \termforward{random forcing} duality of
§{sec:cohen-forcing-detail}--§{sec:random-forcing-detail} gives a related comparison: a Cohen real avoids every
meager Borel set coded in the ground model, and a random real avoids every null Borel set coded there.
For Borel tail sets, the corresponding 0-1 law says that each set is either meager or comeager, respectively null
or conull. Thus the associated generic real belongs to such a set exactly in the comeager or conull case.
<!-- formalization: skip-end -->

## Measure Algebras {#sec:measure-algebras-maharam}

\begin{mathmeta}
  \define{MeasureAlg}
  \vars{n}{Nat}
  \vars{u}{Real}
  \vars{s,w}{Seq}
  \vars{D}{Set}
  \vars{t}{Real}
\end{mathmeta}

For a finite Borel measure $\mu$ on a Polish space $X$, the \termdefine{measure algebra} is the Boolean algebra
$$\MeasureAlg{X}{\mu} \;:=\; \mathrm{Borel}(X) / \mathrm{null}_\mu,$$
the Borel sets modulo $\mu$-null sets, with $[A] \le [B]$ iff $\mu(\SetDifference{A}{B}) = 0$.
For non-atomic probability measures, the following theorem determines this measure algebra up to isomorphism.

\begin{theorem*}[\termdefineas{Maharam theorem}{Maharam}, simplest form] For any two non-atomic probability measures
$\mu, \nu$ on standard Borel spaces $X, Y$, the measure algebras $\Pair{\MeasureAlg{X}{\mu}}{\mu}$ and
$\Pair{\MeasureAlg{Y}{\nu}}{\nu}$ are isomorphic as measure algebras. A witness is a measure-preserving Borel
isomorphism
$\SetDifference{X}{N} \to \SetDifference{Y}{N'}$ defined off null sets.

\end{theorem*}

<!-- formalization: skip (classification analogy following Maharam's theorem) -->
This is the probability-space analogue of the classification theorem for uncountable standard Borel spaces: once atoms
are absent, there is only one probability algebra up to null sets. A standard representative is the unit interval
with Lebesgue measure, or equivalently Cantor space with fair-coin product measure.

<!-- formalization: structural (proof goal only) -->
\begin{proof}[Proof for non-atomic standard probability spaces] We show that every non-atomic standard probability space
is measure-isomorphic modulo null sets to $\Pair{\ClosedInterval{0}{1}}{\lambda}$.

First suppose $X=\ClosedInterval{0}{1}$ with a non-atomic Borel probability measure $\mu$. Its distribution function
$$F(t):=\mu(\ClosedInterval{0}{t})$$
is continuous and nondecreasing, with $F(0)=0$ and $F(1)=1$. Define the generalized inverse
$$G(u):=\inf\{t\in\ClosedInterval{0}{1}:F(t)\ge u\}.$$

For each $u\in\ClosedInterval{0}{1}$, the set $C_u:=\{t\in\ClosedInterval{0}{1}:u\le F(t)\}$ contains $1$ and is closed.
It therefore contains its infimum, so $u\le F(G(u))$. Monotonicity of $F$ now gives
$$G(u)\le t\quad\Longleftrightarrow\quad u\le F(t)
\qquad\Pair{u}{t}\in \ClosedInterval{0}{1}.$$
In particular, $G$ is nondecreasing. By the intermediate value theorem, choose $t$ with $F(t)=u$.
The equivalence gives $G(u)\le t$, whence
$$u\le F(G(u))\le F(t)=u.$$
Thus $F(G(u))=u$ for every $u$, including both endpoints. Both $F$ and $G$ are Borel maps.

The equivalence also identifies every initial-interval preimage:
$$\{u:G(u)\le t\}=\ClosedInterval{0}{F(t)},\qquad
\lambda(\{u:G(u)\le t\})=F(t)=\mu(\ClosedInterval{0}{t}).$$
Initial intervals determine Borel probability measures on the unit interval, so $G_*\lambda=\mu$.
Pushing this identity forward by $F$ and using $F\circ G=\mathrm{id}$ gives
$$F_*\mu=F_*(G_*\lambda)=(F\circ G)_*\lambda=\lambda.$$

Let $D$ be the set of values whose fibers under $F$ contain more than one point.
If $x<y$ and $F(x)=F(y)=u$, choose a rational $q$ strictly between $x$ and $y$.
Monotonicity gives $F(q)=u$, so
$$D\IncludedIn F(\QQ\cap\ClosedInterval{0}{1}).$$
Thus $D$ is countable, Borel, and Lebesgue null. By $F_*\mu=\lambda$, the Borel set
$N:=F^{-1}(D)$ is $\mu$-null. If $t\notin N$, the equality $F(G(F(t)))=F(t)$ and the singleton-fiber condition
imply $G(F(t))=t$. Conversely, $u\notin D$ implies $G(u)\notin N$ because $F(G(u))=u$.
Consequently the restrictions
$$\begin{aligned}
F&:\SetDifference{\ClosedInterval{0}{1}}{N}\longrightarrow\SetDifference{\ClosedInterval{0}{1}}{D},\\
G&:\SetDifference{\ClosedInterval{0}{1}}{D}\longrightarrow\SetDifference{\ClosedInterval{0}{1}}{N}
\end{aligned}$$
are inverse Borel maps. Their measure-preserving property follows by restricting the pushforward identities
to these conull Borel subspaces.

For a general standard Borel $X$ with non-atomic $\mu$, choose a Borel isomorphism
$$\theta:X\to B\IncludedIn\ClosedInterval{0}{1}$$
onto a Borel subset, using §{sec:standard-borel-classification}. Regard $\eta:=\theta_*\mu$ as a measure on
$\ClosedInterval{0}{1}$, so $\eta(\SetDifference{\ClosedInterval{0}{1}}{B})=0$. It is again a non-atomic probability
measure.
Fix $x_0\in X$, and extend $\theta^{-1}$ to a Borel map $q:\ClosedInterval{0}{1}\to X$ by setting $q(u)=x_0$ outside
$B$.
Then $q\circ\theta=\mathrm{id}$ everywhere and $\theta\circ q=\mathrm{id}$ $\eta$-almost everywhere.
Apply the interval construction to $\eta$, and put
$$f_X:=F\circ\theta,\qquad g_X:=q\circ G.$$
The pushforward identities give
$$\begin{aligned}
(f_X)_*\mu&=F_*\eta=\lambda,\\
(g_X)_*\lambda&=q_*\eta=\mu.
\end{aligned}$$

Moreover, $g_X(f_X(x))=x$ for $\mu$-almost every $x$: outside the inverse image of the exceptional set
for $G\circ F$, this follows from $q\circ\theta=\mathrm{id}$. Since $G_*\lambda=\eta$ and $\eta(B)=1$,
we have $G(u)\in B$ for $\lambda$-almost every $u$. At these points,
$$f_X(g_X(u))=F(\theta(q(G(u))))=F(G(u))=u.$$
Thus $f_X$ and $g_X$ preserve measure and are inverse almost everywhere.

Construct $f_Y,g_Y$ in the same way for $\Pair{Y}{\nu}$, and set
$$h:=g_Y\circ f_X:X\to Y,\qquad k:=g_X\circ f_Y:Y\to X.$$
These Borel maps preserve measure. They satisfy $k(h(x))=x$ for $\mu$-almost every $x$ and
$h(k(y))=y$ for $\nu$-almost every $y$. For example, the first identity follows from
$$k(h(x))=g_X(f_Y(g_Y(f_X(x))))=g_X(f_X(x))=x.$$
The middle equality fails only when $f_X(x)$ belongs to a $\lambda$-null exceptional set, whose inverse image
is $\mu$-null because $(f_X)_*\mu=\lambda$. The other identity follows in the same way.

To obtain exact inverse maps on Borel subspaces, put
$$\begin{aligned}
L&:=\{x:k(h(x))=x\},&R&:=\{y:h(k(y))=y\},\\
X_0&:=L\cap h^{-1}(R),&Y_0&:=R.
\end{aligned}$$
Both $L$ and $R$ are conull Borel sets, and $h$ preserves measure, so $X_0$ and $Y_0$ are conull Borel sets.
For $x\in X_0$ we have $h(x)\in Y_0$ and $k(h(x))=x$. If $y\in Y_0$, then $h(k(y))=y$ and
$k(h(k(y)))=k(y)$, so $k(y)\in X_0$. Hence the restrictions of $h$ and $k$ are inverse Borel maps
between $X_0$ and $Y_0$. Restricting the pushforward identities shows that they preserve the subspace measures.

For a Borel set $S\IncludedIn X$, the sets $h(S\cap X_0)$ and $k^{-1}(S)$ agree on $Y_0$.
The first is Borel because the restriction of $h$ is a Borel isomorphism. Thus the induced maps on measure algebras are
$$\begin{aligned}
\Phi([S])&:=[h(S\cap X_0)]=[k^{-1}(S)],\\
\Psi([T])&:=[h^{-1}(T)].
\end{aligned}$$
Inverse images under $h$ and $k$ preserve null sets, so these maps are well-defined. They preserve Boolean operations
because inverse images do. The almost-everywhere inverse identities imply that $\Phi$ and $\Psi$ are inverse.
Finally,
$$\nu(k^{-1}(S))=\mu(S),\qquad \mu(h^{-1}(T))=\nu(T),$$
so the isomorphisms preserve measure.
\end{proof}

The atoms are the only extra data in the finite-measure case. For a finite Borel measure $\mu$, an
\termdefine{atom of a measure} is a Borel set $E$ with $\mu(E)>0$ such that every Borel $F\IncludedIn E$ satisfies
$\mu(F)=0$ or $\mu(F)=\mu(E)$. Equivalently, its class is an atom of the Boolean algebra $\MeasureAlg{X}{\mu}$.

\begin{proposition*}[\termdefineas{atomic decomposition of a measure}{Atomic decomposition}]
Let $\mu$ be a finite Borel measure on a standard Borel space $X$. Put
$$A:=\{x\in X:\mu(\{x\})>0\},\qquad X_{\mathrm{na}}:=\SetDifference{X}{A}.$$
Then $A$ is countable, and $\mu_{\mathrm{na}}:=\restrict{\mu}{X_{\mathrm{na}}}$, regarded as a measure on the
Borel subspace $X_{\mathrm{na}}$, has no atoms. There is a measure-preserving Boolean algebra isomorphism
$$\MeasureAlg{X}{\mu}
\;\cong\;
\MeasureAlg{X_{\mathrm{na}}}{\mu_{\mathrm{na}}}\times\PowerSet{A},$$
where a subset $S\IncludedIn A$ has weight
$$w(S):=\sum_{x\in S}\mu(\{x\}).$$
\end{proposition*}

\begin{proof}[Proof]
First let $E$ be an atom, and choose a countable point-separating Borel family $\Sequence{G_n}{n\in\omega}$.
For each $n$, put
$$V_n:=
\begin{cases}
G_n,&\mu(E\cap G_n)=\mu(E),\\
\SetDifference{X}{G_n},&\mu(E\cap G_n)=0.
\end{cases}$$
Then $\mu(\SetDifference{E}{V_n})=0$. Consequently
$$C:=E\cap\bigcap_n V_n\qquad\text{satisfies}\qquad\mu(C)=\mu(E)>0.$$
All points of $C$ have the same membership pattern in the separating family, so $C$ has at most one point.
Thus $C=\{x\}$ for some $x$, and $\mu(\SetDifference{E}{\{x\}})=0$. Every atom is therefore concentrated at a point.

For each $n\ge1$, the set
$$A_n:=\{x\in X:\mu(\{x\})\ge1/n\}$$
is finite: any $k$ distinct members would contribute total mass at least $k/n$, bounded by $\mu(X)$.
Since $A=\bigcup_{n\ge1}A_n$, the set $A$ is countable and Borel.
Every point of $X_{\mathrm{na}}$ has zero $\mu_{\mathrm{na}}$-mass. If this restricted measure had an atom,
the preceding argument would produce a point of positive mass, a contradiction.

The isomorphism is
$$[B]\longmapsto\Pair{[B\cap X_{\mathrm{na}}]}{B\cap A}.$$
Changing a representative on a null set changes neither the first class nor the second set, because every point of
$A$ has positive mass. Its inverse sends $\Pair{[C]}{S}$ to $[C\cup S]$; every subset of the countable Borel set $A$ is
Borel. These maps preserve Boolean operations because $X_{\mathrm{na}}$ and $A$ partition $X$.
They preserve measure since
$$\begin{aligned}
\mu(B)&=\mu_{\mathrm{na}}(B\cap X_{\mathrm{na}})+w(B\cap A)\\
&=\mu_{\mathrm{na}}(B\cap X_{\mathrm{na}})
  +\sum_{x\in B\cap A}\mu(\{x\}).
\end{aligned}$$
\end{proof}

Thus the \termforward{complete invariant} of a standard probability algebra is the total mass of the non-atomic
part together with the multiset of atom masses. \termuseas{Maharam theorem}{Maharam's theorem} is the special case
where the non-atomic mass is $1$ and the atom list is empty.

\begin{proposition*}[Complete invariant for finite measure algebras]
Let $\mu$ and $\nu$ be finite Borel measures on standard Borel spaces $X$ and $Y$.
Write $A$ and $B$ for their sets of positive-mass points, and $\mu_{\mathrm{na}}$ and
$\nu_{\mathrm{na}}$ for the restrictions to their complements.
There is a measure-preserving Boolean algebra isomorphism
$\MeasureAlg{X}{\mu}\cong\MeasureAlg{Y}{\nu}$ if and only if the non-atomic parts have the same
total mass and there is a bijection $f:A\to B$ such that
$$\nu(\{f(x)\})=\mu(\{x\})\qquad(x\in A).$$
The sets $A$ and $B$ may be countably infinite; the atom-mass multiset is understood in this sense.
\end{proposition*}

\begin{proof}[Proof]
Suppose first that the non-atomic masses agree, with common value $m$, and that $f$ is such a bijection.
If $m>0$, normalize the two non-atomic measures by $m^{-1}$ and apply Maharam's theorem to obtain an
isomorphism of their probability algebras. Scaling back by $m$ preserves the same null ideals and
makes this isomorphism preserve the original measures. If $m=0$, each non-atomic measure algebra
has just one element, so the unique map is a measure-preserving Boolean algebra isomorphism.
On the atomic factors, direct image under $f$ is an isomorphism $\PowerSet{A}\to\PowerSet{B}$,
and for every $S\IncludedIn A$ it preserves weight because
$$\sum_{y\in f(S)}\nu(\{y\})=\sum_{x\in S}\mu(\{x\}).$$
Combining these two isomorphisms with the atomic decompositions gives the required isomorphism.

Conversely, a Boolean algebra isomorphism preserves atoms. By the atomic decomposition, the atoms
are exactly the classes of the singletons at positive-mass points. Distinct such points give distinct
classes, so a measure-preserving isomorphism induces a bijection $f:A\to B$ preserving their masses.
It therefore preserves the sum of all atomic masses. It also preserves the top element and hence
the total mass. In the decompositions
$$\mu(X)=\mu_{\mathrm{na}}(\SetDifference{X}{A})+\sum_{x\in A}\mu(\{x\}),\qquad
\nu(Y)=\nu_{\mathrm{na}}(\SetDifference{Y}{B})+\sum_{y\in B}\nu(\{y\}),$$
all terms are finite. Cancelling the equal atomic masses proves equality of the non-atomic masses.
\end{proof}

The finite cylinder partitions give an explicit instance of disintegration.

\begin{mathmeta}
  \define{SequenceTailMap}
\end{mathmeta}

\begin{proposition*}[\termdefineas{conditional measures on cylinders}{Conditional measures on cylinders}]
Let $\lambda$ be the fair-coin measure on $\CantorSpace$, and let $n\in\NN$. Write
$$\pi_n(x):=\restrict{x}{n},\qquad
\SequenceTailMap{n}(x)(k):=x(n+k).$$
Let $\nu_n$ be the distribution of $\pi_n$, so that $\nu_n(\{s\})=2^{-n}$ for every $s\in\funcspace{n}{2}$.
For each such $s$ and every Borel set $A$, put
$$\lambda_s(A):=2^n\lambda(A\cap\cyl{s}).$$
These are probability measures with $\lambda_s(\cyl{s})=1$, and they give the disintegration along $\pi_n$:
for every Borel $A\IncludedIn\CantorSpace$ and every $D\IncludedIn\funcspace{n}{2}$,
$$\begin{aligned}
\int_D\lambda_s(A)\,d\nu_n(s)
&=\sum_{s\in D}2^{-n}\lambda_s(A)\\
&=\lambda(A\cap\pi_n^{-1}(D)).
\end{aligned}$$
Moreover, removing the fixed prefix leaves fair-coin measure: for every Borel $B\IncludedIn\CantorSpace$,
$$\lambda_s(\SequenceTailMap{n}^{-1}(B))=\lambda(B).$$
\end{proposition*}

\begin{proof}[Proof]
The cylinder $\cyl{s}$ has measure $2^{-n}$, so the normalized restriction $\lambda_s$ is a probability measure
concentrated on that cylinder. The map $s\mapsto\lambda_s$ is measurable because its domain is finite.
Since the length-$n$ cylinders form a disjoint partition,
$$\sum_{s\in\funcspace{n}{2}}2^{-n}\lambda_s(A)
=\sum_{s\in\funcspace{n}{2}}\lambda(A\cap\cyl{s})=\lambda(A).$$
The fiber concentration and this identity give the full conditional identity by the argument in
§{sec:disintegration}; on the finite base its integral is the displayed weighted sum.

To identify the tail law, take a finite binary word $w$. Directly from the definition of a cylinder,
$$\cyl{s}\cap\SequenceTailMap{n}^{-1}(\cyl{w})=\cyl{s\concat w}.$$
Consequently
$$\begin{aligned}
\lambda_s(\SequenceTailMap{n}^{-1}(\cyl{w}))
&=2^n\lambda(\cyl{s\concat w})\\
&=2^n2^{-(n+\Length{w})}=2^{-\Length{w}}=\lambda(\cyl{w}).
\end{aligned}$$
Two cylinders with nonempty intersection are nested, so the cylinders together with $\emptyset$ form a
$\pi$-system. They generate the
Borel sets and include the whole space. Uniqueness of finite measures on a generating $\pi$-system therefore
extends the equality to every Borel set.

Finally, uniqueness in the disintegration theorem holds outside a $\nu_n$-null set. Each singleton has positive
$\nu_n$-measure, so that null set is empty: the conditional probability is determined at every prefix.
\end{proof}

\begin{mathmeta}
  \define{MeasureAlgDistance}
\end{mathmeta}

For a finite measure $\mu$, the \termdefine{measure-algebra metric} is
$$\MeasureAlgDistance{\mu}{[A]}{[B]}:=\mu(\SymmetricDifference{A}{B}).$$
Changing either representative on a null set does not change this value. It vanishes exactly when $[A]=[B]$;
symmetry is immediate, and the triangle inequality follows from
$$\mu(\SymmetricDifference{A}{C})
\le\mu(\SymmetricDifference{A}{B})+\mu(\SymmetricDifference{B}{C}).$$
Thus this is a genuine metric on the quotient.

\begin{proposition*}[\termdefineas{dyadic approximation of measure algebras}{Dyadic approximation}]
Let $\lambda$ be the fair-coin measure on $\CantorSpace$, and let $\pi_n$ be the length-$n$ prefix projection. Put
$$\mathcal A_n:=\{[\pi_n^{-1}(S)]:S\IncludedIn\funcspace{n}{2}\}.$$
Then $\mathcal A_n$ is a finite Boolean subalgebra with exactly $2^n$ atoms, namely the classes $[\cyl{s}]$
for length-$n$ words $s$. Each has measure $2^{-n}$ and splits into two atoms of equal measure at the next level.
The subalgebras increase with $n$, and their union is countable and dense in the \termuse{measure-algebra metric}.
Every non-atomic standard probability algebra has such a sequence of finite Boolean subalgebras.
\end{proposition*}

\begin{proof}[Proof]
The map $S\mapsto[\pi_n^{-1}(S)]$ preserves Boolean operations. It is injective: if two sets of words differ,
the symmetric difference of their inverse images contains a cylinder of measure $2^{-n}>0$.
Thus $\mathcal A_n$ is isomorphic to the powerset algebra of the $2^n$ binary words of length $n$.
Its atoms correspond precisely to the singletons, giving the stated atom count and measures.

Appending the next bit gives the disjoint partition
$$\cyl{s}=\cyl{s\concat0}\cup\cyl{s\concat1},\qquad
\lambda(\cyl{s\concat b})=\tfrac12\lambda(\cyl{s})\quad(b\in2).$$
Consequently $\mathcal A_n\IncludedIn\mathcal A_{n+1}$. Each level is finite, so
$\bigcup_n\mathcal A_n$ is countable.

For density, let $A$ be Borel and let $\varepsilon>0$. The finite-coordinate events form a generating algebra,
so the \termuseas{approximation by a generating algebra}{generating-algebra approximation lemma} gives an event $C$
depending on a finite coordinate set $J$ such that $\lambda(\SymmetricDifference{A}{C})<\varepsilon$.
Choose $n$ larger than every member of $J$. Then $C=\pi_n^{-1}(S)$ for some $S\IncludedIn\funcspace{n}{2}$, since
its membership is decided by the first $n$ bits. Therefore $[C]\in\mathcal A_n$ and
$$\MeasureAlgDistance{\lambda}{[A]}{[C]}<\varepsilon,$$
which proves density.

For a non-atomic standard probability space $\Pair{X}{\mu}$, choose the isomorphism
$$\Phi:\MeasureAlg{\CantorSpace}{\lambda}\longrightarrow\MeasureAlg{X}{\mu}$$
constructed in the proof of \termuseas{Maharam theorem}{Maharam's theorem}. Its inverse-image formula commutes
with symmetric difference and preserves measure, so
$$\MeasureAlgDistance{\mu}{\Phi(a)}{\Phi(b)}=\MeasureAlgDistance{\lambda}{a}{b}.$$
Transport each $\mathcal A_n$ by $\Phi$. The finite Boolean structure, atom counts, atom measures, and equal
splitting are preserved. The union remains countable, and the isometry makes it dense.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
cccの具体的な局所証明はMeasureAlgebra.countable_pairwiseDisjointへ接続済み。
nonatomic標準確率代数の同型の説明もMaharamStandardBorel.maharamへ接続した。
残る文は既出のdyadic近似と後続のrandom forcingとの位置付けを述べる参照・応用案内で、新しい局所証明ではない。)
--> \termuseas{Maharam theorem}{Maharam's theorem} and the
\termuseas{dyadic approximation of measure algebras}{dyadic approximation} provide the measure-theoretic
foundation for the \termuse{random forcing} developed in §{sec:random-forcing-detail}.<!--
formalization: skip-end
-->
They identify every non-atomic standard probability algebra with the fair-coin algebra, independently of
its chosen Polish presentation. <!--
formalization: skip-begin (引用・背景説明・読書案内:
cccの具体的な局所証明はMeasureAlgebra.countable_pairwiseDisjointへ接続済み。
nonatomic標準確率代数の同型の説明もMaharamStandardBorel.maharamへ接続した。
残る文は既出のdyadic近似と後続のrandom forcingとの位置付けを述べる参照・応用案内で、新しい局所証明ではない。)
--> The cylinder partitions translate finite approximations in this algebra into
fair-coin probability statements.<!--
formalization: skip-end
-->  Positivity of the measure makes the Boolean algebra ccc:
for each positive integer $n$, an antichain has only finitely many members of measure at least $1/n$,
so every antichain is countable.

<!-- formalization: skip-begin (classification comparison and chapter summary) -->
**Classification reading.** Probability-measure isomorphism is the tame counterpart to the wild classification problems
in §{sec:borel-reducibility}. For non-atomic standard probability spaces the invariant is trivial: every such
probability algebra is the Lebesgue one. With atoms allowed, the invariant is still concrete and countable data: total
non-atomic mass plus the multiset of atom masses. Thus measure algebras give a useful positive example of
\termforward{smooth} classification, using only the standard-Borel and measure regularity machinery already developed
here.

<!-- formalization: skip-end -->
