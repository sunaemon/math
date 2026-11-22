# Borel Reducibility: Synthesis {#sec:borel-reducibility}

\begin{mathmeta}
  \forward{UniversalCountableER}
  \vars{t}{Real}
\end{mathmeta}
<!-- formalization: skip-begin (chapter synthesis and transition to the next part) -->
Borel reducibility is the comparison language for classification theorems. Instead of asking only whether a
classification exists, it asks what kind of invariant would be needed and whether one classification problem can be
transformed into another by a Borel procedure. Smoothness, $\EventualEqualityER$, hyperfiniteness, countable-structure
classification,
and analytic completeness become landmarks on one scale rather than isolated phenomena.

This perspective turns negative results into precise mathematical statements. Saying that a problem is not smooth, not
classifiable by countable structures, or $\bSigma^1_1$-complete identifies the exact failure mode of classification. The
earlier material on Borel sets, analytic sets, effective ranks, and Polish-group actions becomes usable here as a
toolkit for proving where a problem sits in the hierarchy.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter motivation, operator-algebra orientation, and declaration of proof scope) -->
Equivalence relations on Polish spaces underlie much of modern classification: isomorphism of countable structures,
conjugacy of measure-preserving transformations, isomorphism of separable $C^*$-algebras, orbit equivalence of group
actions. \termdefine{Borel reducibility} organizes these problems into a hierarchy of comparative complexity,
formalizing what it means for one classification problem to "reduce to" another via a definable assignment of complete
invariants.

Start with a tame representation problem. A nondegenerate representation of the commutative $C^*$-algebra $C_0(\R)$ on a
separable Hilbert space is, by the spectral theorem, the same data as a projection-valued measure on $\R$, or
equivalently a self-adjoint operator. For irreducible representations the classification is even simpler: each point
$t\in\R$ gives the one-dimensional representation $f\mapsto f(t)$, and every irreducible representation is unitarily
equivalent to exactly one of these. Thus classifying irreducible representations of $C_0(\R)$ is just equality on $\R$.

This real parameter also appears as the frequency in the Fourier transform of §{sec:tte-fourier-examples}.
The standard Fourier identification $C^*(\R)\cong C_0(\R)$ identifies the group $C^*$-algebra of the additive real
line with continuous functions vanishing at infinity on the frequency line. Under this identification, evaluation
at $\xi$ corresponds to the character $x\mapsto e^{-2\pi\mathrm i x\xi}$; its integrated action on a function in
$L^1(\R,\C)$ is precisely that function's Fourier transform at $\xi$. Thus the classification parameter becomes
the frequency.

That example is smooth because the invariant is a real number. General classification problems rarely come with such a
clean parameter space. One may have a standard Borel space $X$ of objects, such as representations, algebras, graphs, or
transformations, and an equivalence relation $E$ expressing "same up to the chosen isomorphism." A proposed
classification by invariants in another problem $\Pair{Y}{F}$ is exactly a definable assignment $x\mapsto f(x)$ such
that two
objects are $E$-equivalent precisely when their invariants are $F$-equivalent. Borel reducibility is the formal version
of this comparison.

Proof scope: this is a synthesis chapter, but not merely a list of slogans. It proves the local claims
needed to read the hierarchy: how reductions compose, why smoothness amounts to having Borel complete invariants, how
Borel
transversals give smoothness, why $\EventualEqualityER$ is nonsmooth, and how the Glimm--Effros and Silver dichotomies
feed into
classification. The $\EventualEqualityER$ proof is internal: it uses the Hewitt--Savage zero-one law from
§{sec:zero-one-laws}, not
HKL.
The specialist arguments for both HKL and Silver are assigned to §{sec:effective-dst-dichotomies}. This chapter uses
their
conclusions to explain classification; the generic-pair splitting and coherent-fusion arguments are proved there. Some
results about countable Borel equivalence relations — Feldman--Moore, the
universality of $\UniversalCountableER$, and the Dougherty--Jackson--Kechris hyperfiniteness theorem — are major
external theorems.
They are marked as such rather than being compressed into misleading one-paragraph "proofs."
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

The entry prerequisites are standard Borel spaces from §{sec:standard-borel-spaces} and analytic sets from
§{sec:analytic-sets}. The orbit examples use §{sec:polish-group-orbit-er}; the proof that eventual equality is
nonsmooth uses the Hewitt--Savage law in §{sec:zero-one-laws}. Treat the Silver and HKL statements as
available results on a first pass. To verify their proofs, return through §{sec:effective-dst} and
§{sec:effective-dst-ranks} to §{sec:effective-dst-dichotomies}. The Banach-space case study is an optional
application. By the end, readers should be able to specify the invariants a reduction transports and
distinguish smoothness, countable classification, and the stronger obstructions displayed here.

<!-- formalization: skip-end -->

## Reductions Between Equivalence Relations {#sec:reductions-equivalence}

\begin{mathmeta}
  \define{BorelReducesTo,BorelEquivalentTo,RealEqualityER}
  \vars{h}{Fun(Real,Prod(Real,Nat))}
\end{mathmeta}
Let $E$ and $F$ be equivalence relations on standard Borel spaces $X$ and $Y$. Say $E$ is
\termdefine{Borel reducible} to $F$, written $E \BorelReducesTo F$, if there exists a Borel function $f : X \to Y$ with
$$x \mathrel{E} x' \;\Longleftrightarrow\; f(x) \mathrel{F} f(x') \qquad \Pair{x}{x'}\in X.$$
Such $f$ sends each $E$-class into a single $F$-class, sends distinct $E$-classes to distinct $F$-classes, and does so
by a Borel map on representatives. Equivalently, it gives a \termdefine{Borel-definable} injection from the quotient
$X/E$ into $Y/F$. Bidirectional reducibility $E \BorelEquivalentTo F$ means that the two quotients have the same size on
the
\termdefine{Borel cardinality} scale: after identifying mutually reducible problems, $\BorelReducesTo$ becomes a partial
order on
$\BorelEquivalentTo$-classes.

This is weaker than isomorphism of equivalence relations on the underlying spaces. Let $E=\RealEqualityER$ be equality
on
$\R$, and let $F$ be the equivalence relation on $\R\times\{0,1\}$ defined by
$$
\Pair{r}{i}\mathrel F\Pair{s}{j}\quad\Longleftrightarrow\quad r=s.
$$
Then $E\BorelReducesTo F$ by $r\mapsto\Pair{r}{0}$, while $F\BorelReducesTo E$ by $\Pair{r}{i}\mapsto r$. Hence
$E\BorelEquivalentTo
F$. But there is no Borel
isomorphism $h:\R\to\R\times\{0,1\}$ whose pullback of $F$ is equality and whose image is all of $\R\times\{0,1\}$. If
such an $h$ existed, the two points $\Pair{r}{0}$ and $\Pair{r}{1}$ would have distinct preimages by injectivity and
surjectivity,
but they are $F$-equivalent, so the pullback condition would force those preimages to be equal. Thus Borel cardinal
equivalence records mutual embeddability of quotient problems, not literal Borel isomorphism of their class structures.

The relation $\BorelReducesTo$ is transitive. If $f:X\to Y$ reduces $E$ to $F$ and $g:Y\to Z$ reduces $F$ to $H$, then
$g\circ f$
is Borel and
$$
x\mathrel E x'
\Longleftrightarrow
f(x)\mathrel F f(x')
\Longleftrightarrow
g(f(x))\mathrel H g(f(x')).
$$
It is reflexive by the identity map. Hence $\BorelEquivalentTo$ is an equivalence relation on classification problems,
and $\BorelReducesTo$
descends to a genuine partial order on $\BorelEquivalentTo$-classes.

<!-- formalization: skip (contextual comparison with informal transfer arguments) -->
The same Borel-transfer idea appears informally throughout descriptive set theory — proving a theorem on $\BaireSpace$
first and pushing it forward to a general Polish space along the $\rho_X$ of §{sec:cauchy-representation-admissibility}
is one widely used instance. Borel reducibility is the precise framework that makes such transfer arguments comparable
across problems, with the descriptive complexity of the graph of $E$ (Borel, $\bSigma^1_1$, $\bPi^1_1$, …) further
stratifying the hierarchy.

## Smooth Equivalence Relations {#sec:smooth-equivalence}

\begin{mathmeta}
  \vars{f,n}{Nat}
\end{mathmeta}

$E$ is \termdefine{smooth} (or *concretely classifiable*) if $E \BorelReducesTo \RealEqualityER$, where
$\RealEqualityER$ is equality on
$\R$. By Kuratowski's isomorphism theorem in §{sec:kuratowski-isomorphism}, the choice of uncountable standard Borel
codomain is immaterial. Concretely, $E$ is smooth iff there is a Borel map $f : X \to \R$ separating $E$-classes — a
Borel \termdefine{complete invariant}.

*   Equality on any standard Borel space is trivially smooth.
*   Any Borel equivalence relation with countably many classes is \termuse{smooth}: enumerate the classes and assign
    each $x$ its index. Each class is Borel because it is a section of $E$, so the index map is Borel.
*   *Unitary equivalence of compact self-adjoint operators* on a separable Hilbert space is smooth: the ordered
    eigenvalue lists and the dimension of the kernel give a Borel complete invariant.

For the last example, fix a separable Hilbert space $H$. If $A$ is compact and self-adjoint, let
$$
\lambda^+_0(A)\ge\lambda^+_1(A)\ge\cdots\ge0,
\qquad
\lambda^-_0(A)\ge\lambda^-_1(A)\ge\cdots\ge0
$$
list, with multiplicity and padded by zeros, the positive eigenvalues of $A$ and the absolute values of its negative
eigenvalues. Let $\kappa(A):=\dim\ker(A)\in\omega\cup\{\infty\}$. The compact spectral theorem gives an orthogonal
decomposition into the corresponding finite-dimensional eigenspaces and the kernel. Consequently, compact
self-adjoint operators $A$ and $B$ are unitarily equivalent exactly when
$$
\Tuple{\Sequence{\lambda^+_n(A)}{n\in\omega},\Sequence{\lambda^-_n(A)}{n\in\omega},\kappa(A)}
=
\Tuple{\Sequence{\lambda^+_n(B)}{n\in\omega},\Sequence{\lambda^-_n(B)}{n\in\omega},\kappa(B)}.
$$
The norm topology makes the space of compact self-adjoint operators Polish. To see separability, approximate
a compact operator uniformly on the unit ball by projecting its image onto the span of a finite
$\varepsilon$-net. The approximants have finite-dimensional range and are finite sums of rank-one operators.
For each fixed number of summands these sums are continuously parameterized by finitely many pairs of vectors
in $H$, so their union is separable. Compact operators lie in its norm closure and form a norm-closed subset
of the complete space of bounded operators. The self-adjoint operators form a closed subset as well, because
the adjoint operation is norm-continuous. Thus the compact self-adjoint parameter space is complete and
separable, and its Borel structure is standard.

\begin{mathmeta}
  \define{OrthogonalComplement,MinMaxValue}
\end{mathmeta}
Work with this norm topology. Write $\OrthogonalComplement{F}$ for the orthogonal complement of a subspace $F$.
The nonnegative min--max values are
$$\MinMaxValue{A}{n}:=
\inf_{\dim F\le n}\ \sup_{\substack{x\in\OrthogonalComplement{F}\\\Norm{x}\le1}}
\operatorname{Re}\Pair{x}{Ax},$$
where $F$ ranges over finite-dimensional subspaces of $H$. Including $x=0$ makes these values nonnegative,
even if $H$ is zero-dimensional. For unit-ball vectors, the quadratic forms of $A$ and $B$ differ by at most
$\Norm{A-B}$. Taking suprema and infima preserves this bound, so
$$\Abs{\MinMaxValue{A}{n}-\MinMaxValue{B}{n}}\le\Norm{A-B}.$$
The values decrease with $n$. For a finite-rank operator they eventually vanish: discard a finite-dimensional
subspace on whose orthogonal complement the operator vanishes. Finite-rank approximation therefore gives
$\MinMaxValue{A}{n}\to0$ for compact $A$.

\begin{mathmeta}
  \define{PositiveSpectralCount}
\end{mathmeta}
Choose an orthonormal eigenbasis for $A$, including a basis of its kernel. For $r>0$, let
$\PositiveSpectralCount{A}{r}$ count its vectors whose eigenvalues exceed $r$.
This count is finite. Otherwise, for every $n$ choose $n+1$ such vectors. Their span meets the orthogonal
complement of every subspace of dimension at most $n$ in a unit vector, whose quadratic value is greater
than $r$. The minimum of the finitely many chosen eigenvalues gives a bound independent of the discarded
subspace. Thus $\MinMaxValue{A}{n}>r$ for every $n$, contradicting convergence to zero.

The same dimension argument, now using all the $\PositiveSpectralCount{A}{r}$ basis vectors above $r$,
gives $\MinMaxValue{A}{n}>r$ when $n<\PositiveSpectralCount{A}{r}$. If
$\PositiveSpectralCount{A}{r}\le n$, discard their span. Parseval's identity bounds the quadratic form
by $r$ on the remaining unit ball, so $\MinMaxValue{A}{n}\le r$. Consequently,
$$r<\MinMaxValue{A}{n}\quad\Longleftrightarrow\quad n<\PositiveSpectralCount{A}{r}
\qquad(r>0).$$
These threshold counts identify the decreasing sequence $\MinMaxValue{A}{n}$ with the positive eigenvalues,
counted with multiplicity and padded by zeros. Hence $\lambda^+_n(A)=\MinMaxValue{A}{n}$.
Applying the same argument to $-A$ gives $\lambda^-_n(A)=\MinMaxValue{-A}{n}$.
Both coordinate lists are therefore continuous for the norm topology.

To check the remaining coordinate, let $P_A$ be the orthogonal projection onto
$\ker(A)$. Fix a dense sequence $\Sequence{d_n}{n\in\omega}$ in $H$.
Since $A$ is self-adjoint, the closure of its range is the orthogonal complement of its kernel.
The projection theorem and density therefore give, for each $x\in H$,
$$\Norm{P_Ax}=\inf_{n\in\omega}\Norm{x-Ad_n}.$$
Each function on the right depends norm-continuously on $A$, so this countable infimum is Borel.
Choose a fixed orthonormal basis $\IndexedFamily{e_j}{j\in J}$ of $H$, where $J$ is finite or countable.
Parseval's identity and interchange of nonnegative sums give
$$\kappa(A)=\sum_{j\in J}\Norm{P_Ae_j}^2.$$
Indeed, expanding each $P_Ae_j$ in an orthonormal basis of the kernel and interchanging the sums makes
each kernel basis vector contribute $1$. This is a sum of nonnegative extended real numbers, so an
infinite-dimensional kernel gives $\infty$. The countable sum is Borel.
Thus the displayed complete invariant is Borel and reduces unitary
equivalence to equality on a standard Borel sequence space.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
一般self-adjoint作用素の測度類不変量に関する適用限界の注意。具体的な反例・構成・証明をこの章で提示せず、
後続の局所的な補題としても使用しない。直前のcompact作用素の局所証明とは別の背景説明である。)
--> The compactness restriction is essential to this argument. For a general self-adjoint operator, the spectral theorem
produces a measure class together with a multiplicity function. Equality of Borel measure codes is finer than equality
of measure classes, and the quotient by mutual absolute continuity is not itself a standard Borel invariant space. The
spectral data are complete invariants, but they do not give a reduction to equality merely by choosing measure codes.
<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
連分数homeomorphismを用いる実際のBorel埋め込みとsmoothnessはBorelReductionProseで証明した。
未リンク部分は無限列自体ではなく有限誤差を同一視することが障害になるという節導入・後続のE0への案内で、新たな局所的証明ではない。)
-->
Smoothness is the bottom of the Borel reducibility hierarchy. It includes equality on spaces that already carry infinite
coordinate data.<!--
formalization: skip-end
-->  For example, equality on $\BaireSpace$ is smooth: the continued-fraction homeomorphism
$\BaireSpace\cong\SetDifference{\R}{\QQ}$ from §{sec:simple-continued-fractions} embeds $\BaireSpace$ into $\R$ as a
Borel
subset, and equality of Baire-space codes becomes ordinary equality of the corresponding irrational reals. <!--
formalization: skip-begin (引用・背景説明・読書案内:
連分数homeomorphismを用いる実際のBorel埋め込みとsmoothnessはBorelReductionProseで証明した。
未リンク部分は無限列自体ではなく有限誤差を同一視することが障害になるという節導入・後続のE0への案内で、新たな局所的証明ではない。)
--> Thus infinite
sequences themselves are not the obstruction. The first obstruction appears when equality is weakened to equality
*modulo finitely many errors*, which is the relation $\EventualEqualityER$ below.<!--
formalization: skip-end
-->

Transversals give a useful sufficient criterion. A \termdefine{Borel transversal} for $E$ is a Borel set
$T\IncludedIn X$ meeting every $E$-class in exactly one point.

\begin{proposition*}[Standard-Borel invariant criterion] Let $E$ be a Borel equivalence relation on a standard Borel
space $X$. If $Y$ is a standard Borel space and $c:X\to Y$ is Borel with
$$
x\mathrel E x'
\quad\Longleftrightarrow\quad
c(x)=c(x').
$$
then $E$ is smooth.
\end{proposition*}

\begin{corollary*}[Complete-invariant characterization] The relation $E$ is smooth iff it has a Borel complete invariant
with values in some standard Borel space.
\end{corollary*}

\begin{corollary*}[Transversal criterion] If a Borel equivalence relation $E$ has a Borel transversal, then it
is smooth.
\end{corollary*}

\begin{proof}[Proof] By the classification of standard Borel spaces in §{sec:standard-borel-classification}, there is a
Borel injection $j:Y\to\R$. Then $j\circ c$ is a real-valued Borel complete invariant, proving the proposition. The
forward implication of the first corollary uses $Y=\R$, and the reverse implication is the proposition.

For the corollary, let $T$ be a Borel transversal and define $c(x)$ to be the unique point of $T$ in the $E$-class of
$x$. The graph of $c$ is
$$
\{\Pair{x}{t}\in X\times T:x\mathrel E t\}.
$$
Equivalently, it is the Borel subset $E\cap(X\times T)$ of $X\times X$. Its vertical section over $x$ is the singleton
consisting of the unique representative of the $E$-class of $x$ in $T$. Applying the
\termuse{Lusin--Suslin theorem} from §{sec:lusin-souslin-theorem} to the injective projection
$$
E\cap(X\times T)\longrightarrow X,\qquad \Pair{x}{t}\longmapsto x,
$$
shows that its image is Borel and that the inverse map $x\mapsto \Pair{x}{c(x)}$ is Borel. The image is all of $X$
because $T$
meets every class, so $c$ is Borel and separates exactly the $E$-classes.
\end{proof}

## $\EventualEqualityER$ and the Glimm–Effros Dichotomy {#sec:e0-glimm-effros}

\begin{mathmeta}
  \vars{N}{Nat}
  \vars{c}{Real}
  \vars{t}{Real}
  \vars{f}{Fun(Name,Real)}
\end{mathmeta}
\index{E0@$\EventualEqualityER$}

\begin{mathmeta}
  \define{EventualEqualityER}
\end{mathmeta}
A representative example of a nonsmooth Borel equivalence relation is **$\EventualEqualityER$**, *eventual agreement* on
$\CantorSpace$. Think of a
point of $\CantorSpace$ as an infinite binary record. Equality asks that two records agree at every coordinate;
$\EventualEqualityER$
asks only that they agree from some finite stage onward:
$$x \mathrel{\EventualEqualityER} y \;\Longleftrightarrow\; \exists N \in \omega,\, \forall n \ge N,\; x_n = y_n.$$
Equivalently, $x$ and $y$ may differ, but only in finitely many coordinates. Each $\EventualEqualityER$-class is
therefore a countable
cloud around one binary sequence, obtained by changing finitely many bits.

$\EventualEqualityER$ is Borel because it is the countable union, over $N$, of the closed relations requiring agreement
at every
coordinate $n\ge N$. Every class is countable: it is the orbit of $x$ under the action of
$G = \bigoplus_n\ZZ/2\ZZ$ on $\CantorSpace$ by coordinate-wise XOR.

$\EventualEqualityER$ is *not smooth*. Suppose toward a contradiction that a Borel reduction $f : \CantorSpace \to \R$
reduced $\EventualEqualityER$ to
equality on $\R$. Then $f$ is constant on $\EventualEqualityER$-classes. If $B \IncludedIn \R$ is Borel, the preimage
$f^{-1}(B)$ is
$\EventualEqualityER$-saturated: changing finitely many bits cannot change membership in it.

Every $\EventualEqualityER$-saturated Borel set is invariant under finite-support permutations of coordinates, because
such a
permutation changes only finitely many coordinates of each binary sequence. Hence the Hewitt--Savage zero-one law of
§{sec:zero-one-laws}, applied to the fair-coin product measure $\mu$, gives
$$
\mu(f^{-1}(B))\in\{0,1\}
\qquad(B\in\mathcal B(\R)).
$$
Let $\nu:=f_*\mu$ be the pushforward probability measure on $\R$. The displayed equation says that every Borel subset of
$\R$ has $\nu$-measure $0$ or $1$.

Such a probability measure on $\R$ must be a point mass. Indeed, if some singleton had measure strictly between $0$ and
$1$, the zero-one property would already fail. If every singleton had measure $0$, then the distribution function
$F(t)=\nu(\RightClosedInterval{-\infty}{t})$ would be continuous, with limits $0$ and $1$ at $\pm\infty$; choosing $t$
with $0<F(t)<1$
again
contradicts the zero-one property. Therefore $\nu=\delta_c$ for some $c\in\R$, and
$$\mu(f^{-1}(\{c\}))=1.$$
The level set $f^{-1}(\{c\})$ is nonempty. Since a reduction identifies exactly equivalent points, it is one
$\EventualEqualityER$-class. Every such class is countable, and the fair-coin product measure is nonatomic, so
this level set has measure zero. This contradicts its measure being one. Hence $\EventualEqualityER$ is not smooth.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
最小nonsmooth
benchmarkという数学的内容はHKLDichotomy.hkl_reducible_iff_nonsmoothへ接続した。
未リンク部分はGlimm–Effros/HKLの呼称・引用と、この例の位置付けを述べる文献案内。)
-->
The \termforward{Glimm--Effros dichotomy} below shows that this example is not merely one nonsmooth relation among many.
We use the Harrington--Kechris--Louveau form [@HarringtonKechrisLouveau1990].<!--
formalization: skip-end
-->  It is the minimal nonsmooth benchmark for
Borel equivalence relations: every Borel equivalence relation is either smooth or has $\EventualEqualityER$
Borel-reducing to it.

\begin{theorem*}[\termdefineas{Glimm--Effros dichotomy}{Harrington–Kechris–Louveau}]
For every Borel equivalence relation $E$, exactly one of the following holds:

\begin{itemize}
\item $E$ is smooth, or
\item $\EventualEqualityER \BorelReducesTo E$.
\end{itemize}

\end{theorem*}

\begin{proof}[Proof] The alternatives are mutually exclusive. If $E$ is smooth and $\EventualEqualityER \BorelReducesTo
E$, then composing a
reduction $\EventualEqualityER \BorelReducesTo E$ with a complete Borel invariant for $E$ gives a complete Borel
invariant for $\EventualEqualityER$,
contradicting the nonsmoothness of $\EventualEqualityER$ proved above.

For the converse, assume $E$ is not smooth, and choose a Polish topology presenting the underlying
standard Borel space. The
\termforwardas{Harrington--Kechris--Louveau embedding}{Harrington--Kechris--Louveau embedding theorem}, whose proof is
given in §{sec:edst-gh-hkl}, gives a continuous injection
$$\pi:\CantorSpace\to X$$
such that
$$a \mathrel{\EventualEqualityER} b
\quad\Longleftrightarrow\quad
\pi(a)\mathrel E\pi(b).$$
This $\pi$ is a Borel reduction from $\EventualEqualityER$ to $E$. Hence nonsmoothness implies
$\EventualEqualityER\BorelReducesTo E$, completing the dichotomy.
\end{proof}

This is a strict dichotomy: nothing strictly $\BorelReducesTo$-between smooth and "$\EventualEqualityER$-above" exists.

<!-- formalization: skip-begin (historical context and external operator-algebra application) -->
The original
measure-theoretic version, due to Glimm [@Glimm1961] and Effros [@Effros1965] for orbit equivalence relations of Polish
group actions, predates the general Borel statement; Harrington, Kechris, and Louveau [@HarringtonKechrisLouveau1990]
extended it via effective descriptive set theory.

**Operator-algebra example.** Let $A$ be a separable $C^*$-algebra, and consider unitary equivalence on its irreducible
representations on the disjoint union of representation spaces for each positive finite dimension and for countably
infinite dimension, with their usual standard Borel coding. Unitary equivalence of irreducible representations
is a Borel relation on this space.  Glimm's theorem says that this equivalence relation is smooth exactly when
$A$ is type I [@Glimm1961;
@Effros1965]. Thus type-I algebras have a standard-Borel dual, while non-type-I algebras have nonsmooth representation
theory; by the \termuse{Glimm--Effros dichotomy}, $\EventualEqualityER$ then Borel-reduces to unitary equivalence of
irreducible
representations of $A$.
<!-- formalization: skip-end -->

## Silver's Dichotomy {#sec:silver-dichotomy}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後に述べるSilver dichotomyへの導入と歴史的帰属・出典表示。Silverの定理と局所的な証明は別に対応済み。)
-->
A coarser dichotomy holds for the broader pointclass $\bPi^1_1$ — coanalytic equivalence relations. It is due to Silver
[@Silver1980].<!--
formalization: skip-end
-->

\begin{theorem*}[\termdefineas{Silver's dichotomy}{Silver}] Let $E$ be a $\bPi^1_1$ equivalence
relation on a Polish space $X$. Then either $E$ has at most countably many classes, or there exists a nonempty
perfect set $P
\IncludedIn X$ of pairwise $E$-inequivalent points.

\end{theorem*}

\begin{proof}[Proof]
If $E$ has uncountably many classes, apply the Silver fusion theorem of §{sec:edst-silver-fusion}, relativized to a
real parameter coding the space and the coanalytic relation. It gives a continuous injection
$\pi:\CantorSpace\to X$ whose distinct images are $E$-inequivalent. The image of the compact Cantor space is compact,
and the continuous injection into the Hausdorff space $X$ is a homeomorphism onto that image. Hence the image is a
perfect $E$-antichain. Conversely, such an antichain meets uncountably many classes, so the two alternatives are
mutually exclusive.

The proof in §{sec:edst-silver-fusion} defines $\pi(a)$ as an actual member of every analytic condition along its
branch, using retained tree witnesses. Distinct branches give product-generic pairs, to which the proved Silver
splitting lemma applies. It does not require the ordinary closures of the conditions to be $E$-separated.
\end{proof}

In the latter case $\Card{X/E} = 2^{\alephNull}$, so the cardinality of $X/E$ never lands strictly between $\alephNull$
and $2^{\alephNull}$ — even when CH fails. <!--
formalization: skip-begin (引用・背景説明・読書案内:
Cantor
antichainからquotientの濃度がcontinuumになる帰結はBorelReductionProse.quotient_cardinal
_of_cantor_antichainへ接続した。残りはperfect set propertyとの類比と有効的方法の意義を述べる概説で、
追加の局所的証明を提示しない。)
--> This extends the perfect set property of §{sec:perfect-set-theorem} from
sets to equivalence relations, and is a paradigmatic application of effective methods to lift regularity from Borel to
coanalytic objects.<!--
formalization: skip-end
-->

## The Proofs of Silver and HKL {#sec:borel-reducibility-imported-engines}

<!-- formalization: skip-begin (reading order for the proofs of Silver and HKL) -->
This chapter introduces the Glimm--Effros and Silver dichotomies through their classification consequences. Their
specialist proofs belong to §{sec:effective-dst-dichotomies}, after the lightface foundations have been established.
Both
proofs are developed there, including the splitting arguments and the verification of branch limits.

The bridge from effective statements to classical statements is **relativization**: a boldface analytic or coanalytic
object can be treated as lightface relative to a real parameter coding the relevant Polish presentation, Borel relation,
tree, or reduction. A theorem proved uniformly relative to that parameter then gives the corresponding boldface theorem.

The proof development has the following order.

1.  Establish boundedness and separation, then the \termforward{Gandy--Harrington topology} in
    §{sec:edst-gh-topology} as common tools.
2.  Develop coanalytic ranks, prove the splitting step, and verify the perfect-antichain fusion for Silver in
    §{sec:edst-coanalytic-ranks-silver}.
3.  Construct the nonsmooth kernel, prove the compatible-refinement lemmas, and carry out the coherent fusion for HKL
    in §{sec:edst-gh-hkl}. Verify both directions of the reduction of $\EventualEqualityER$.
4.  Return to the deductions of the dichotomies in §{sec:silver-dichotomy} and §{sec:e0-glimm-effros}, checking their
    hypotheses against the proved lemmas.

Silver fusion in §{sec:edst-silver-fusion} retains analytic witnesses and obtains inequivalence from product
genericity. The HKL construction in §{sec:edst-hkl-fusion} additionally retains relations on a finite tree to obtain
equivalence for eventually equal branches. These are the precise inputs to the two dichotomy arguments above.
<!-- formalization: skip-end -->

## Countable Borel Equivalence Relations and Hyperfiniteness {#sec:countable-borel-er-hyperfinite}

A Borel equivalence relation $E$ on a standard Borel space $X$ is a \termdefine{countable Borel equivalence relation} if
every $E$-class is countable. <!--
formalization: skip-begin (引用・背景説明・読書案内:
countable Borel equivalence relationの定義と、
E0がBorel・各類可算・nonsmoothであるという具体的事実はBorelReductionProseへ接続した。
残る「最初の大きな領域」「内部構造が複雑」は後続の節の位置付けを述べる説明で、追加の構成や証明ではない。)
--> These relations form the first large region above smoothness:<!--
formalization: skip-end
-->  $\EventualEqualityER$ itself
is countable,
but countability of classes does not imply smoothness<!--
formalization: skip-begin (引用・背景説明・読書案内:
countable Borel equivalence relationの定義と、
E0がBorel・各類可算・nonsmoothであるという具体的事実はBorelReductionProseへ接続した。
残る「最初の大きな領域」「内部構造が複雑」は後続の節の位置付けを述べる説明で、追加の構成や証明ではない。)
--> , and the reducibility structure inside the countable region is
already intricate.<!--
formalization: skip-end
-->

<!-- formalization: skip-begin (external Feldman--Moore theorem and reference discussion) -->
The basic representation theorem is Feldman--Moore [@FeldmanMoore1977].

\begin{theorem*}[\termdefineas{Feldman--Moore theorem}{Feldman--Moore}] Every
\termuse{countable Borel equivalence relation} is the orbit relation of a Borel action of a countable discrete group.
Equivalently, countable Borel
equivalence relations are exactly the quotients produced by countably many Borel automorphisms.

\end{theorem*}

**Reference and discussion.** The proof uses the
\termuse{Lusin--Novikov uniformization theorem} from §{sec:uniformization}. Apply it first to the relation and then
to the inverse graphs of the resulting partial functions. This yields countably many partial Borel bijections
whose graphs cover $E\IncludedIn X\times X$. A partial bijection need not extend on its whole domain to a total
bijection. Instead, remove its fixed points and split its domain into countably many Borel pieces such that each
piece is disjoint from its image. A countable separating family of Borel sets provides these pieces. On each
piece, swap points with their images and fix all other points of $X$. These are Borel involutions whose graphs
lie in $E$. Their generated countable group has orbit relation exactly $E$.

Full proofs appear in [@Kechris1995, §18; @Gao2009, Ch. 7].
<!-- formalization: skip-end -->

<!-- formalization: skip (transition following the external representation theorem) -->
This is why the subject sits at the intersection of descriptive set theory, measurable dynamics, and geometric group
theory.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
実際のF2=FreeGroup(Fin 2)のbinary shiftと、そのcountable/Polishなcode space・座標wise
action・closed graphsの可算和によるBorel軌道関係・可算な各類をBinaryShiftBenchmarkへ狭く接続した。
未リンクのuniversality、任意のcountable Borel graphingのcoding、
countable領域の最大要素という帰結はDougherty–Jackson–Kechris 1994に明示的に引用する外部入力で、
普遍還元をここで構成済みとは扱わない。)
--> \begin{mathmeta}
  \define{UniversalCountableER}
\end{mathmeta}
There is a universal countable Borel equivalence relation.<!--
formalization: skip-end
-->  Let $F_2$ act by shift on $2^{F_2}$,
$$
(g\cdot x)(h)=x(g^{-1}h),
$$
on the entire shift space. Its orbit relation $\UniversalCountableER$ <!--
formalization: skip-begin (引用・背景説明・読書案内:
実際のF2=FreeGroup(Fin 2)のbinary shiftと、そのcountable/Polishなcode space・座標wise
action・closed graphsの可算和によるBorel軌道関係・可算な各類をBinaryShiftBenchmarkへ狭く接続した。
未リンクのuniversality、任意のcountable Borel graphingのcoding、
countable領域の最大要素という帰結はDougherty–Jackson–Kechris 1994に明示的に引用する外部入力で、
普遍還元をここで構成済みとは扱わない。)
--> is universal among countable
Borel
equivalence relations: for every countable Borel $E$, one has $E\BorelReducesTo \UniversalCountableER$
[@DoughertyJacksonKechris1994]. This
universality theorem is another deep result of countable Borel equivalence relation theory; the proof codes an arbitrary
countable Borel graphing into this shift action of the free group. Thus the countable region has a top element, unlike
the whole Borel reducibility hierarchy.<!--
formalization: skip-end
-->

The most important tame subclass is the class of \termdefineas{hyperfiniteness}{hyperfinite} equivalence relations. A
countable Borel equivalence relation $E$ is hyperfinite if
$$
E=\bigcup_n E_n
$$
for an increasing sequence of finite Borel equivalence relations $E_n$. Hyperfiniteness says that the infinite classes
can be exhausted by finite approximations in a Borel-uniform way. The relation $\EventualEqualityER$ is hyperfinite: let
$E_n$ identify
two binary sequences when they agree from coordinate $n$ onward; each $E_n$-class has size at most $2^n$, and $\bigcup_n
E_n=\EventualEqualityER$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
nonsmoothなhyperfinite関係にE0が還元される局所的な主張は、有限Borel
approximationsからBorelnessを得て、実際のHKL構成へ適用する証明に接続した。
逆方向の還元があるときのbireducibilityもその入力を明示する。未リンクの全hyperfinite関係のE0への還元、
Zの作用のhyperfiniteness、成長条件の研究背景は引用するDJKの外部定理であり、
そのfinite-approximation構成を仮定なしに証明したとは扱わない。)
-->
The Dougherty--Jackson--Kechris theorem identifies $\EventualEqualityER$ as the universal hyperfinite countable Borel
equivalence
relation [@DoughertyJacksonKechris1994]. Every hyperfinite countable Borel equivalence relation reduces to
$\EventualEqualityER$, and<!--
formalization: skip-end
-->
every nonsmooth hyperfinite one contains the same first obstruction to smoothness by Glimm--Effros. <!--
formalization: skip-begin (引用・背景説明・読書案内:
nonsmoothなhyperfinite関係にE0が還元される局所的な主張は、有限Borel
approximationsからBorelnessを得て、実際のHKL構成へ適用する証明に接続した。
逆方向の還元があるときのbireducibilityもその入力を明示する。未リンクの全hyperfinite関係のE0への還元、
Zの作用のhyperfiniteness、成長条件の研究背景は引用するDJKの外部定理であり、
そのfinite-approximation構成を仮定なしに証明したとは扱わない。)
--> The proof is not
reproduced here; it is a substantial finite-approximation theorem, not a formal consequence of the definition of
\termuse{hyperfiniteness}. For Borel actions of $\ZZ$, hyperfiniteness is automatic [@DoughertyJacksonKechris1994]; the
broader hyperfiniteness problem asks which group actions and coarse geometric hypotheses force this finite-approximation
behavior.<!--
formalization: skip-end
-->

<!-- formalization: skip-begin (external hierarchy of countable Borel equivalence relations) -->
The structure between $\EventualEqualityER$ and $\UniversalCountableER$ is rich rather than empty. Adams and Kechris
[@AdamsKechris2000] produced
continuum-many pairwise $\BorelReducesTo$-incomparable countable Borel equivalence relations strictly between them,
using rigidity
for actions of linear algebraic groups. Jackson--Kechris--Louveau [@JacksonKechrisLouveau2002] proved that every Borel
action of a finitely generated group of polynomial growth generates a hyperfinite relation. More recently,
Conley--Jackson--Marks--Seward--Tucker-Drob [@ConleyJacksonMarksSewardTuckerDrob2023] reproved and extended this result
using Borel asymptotic dimension, turning geometric growth constraints into Borel finite-approximation data.
Grebík--Higgins [@GrebikHiggins2026] show that the set of locally finite Borel graphs having finite Borel
asymptotic dimension is $\bSigma^1_2$-complete. This measures the complexity of the property across coded
graphs, rather than the Borel reducibility degree of any individual graph's connectedness relation.
<!-- formalization: skip-end -->

<!-- formalization: skip (section synthesis) -->
Countable Borel equivalence relations therefore give the first sustained test of Borel reducibility as a classification
scale. Smoothness asks for a single Borel invariant. Hyperfiniteness asks for finite Borel approximations. Universality
at $\UniversalCountableER$ says that every countable-class classification problem can be coded by one fixed
free-group action.

## Above $\EventualEqualityER$ {#sec:above-e0}

<!-- formalization: skip-begin (survey of external hierarchy and completeness theorems) -->
\begin{mathmeta}
  \define{EventualRowEqualityER}
\end{mathmeta}
The hierarchy above $\EventualEqualityER$ is rich and largely uncharted. Some landmarks:

*   **$\EventualRowEqualityER$**, eventual agreement on $\funcspace{\omega}{\R}$, is strictly $\BorelReducesTo$-above
    $\EventualEqualityER$ and is a standard example of a
    Borel equivalence relation *not* induced by any Polish group action [@KechrisLouveau1997].
*   **Countable Borel equivalence relations**, §{sec:countable-borel-er-hyperfinite}, have a universal element
    $\UniversalCountableER$ and a tame hyperfinite subregion governed by $\EventualEqualityER$.
*   **\termuseas{classifiable by countable structures}{Classifiable by countable structures}**: $E \BorelReducesTo
    {\cong_L}$
    for the isomorphism relation on countable $L$-structures, some countable language $L$. Hjorth's theory of
    **\termuse{turbulence}** [@Hjorth2000] supplies a powerful obstruction: §{sec:polish-groups-turbulence}
    states the external theorem that
    the orbit equivalence relation of a turbulent Polish group action is not classifiable by countable structures.
*   The **universal analytic equivalence relation** sits at the top of $\bSigma^1_1$ equivalence relations
    [@LouveauRosendal2005]. Many
    familiar isomorphism problems reduce to it: isomorphism of separable Banach spaces is universal for
    analytic equivalence relations under Borel reducibility
    [@FerencziLouveauRosendal2009], formalizing the slogan "as hard to classify as anything analytic." Isomorphism of
    separable $C^*$-algebras instead is complete among orbit equivalence relations of Polish group actions
    [@Sabok2016].

The systematic reference is [@Gao2009]; [@Hjorth2000] develops the orbit-equivalence-relation side and turbulence in
depth.
<!-- formalization: skip-end -->

## Case Study: Separable Banach Spaces {#sec:banach-spaces-case-study}
\index{separable Banach space}
\index{Banach space!classification}

<!-- formalization: skip-begin (external Banach-space coding and completeness results) -->
Separable Banach spaces give a second compact test case, complementary to the
\termuse{Friedman--Stanley theorem} for countable graphs in §{sec:countable-graphs-case-study}. The point is not to
develop Banach-space theory, but to show how the same Borel-reducibility language applies once the objects are no longer
countable structures.

There is a standard Borel space coding all separable Banach spaces: view each separable Banach space isometrically as a
closed linear subspace of $C(\ClosedInterval{0}{1})$ and use the Effros--Borel structure on the closed subsets. Both
linear isometry and
linear isomorphism are analytic in this coding, so both are legitimate classification problems on standard Borel
parameter spaces.

The contrast with the graph case is sharp. The \termuse{Friedman--Stanley theorem} says that countable graphs are
universal for classification by countable structures, while separable Banach-space isomorphism is
universal among analytic equivalence relations under Borel reducibility [@FerencziLouveauRosendal2009]. In
Borel-reducibility terms, this says that no reasonable
countable-invariant target can capture arbitrary separable Banach spaces; the full isomorphism problem is as complicated
as any analytic equivalence relation. The example uses the machinery already in place — Effros coding, analytic
orbit-style relations, and the hierarchy above $\EventualEqualityER$ — without importing Banach-space classification
theory into the
text.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (transition to the next part) -->
\part{Effective Definability and Forcing}\label{sec:logical-computable-extensions}

The preceding part studied regularity, selection, and classification in Polish spaces. This part asks how
those conclusions depend on the surrounding universe of sets and on the definitions and parameters allowed.
Forcing extends a set-theoretic model and lets us distinguish properties preserved by extension from those
whose truth can change. Effective descriptive set theory restricts definitions and parameters, making the
information needed to describe sets part of the theory itself.

The forcing chapter develops Polish-space applications through Cohen and random reals, absoluteness, and
independence of regularity properties.\termref{absoluteness} The three effective descriptive set theory
chapters proceed from lightface hierarchies to ranks and refinements, then to the Silver and
Harrington--Kechris--Louveau dichotomies. Their proofs supply the results used for classification in
§{sec:borel-reducibility}. The effective route uses the numerical computation background in the appendices
and can be read without the forcing chapter. Computation on names and realizability form the next part.
<!-- formalization: skip-end -->
