# Borel Structure {#sec:borel-structure}
\index{Borel structure}

<!-- formalization: skip-begin (chapter intro / Borel σ-algebra motivation) -->
The Borel $\sigma$-algebra of a topological space is the smallest $\sigma$-algebra containing the open sets.
Equivalently, it is obtained from the open sets by iterating countable unions and complements, with countable
intersections falling out by De Morgan duality.

For Polish spaces this measurable structure is rich enough for analysis and probability, but still controlled enough to
admit ranks, codes, and transfer theorems. The first ranks already carry real topology: $\Gdelta$ subsets of a Polish
space are exactly its Polish subspaces, and the hierarchy stabilizes at the first uncountable ordinal. The standard
reference for the classical descriptive set theory developed in this and the surrounding chapters is [@Kechris1995].

The chapter has two stages. §{sec:borel-hierarchy-levels} develops the hierarchy and its concrete
Baire-space examples. §{sec:borel-codes} then records the constructions by codes, distinguishes the relevant
ranks, and explains validity and evaluation.
<!-- formalization: skip-end -->

## Hierarchy Levels and Concrete Examples {#sec:borel-hierarchy-levels}

### $\Fsigma$ and $\Gdelta$ Sets {#sec:fsigma-gdelta-sets}

\begin{mathmeta}
  \vars{p}{Nat}
\end{mathmeta}
\index{Fsigma set@$\Fsigma$ set}
\index{Gdelta set@$\Gdelta$ set}

\begin{mathmeta}
  \define{GdeltaSigma,FsigmaDelta}
\end{mathmeta}

Recall from Alexandrov's theorem in §{sec:alexandrov-theorem} that $\Fsigma$ means a countable union of closed sets and
$\Gdelta$ means a countable intersection of open sets. The two classes are dual:
$$A \text{ is } \Fsigma \quad\Longleftrightarrow\quad \SetDifference{X}{A} \text{ is } \Gdelta.$$

Longer strings record iterated operations from inside out:

*   **$\GdeltaSigma$** means a countable union of $\Gdelta$ sets, i.e. a set of the form
    $$\bigcup_{n \in \omega}\bigcap_{m \in \omega} U_{n,m}$$
    with each $U_{n,m}$ open.
*   **$\FsigmaDelta$** means a countable intersection of $\Fsigma$ sets, i.e. a set of the form
    $$\bigcap_{n \in \omega}\bigcup_{m \in \omega} C_{n,m}$$
    with each $C_{n,m}$ closed.

The same convention continues: the final symbol is the outermost operation, and the initial letter tells whether the
construction starts from closed sets ($F$) or open sets ($G$).

In metric spaces, every closed set $C$ is $\Gdelta$. The empty set is open and hence $\Gdelta$; for $C\ne\emptyset$,
$$C = \bigcap_{n \ge 1} \{x : d(x,C) < 1/n\}.$$
This is the basic reason the finite Borel levels line up with the classical $\Fsigma/\Gdelta$ notation.

### The Borel Hierarchy {#sec:borel-hierarchy}

\begin{mathmeta}
  \define{omegaOneOrd}
  \forward{alephCard}
  \define{bSigma,bPi,bDelta}
  \vars{n,p}{Nat}
\end{mathmeta}

<!-- formalization: skip (notation-only introduction of the standard first uncountable ordinal omega_1 and the
  cardinal aleph_1; the cardinality identity is standard set-theoretic background (mathlib Cardinal.ord_aleph), not a
  claim this chapter proves) -->
Throughout, $\omegaOneOrd$ denotes the \termdefine{first uncountable ordinal}: the least ordinal whose
underlying set is uncountable, equivalently the set of all countable ordinals. Its cardinality is $\alephCard{1}$.

A \termdefine{pointclass} is a class of sets of points, usually sets of reals or subsets of a fixed Polish space. The
\termdefine{Borel hierarchy} on a metric space $X$ is the transfinite sequence of pointclasses $\bSigma^0_\alpha(X)$ and
$\bPi^0_\alpha(X)$ defined by recursion on ordinals $\alpha \ge 1$. Pointclass indices in this recursion range over
these positive levels. In the rest of this definition, and whenever the ambient space is clear, we suppress $X$ and
write $\bSigma^0_\alpha$, $\bPi^0_\alpha$, and $\bDelta^0_\alpha$.

*   $\bSigma^0_1$ = open sets;  $\bPi^0_1$ = closed sets.
*   For $\alpha > 1$,
    $$
    \bSigma^0_\alpha
    =
    \left\{\bigcup_{n \in \omega} A_n :
    A_n \in \bPi^0_{\beta_n}
    \text{ for some } \beta_n < \alpha
    \text{, for each } n
    \right\}.
    $$
*   $\bPi^0_\alpha = \{\SetDifference{X}{A} : A \in \bSigma^0_\alpha\}$.
*   $\bDelta^0_\alpha := \bSigma^0_\alpha \cap \bPi^0_\alpha$.

The quantifier "for some $\beta_n < \alpha$, for each $n$" is essential. At a limit level it permits a countable union
whose terms have ranks climbing toward the limit; it does not require all terms to come from one fixed earlier level.

For a pointclass $\Gamma$ and a set $P\IncludedIn Z$, say that $P$ is
\termdefineas{Gamma-hard}{$\Gamma$-hard} with respect to Baire-space reductions if every
$B\in\Gamma(\BaireSpace)$ is the continuous preimage of $P$ under some continuous map $\BaireSpace\to Z$. The set
$P$ is \termdefineas{Gamma-complete}{$\Gamma$-complete} if, in addition, $P\in\Gamma(Z)$. This convention makes both
the source of the reductions and the ambient space of $P$ explicit.

At the first nontrivial stage the recursive definition recovers the classical notation. Since the only ordinal below $2$
and at least $1$ is $1$,
$$
\begin{aligned}
\bSigma^0_2
&= \left\{\bigcup_{n \in \omega} A_n : A_n \in \bPi^0_1
\text{ for each } n\right\} \\
&= \left\{\bigcup_{n \in \omega} F_n : F_n \text{ is closed for each } n\right\}
= \Fsigma.
\end{aligned}
$$
Taking complements,
$$
\SetDifference{X}{\bigcup_n C_n}=\bigcap_n(\SetDifference{X}{C_n}),
$$
and hence
$$
\begin{aligned}
\bPi^0_2
&= \{\SetDifference{X}{A} : A \in \bSigma^0_2\} \\
&= \left\{\bigcap_{n \in \omega} U_n : U_n \text{ is open for each } n\right\}
= \Gdelta.
\end{aligned}
$$

At $\alpha=3$ the union pieces may come from $\bPi^0_1$ or $\bPi^0_2$:
$$
\bSigma^0_3
= \left\{\bigcup_{n \in \omega} A_n :
A_n \in \bPi^0_1 \cup \bPi^0_2
\text{ for each } n\right\}.
$$
Because closed sets are $\Gdelta$ in metric spaces, $\bPi^0_1 \IncludedIn \bPi^0_2$, so this is the class of countable
unions of $\Gdelta$ sets: $\GdeltaSigma$. Complementing gives $\FsigmaDelta$.

In a metric space the hierarchy is monotone: whenever $1\leq\beta\leq\gamma$,
$$
\bSigma^0_\beta\IncludedIn\bSigma^0_\gamma,
\qquad
\bPi^0_\beta\IncludedIn\bPi^0_\gamma.
$$
Moreover, for every $\alpha\geq 1$,
$$
\bSigma^0_\alpha\IncludedIn\bPi^0_{\alpha+1},
\qquad
\bPi^0_\alpha\IncludedIn\bSigma^0_{\alpha+1}.
$$
Above level $1$ these facts follow directly from the union and complement clauses. The metric-space base case uses that
open sets are $\Fsigma$ and closed sets are $\Gdelta$.

Continuous preimages preserve every Borel level. If $f:Y\to X$ is continuous and
$A\in\bSigma^0_\alpha(X)$, then $f^{-1}(A)\in\bSigma^0_\alpha(Y)$, and likewise for $\bPi^0_\alpha$ and
$\bDelta^0_\alpha$. This follows by induction on $\alpha$, since continuous preimages send open sets to open sets and
commute with complements and countable unions.

Limit levels are where the recursion stops being merely notational. The tempting but wrong simplification of the limit
clause is
$$
\bSigma^0_\lambda \stackrel{?}{=} \bigcup_{\alpha<\lambda}\bSigma^0_\alpha,
$$
which would only keep sets already appearing at one fixed earlier level. It would miss countable unions whose $n$-th
term has complexity increasing with $n$ — exactly the sets the recursive definition was designed to admit.

The first failure occurs at $\lambda=\omega$. The correct definition permits sets of the form
$$
\bigcup_n A_n
\qquad\text{with}\qquad
A_n \in \bPi^0_{\beta_n}(\R),\;\beta_n<\omega,
$$
with no finite bound on the ranks $\beta_n$. The naive rule would give only $\bigcup_{m<\omega}\bSigma^0_m(\R)$, the
sets appearing at some finite level. The construction in §{sec:borel-hierarchy-baire} exhibits a set at level $\omega$
that lies at no finite level.

The recursion may be written for all ordinals, but no new sets appear after $\omegaOneOrd$. At the first
uncountable stage,
$$
\bSigma^0_{\omegaOneOrd}
= \left\{\bigcup_n A_n : A_n \in \bPi^0_{\beta_n}
\text{ for some } \beta_n < \omegaOneOrd
\text{, for each } n\right\}.
$$
By the regularity of $\omegaOneOrd$ proved in §{sec:ordinals-cofinality}, the countable set of indices
$\{\beta_n:n\in\omega\}$ has a supremum $\gamma<\omegaOneOrd$. Hence all terms already lie below one countable bound,
and the union lies in
$\bSigma^0_{\gamma+1}$. Therefore
$$
\bSigma^0_{\omegaOneOrd}
= \bigcup_{\alpha < \omegaOneOrd}\bSigma^0_\alpha.
$$
The reverse inclusion follows from monotonicity.
Taking complements gives the analogous identity
$$
\bPi^0_{\omegaOneOrd}
= \bigcup_{\alpha < \omegaOneOrd}\bPi^0_\alpha.
$$
The class $\bSigma^0_{\omegaOneOrd}$ is closed under countable unions: if $A_n \in \bSigma^0_{\alpha_n}$ with
$\alpha_n < \omegaOneOrd$, then $\beta := \sup_n\alpha_n < \omegaOneOrd$ by regularity, hence $A_n \in
\bSigma^0_{\alpha_n}\IncludedIn\bPi^0_{\alpha_n+1}\IncludedIn\bPi^0_{\beta+1}$, and so $\bigcup_n A_n \in
\bSigma^0_{\beta+2} \IncludedIn \bSigma^0_{\omegaOneOrd}$.

To prove closure under complement, take $A\in\bSigma^0_{\omegaOneOrd}$. Stabilization gives
$A\in\bSigma^0_\alpha$ for some $1\leq\alpha<\omegaOneOrd$, so
$\SetDifference{X}{A}\in\bPi^0_\alpha$. Viewing this set as a one-term countable union places it in
$\bSigma^0_{\alpha+1}\IncludedIn\bSigma^0_{\omegaOneOrd}$. Thus
$\bSigma^0_{\omegaOneOrd}$ is complement-closed. Since $\bPi^0_{\omegaOneOrd}$ consists of complements of
$\bSigma^0_{\omegaOneOrd}$ sets, this closure forces
$$\bSigma^0_{\omegaOneOrd} \;=\; \bPi^0_{\omegaOneOrd};$$
the members of this common class are the \termdefineas{Borel set}{Borel sets} of $X$, and the common class is the Borel
$\sigma$-algebra of $X$.

A map $f:X\to Y$ between topological spaces is a \termdefine{Borel-measurable map} if $f^{-1}(V)$ is Borel in $X$ for
every open set $V\IncludedIn Y$. This open-set criterion is equivalent to requiring $f^{-1}(B)$ to be Borel in $X$ for
every Borel set $B\IncludedIn Y$: the family
$$
\{B\IncludedIn Y:f^{-1}(B)\text{ is Borel in }X\}
$$
is a $\sigma$-algebra because inverse images commute with complements and countable unions, and a $\sigma$-algebra that
contains the open sets contains the Borel $\sigma$-algebra.

<!-- formalization: skip (stabilization-method observation and guide to strictness results) -->
The stabilization argument uses regularity of $\omegaOneOrd$, not separability. In §{sec:finite-borel-universal} we
prove
finite-level strictness on Baire space and Cantor space. In §{sec:finite-borel-strictness-polish}, the perfect set
theorem
extends this result to every uncountable Polish space. On these spaces, the full theorem says that each new
countable level below $\omegaOneOrd$ contains sets not appearing at earlier levels [@Kechris1995, §22].

#### Universal Sets and Finite-Level Strictness {#sec:finite-borel-universal}

\begin{mathmeta}
  \vars{a}{Name}
  \vars{k}{Nat}
\end{mathmeta}

<!-- formalization: skip-begin (roadmap to the universal-set constructions below) -->
A universal set records a family of sets as its sections. We construct such sets for each finite Borel level and use
a diagonal argument to show that the levels are distinct on Baire space and Cantor space.
<!-- formalization: skip-end -->

\begin{theorem*}[Finite-level universal sets]
For every integer $n\ge1$, there is a $\bSigma^0_n$ set
$U_n\IncludedIn\BaireSpace\times\BaireSpace$ whose vertical sections are exactly the $\bSigma^0_n$ subsets of
$\BaireSpace$. The same statement holds with $\CantorSpace$ in place of $\BaireSpace$.
\end{theorem*}

\begin{proof}[Proof]
For $n=1$, let $\sigma:\omega\to\finseq{\omega}$ enumerate the finite words and put
$$
U_1:=\{\Pair{a}{p}:\exists k\;(a(k)\ne0\text{ and }\sigma(k)\prefixOf p)\}.
$$
This is a union of open rectangles, hence open. For an open set $S$, choose $a(k)=1$ when
$\cyl{\sigma(k)}\IncludedIn S$ and $a(k)=0$ otherwise. Since the cylinders form a basis,
$S=(U_1)_a$; in particular, the constant zero parameter represents the empty set.
Fix a bijection $q:\omega\times\omega\to\omega$ and decode each parameter by
$$a_k(j):=a(q(k,j)).$$
Every sequence of parameters can be packed in this way: given $\Sequence{b_k}{k\in\omega}$, set $a(q(k,j)):=b_k(j)$.
For each $k$, the map $a\mapsto a_k$ is continuous because each output coordinate reads one input coordinate.
Suppose $U_n$ has been constructed, and define
$$
\Pair{a}{p}\in U_{n+1}\quad\Longleftrightarrow\quad
\exists k\;\Pair{a_k}{p}\notin U_n.
$$
For each $k$, the map $\Pair{a}{p}\mapsto\Pair{a_k}{p}$ is continuous. Thus $U_{n+1}$ is a countable union of
$\bPi^0_n$ sets and belongs to $\bSigma^0_{n+1}$. Conversely, monotonicity of the hierarchy lets us write any
$S\in\bSigma^0_{n+1}$ as $S=\bigcup_k F_k$ with every $F_k\in\bPi^0_n$, even when its original union uses
lower levels. Choose $b_k$ so that $\SetDifference{\BaireSpace}{F_k}=(U_n)_{b_k}$, and pack these parameters into $a$.
Then $S=(U_{n+1})_a$. Every section has the claimed Borel complexity, since $p\mapsto\Pair{a}{p}$ is continuous.
On $\CantorSpace$, enumerate finite binary words and use the same formulas. The base parameters are binary,
and pairing coordinates also packs countably many binary parameters into a binary parameter.
\end{proof}

\begin{theorem*}[Finite Borel strictness on sequence spaces]
For $X=\BaireSpace$ or $X=\CantorSpace$ and every integer $n\ge1$, the classes $\bSigma^0_n$ and $\bPi^0_n$ of
subsets of $X$ are distinct.
\end{theorem*}

\begin{proof}[Proof]
On $\BaireSpace$, let $U_n$ be the preceding universal set and define
$$D_n:=\{a\in\BaireSpace:\Pair{a}{a}\notin U_n\}.$$
The diagonal map $a\mapsto\Pair{a}{a}$ is continuous, so $D_n\in\bPi^0_n$. If it were also in $\bSigma^0_n$,
universality would give $D_n=(U_n)_a$ for some $a$, whence
$$a\in D_n\quad\Longleftrightarrow\quad\Pair{a}{a}\in U_n\quad\Longleftrightarrow\quad a\notin D_n,$$
a contradiction. The same argument on $\CantorSpace$ gives a $\bPi^0_n$ set outside $\bSigma^0_n$ there as well.
Taking complements gives a $\bSigma^0_n$ set outside $\bPi^0_n$ in each space.
\end{proof}

### Baire-Space Reading of the Hierarchy {#sec:borel-hierarchy-baire}

\begin{mathmeta}
  \vars{p}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

In Baire space the abstract hierarchy has a concrete location in the cylinder/tree picture.
The first levels say which kind of finite evidence decides the question.
By §{sec:closed-sets-trees}, open sets are coded by saturated up-sets of prefixes. For an open set $A$, membership
$x\in A$ is confirmed by finding a prefix $s$ of $x$ with $\cyl{s}\IncludedIn A$.
The same section codes a closed set $F$ as the body of a pruned subtree. Nonmembership $x\notin F$ is confirmed by
finding a prefix of $x$ that falls out of that tree.
A $\bDelta^0_1$ set is both open and closed, so finite prefix information decides the answer either way.

Beyond these first levels, the construction in §{sec:borel-codes} records the required countable unions and
complements as inductive constructor data.

For example, in $\BaireSpace$ the set
$$
\{x : x(n)=0 \text{ for infinitely many } n\}
=
\bigcap_{m\in\omega}\bigcup_{n\ge m}\{x:x(n)=0\}
$$
is $\Gdelta$, hence $\bPi^0_2$: after every finite stage there must be a later zero. Its complement, the set of
sequences eventually avoiding $0$, is $\Fsigma$:
$$
\{x : \exists m\,\forall n\ge m\,x(n)\ne 0\}
=
\bigcup_{m\in\omega}\bigcap_{n\ge m}\{x:x(n)\ne 0\}.
$$
This is the typical Baire-space reading of the hierarchy: existential countable choices appear as countable unions,
universal countable requirements as countable intersections, and closed conditions as infinite branches through trees.

#### A set of no finite Borel rank {#sec:borel-no-finite-rank}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{s}{Seq}
\end{mathmeta}

A concrete $\bSigma^0_\omega$ set of no finite rank can be written directly in Baire space. The countable disjoint union
$$I:=\ExternalDisjointUnion_{k\geq 1}\seqPower{\omega}{k}$$
is countably infinite. A bijection $I\cong\omega$ reindexes coordinates and gives a homeomorphism
$$
\BaireSpace
\cong \funcspace{I}{\omega}
\cong \prod_{k\ge 1}\funcspace{\seqPower{\omega}{k}}{\omega}.
$$
Write $x_k \in \funcspace{\seqPower{\omega}{k}}{\omega}$ for the $k$-th slice of $x \in \BaireSpace$. For $k\ge 1$, let
$$
P_k =
\{y \in \funcspace{\seqPower{\omega}{k}}{\omega} :
\forall n_1\,\exists n_2\,\forall n_3\cdots Q n_k\,
y(n_1,\ldots,n_k)=0\},
$$
where the quantifiers alternate and $Q$ is $\forall$ when $k$ is odd and $\exists$ when $k$ is even.

\begin{lemma*}[\termdefineas{finite-rank clopen normal form}{Finite-rank clopen normal form}]
For $k\ge1$, every $\bPi^0_k$ set $B\IncludedIn\BaireSpace$ has a family of clopen sets
$C_{n_1,\ldots,n_k}$ such that
$$
x\in B
\quad\Longleftrightarrow\quad
\forall n_1\,\exists n_2\,\forall n_3\cdots Q n_k\;
x\in C_{n_1,\ldots,n_k},
$$
with the same alternating quantifiers as above.
\end{lemma*}

\begin{proof}[Proof]
Induct on $k$. For $k=1$, the set $B$ is closed. Enumerate all finite words as $s_i$ and put
$$
C_i:=\begin{cases}
\SetDifference{\BaireSpace}{\cyl{s_i}},&\cyl{s_i}\IncludedIn\SetDifference{\BaireSpace}{B},\\
\BaireSpace,&\text{otherwise}.
\end{cases}
$$
Each $C_i$ is clopen and $B=\bigcap_i C_i$, since every point outside $B$ lies in a cylinder contained in its open
complement. This enumeration handles an empty or finite cylinder cover by inserting copies of the whole space.

For the successor step, write $B^c=\bigcup_i F_i$ with every $F_i\in\bPi^0_k$ by the successor-level normalization
used in §{sec:finite-borel-universal}. Choose a clopen normal form for each $F_i$ by induction. Then
$$x\in B\quad\Longleftrightarrow\quad\forall i\;x\notin F_i.$$
Negating each chosen normal form reverses all its quantifiers and complements its clopen matrix.
Prepending the universal quantifier over $i$ therefore gives the required alternating form of length $k+1$.
\end{proof}

\begin{proposition*}[\termdefineas{completeness of alternating-quantifier sets}
  {Completeness of alternating-quantifier sets}]
For every $k\ge1$, the set $P_k$ is $\bPi^0_k$-complete under continuous reductions from Baire space.
\end{proposition*}

\begin{proof}[Proof]
The matrix $y(n_1,\ldots,n_k)=0$ is clopen. Starting from this matrix, the innermost quantifier gives a closed or
open set, and each subsequent universal or existential quantifier gives a countable intersection or union.
Thus the displayed alternating formula puts $P_k$ in $\bPi^0_k$.

For any $B\in\bPi^0_k$, choose its clopen matrix from the preceding lemma and define
$f:\BaireSpace\to\funcspace{\seqPower{\omega}{k}}{\omega}$ by
$$
f(x)\Tuple{n_1,\ldots,n_k}=
\begin{cases}
0,&x\in C_{n_1,\ldots,n_k},\\
1,&x\notin C_{n_1,\ldots,n_k}.
\end{cases}
$$
Each coordinate of $f$ is continuous because its two fibers are clopen. Therefore $f$ is continuous, and
$x\in B$ iff $f(x)\in P_k$. This proves completeness.
\end{proof}

\begin{theorem*}[\termdefineas{Borel set of no finite rank}{A Borel set of no finite rank}]
The set
$$A:=\{x\in\BaireSpace:x_k\in P_k\text{ for some }k\ge1\}$$
belongs to $\bSigma^0_\omega$ and belongs to neither $\bSigma^0_m$ nor $\bPi^0_m$ for any integer $m\ge1$.
\end{theorem*}

\begin{proof}[Proof]
Each set $\{x:x_k\in P_k\}$ is the continuous preimage of $P_k$ under the slice projection, so it belongs to
$\bPi^0_k$. Their countable union $A$ therefore belongs to $\bSigma^0_\omega$.

For each $k\ge1$, define the continuous map
$\iota_k:\funcspace{\seqPower{\omega}{k}}{\omega}\to\BaireSpace$ by putting its argument in the $k$-th slice
and the constant-one function in every other slice. The constant-one function lies outside each $P_j$:
its innermost zero test is always false, and quantifying this false predicate over the nonempty set $\omega$
leaves it false at every stage. Hence
$$\iota_k^{-1}(A)=P_k.$$

If $A\in\bSigma^0_m$, take $k=m$. The preceding preimage equality would imply $P_m\in\bSigma^0_m$.
By completeness, every $\bPi^0_m$ subset of Baire space would then belong to $\bSigma^0_m$, contradicting the
diagonal witness from §{sec:finite-borel-universal}. Finally, if $A\in\bPi^0_m$, then
$A\in\bSigma^0_{m+1}$ by the successor inclusion, which has just been ruled out.
\end{proof}

#### Cantor space {#sec:hierarchy-cantor}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{s}{Seq}
\end{mathmeta}

The Cantor space $\CantorSpace$ admits the same cylinder/tree picture, with two compactness-driven simplifications.
Trees range over $\finseq{2}$ instead of $\finseq{\omega}$, so closed sets are bodies $\TreeBody{T}$ of pruned *binary*
trees. And because $\CantorSpace$ is itself compact, every closed subset is compact, every open cover of a clopen set by
cylinders has a finite subcover, and so every clopen set is a *finite* union of cylinders — equivalently, decided by
reading a single bounded prefix length.

| class | Cantor-space form |
|-------|-------------------|
| $\bSigma^0_1$ | unions of binary cylinders $\bigcup_{s\in S}\cyl{s}$, $S\IncludedIn\finseq{2}$ |
| $\bPi^0_1$ | bodies $\TreeBody{T}$ of pruned binary trees $T\IncludedIn\finseq{2}$; necessarily compact |
| $\bDelta^0_1$ | finite unions of cylinders, equivalently sets decided at some bounded depth $N$ uniformly in $x$ |
| $\bSigma^0_2$ | countable unions $\bigcup_n\TreeBody{T_n}$ of binary tree bodies |
| $\bSigma^0_\alpha,\bPi^0_\alpha$ ($\alpha\ge 3$) | identical recursive form to Baire space |

The boundedness of $\bDelta^0_1$ is the substantive difference. For example,
$$
C:=\{x\in\BaireSpace:x(x(0)+1)=0\}
$$
is clopen: membership and nonmembership are decided by the prefix of length $x(0)+2$, but no single prefix length works
uniformly for every $x$. In Cantor space König's lemma forces a uniform bound. From level $2$ upward the structural form
is identical to Baire space, with binary tree bodies replacing $\omega$-branching ones.

<!-- formalization: skip-begin (external full transfinite Borel strictness theorem) -->
The hierarchy is strict at every countable level on $\CantorSpace$ — this is the standard Borel-hierarchy theorem for
any uncountable Polish space.
<!-- formalization: skip-end -->
The level-$\omega$ construction above adapts by replacing each slice
$\funcspace{\seqPower{\omega}{k}}{\omega}$ with the binary-valued slice
$\funcspace{\seqPower{\omega}{k}}{2}$ and defining $P_k^{(2)}$ by the same alternating condition. The reductions above
already take only the values $0$ and $1$, and coordinate reindexing gives
$$
\prod_{k\geq 1}\funcspace{\seqPower{\omega}{k}}{2}
\cong\CantorSpace,
$$
which yields the Cantor-space example.

## Borel Codes {#sec:borel-codes}

A \termforward{Borel code} records how a set is built from basic open sets by complements and countable unions.
We first define these records as inductive data, just as terms and formulas are defined by constructors in
§{sec:appendix-logic}. Their interpretation is then given by structural recursion. Later we encode the same data
as real parameters, so that statements about Borel sets can be expressed as statements about reals.

### Construction {#sec:borel-codes-construction}

\begin{mathmeta}
  \vars{k,m,n}{Nat}
\end{mathmeta}

Fix a Polish space $X$ and a countable open base $\IndexedFamily{U_n}{n\in\omega}$ for its topology.
\begin{mathmeta}
  \define{BorelLeafCode,BorelComplementCode,BorelUnionCode}
\end{mathmeta}
\begin{definition*}
The formal expressions generated inductively by the following rules are called \termdefineas{Borel code}{Borel codes}:
\begin{enumerate}
\item For each $n\in\omega$, $\BorelLeafCode{n}$ is a Borel code.
\item If $c$ is a Borel code, then $\BorelComplementCode{c}$ is a Borel code.
\item If each term of $\Sequence{c_k}{k\in\omega}$ is a Borel code, then
$\BorelUnionCode{\Sequence{c_k}{k\in\omega}}$ is a Borel code.
\item Only expressions generated by the preceding rules are Borel codes.
\end{enumerate}
\end{definition*}

The third rule takes an arbitrary countable sequence of previously constructed codes as its argument.
It need not be a finite list or a computable sequence.

The set $A_c\IncludedIn X$ interpreted by a code is defined by structural recursion:
$$
\begin{aligned}
A_{\BorelLeafCode{n}}&:=U_n,\\
A_{\BorelComplementCode{c}}&:=\SetDifference{X}{A_c},\\
A_{\BorelUnionCode{\Sequence{c_k}{k\in\omega}}}&:=\bigcup_{k\in\omega}A_{c_k}.
\end{aligned}
$$
In particular, different codes can have the same interpretation.

By structural induction, $A_c$ is Borel for every code $c$: basic open sets are Borel, and Borel sets are
closed under complements and countable unions.

Allowing only complement and countable union suffices because countable intersection is recoverable as
$$\bigcap_n B_n = \SetDifference{X}{\bigcup_n (\SetDifference{X}{B_n})}.$$
Finite nonempty unions and intersections are obtained by repeating terms in a countable sequence.
The whole space is coded by $\BorelUnionCode{\Sequence{\BorelLeafCode{n}}{n\in\omega}}$, since $\bigcup_nU_n=X$;
its complement codes the empty set. Thus the three constructors suffice for the whole Borel $\sigma$-algebra.

For example, let $F\IncludedIn X$ be closed. If $F=X$, use $\BorelUnionCode{\Sequence{\BorelLeafCode{n}}{n\in\omega}}$.
Otherwise its open complement is nonempty. Enumerate the basis sets it contains, with repetitions if necessary, as
$$\SetDifference{X}{F}=\bigcup_n U_{i_n}.$$
Then $\BorelComplementCode{\BorelUnionCode{\Sequence{\BorelLeafCode{i_n}}{n\in\omega}}}$ codes $F$.
The distinction matters because the union constructor takes a sequence indexed by $\omega$; it has no empty input.

If $A=\bigcap_m\bigcup_n C_{m,n}$ is an $\FsigmaDelta$ set, choose codes $c_{m,n}$ for the closed sets $C_{m,n}$.
Put
$$
\begin{aligned}
d_m&:=\BorelUnionCode{\Sequence{c_{m,n}}{n\in\omega}},\\
e&:=\BorelComplementCode{\BorelUnionCode{\Sequence{\BorelComplementCode{d_m}}{m\in\omega}}}.
\end{aligned}
$$
Then $A_{d_m}=\bigcup_n C_{m,n}$ and $A_e=A$, directly by the three evaluation rules.

### Every Borel set has a code {#sec:borel-codes-every-borel}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

By the rank stabilization at $\omegaOneOrd$ from §{sec:borel-hierarchy}, every Borel set $A\IncludedIn X$ lies in
$\bSigma^0_\alpha(X)$ or $\bPi^0_\alpha(X)$ for some $\alpha<\omegaOneOrd$. Construct a code by recursion on $\alpha$:

*   $\alpha=1$: let $e$ be the empty-set code constructed above. For each $n$, put $c_n:=\BorelLeafCode{n}$ if
    $U_n\IncludedIn A$, and $c_n:=e$ otherwise. Then $\BorelUnionCode{\Sequence{c_n}{n\in\omega}}$ codes the open set
    $A$,
    including $A=\emptyset$.
*   $\alpha>1$, $A\in\bSigma^0_\alpha$: write $A=\bigcup_n B_n$ with $B_n\in\bPi^0_{\beta_n}(X)$ and
    $\beta_n<\alpha$. Recursively choose a code $c_n$ for each $B_n$; then
    $\BorelUnionCode{\Sequence{c_n}{n\in\omega}}$ codes $A$.
*   $A\in\bPi^0_\alpha$: first construct a code $c$ for $\complement A\in\bSigma^0_\alpha$, then use
    $\BorelComplementCode{c}$.

At a limit ordinal $\lambda$, no extra constructor is needed. The definition of $\bSigma^0_\lambda$ already expresses
its members as countable unions of sets from classes $\bPi^0_{\beta_n}$ with $\beta_n<\lambda$.
Thus the same union constructor handles the limit step in the \termuse{Borel hierarchy}.

<!-- formalization: skip (non-canonicity remark; existence is formalized as exists_decode_eq) -->
The construction depends on choices of representations at each step, hence the code is not canonical, but every
\termuse{Borel set} admits at least one \termuseas{Borel code}{code}. Non-canonicity is useful rather than harmful:
different proofs that a set is Borel give different codes, and later arguments can choose whichever code has the best
rank, uniformity, or \termforwardas{absoluteness}{absoluteness properties}.

### Encoding the data as a real {#sec:borel-codes-encoding}

\begin{mathmeta}
  \vars{c}{Name}
  \vars{k}{Nat}
\end{mathmeta}

To use a Borel code as a real parameter, record its constructors in a sequence of natural numbers.
A finite sequence $s$ specifies a position in the data: $\emptyset$ denotes the whole code, and $s\concat(k)$
denotes the position of the $k$-th immediate subcode of the code at $s$.

\begin{mathmeta}
  \define{FiniteSequenceCode}
\end{mathmeta}

Fix a bijection
$$
\finseq{\omega}\longrightarrow\omega,\qquad s\longmapsto\FiniteSequenceCode{s}.
$$
The natural number $\FiniteSequenceCode{s}$ is the code of the finite sequence $s$ under this fixed bijection.
We use the concrete list coding constructed in §{sec:lambda-finite-lists} for this bijection.
Thus corner notation for finite sequences has the same meaning in the classical and computational chapters.

An external record of a \termuse{Borel code} is a function $c\in\BaireSpace$ whose value
$c(\FiniteSequenceCode{s})$ records the constructor at position $s$. Use $0$ for an unused position,
$1$ for a countable union, $2$ for a complement, and $n+3$ for a leaf specifying $U_n$.
Record the inductive constructors as follows:

*   For $\BorelLeafCode{n}$ at position $s$, record $n+3$ at $s$; it has no subcodes.

*   For $\BorelComplementCode{d}$ at position $s$, record $2$ at $s$ and record $d$ starting at $s\concat(0)$.

*   For $\BorelUnionCode{\Sequence{d_k}{k\in\omega}}$ at position $s$, record $1$ at $s$ and record each $d_k$
    starting at $s\concat(k)$.

For example, $\BorelComplementCode{\BorelLeafCode{n}}$ has the record
$$c(\FiniteSequenceCode{\emptyset})=2,\qquad c(\FiniteSequenceCode{\SingletonSeq{0}})=n+3,$$
with value $0$ at every other position. Thus $\FiniteSequenceCode{s}$ specifies where to look,
whereas $c(\FiniteSequenceCode{s})$ specifies which constructor is there.

We also allow the immediate subcodes of a union to be numbered by any nonempty subset of $\omega$,
and the unique subcode of a complement to have any number. This only changes the indexing of subcodes;
§{sec:borel-codes-rank} proves that reindexing preserves evaluation and the ordinal measures.
A position is present when its recorded value is not $0$. A valid record has a present empty position,
all prefixes of a present position are present, and the leaf, complement, and union cases have respectively
zero, exactly one, and at least one immediate subcode. In addition, following immediate subcodes cannot continue
indefinitely. These conditions permit reconstruction by the same inductive rules that define Borel codes.

To evaluate a record, apply the three evaluation rules from §{sec:borel-codes} to its subcodes.
Writing $A_s$ for the set represented at a present position $s$, we have:

*   If $c(\FiniteSequenceCode{s})=n+3$, set $A_s:=U_n$.

*   If $c(\FiniteSequenceCode{s})=1$, set
    $$A_s:=\bigcup\{A_{s\concat(k)}:c(\FiniteSequenceCode{s\concat(k)})\ne0\}.$$

*   If $c(\FiniteSequenceCode{s})=2$, with its unique subcode at $s\concat(k)$, set
    $$A_s:=\SetDifference{X}{A_{s\concat(k)}}.$$

The whole record represents $A_c:=A_\emptyset$. This is the same evaluation of inductive data as before,
now carried out on the recorded positions.

### Borel rank and structural rank {#sec:borel-codes-rank}

\begin{mathmeta}
  \vars{k,p}{Nat}
\end{mathmeta}

The \termdefineas{tree rank}{structural rank} of a code measures the nesting of its constructors. Define it by
structural recursion:
$$
\begin{aligned}
\rho(\BorelLeafCode{n})&=0,\\
\rho(\BorelComplementCode{d})&=\rho(d)+1,\\
\rho(\BorelUnionCode{\Sequence{d_k}{k\in\omega}})&=\sup_k(\rho(d_k)+1).
\end{aligned}
$$
Every immediate subcode has smaller rank. Thus recursion on subcodes is justified even when there is no
common finite bound on their nesting depths.

To bound the Borel rank of $A_c$, use an ordinal measure adapted to the decoding operations. Define the
\termdefine{Borel code level} $\ell(c)$ by structural recursion on the code:
$$
\begin{aligned}
\ell(\BorelLeafCode{n}) &= 1,\\
\ell(\BorelComplementCode{c'}) &= \ell(c') + 1,\\
\ell(\BorelUnionCode{\Sequence{c_k}{k\in\omega}}) &= \sup_k \ell(c_k).
\end{aligned}
$$
This differs from $\rho$: a union need not increase the code level above the levels of its subcodes.
The code level gives an upper bound on the Borel rank of the decoded set:
$$
A_c \in \bSigma^0_{\ell(c)}(X).
$$
The proof is induction on the code, following the three clauses. A leaf decodes to a basic open set, so $A_c \in
\bSigma^0_1$. A complement decodes to $\SetDifference{X}{A_{c'}}$ with $A_{c'} \in \bSigma^0_{\ell(c')}$; this
set is $\bPi^0_{\ell(c')}$, hence $\bSigma^0_{\ell(c')+1}$. A union decodes to $\bigcup_k A_{c_k}$ with each
$A_{c_k} \in \bSigma^0_{\ell(c_k)} \IncludedIn \bSigma^0_{\sup_k \ell(c_k)}$, and each level $\bSigma^0_\gamma$ is
closed under countable unions, so the union stays at level $\sup_k \ell(c_k)$. Since every $\ell(c)$ is a countable
ordinal, a countable-rank code always decodes to a Borel set of countable Borel rank.

Conversely, the recursive construction in the previous subsection gives inductive constructor data for every
Borel set. Neither the code level nor the structural rank need be the least Borel level of the decoded set:
redundant complements can increase both without changing that set.

Structural induction shows that $\rho(c)$ is countable for every code $c$: each constructor takes a successor
or the supremum of countably many countable successors. Regularity of $\omegaOneOrd$ keeps the result countable.
This explains why the recursive data suffice for the Borel hierarchy up to its stabilization at $\omegaOneOrd$.

\begin{lemma*}[\termdefineas{reindexing Borel-code children}{Reindexing the subcodes of a Borel code}]
In evaluating a union and computing its code level and structural rank, any nonempty family of immediate subcodes
numbered by a subset of $\omega$ may be replaced by a sequence indexed by $\omega$ that enumerates every member,
with repetitions allowed. All three values remain unchanged. A complement still uses its unique subcode.
\end{lemma*}

\begin{proof}[Proof]
Let $C\IncludedIn\omega$ be the nonempty set of subcode numbers of a union, and choose a surjection
$e:\omega\to C$. For any family of sets $A_k$ and any family of ordinals $\alpha_k$, surjectivity gives
$$\bigcup_{n\in\omega} A_{e(n)}=\bigcup_{k\in C}A_k,
\qquad
\sup_{n\in\omega}\alpha_{e(n)}=\sup_{k\in C}\alpha_k.$$
For the code level, use the subcodes' levels as $\alpha_k$; for the structural rank, use their ranks plus $1$.
The leaf and complement clauses are unchanged. Induction on immediate subcodes now proves preservation of all three
recursively computed values. The enumerations are chosen set-theoretically; no effective choice from a code is asserted.
\end{proof}

This reconstructs inductive constructor data from any valid external record, preserving interpretation, level,
and rank. Conversely, the recording rules in §{sec:borel-codes-encoding} turn inductive data into a valid external
record. The three evaluation equations show that this preserves the represented set.
Thus the coding construction and the ordinal bounds apply to the external records as well.

### Valid external records {#sec:borel-codes-valid-records}

\begin{mathmeta}
  \define{BorelCodes}
  \vars{x}{Name}
  \vars{n}{Nat}
\end{mathmeta}

Let $\BorelCodes \IncludedIn \BaireSpace$ be the set of valid external records of Borel codes.
Besides the local recording rules, validity requires that following immediate subcodes cannot continue indefinitely:
$$\forall x \in \BaireSpace\ \exists n\ c(\FiniteSequenceCode{\restrict{x}{n}})=0.$$
Here $x$ specifies successive choices of subcode numbers.

<!-- formalization: skip (reading guide for later code-definability results) -->
The construction and structural recursion above suffice to interpret each valid record. The complexity of the
set of valid records and the uniform descriptions of evaluation are studied in §{sec:borel-codes-pi11}, after
analytic sets and Polish-topology refinement have been introduced. Those results are not needed to construct a
code or evaluate a fixed valid code.

### Later uses of codes {#sec:borel-codes-why}

\begin{mathmeta}
  \forward{lSigma,lPi,lDelta}
\end{mathmeta}

<!-- formalization: skip-begin (brief guide to later universal-set, boundedness, absoluteness and effective results;
  these applications are deferred to the linked sections) -->
The code construction connects with four recurring uses of parameters.

*   **Universal sets.** Codes provide parameters for families of Borel sets, as in §{sec:finite-borel-universal}.
    The effective versions of these constructions are developed in §{sec:edst-universal}.
*   **Boundedness.** The positions of successive subcodes form a well-founded tree, and its usual rank is the
    structural rank defined above. This connects our data with the
    \termforwardas{boundedness theorem for well-founded trees}{boundedness theorem} in §{sec:edst-boundedness},
    which gives a common countable rank bound for analytic families of well-founded trees.
*   **Absoluteness.** In §{sec:forcing-absoluteness}, evaluation of the same Borel code in a ground model and a forcing
    extension agrees on ground-model points.
*   **Effectivization.** For a recursively presented Polish space with its effective basis and recursive coding
    conventions, recursive Borel codes describe the hyperarithmetic sets $\lDelta^1_1$. The corresponding relativized
    statement recovers all Borel sets by allowing real parameters. This requires an effective presentation, not merely
    an arbitrary enumeration of a topological basis; see §{sec:hyperarithmetic-hierarchy}.
<!-- formalization: skip-end -->
