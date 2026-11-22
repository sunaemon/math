# Analytic Sets and Suslin Schemes {#sec:analytic-sets-suslin-schemes}

<!-- formalization: skip-begin (chapter motivation, scope, and references) -->
The Borel hierarchy stratifies sets generated from the open sets by countable unions, intersections, and complements.
Pushing past it requires a new operation: \termdefineas{projection operation}{projection}. This chapter develops the
first projection class, the analytic sets, and the equivalent tree form supplied by
\termforwardas{Suslin scheme}{Suslin schemes}. The central boundary at this level is Suslin's theorem: a set is Borel
exactly when it is both analytic and
coanalytic. The standard reference for this material, including the effective refinement, is [@Moschovakis2009];
[@MansfieldWeitkamp1985] is a complementary treatment emphasizing the recursion-theoretic side.
<!-- formalization: skip-end -->

## Analytic Sets {#sec:analytic-sets}

\begin{mathmeta}
  \vars{p}{Name}
  \vars{n}{Nat}
  \vars{s}{Seq(Nat)}
\end{mathmeta}

A subset $A \IncludedIn X$ of a Polish space is \termdefineas{analytic set}{analytic} ($\bSigma^1_1$) if it is the
continuous image of a Polish space.

\begin{proposition*}[\termdefineas{closed-projection characterization of analytic sets}{Closed-projection theorem}]
The set $A$ is analytic if and only if it is the projection to $X$ of a closed subset of $X \times \BaireSpace$.
\end{proposition*}

\begin{proof}[Proof] Suppose first that $A$ is analytic. If $A=\emptyset$, use the empty closed subset of $X\times
\BaireSpace$. Otherwise, write $A=g(Z)$ for a nonempty Polish space $Z$ and a continuous map $g:Z\to X$. By the
universal continuous-surjection theorem of §{sec:universal-continuous-surjection}, there is a continuous surjection
$q:\BaireSpace\to Z$. The graph
$$
C:=\{\Pair{g(q(p))}{p}:p\in\BaireSpace\}
$$
is closed in $X\times\BaireSpace$, because $X$ is Hausdorff and $g\circ q$ is continuous, and its projection to $X$ is
$A$.

Conversely, if $C\IncludedIn X\times\BaireSpace$ is closed, then $C$ is Polish by the closed-subspace result of
§{sec:polish-key-properties}. The coordinate projection $C\to X$ is continuous, so its image is analytic.
\end{proof}

Complements of analytic sets are \termdefineas{coanalytic set}{coanalytic} ($\bPi^1_1$).

The following \termforward{Suslin's theorem} identifies the first projective ambiguity class with the Borel sets.

\begin{theorem*}[\termdefineas{Suslin's theorem}{Suslin}] For a subset $A$ of a Polish space $X$, the following are
equivalent:

\begin{enumerate}
\item $A$ is Borel.
\item $A$ is both analytic and coanalytic.
\item Both $A$ and $\SetDifference{X}{A}$ are analytic.
\end{enumerate}

\end{theorem*}

Equivalently,
$$\bDelta^1_1(X) \;:=\; \bSigma^1_1(X) \cap \bPi^1_1(X) \;=\; \mathcal B(X).$$
Thus the first projective ambiguity class is not a new class at all: it is exactly the Borel $\sigma$-algebra.

\begin{proof}[Proof] The equivalence of (2) and (3) is just the definition of coanalytic: $A$ is coanalytic exactly when
$\SetDifference{X}{A}$ is analytic.

Suppose first that $A$ is Borel. By \termuse{Kuratowski's refinement theorem} in §{sec:polish-topology-refinement},
refine the topology of $X$ to a Polish topology $\tau'$ with the same Borel sets and with $A$ clopen. The identity map
$$
\Pair{X}{\tau'}\longrightarrow \Pair{X}{\tau}
$$
is continuous because $\tau'$ refines $\tau$. Since $A$ is clopen in $\Pair{X}{\tau'}$, it is Polish in the subspace
topology
by the closed-subspace result of §{sec:polish-key-properties}. The identity map sends this Polish space continuously
onto
$A$ as a subset of the original space. Thus $A$ is analytic. The same argument applied to the Borel set
$\SetDifference{X}{A}$ shows that $\SetDifference{X}{A}$ is analytic.

Conversely, suppose that both $A$ and $\SetDifference{X}{A}$ are analytic. By \termforward{Lusin separation theorem},
proved in
§{sec:lusin-separation} of the next chapter, there is a Borel set $B\IncludedIn X$ such that
$$A\IncludedIn B\IncludedIn \SetDifference{X}{(\SetDifference{X}{A})}=A.$$
Hence $B=A$, so $A$ is Borel.
\end{proof}

\begin{proposition*}[Further characterizations of analytic sets] For $A\IncludedIn X$, the following are equivalent:

\begin{enumerate}
\item $A$ is analytic.
\item The set $A$ is the projection to $X$ of a Borel subset of $X\times Y$ for some Polish space $Y$.
\item The set $A$ is the image of a Borel subset of a Polish space under a Borel map into $X$.
\end{enumerate}

\end{proposition*}

\begin{proof}[Proof] The \termuse{closed-projection characterization of analytic sets} gives (1) $\Rightarrow$ (2).
For (2) $\Rightarrow$ (1), the Borel-to-analytic implication of \termuse{Suslin's theorem} makes the Borel subset of
$X\times Y$ analytic, and continuous images of analytic sets are analytic. Applying this to the coordinate projection
gives $A$.

The same closed subset of $X\times\BaireSpace$, viewed as a Borel domain for the coordinate projection, proves (1)
$\Rightarrow$ (3). Conversely, suppose $A=f(D)$, where $D$ is Borel in a Polish space $Y$ and $f:Y\to X$ is Borel.
Choose a countable base $\Sequence{V_n}{n\in\omega}$ of $X$ and apply \termuse{Kuratowski's refinement theorem} to the
family
$$E_0:=D,\qquad E_{n+1}:=f^{-1}(V_n)\quad(n\in\omega).$$
Every $E_n$ is Borel. In the resulting Borel-preserving Polish topology on $Y$, all the $E_n$ are clopen.
Thus $D$ is Polish, and $f$ is continuous because the inverse image of every basic open set is open.
The restriction $f|_D$ is continuous and has image $A$, so $A$ is analytic.
\end{proof}

More generally, if $D$ is analytic in a Polish space $Y$ and $f:Y\to X$ is Borel, then $f(D)$ is analytic.
For $D=\emptyset$ this is immediate. Otherwise, take a continuous map $h:\BaireSpace\to Y$ with $h(\BaireSpace)=D$.
The composite $f\circ h$ is Borel, and
$$f(D)=(f\circ h)(\BaireSpace).$$
Applying the Borel-image characterization to the Borel domain $\BaireSpace$ proves the claim.

The inclusion of Borel sets into $\bSigma^1_1$ can be strict: there are analytic sets that are not Borel. To
describe a tree example, let $\mathcal T$ be the space of trees on $\omega$,
including the empty tree, viewed through their indicator functions as a closed subspace of $2^{\finseq{\omega}}$.
Each violation of closure under initial segments is detected by two indicator coordinates, so the tree
condition is closed and $\mathcal T$ is Polish.
The branch relation is
$$R:=\{\Pair{T}{p}\in\mathcal T\times\BaireSpace:\forall n\in\omega,\ \restrict{p}{n}\in T\}.$$
For each finite word $s$, the condition $s\in T$ is clopen, and the cylinder $\cyl{s}$ is clopen. Therefore
$$
R=\bigcap_{s\in\finseq{\omega}}
\left(\{T\in\mathcal T:s\in T\}\times\BaireSpace
\;\cup\;\mathcal T\times\bigl(\SetDifference{\BaireSpace}{\cyl{s}}\bigr)\right)
$$
is closed. Its projection $I:=\{T\in\mathcal T:\TreeBody{T}\ne\emptyset\}$, the set of ill-founded trees, is analytic.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
未リンク部分は末尾の非Borel性の引用だけ。Kechris/Moschovakisの外部定理として明記され、
局所的な閉分岐関係・解析性の構成は既存Leanに接続済み。非Borel性を局所的に証明したとは扱わない。)
--> We use the classical theorem that $I$ is not Borel [@Kechris1995; @Moschovakis2009].<!--
formalization: skip-end
-->

The transport of this example to every uncountable Polish space is proved in
§{sec:analytic-nonborel-transfer}, after the general Borel classification. The present tree example already
shows that analytic projections need not be Borel.

## Suslin Operation and Suslin Schemes {#sec:souslin-operation-suslin-schemes}

\begin{mathmeta}
  \vars{p}{Name}
  \vars{k,n}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

<!-- formalization: skip (transition from projections to the internal tree form) -->
Projection is the external definition of analytic sets. The internal tree form is the \termdefine{Suslin operation},
which turns a tree-indexed family of sets into a set of points admitting one successful infinite branch of
approximations.

Let $\IndexedFamily{A_s}{s\in\finseq{\omega}}$ be a family of subsets of a space $X$. The \termuse{Suslin operation}
$\mathcal A$
sends
this family to
$$
\mathcal A(A_s)
\;:=\;
\bigcup_{p\in\BaireSpace}\ \bigcap_{n\in\omega} A_{\restrict{p}{n}}.
$$
Thus
$$
x\in\mathcal A(A_s)
\quad\Longleftrightarrow\quad
\exists p\in\BaireSpace\ \forall n\; x\in A_{\restrict{p}{n}}.
$$
The sequence $p$ is a witness branch. A family $\{A_s\}$ used in this way is called a \termdefine{Suslin scheme}. It is
\termdefineas{monotone Suslin scheme}{monotone} if
$$A_{s\concat(k)}\IncludedIn A_s\qquad(s\in\finseq{\omega},\ k\in\omega),$$
and, in a metric space $\Pair{X}{d}$, a monotone scheme is \termdefineas{regular Suslin scheme}{regular} if additionally
the
sets are closed and
$$\MetricDiameter{d}{A_s}\le 2^{-\Length{s}}.$$

The operation contains ordinary countable unions as a degenerate case: if $A_\emptyset=X$, $A_{(n)}=B_n$, and
$A_s=A_{\restrict{s}{1}}$ for all nonempty $s$, then
$$\mathcal A(A_s)=\bigcup_n B_n.$$

<!-- formalization: skip (comparison with ordinary Borel operations) -->
But it is stronger than the Borel operations because the existential choice is an infinite branch, not a single natural
number. This is exactly the additional projection quantifier in the definition of analytic sets.

\begin{proposition*}[Closed schemes produce analytic sets] If $X$ is Polish and each $F_s\IncludedIn X$ is closed, then
$\mathcal A(F_s)$ is analytic.
\end{proposition*}

\begin{proof}[Proof] Consider
$$
C
:=
\{\Pair{p}{x}\in\BaireSpace\times X:\forall n,\ x\in F_{\restrict{p}{n}}\}.
$$
For fixed $n$, the condition $x\in F_{\restrict{p}{n}}$ defines the closed set
$$
\bigcup_{\Length{s}=n}\cyl{s}\times F_s.
$$
It is closed because its complement is
$$
\bigcup_{\Length{s}=n}\cyl{s}\times (\SetDifference{X}{F_s}),
$$
which is open. Hence $C$ is closed as a countable intersection of closed sets. Its projection to $X$ is exactly
$\mathcal A(F_s)$, so $\mathcal A(F_s)$ is analytic.
\end{proof}

<!-- formalization: skip (transition to the representation theorem) -->
Conversely, every analytic set comes from a regular Suslin scheme.

\begin{theorem*}[\termdefineas{Suslin-scheme representation theorem}{Suslin-scheme representation}] For a subset $A$ of
a Polish space $X$, the following are equivalent:

\begin{enumerate}
\item $A$ is analytic.
\item There is a family of closed sets $\IndexedFamily{F_s}{s\in\finseq{\omega}}$ with
    $$A=\mathcal A(F_s).$$
\item There are a complete compatible metric $d\le1$ on $X$ and a Suslin scheme
    $\IndexedFamily{F_s}{s\in\finseq{\omega}}$ that is regular with respect to $d$, with
    $$A=\mathcal A(F_s).$$
\end{enumerate}

\end{theorem*}

\begin{proof}[Proof] The implication (3) $\Rightarrow$ (2) is immediate, and (2) $\Rightarrow$ (1) is the proposition
that closed schemes produce analytic sets.

For (1) $\Rightarrow$ (3), the definition of analytic and the universal continuous-surjection theorem of
§{sec:universal-continuous-surjection} give a closed set $P\IncludedIn\BaireSpace$ and a continuous map $f:P\to X$ with
$A=f(P)$. For $A=\emptyset$, take $P=\emptyset$; otherwise one may take $P=\BaireSpace$. Fix a complete compatible
metric $d$ on $X$ bounded by $1$, using the bounded-metric construction of §{sec:polish-proof-tools}.

We recursively build relatively clopen pieces $P_s\IncludedIn P$ and closed sets
$$F_s:=\Closure{f(P_s)}$$
so that:

\begin{enumerate}
\item $P_\emptyset=P$;
\item $P_{s\concat(k)}\IncludedIn P_s$;
\item $P_s=\bigcup_k P_{s\concat(k)}$;
\item $\MetricDiameter{\SeqMetricName}{P_s}\le 2^{-\Length{s}}$ whenever $s\ne\emptyset$;
\item $\MetricDiameter{d}{F_\emptyset}\le1$, and $\MetricDiameter{d}{F_s}\le 2^{-\Length{s}}$ whenever
      $s\ne\emptyset$.
\end{enumerate}

Suppose $P_s$ is given, and put $\epsilon:=2^{-(\Length{s}+1)}$. For each $u\in P_s$, continuity of $f$ and the relative
clopen basis of $P$ give a relatively clopen neighborhood $V$ of $u$ such that
$$
V\IncludedIn P_s\cap\MetricBall{\SeqMetricName}{u}{\epsilon/2}
\cap f^{-1}(\MetricBall{d}{f(u)}{\epsilon/2}).
$$
The triangle inequality gives both $\MetricDiameter{\SeqMetricName}{V}\le\epsilon$ and
$\MetricDiameter{d}{f(V)}\le\epsilon$. These neighborhoods cover $P_s$. By second countability, choose a countable
subcover $\Sequence{B_k}{k\in\omega}$; if $P_s=\emptyset$, take every $B_k$ empty.

Define the children directly by
$$
P_{s\concat(k)}:=\SetDifference{B_k}{\bigcup_{j<k}B_j}.
$$
Each child is relatively clopen because only finitely many earlier clopen sets are removed. The children are pairwise
disjoint, and they cover $P_s$: a point belongs to the child with the least index of a covering set containing it.
Empty children remain in the indexing. Since $P_{s\concat(k)}\IncludedIn B_k$, both diameter bounds pass to each
child. Taking closures of their images gives $F_{s\concat(k)}$. The containment
$P_{s\concat(k)}\IncludedIn P_s$ makes these closures subsets of $F_s$, and closure does not increase metric diameter.

Now show $A=\mathcal A(F_s)$. If $x=f(u)$ for some $u\in P$, then at each level choose the unique child containing $u$.
This gives a branch $p\in\BaireSpace$ with $u\in P_{\restrict{p}{n}}$ for all $n$, hence
$$x=f(u)\in F_{\restrict{p}{n}}\qquad(n\in\omega),$$
so $x\in\mathcal A(F_s)$.

Conversely, suppose $x\in\mathcal A(F_s)$, witnessed by $p$. For each $n$, choose $u_n\in P_{\restrict{p}{n}}$ with
$$d(f(u_n),x)\le 2^{-n};$$
this is possible because $x\in\Closure{f(P_{\restrict{p}{n}})}$. For $m,\ell\ge n\ge1$, nesting and the diameter bound
give
$$\SeqMetric{u_m}{u_\ell}\le2^{-n}.$$
Thus $\Sequence{u_n}{n\in\omega}$ is Cauchy in the complete space $P$. Let $u$ be its limit. For each $n$, all
sufficiently late terms lie
in the relatively closed set $P_{\restrict{p}{n}}$, so
$$u\in\bigcap_n P_{\restrict{p}{n}}\IncludedIn P.$$
The shrinking diameters make this intersection contain at most one point. Continuity gives $f(u_n)\to f(u)$, whereas
the approximation estimate gives $f(u_n)\to x$. Uniqueness of limits yields $f(u)=x$, so $x\in f(P)=A$.
\end{proof}

<!-- formalization: skip-begin (interpretive summary, warnings, and pointer to a later application) -->
This theorem is the tree version of the projection definition. A point lies in an analytic set exactly when there is an
infinite branch through a scheme of closed approximations whose intersection converges to that point.

Two warnings are useful.

*   The Suslin operation applied to closed sets need not produce a Borel set; in fact it produces exactly the analytic
    sets. This is the first place where the Borel hierarchy is no longer closed under a natural operation.
*   The operation is not complement-stable. Complementing analytic sets gives coanalytic sets, and the equality
    $\bSigma^1_1\cap\bPi^1_1=\text{Borel}$ is precisely Suslin's theorem.

The Lusin--Suslin argument in §{sec:lusin-souslin-proof} is a controlled version of the same idea. There Lusin
separation builds Borel tests for the finite prefixes of the unique source point; shrinking image-neighborhoods then
force those prefixes to converge back to a genuine preimage.
<!-- formalization: skip-end -->

## Definability and Uniform Evaluation of Borel Codes {#sec:borel-codes-pi11}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

<!-- formalization: skip (return to the Borel-code infrastructure) -->
We now return to the valid records defined in §{sec:borel-codes-valid-records}. The analytic and coanalytic
classes give a language for the complexity of validity, while §{sec:polish-topology-refinement} supplies the
refinement used in uniform evaluation. These results describe families of codes; the interpretation of an
individual valid code remains the structural recursion of §{sec:borel-codes}.
Fix a Polish space $X$ with a countable base $\Sequence{U_n}{n\in\omega}$, using the coding conventions of
§{sec:borel-codes}.

\begin{proposition*}[\termdefineas{coanalyticity of valid Borel codes}{Coanalyticity of valid Borel codes}]
The set $\BorelCodes$ is coanalytic.
\end{proposition*}

\begin{proof}[Proof]
The local syntax conditions are Borel: each refers to finitely many label coordinates, followed by countable
quantifiers over positions and subcode numbers. Failure of termination is witnessed by a sequence of present positions,
each specifying an immediate subcode of its predecessor. Give finite words the discrete topology. The relation
between a code
and such a sequence is closed, since each successive-subcode condition is clopen and there are countably many of them.
Its projection is analytic. Invalidity is the union of this projection and the Borel set of syntax failures,
so invalidity is analytic and validity is coanalytic.
\end{proof}

<!-- formalization: skip-begin (external completeness classification, not used by the local evaluation proof) -->
In fact, $\BorelCodes$ is $\bPi^1_1$-complete [@Kechris1995]. The completeness assertion is not needed for
coding or evaluation here.
<!-- formalization: skip-end -->

The \termdefine{decoding relation} is
$$D := \{\Pair{c}{x} : c \in \BorelCodes,\, x \in A_c\}.$$
The following uniform descriptions distinguish evaluation on valid codes from a statement about all real parameters.

\begin{proposition*}[\termdefineas{uniform evaluation of Borel codes}{Uniform evaluation of Borel codes}]
There are analytic sets $V,F\IncludedIn\BaireSpace\times X$ such that, for every valid code $c$ and every $x\in X$,
$$x\in A_c\quad\Longleftrightarrow\quad\Pair{c}{x}\in V
\quad\Longleftrightarrow\quad\Pair{c}{x}\notin F.$$
Thus evaluation is relatively $\bDelta^1_1$ on $\BorelCodes\times X$.
\end{proposition*}

\begin{proof}[Proof]
For a candidate code, assign a truth bit $u_s$ to every finite word $s$, with value $0$ at unused positions.
At a leaf specifying $U_n$, require $u_s=1$ exactly when $x\in U_n$.
At a complement position, require opposite bits at that position and each present immediate subcode.
At a union position with bit $1$, store a selected subcode number $j_s$ and require that the subcode is present and
has bit $1$.
Conversely, any present subcode with bit $1$ must force its containing union to have bit $1$.
The numbers $j_s$ at all other positions are immaterial. These conditions define a certificate relation on all candidate
codes, without first testing validity.

By the refinement theorem in §{sec:polish-topology-refinement}, choose a finer Polish topology on $X$ making all
$U_n$ clopen. Each certificate condition is now clopen in the code, point, truth bits, and selected subcode numbers.
For the condition using $j_s$, fix each possible value $k$ and impose the corresponding implication.
The conjunction of the resulting countably many conditions is closed. Requiring the bit at the empty position to be
$1$ or $0$
still gives a closed relation. Its two projections onto the code and point coordinates are analytic.
The identity map from the refined product to the original product is continuous, so these same sets, denoted by
$V$ and $F$, are analytic in the original topology too.

For a valid code, induction on immediate subcodes gives a unique rule-obeying truth assignment.
Choosing a true subcode at every true union position extends it to a certificate.
Conversely, the local rules force every certificate to have exactly this truth assignment.
Its bit at the empty position is $1$ exactly when $x\in A_c$, and is $0$ exactly when $x\notin A_c$.
This proves the two equivalences.
\end{proof}

The descriptions $V$ and $F^c$ agree on valid codes. <!--
formalization: skip-begin (引用・背景説明・読書案内:
VとFの補集合がvalid
codes上で一致する局所的主張はdecodingRelation_eq_restricted_evaluationへ接続した。
残りは直前でKechrisを引用するvalid-code域の非Borel性を踏まえた適用範囲の説明で、新しい局所証明を提示する箇所ではない。)
--> This does not assert that $D$ is Borel in the ambient product:
the domain $\BorelCodes$ is non-Borel, so \termuse{Suslin's theorem} cannot be applied to these restricted
descriptions to draw that conclusion.<!--
formalization: skip-end
-->
