# Baire-Class Functions {#sec:baire-class-functions}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{t}{Real}
  \vars{u,v_*,s_*,\tilde{s}}{Fun(Real,Real)}
  \vars{s}{Fun(Real,Nat)}
\end{mathmeta}

<!-- formalization: skip-begin (chapter motivation and scope) -->
The \termuse{Borel hierarchy} of §{sec:borel-hierarchy} classifies definable *sets*. There is a parallel vocabulary for
definable *functions*. Continuous maps are the zeroth level.
Baire-class functions are obtained from continuous maps by iterating pointwise limits.
They measure how far a function is from
being continuous while keeping its inverse images inside the Borel hierarchy.

This chapter studies the relation between Baire classes and the Borel complexity of inverse images of open sets.
It also shows that a pointwise limit of functions of class at most $\alpha$ has class at most $\alpha+1$.
For real-valued functions on Polish spaces, the \termforward{Lebesgue--Hausdorff theorem} gives a characterization
of each Baire class by inverse images. We state this converse at the end of the chapter.
<!-- formalization: skip-end -->

Let $X$ be a topological space and let $Y$ be a metrizable space. A function $f:X\to Y$ is
\termdefineas{Baire class 0}{Baire class $0$} if it is continuous. For a nonzero countable ordinal $\alpha$, $f$ is
\termdefineas{Baire class alpha}{Baire class $\alpha$} if there is a sequence $\Sequence{f_n}{n\in\omega}$ of functions
$X\to Y$
of Baire classes
$<\alpha$ such that
$$
f(x)=\lim_{n\to\infty} f_n(x)
$$
for every $x\in X$. At a successor stage this says "pointwise limit of functions of the preceding accumulated classes";
at a limit stage the witness classes need not have a common bound below the limit. Only each individual term must have
class $<\alpha$.

The classes are cumulative. If $\beta<\alpha$ and $f$ belongs to Baire class $\beta$, then the constant sequence
$f,f,\ldots$ witnesses that $f$ also belongs to Baire class $\alpha$. Thus "Baire class at most $\alpha$" means
membership in this cumulative class; the exact Baire class, when needed, is the least such ordinal.

<!-- formalization: skip (expository explanation of the roles of the two topologies) -->
Continuity is defined using the topologies on $X$ and $Y$, and the limit at each $x$ is taken in the topology on $Y$.
Thus the Baire classes do not depend on the choice of a compatible metric. Pointwise convergence is required;
uniform convergence is not.

\begin{proposition*}[Basic closure under pointwise limits]
If each $f_n:X\to Y$ has \termuseas{Baire class alpha}{Baire class at most $\alpha$}, then the pointwise limit
$f=\lim_n f_n$, when it exists everywhere, has Baire class at most $\alpha+1$.
\end{proposition*}

\begin{proof}
This is built into the definition: every $f_n$ has class $<\alpha+1$, and $f$ is their pointwise limit.
\end{proof}

\begin{example*}[Indicators of closed sets]
Let $F$ be a closed subset of a metric space $X$. Its \termdefine{indicator function} is the real-valued function
$$
\IndicatorFunction{F}(x)=\begin{cases}1&x\in F,\\0&x\notin F.\end{cases}
$$
If $F=\emptyset$, this is the constant-zero function. Otherwise, for $n\ge1$ put
$$
u_{F,n}(x)=\max\{0,1-n d(x,F)\}.
$$
Distance to a nonempty set is continuous, so each $u_{F,n}$ is continuous. On $F$ its value is $1$; outside $F$,
closedness gives $d(x,F)>0$, so its value is eventually $0$. Thus $u_{F,n}\to \IndicatorFunction{F}$
pointwise, and $\IndicatorFunction{F}$ has Baire
class at most $1$. It is continuous exactly when $F$ is clopen: the inverse images of small open intervals about
$1$ and $0$ are $F$ and its complement. In particular, the indicator of a closed set that is not open has exact
Baire class $1$.
\end{example*}

\begin{example*}[Derivatives are Baire one]
Let $u:\R\to\R$ be differentiable. The difference quotients
$$
v_n(t)=n\bigl(u(t+1/n)-u(t)\bigr),\qquad n\ge1,
$$
are continuous and converge to $u'(t)$ at each point. Hence every derivative has Baire class at most $1$.
For a concrete discontinuous derivative, take
$$
u(t)=\begin{cases}t^2\sin(1/t)&t\ne0,\\0&t=0.\end{cases}
$$
Then $u'(0)=0$, while $u'(t)=2t\sin(1/t)-\cos(1/t)$ for $t\ne0$. As $t\to0$, the first term tends to $0$ but the
second has no limit. Thus $u'$ is discontinuous at $0$ and has exact Baire class $1$.
\end{example*}

<!-- formalization: skip-begin (transition to the following formal statement) -->
The next theorem bounds the Borel complexity of inverse images of open sets in terms of the Baire class.
<!-- formalization: skip-end -->

\begin{theorem*}[Inverse-image bound] Let $X$ and $Y$ be metric spaces, and let $\alpha<\omegaOneOrd$. If $f:X\to Y$
has \termuseas{Baire class alpha}{Baire class $\alpha$}, then for every open set $V\IncludedIn Y$,
$$
f^{-1}(V)\in\bSigma^0_{\alpha+1}(X).
$$

\end{theorem*}

\begin{proof}[Proof] We argue by induction on $\alpha$.

For $\alpha=0$, the function $f$ is continuous, so $f^{-1}(V)$ is open, hence in $\bSigma^0_1(X)$.

Assume $\alpha>0$ and the result holds for all smaller classes. Choose functions $f_n:X\to Y$ of classes
$\alpha_n<\alpha$ with $f_n(x)\to f(x)$ for every $x$. Fix an open set $V\IncludedIn Y$.

Because $Y$ is metric,
$$
V=\bigcup_{k\ge 1} F_k
$$
for closed sets $F_k\IncludedIn V$ chosen for instance as
$$
F_k=\{y\in Y:d(y,\SetDifference{Y}{V})\ge 2^{-k}\},
$$
with the convention that $d(y,\emptyset)=1$. These sets may be empty, but their union is $V$: if $y\in V$, openness
gives $d(y,\SetDifference{Y}{V})>0$, so $y\in F_k$ for all sufficiently large $k$.

We claim that
$$
f^{-1}(V)
=
\bigcup_{k\ge 1}\bigcup_{N\in\omega}\bigcap_{n\ge N} f_n^{-1}(F_k).
$$
If $x\in f^{-1}(V)$, choose $k$ so large that $d(f(x),\SetDifference{Y}{V})>2^{-k}$. Then $f(x)$ lies in the interior of
$F_k$,
and $f_n(x)\to f(x)$ gives $f_n(x)\in F_k$ for all sufficiently large $n$. This puts $x$ in the right-hand side.
Conversely, if $x$ belongs to the right-hand side, then for some $k,N$ all $f_n(x)$ with $n\ge N$ lie in the closed set
$F_k$. Passing to the limit gives $f(x)\in F_k\IncludedIn V$.

By the induction hypothesis applied to the open complement $\SetDifference{Y}{F_k}$, each
$$
f_n^{-1}(\SetDifference{Y}{F_k})
$$
lies in $\bSigma^0_{\alpha_n+1}(X)$, with $\alpha_n+1\le\alpha$ because $\alpha_n<\alpha$. Therefore $f_n^{-1}(F_k)$
lies in $\bPi^0_\alpha(X)$ by the monotonicity proved in §{sec:borel-hierarchy}. Countable intersections of
$\bPi^0_\alpha$ sets remain in
$\bPi^0_\alpha$: after taking complements, this is the closure of $\bSigma^0_\alpha$ under countable unions, which
follows directly from the recursive definition for $\alpha\ge 2$, and is the ordinary closure of open sets under
countable unions when $\alpha=1$. The displayed formula writes $f^{-1}(V)$ as a countable union of $\bPi^0_\alpha$ sets,
hence $f^{-1}(V)\in\bSigma^0_{\alpha+1}(X)$.
\end{proof}

<!-- formalization: skip-begin (transition to the following formal statement) -->
For class $1$ this specializes to a useful concrete statement:
<!-- formalization: skip-end -->

\begin{corollary*} If $X$ and $Y$ are metric spaces and $f:X\to Y$ is a pointwise limit of continuous functions, then
$f^{-1}(V)$ is $\Fsigma$ for every open $V\IncludedIn Y$. In particular, every
\termuseas{Baire class alpha}{Baire-one} function is \termuseas{Borel-measurable map}{Borel measurable}.

\end{corollary*}

\begin{proof}[Proof] Apply the inverse-image bound above with $\alpha=1$. The class $\bSigma^0_2$ is exactly the
$\Fsigma$ class, and the open-set criterion in §{sec:borel-hierarchy} gives Borel measurability.
\end{proof}

<!-- formalization: skip-begin (transition to the following formal statement) -->
The inverse-image bound can also rule out a proposed Baire class. The next example uses this to distinguish
class $2$ from class $1$.
<!-- formalization: skip-end -->

\begin{example*}[\termdefine{Dirichlet function}]
The indicator of the rationals,
$$
D(t)=\begin{cases}1&t\in\QQ,\\0&t\notin\QQ,\end{cases}
$$
has exact Baire class $2$. To obtain the upper bound, enumerate $\QQ=\{q_0,q_1,\ldots\}$ and put
$F_n=\{q_0,\ldots,q_n\}$. Each $F_n$ is closed, so its indicator $\IndicatorFunction{F_n}$ has Baire class at
most $1$ by the
closed-set example. At a rational point these indicators are eventually $1$, and at an irrational point they are
always $0$. Hence $\IndicatorFunction{F_n}\to D$ pointwise, so $D$ has Baire class at most $2$.

If $D$ had Baire class $1$, the preceding corollary would imply that
$$
D^{-1}\bigl(\OpenInterval{-1/2}{1/2}\bigr)=\SetDifference{\R}{\QQ}
$$
is $\Fsigma$. But the irrationals are not $\Fsigma$, as shown using the Baire category theorem in
§{sec:alexandrov-theorem}. This proves that the class is exactly $2$.
\end{example*}

The same induction on the Baire class also gives the expected closure under composition.

\begin{proposition*}[Composition with continuous maps] Let $X,Y,Z$ be topological spaces, with $Y$ and $Z$ metrizable
where Baire classes are used. If $f:X\to Y$ has \termuseas{Baire class alpha}{Baire class $\alpha$} and $g:Y\to Z$ is
continuous, then $g\circ f$ has Baire class $\alpha$. If $h:Z\to X$ is continuous, then $f\circ h$ has Baire class
$\alpha$.

\end{proposition*}

\begin{proof}[Proof] For $\alpha=0$ this is ordinary closure of continuous maps under composition. For $\alpha>0$, write
$f=\lim_n f_n$ pointwise with $f_n$ of classes $<\alpha$. Then $g\circ f=\lim_n g\circ f_n$ pointwise by continuity of
$g$, and the induction hypothesis puts each $g\circ f_n$ below $\alpha$. Similarly, $f\circ h=\lim_n f_n\circ h$, and
each $f_n\circ h$ has class $<\alpha$ by induction.
\end{proof}

<!-- formalization: skip-begin (classical real-valued Lebesgue--Hausdorff converse cited to Kechris §24; the reverse
  implication is not proved in this chapter) -->
For real-valued functions on Polish spaces, the inverse-image condition also characterizes the Baire class.

\begin{theorem*}[\termdefineas{Lebesgue--Hausdorff theorem}{Lebesgue--Hausdorff}] Let $X$ be a Polish space and let
$0<\alpha<\omegaOneOrd$. A function $f:X\to\R$ belongs to
\termuseas{Baire class alpha}{Baire class $\alpha$} iff
$f^{-1}(V)\in\bSigma^0_{\alpha+1}(X)$ for every open $V\IncludedIn\R$.
\end{theorem*}

**Reference and discussion.** The forward implication is the inverse-image theorem proved above.
We use the reverse implication as an external theorem; see [@Kechris1995, §24] for its proof.
<!-- formalization: skip-end -->

\begin{example*}[The converse depends on the codomain]
Give $\{0,1\}$ the discrete topology and define $s:\R\to\{0,1\}$ by
$$
s(t)=\begin{cases}1&t>0,\\0&t\le 0.\end{cases}
$$
The inverse images of open subsets of $\{0,1\}$ are $\emptyset$, $\R$, $\OpenInterval{0}{\infty}$, and
$\RightClosedInterval{-\infty}{0}$;
all are $\Fsigma$ in $\R$. However, every continuous map from the connected space $\R$ to the discrete space
$\{0,1\}$ is constant, and a pointwise limit of constant maps is constant. Hence $s$ is not of Baire class $1$.
For comparison, the real-valued function $\tilde{s}:\R\to\R$ with the same values is the pointwise limit of
$$
s_n(t)=\min\{1,\max\{0,nt\}\},\qquad n\ge1.
$$
Each $s_n$ is continuous: it is $0$ on the negative half-line, rises linearly from $0$ to $1$, and then stays $1$.
These approximations take intermediate real values, so they are not maps into the discrete space $\{0,1\}$.
Thus the codomain matters even when the limiting functions take the same values, and the real-valued converse
cannot be extended to arbitrary metrizable codomains.
\end{example*}
