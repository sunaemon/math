# Algorithmic Randomness {#sec:computational-choice-randomness}

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Read the cylinder measure algorithms in §{sec:tte-cantor-open-measure} before this chapter, and use
§{sec:tte-null-spheres} for the extension to computable Polish measures. The definitions require effectively
open sets and uniform numerical programs from §{sec:tte-effective-open-closed} and §{sec:tte-finite-data}.
Neither the Fourier examples nor forcing extensions are needed: §{sec:random-forcing-detail} supplies a
comparison with a different notion of null-set avoidance. The goal is to distinguish Martin-Löf, Schnorr, and
weak 2-randomness by the information required of their tests. Read the universal-test and separation arguments
first at the level of open sets and measure bounds; their finite-list programs certify the effective steps
without making the final random point computable.

<!-- formalization: skip-end -->

## Randomness Tests and Null-Set Avoidance {#sec:tte-algorithmic-randomness}

\begin{mathmeta}
  \vars{a,x}{Name}
  \vars{e,k,n,p}{Nat}
  \vars{b}{Rat}
  \vars{u,w}{Seq}
  \vars{h,s,t}{Nat}
  \vars{a_*}{Name}
\end{mathmeta}
\index{Martin-Lof randomness@Martin-Löf randomness}
\index{Schnorr randomness}
\index{computable measure}

<!-- formalization: skip (conceptual comparison with random forcing) -->
\termuse{random forcing} in §{sec:random-forcing-detail} says that a random real over a countable ground model avoids
every null Borel set coded in that model. \termdefine{Algorithmic randomness} makes this statement effective: the null
sets to be avoided are no longer arbitrary ground-model codes, but computably presented null tests.

Start with Cantor space and the fair-coin measure $\mu$. A
\termdefineas{Martin-Lof test}{Martin-Löf test} [@MartinLof1966] is a uniformly effectively open sequence
$\Sequence{U_n}{n\in\omega}$ such that
$$\mu(U_n)\le 2^{-n}.$$
A real $x\in\CantorSpace$ is \termdefineas{Martin-Lof randomness}{Martin-Löf random} if
$$x\notin\bigcap_n U_n$$
for every Martin-Löf test $\Sequence{U_n}{n\in\omega}$. Equivalently, $x$ lies outside the intersection of every
uniformly effectively open
sequence whose measures shrink at the prescribed computable rate $\mu(U_n)\le 2^{-n}$. Dropping that rate and requiring
avoidance of every effectively presented null $G_\delta$ set instead gives the strictly stronger notion of
\termdefine{weak 2-randomness}. Thus Martin-Löf randomness is the rate-bounded effective analogue of the forcing
slogan "the random real avoids every old null set"; it does not quantify over all effective null $G_\delta$ codes.

Here uniform effective openness means that one closed numerical lambda term $P$ computes a table
$p(\NatPair{n}{s})$ of valid cylinder entries, with
$$U_n=\bigcup_s V_{p(\NatPair{n}{s})}.$$
Both the row $n$ and the enumeration stage $s$ are numerical inputs to the same program. The entry convention
is that of §{sec:tte-cantor-open-measure}; in particular, empty stages and repetitions are allowed.

The definition extends from Cantor space to any computable Polish probability space. For a
\termuseas{computable measure}{computable probability measure} $\mu$, a Martin-Löf test relative to $\mu$ is a
uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$. A point is $\mu$-Martin-Löf
random if it
avoids all such tests.

<!-- formalization: skip (cited external valuation-integral characterization) -->
The valuation definition in §{sec:tte-null-spheres} is equivalent to computability of
integrals of bounded computable continuous functions, uniformly when a rational bound on their absolute values
is supplied. We use this equivalence as an external theorem; Hoyrup and Rojas develop the formulation for
spaces with computable metric presentations [@HoyrupRojas2009].

\termdefine{Schnorr randomness} tightens the measure side of the test [@Schnorr1971]. A \termdefine{Schnorr test} is a
Martin-Löf test $\Sequence{U_n}{n\in\omega}$ for which the real number $\mu(U_n)$ is computable uniformly in $n$. Every
Martin-Löf random
point is Schnorr random. The converse fails already for fair-coin measure on Cantor space. The distinction
matters because Schnorr randomness treats the measure of
the test itself as part of the effective data, matching the computable-analysis principle that negative information
should be supplied with a usable modulus rather than only an existence proof.

In the Schnorr condition, uniform computability of the measures means that there are fast Cauchy names $q_n$
of $\mu(U_n)$ and one closed numerical term $M$ satisfying
$$M\ChurchNumeral{\NatPair{n}{k}}\to_\beta^*\ChurchNumeral{q_n(k)}.$$
The precision $k$ is an input, as is the test row $n$. We now work with the fair-coin measure on Cantor space.

\begin{proposition*}[\termdefineas{randomness implications}{Implications between randomness notions}]
Every weakly 2-random point is Martin-Löf random, and every Martin-Löf random point is Schnorr random.
\end{proposition*}

\begin{proof}[Proof]
For a Martin-Löf test, monotonicity of the measure gives
$$0\le\mu\left(\bigcap_m U_m\right)\le\mu(U_n)\le 2^{-n}\qquad(n\in\NN).$$
Letting $n$ tend to infinity shows that the intersection is null. The same enumeration is therefore a weak
2-randomness test, so avoiding all such tests implies avoidance of every Martin-Löf test. A Schnorr test
already is a Martin-Löf test, which proves the second implication.
\end{proof}

\begin{mathmeta}
  \forward{LambdaListField,LambdaLeCase}
\end{mathmeta}

\begin{lemma*}[\termdefineas{bounded cylinder enumeration}{Restricting a cylinder enumeration to a measure bound}]
Let $p$ be a computable name of a Cantor open set and let $b\in\QQ$ satisfy $b\ge 0$.
One can compute a valid name $\widetilde p$ with $\mu(U_{\widetilde p})\le b$.
If $\mu(U_p)\le b$ already holds, then $\widetilde p=p$.
The construction is uniform in a numerical parameter for the name and the bound.
\end{lemma*}

\begin{proof}[Proof]
Start with $L_0:=[]$. At stage $s$, compute the exact rational measure of the finite union obtained by
adding $p(s)$ to the accepted list. Define
$$\widetilde p(s):=\begin{cases}
p(s),&\mu(U_{p(s)::L_s})\le b,\\
0,&\mu(U_{p(s)::L_s})>b,
\end{cases}\qquad L_{s+1}:=\widetilde p(s)::L_s.$$
The finite-union algorithm in §{sec:tte-cantor-open-measure} decides the comparison, including equality.
Every entry remains valid. Induction gives $\mu(U_{L_s})\le b$; these finite unions increase to
$U_{\widetilde p}$, so continuity of measure gives the same bound for the union. Also $U_{L_s}\IncludedIn U_p$.
If $\mu(U_p)\le b$, every candidate union is a subset of $U_p$, so every entry is accepted.

Here is the parameterized lambda program. Let $F$ be the finite-union measure program, let $B$ return a
rational code for the bound, and let $C$ return the candidate entry on input $\NatPair{h}{k}$.
In the following abbreviations, $r$ is the accepted-list code and all displayed expressions denote lambda terms:
$$\begin{aligned}
D(h,k,r)&:=\LambdaListCons\,(C(\LambdaNumericPair\,h\,k))\,r,\\
T(h,k,r)&:=\LambdaRationalLess(\LambdaNumericPair\,(Bh)\,(F(D(h,k,r)))),\\
R(h,k,r)&:=\LambdaZeroTest\,T(h,k,r)\,D(h,k,r)\,(\LambdaListCons\,\ChurchNumeral{0}\,r),\\
H&:=\lambdaab{h}{\lambdaab{k}{\lambdaab{r}{R(h,k,r)}}},\qquad B_0:=\lambdaab{h}{\ChurchNumeral{0}},\\
S&:=\lambdaab{z}{\LambdaParamRec{B_0}{H}\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)},\\
P&:=\lambdaab{z}{\LambdaListField{1}\bigl(S(\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,
 (\LambdaSucc(\LambdaNumericProjection{2}z)))\bigr)}.
\end{aligned}$$
Expand the abbreviations inside the abstractions. The comparison returns zero exactly when the candidate is
within the bound. The state program $S$ computes the accepted list by parameterized recursion, and $P$ reads
its head after one further update. Thus the parameter $h$ remains an input throughout the calculation.
All component programs terminate, so this gives a closed total numerical program whenever $B$ and $C$ are such programs.
\end{proof}

\begin{theorem*}[\termdefineas{universal Martin-Lof test}{Universal Martin-Löf test}]
There is a Martin-Löf test $\Sequence{V_n}{n\in\omega}$ such that, for every Martin-Löf test
$\Sequence{U_n}{n\in\omega}$, some program index $e$ satisfies
$$U_{n+e+1}\IncludedIn V_n\qquad(n\in\NN).$$
Consequently, $x$ is Martin-Löf random if and only if $x\notin\bigcap_n V_n$.
\end{theorem*}

\begin{proof}[Proof]
Enumerate all closed numerical lambda programs by their syntax codes, replacing an invalid code by a fixed
closed term as in §{sec:lambda-program-input-codes}. The program with index $e$ need not terminate or enumerate
valid entries. Instead of waiting for it, use the total finite-certificate test $\LambdaOutputCandidate$.
At stage $t=\NatPair{s}{k}$ of row $\Pair{e}{n}$, unpair $k$ into an output $a$ and a certificate bound. Emit $a$ if
the certificate verifies output $a$ on input $\NatPair{n}{s}$ and $a$ is a valid cylinder entry; otherwise emit zero.
Call this total table $c(\NatPair{\NatPair{e}{n}}{t})$.

Validity is a finite binary-digit test. For a word code $w$, take
$$\begin{aligned}
Q&:=\lambdaab{z}{\LambdaLeCase{\LambdaListGet\,z}{\ChurchNumeral{1}}{\ChurchNumeral{1}}{\ChurchNumeral{0}}},\\
D&:=\lambdaab{w}{\LambdaBoundedProduct{Q}(\LambdaNumericPair\,w\,(\LambdaListLength\,w))}.
\end{aligned}$$
The output of $D$ is nonzero exactly when every decoded digit is at most one. The padding entry is valid;
for $a>0$, apply this test to the word code $a-1$. To display the full candidate program, abbreviate the
numerical projections as $\pi_i:=\LambdaNumericProjection{i}$ and set
$$\begin{gathered}
\begin{aligned}
E(z)&:=\pi_1(\pi_1z),&N(z)&:=\pi_2(\pi_1z),\\
J(z)&:=\pi_1(\pi_2z),&K(z)&:=\pi_2(\pi_2z),\\
O(z)&:=\pi_1(K(z)).
\end{aligned}\\
\begin{aligned}
T(z)&:=\LambdaOutputCandidate\,E(z)\,(\LambdaNumericPair\,N(z)\,J(z))\,K(z),\\
A(z)&:=\LambdaZeroTest\,(D(\LambdaPred\,O(z)))\,\ChurchNumeral{0}\,O(z),\\
C&:=\lambdaab{z}{\LambdaZeroTest\,T(z)\,\ChurchNumeral{0}\,A(z)}.
\end{aligned}
\end{gathered}$$
For output zero the same formula returns zero. Thus all stages terminate, all nonzero entries are valid,
and both the program index and the test row remain numerical inputs.

Apply the preceding lemma to each row with bound $2^{-n}$. Write $\widehat c_{e,n}$ for the resulting name
and $G_{e,n}:=U_{\widehat c_{e,n}}$. One closed program $R$ computes all these names on input
$\NatPair{\NatPair{e}{n}}{t}$: use $C$ above as its candidate program and
$B:=\lambdaab{h}{\LambdaDyadic(\LambdaNumericProjection{2}h)}$ as its bound program.
Then $\mu(G_{e,n})\le 2^{-n}$ for every $e,n$, regardless of the original program's behavior.
If index $e$ computes a genuine test $\Sequence{U_n}{n\in\omega}$, every accepted certificate for row $n$ has the same
output as
that test's enumeration, by uniqueness of numerical outputs. Conversely, each actual output has a finite
certificate. Hence the unmodified certificate row names exactly $U_n$. Its measure is already within the
bound, so the lemma leaves it unchanged and $G_{e,n}=U_n$.

Now put
$$V_n:=\bigcup_e G_{e,n+e+1}.$$
The row and stage pairing gives one enumeration program. More explicitly, with
$E(z):=\pi_1(\pi_2z)$ and $L(z):=\LambdaSucc(\LambdaAdd\,(\pi_1z)\,E(z))$, it is
$$V:=\lambdaab{z}{R\bigl(\LambdaNumericPair\,
 (\LambdaNumericPair\,E(z)\,L(z))\,(\pi_2(\pi_2z))\bigr)}.$$
Countable subadditivity gives
$$\mu(V_n)\le\sum_{e=0}^{\infty}2^{-(n+e+1)}=2^{-n}.$$
Thus $\Sequence{V_n}{n\in\omega}$ is a Martin-Löf test. Every genuine test has a closed-program index $e$, and the
equality
$G_{e,m}=U_m$ proved above gives $U_{n+e+1}\IncludedIn V_n$. A point failing any test therefore lies in
$\bigcap_n V_n$. Conversely, a point in that intersection fails this particular Martin-Löf test.
\end{proof}

\begin{corollary*}[\termdefineas{closed class of Martin-Lof random points}{A positive closed class of random points}]
The set $K:=\SetDifference{\CantorSpace}{V_1}$ is closed, its complement has a computable open name,
and $\mu(K)\ge 1/2$. Every point of $K$ is Martin-Löf random.
\end{corollary*}

\begin{proof}[Proof]
The set $V_1$ is effectively open and has measure at most $1/2$, so its complement is closed with measure
at least $1/2$. A point outside $V_1$ is outside $\bigcap_n V_n$, and is therefore Martin-Löf random by the theorem.
\end{proof}

\begin{proposition*}[\termdefineas{limit approximation null test}{A null test for a computable limit approximation}]
Let $a_s\in\CantorSpace$ be a sequence whose bits $a_s(k)$ are computed by one closed numerical term on
input $\NatPair{s}{k}$. Suppose that, for each $k$, the bit $a_s(k)$ eventually equals $x(k)$.
Then a uniformly effectively open sequence has intersection exactly $\{x\}$. In particular, $x$ is not weakly
2-random. No computable rate of stabilization is required.
\end{proposition*}

\begin{proof}[Proof]
Set
$$W_n:=\bigcup_{t\in\NN}\cyl{\restrict{a_{n+t}}{n}}.$$
Let $A$ be the term computing the bits. The finite-tabulation routine preserves the stage parameter and
returns the first $n$ bits in order. Thus the following closed term computes a cylinder-entry table for $W_n$:
$$\begin{aligned}
H&:=\lambdaab{z}{\LambdaAdd\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)},\\
J&:=\lambdaab{z}{\LambdaNumericPair\,(Hz)\,(\LambdaNumericProjection{1}z)},\\
P&:=\lambdaab{z}{\LambdaSucc\,(\LambdaListTabulate{A}(Jz))}.
\end{aligned}$$
On input $\NatPair{n}{t}$, it returns the code of $\restrict{a_{n+t}}{n}$ plus one. This is a valid entry because
all the tabulated values are bits. Every calculation terminates; the program never waits for a coordinate to
stabilize.

For each fixed $n$, the first $n$ coordinates eventually all agree with $x$, so $x\in W_n$.
Conversely, suppose $y\in\bigcap_n W_n$ and fix a coordinate $k$. Choose $N$ so that $a_s(k)=x(k)$ for
all $s\ge N$, and take $n\ge\max\{N,k+1\}$. Membership in $W_n$ supplies a $t$ with
$y\in\cyl{\restrict{a_{n+t}}{n}}$, hence
$$y(k)=a_{n+t}(k)=x(k).$$
This holds at every coordinate, proving $\bigcap_n W_n=\{x\}$. Singletons have fair-coin measure zero by
§{sec:random-forcing-detail}. Thus this is a weak 2-randomness test covering $x$.
\end{proof}

\begin{corollary*}[\termdefineas{computable points fail Schnorr tests}{Computable points are not Schnorr random}]
No computable point of Cantor space is Schnorr random.
\end{corollary*}

\begin{proof}[Proof]
For a computable point $x$, take the constant approximation $a_s=x$ in the preceding construction.
A bit program for this approximation projects $k$ from $\NatPair{s}{k}$ and applies the given bit program
for $x$. Now
$$W_n=\cyl{\restrict{x}{n}},\qquad \mu(W_n)=2^{-n}.$$
These measures have constant fast Cauchy names, computed uniformly by
$$M:=\lambdaab{z}{\LambdaDyadic(\LambdaNumericProjection{1}z)}.$$
The approximation precision is the second component of the input and is unused because the output is exact.
Thus $\Sequence{W_n}{n\in\omega}$ is a Schnorr test, and its intersection contains $x$.
\end{proof}

\begin{proposition*}[\termdefineas{computable limit selection}{Computable approximation outside a small open set}]
Let $p$ be a computable valid name of a Cantor open set with $\mu(U_p)\le 1/2$.
There are a sequence $a_s\in\CantorSpace$ with uniformly computable bits and a point
$x\in\SetDifference{\CantorSpace}{U_p}$ such that each bit $a_s(k)$ eventually equals $x(k)$.
The bit program is obtained uniformly from a numerical program for $p$.
\end{proposition*}

\begin{proof}[Proof]
Put $L_s:=\Tuple{p(0),\ldots,p(s-1)}$, with $L_0=[]$, and use the uncovered mass $G_L(w)$ from
§{sec:tte-cantor-open-measure}. Define binary words by
$$\begin{gathered}
w_{s,0}:=\emptySeq,\qquad w_{s,k+1}:=w_{s,k}\concat b_s(w_{s,k}),\\
b_s(w):=\begin{cases}
0,&G_{L_s}(w\concat0)>0,\\
1,&G_{L_s}(w\concat0)=0.
\end{cases}
\end{gathered}$$
Here $G_{L_s}$ takes nonnegative rational values, so the two cases are exhaustive and decidable.
Set $a_s(k):=b_s(w_{s,k})$. Then $\restrict{a_s}{k}=w_{s,k}$.

Every chosen prefix has positive uncovered mass. Indeed,
$G_{L_s}(\emptySeq)=1-\mu(U_{L_s})\ge 1/2$.
The cylinders $\cyl{w\concat0}$ and $\cyl{w\concat1}$ partition $\cyl{w}$, so
$$G_{L_s}(w)\le G_{L_s}(w\concat0)+G_{L_s}(w\concat1).$$
If the parent has positive uncovered mass and the zero-child has none, the one-child has positive mass.
Induction on $k$ therefore gives $G_{L_s}(w_{s,k})>0$.

For each fixed $k$, the word $w_{s,k}$ eventually stops changing. This is immediate for $k=0$.
Suppose the length-$k$ prefix has stabilized to $w$ after stage $N$.
The finite unions $U_{L_s}$ increase, so $G_{L_s}(w\concat0)$ is nonincreasing in $s$.
Either it stays positive at all stages $s\ge N$, or it becomes zero and remains zero thereafter.
Accordingly, the next bit is always zero or eventually always one. This proves stabilization at length $k+1$.
Let $x(k)$ be the eventual value of $a_s(k)$. No bound on the stabilization stage is claimed.

If $x\in U_p$, some enumerated cylinder $\cyl{u}$ contains $x$.
Choose $s$ after that cylinder has been enumerated and after the first $\Length{u}$ bits have stabilized.
Then $w_{s,\Length{u}}=u$ and $\cyl{u}\IncludedIn U_{L_s}$, contradicting
$G_{L_s}(w_{s,\Length{u}})>0$. Hence $x\notin U_p$.

For completeness, the bit calculation can be written as a closed lambda term. Let $P$ compute $p$,
and let $Z,H$ be the list-fold seed and handler for $G_L$ in §{sec:tte-cantor-open-measure}.
Write $\pi_i:=\LambdaNumericProjection{i}$. In the following abbreviations, $v,w$ are list and word codes,
and $b$ is a bit numeral:
$$\begin{aligned}
R&:=\lambdaab{z}{((\LambdaListFold{Z}{H})(\pi_1z))(\pi_2z)},\\
E(w,b)&:=\LambdaListAppend\,w\,(\LambdaListCons\,b\,\ChurchNumeral{0}),\\
T(v,w)&:=\LambdaRationalLess\bigl(\LambdaNumericPair\,\ChurchNumeral{0}\,
 (R(\LambdaNumericPair\,v\,E(w,\ChurchNumeral{0})))\bigr),\\
B&:=\lambdaab{z}{\LambdaZeroTest\,T(\pi_1z,\pi_2z)\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
\end{aligned}$$
The rational code zero denotes zero, and the strict comparison returns one for a positive mass.
Thus $B$ returns precisely the selected bit.

Retain the finite-list code as a parameter of the recursion:
$$\begin{aligned}
B_0&:=\lambdaab{v}{\ChurchNumeral{0}},\\
J&:=\lambdaab{v}{\lambdaab{k}{\lambdaab{w}{E(w,B(\LambdaNumericPair\,v\,w))}}},\\
S&:=\lambdaab{z}{\LambdaParamRec{B_0}{J}\,(\pi_1z)\,(\pi_2z)},\\
L(z)&:=\LambdaInputPrefix\,P\,(\pi_1z),\\
A&:=\lambdaab{z}{B\bigl(\LambdaNumericPair\,L(z)\,
 (S(\LambdaNumericPair\,L(z)\,(\pi_2z)))\bigr)}.
\end{aligned}$$
Expand the abbreviations inside the abstractions. The list-fold reductions show that $R$ computes $G_L$;
induction on the recursion depth shows that $S$ returns the code of $w_{s,k}$ when supplied with the code of
$L_s$ and $k$. Consequently, $A\,\ChurchNumeral{\NatPair{s}{k}}\to_\beta^*\ChurchNumeral{a_s(k)}$.
All finite-list and rational operations terminate. Neither the approximation nor its program uses a
stabilization bound or an oracle for the limiting point.
\end{proof}

\begin{theorem*}[\termdefineas{weak 2-randomness separation}{Martin-Löf versus weak 2-randomness}]
There is a Martin-Löf random point of Cantor space that is not weakly 2-random.
\end{theorem*}

\begin{proof}[Proof]
Apply the preceding proposition to $U_p=V_1$ from the universal test, whose measure is at most $1/2$.
If $V$ is the universal enumeration program, a program for $p$ is
$$P:=\lambdaab{s}{V(\LambdaNumericPair\,\ChurchNumeral{1}\,s)}.$$
It gives a point $x\notin V_1$ and a uniformly computable approximation to its bits. The point is Martin-Löf
random by the positive-closed-class corollary. The null test for a computable limit approximation constructed
above covers $x$, so $x$ is not weakly 2-random.
\end{proof}

\begin{theorem*}[\termdefineas{computable closed support point}{A computable point with positive local mass}]
Let $K\IncludedIn\CantorSpace$ be effectively closed with positive computable measure.
Then $K$ contains a computable point $x$ such that
$$\mu(K\cap\cyl{\restrict{x}{k}})>0\qquad(k\in\NN).$$
Given programs for the open complement and its measure, and an integer $m$ with $2^{-m}\le\mu(K)$,
the bit program for $x$ is obtained uniformly from these data.
\end{theorem*}

\begin{proof}[Proof]
Write $U_p:=\SetDifference{\CantorSpace}{K}$. Its measure is computable by subtraction from one.
Choose $m$ as in the statement and set $t_k:=2^{-(m+2k)}$.
We construct words $w_k$ of length $k$, starting with $w_0:=\emptySeq$, and maintain
$$\mu(K\cap\cyl{w_k})\ge t_k.$$
Use the local-measure program of §{sec:tte-cantor-open-measure} at the word $w_k\concat0$ and precision
$m+2k+2$. Its rational output value $r_k$ satisfies
$$\Abs{r_k-\mu(K\cap\cyl{w_k\concat0})}\le t_k/8.$$
Choose
$$b_k:=\begin{cases}0,&r_k\ge t_k/2,\\1,&r_k<t_k/2,\end{cases}
\qquad w_{k+1}:=w_k\concat b_k.$$
In the first case the chosen child's mass is at least $3t_k/8$.
In the second, the zero-child's mass is less than $5t_k/8$, so the other child's mass is greater than
$3t_k/8$. Both bounds imply the next invariant because $t_{k+1}=t_k/4$.
The initial invariant follows from $\mu(K)\ge2^{-m}$.

Define $x(k):=b_k$, so $\restrict{x}{k}=w_k$. Every such cylinder meets $K$ in positive measure.
If $x\notin K$, openness of $U_p$ supplies a prefix cylinder of $x$ contained in $U_p$, contradicting
that positive measure. Thus $x\in K$. The construction computes each bit after finitely many exact rational
operations and terminating stage searches; it never waits for equality of an unknown real to zero.

Here are the terms. Let $C$ compute the local mass names, with input consisting of a word code and a
precision. In the following abbreviations, $m,k,w,b$ denote numerals for the lower-bound exponent, depth,
word code, and bit:
$$\begin{aligned}
E(w,b)&:=\LambdaListAppend\,w\,(\LambdaListCons\,b\,\ChurchNumeral{0}),\\
N(m,k)&:=\LambdaSucc(\LambdaAdd\,m\,(\LambdaAdd\,k\,k)),\\
T(m,k,w)&:=\LambdaRationalLess\bigl(\LambdaNumericPair\,
 (C(\LambdaNumericPair\,E(w,\ChurchNumeral{0})\,(\LambdaSucc\,N(m,k))))\,
 (\LambdaDyadic\,N(m,k))\bigr).
\end{aligned}$$
The strict comparison directly returns the bit $b_k$: one selects the one-child, and zero the zero-child.
To iterate while keeping $m$ as a parameter, set
$$\begin{aligned}
B_0&:=\lambdaab{m}{\ChurchNumeral{0}},\\
J&:=\lambdaab{m}{\lambdaab{k}{\lambdaab{w}{E(w,T(m,k,w))}}},\\
S&:=\lambdaab{z}{\LambdaParamRec{B_0}{J}\,(\pi_1z)\,(\pi_2z)},\\
X_m&:=\lambdaab{k}{T(\ChurchNumeral{m},k,S(\LambdaNumericPair\,\ChurchNumeral{m}\,k))}.
\end{aligned}$$
Here $\pi_i:=\LambdaNumericProjection{i}$, and all abbreviations are expanded inside the abstractions.
Induction on $k$ using the parameterized-recursion reductions shows that $S$ returns the code of $w_k$.
Therefore $X_m\ChurchNumeral{k}\to_\beta^*\ChurchNumeral{x(k)}$. Positivity of $\mu(K)$ guarantees that some
integer $m$ satisfies the initial bound; once it is fixed, every subsequent step is computed by these terms.
\end{proof}

\begin{corollary*}[\termdefineas{no universal Schnorr test}{No universal Schnorr test}]
Every Schnorr test is passed by a computable point. Consequently, no single Schnorr test covers all points
that are not Schnorr random.
\end{corollary*}

\begin{proof}[Proof]
Let $\Sequence{U_n}{n\in\omega}$ be a Schnorr test. Then $K:=\SetDifference{\CantorSpace}{U_1}$ is effectively closed
with
computable measure at least $1/2$. If $P,Q$ compute the uniform open table and the uniform measure names,
respectively, specialize them by
$$P_1:=\lambdaab{s}{P(\LambdaNumericPair\,\ChurchNumeral{1}\,s)},\qquad
Q_1:=\lambdaab{k}{Q(\LambdaNumericPair\,\ChurchNumeral{1}\,k)}.$$
Apply the theorem with these programs and $m=1$. The resulting computable point is outside $U_1$,
so it passes this test. It is not Schnorr random, by the earlier corollary about computable points.
Thus this particular test cannot cover all points failing some Schnorr test.
\end{proof}

\begin{lemma*}[\termdefineas{countability of Schnorr tests}{Countability of Schnorr tests}]
The family of all Schnorr tests on $\CantorSpace$ is countable. Hence there is a sequence
$\Sequence{\Sequence{U^e_n}{n\in\NN}}{e\in\NN}$ containing every Schnorr test.
This is a set-theoretic enumeration; its computability is not assumed.
\end{lemma*}

\begin{proof}[Proof]
For each test, choose an index of a closed numerical program enumerating its open table.
If the same index is chosen for two tests, uniqueness of numerical outputs makes their tables equal at
every input, and hence their open sets agree in every row. Thus the chosen indices give an injection into
$\NN$. The family is nonempty: the constant empty test is a Schnorr test, with constant zero open entries
and constant rational zero measure names. A countable nonempty family has an enumeration by $\NN$.
Choosing indices in this argument does not provide a decision procedure for whether an arbitrary program
is a valid Schnorr test.
\end{proof}

\begin{mathmeta}
  \forward{LambdaEqual}
\end{mathmeta}

\begin{lemma*}[\termdefineas{computable cylinder search at a point}{Finding a cylinder at a computable point}]
Let $p$ be a computable valid open name and let $x\in U_p$ be computable.
From the two programs one can compute a binary word $w$ such that $x\in\cyl{w}\IncludedIn U_p$.
\end{lemma*}

\begin{proof}[Proof]
Let $P$ compute $p$ and let $X$ compute the bits of $x$.
At stage $s$, skip the entry if $p(s)=0$. Otherwise decode $p(s)-1$ as a binary word and compare it with
the equally long prefix of $x$. This is a finite calculation. Some comparison succeeds because $x\in U_p$.
For the terms, use
$$\begin{aligned}
D&:=\lambdaab{s}{\LambdaPred(Ps)},\\
F&:=\lambdaab{s}{\LambdaInputPrefix\,X\,(\LambdaListLength(Ds))},\\
T&:=\lambdaab{s}{\LambdaZeroTest\,(Ps)\,\ChurchNumeral{0}\,(\LambdaEqual\,(Ds)\,(Fs))},\\
W&:=\LambdaResultSearch\,
 (\lambdaab{s}{\LambdaZeroTest\,(Ts)\,\ChurchNumeral{1}\,\ChurchNumeral{0}})\,D.
\end{aligned}$$
The search test is zero precisely when a nonempty enumeration entry contains the point.
At the first such stage, $D$ returns the word code, so $W\to_\beta^*\ChurchNumeral{\LambdaListCode{w}}$.
The entry is one of those defining $U_p$, which proves the required containment.
\end{proof}

\begin{lemma*}[\termdefineas{Schnorr closed refinement}{Refining a positive closed set}]
Let $K\IncludedIn\CantorSpace$ be effectively closed with positive computable measure,
let $\Sequence{U_n}{n\in\omega}$ be a Schnorr test, and let $e\in\NN$.
There are an integer $n$ and an effectively closed set $L$ of positive computable measure such that
$$L\IncludedIn K\cap V_e,\qquad L\cap U_n=\emptyset,$$
where $\Sequence{V_e}{e\in\omega}$ is the universal Martin-Löf test constructed above.
\end{lemma*}

\begin{proof}[Proof]
First compute an integer $n$ with $2^{-n}<\mu(K)/2$.
Let $Q$ compute a fast Cauchy name $a$ of the measure of the open complement, and write
$r_s:=q_{a(s)}$. Search for the first $s$ with
$$r_s+2\cdot2^{-s}<1,$$
and put $n:=s+1$. The search terminates because $r_s\to1-\mu(K)<1$.
The Cauchy error bound gives $1-\mu(K)\le r_s+2^{-s}$, hence
$$2^{-s}<\mu(K),\qquad 2^{-n}<\mu(K)/2.$$
To write the search as a lambda term, put $c_1:=\RationalCode{1}{0}{0}$ and use
$$\begin{aligned}
A&:=\lambdaab{s}{\LambdaRationalAdd(\LambdaNumericPair\,(Qs)\,(\LambdaDyadic\,s))},\\
B&:=\lambdaab{s}{\LambdaRationalAdd(\LambdaNumericPair\,(As)\,(\LambdaDyadic\,s))},\\
T&:=\lambdaab{s}{\LambdaRationalLess(\LambdaNumericPair\,(Bs)\,\ChurchNumeral{c_1})},\\
J&:=\LambdaResultSearch\,
 (\lambdaab{s}{\LambdaZeroTest\,(Ts)\,\ChurchNumeral{1}\,\ChurchNumeral{0}})\,\LambdaSucc.
\end{aligned}$$
The rational comparison succeeds at the stated stage and $J\to_\beta^*\ChurchNumeral{n}$.

Set $C:=\SetDifference{K}{U_n}$. Then
$$\mu(C)\ge\mu(K)-\mu(U_n)\ge\mu(K)-2^{-n}>\mu(K)/2>0.$$
Its complement is the union of the open complement of $K$ and $U_n$.
Both have computable open and measure names, so the finite-union proposition makes $C$ effectively closed
with computable measure. The row programs for $U_n$ are obtained by substituting the computed numeral for
the row argument of the two uniform Schnorr-test programs.

Apply the computable-support-point theorem to $C$. It gives a computable point $y\in C$ with
$$\mu(C\cap\cyl{\restrict{y}{k}})>0\qquad(k\in\NN).$$
Every computable point fails Schnorr randomness, hence also Martin-Löf randomness.
By universality, $y\in V_e$. The cylinder-search lemma computes a binary word $w$ with
$y\in\cyl{w}\IncludedIn V_e$. Since $w=\restrict{y}{\Length{w}}$, the set
$$L:=C\cap\cyl{w}$$
has positive measure. It is effectively closed with computable measure by the cylinder-complement lemma.
It is contained in $K\cap V_e$ and disjoint from $U_n$, as required.
\end{proof}

\begin{theorem*}[\termdefineas{Schnorr–Martin-Löf separation}{Schnorr randomness does not imply Martin-Löf randomness}]
There is a point of $\CantorSpace$ which is Schnorr random but not Martin-Löf random.
\end{theorem*}

\begin{proof}[Proof]
Fix a set-theoretic enumeration $\Sequence{\Sequence{U^e_n}{n\in\NN}}{e\in\NN}$ of all Schnorr tests.
Starting with $K_0:=\CantorSpace$, apply the refinement lemma recursively to obtain effectively closed sets
of positive computable measure and integers $n_e$ such that
$$K_{e+1}\IncludedIn K_e\cap V_e,\qquad K_{e+1}\cap U^e_{n_e}=\emptyset.$$
Each set is nonempty and closed in compact Cantor space, and the sets decrease.
Compactness gives a point
$$x\in\bigcap_e K_e.$$
For every $e$, this point is outside $U^e_{n_e}$, so it passes every Schnorr test.
On the other hand, $x\in K_{e+1}\IncludedIn V_e$ for every $e$, hence $x$ fails the universal Martin-Löf test.
Thus it has precisely the asserted two randomness properties.

The finite refinement uses the lambda programs given above for row selection, finite-union measure,
support points, and cylinder search. The enumeration of valid tests and the choice of a point in the infinite
intersection are set-theoretic steps. In particular, the argument does not compute the final point;
no Schnorr-random point is computable.
\end{proof}

<!-- formalization: skip-begin (comparison with random forcing) -->
The hierarchy can be read as three versions of the same null-set avoidance idea:

| setting | avoided sets | generic point |
|---------|--------------|---------------|
| random forcing over $M$ | Borel null sets coded in $M$ | random real over $M$ |
| \termuseas{Martin-Lof randomness}{Martin-Löf} | effectively bounded open tests | Martin-Löf random |
| Schnorr randomness | effectively measured null tests | Schnorr random point |

Thus algorithmic randomness is not an isolated recursion-theoretic add-on. It is the effective measure-theoretic
continuation of random forcing, expressed in the language of computable Polish spaces, effective opens, and
\termuseas{computable measure}{computable probability measures}.
<!-- formalization: skip-end -->

