# Inside the Effective Topos {#sec:inside-effective-topos}
\index{effective topos!internal view}
\index{assembly}
\index{modest set}

<!-- formalization: skip-begin (chapter synthesis and transition to the appendices) -->

The effective topos organizes natural-number realizability into an internal universe. Points of the chosen
objects have realizers, maps transform evidence, and predicates specify how membership is witnessed.
Computable-point assemblies connect this universe to TTE and effective domain presentations. These links
preserve particular constructions, while leaving a distinction between recursive-index evidence and arbitrary
external names.

Its value is diagnostic. Classical theorems that survive internally have computational content; theorems that fail
internally reveal exactly where a proof used nonconstructive information such as excluded middle, unrestricted choice,
or an undecidable comparison of reals. The effective topos therefore closes the computable arc of the text by explaining
why the same Polish-space vocabulary supports both classical and constructive readings.

<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter orientation and imported effective-topos metatheory) -->

§{sec:effective-topos} built $\EffCat$ from the Kleene realizability tripos. We now inspect its internal mathematics.
\termforwardas{assembly}{Assemblies} display objects by external elements and natural-number realizers.
For a \termuse{computable Polish space}, we use the assembly of computable points, rather than all external
points. The \termuse{internal logic} describes constructions witnessed by recursive operations on these realizers.

The chapter first translates computable points and their maps into assemblies, then develops products and function
objects as the basic constructions needed for internal analysis. After the internal principles, the final section
compares zero selection from function names with zero selection from numerical function trackers. These are different
input representations, and their impossibility proofs use different arguments.

Proof scope: this chapter explains how to read the preceding constructions in the internal logic. It uses the
effective-topos construction from
§{sec:effective-topos} and proves the local translations among assemblies, TTE objects, domains, and the displayed
internal principles needed for the book's synthesis. The exact realizability validation of Church's Thesis, Markov's
Principle, and the Continuity Principle is imported from the standard $K_1$ realizability semantics summarized in
Appendix §{sec:realizability-tripos}; this chapter records the internal forms and explains their computational reading
rather than developing a complete effective-topos metatheory [@Hyland1982; @vanOosten2008].

<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Use the objects, truth values, and function objects built in §{sec:effective-topos}, and recall assemblies and
modest sets from §{sec:realizability-assemblies}. The TTE comparison needs only the name-transformer
foundations in §{sec:type-two-lambda-realizers}, while the domain comparison uses
§{sec:domains-tte-equivalence}. First follow products, addition, and evaluation as concrete tests of the
internal interpretation. Read the internal principles with the realizability validation stated in
§{sec:realizability-tripos}; return to the zero-selection arguments to check where uniformity and program
indices matter. The goal is to state which points carry numerical realizers and why an arbitrary external name
cannot silently be substituted for such an index.

<!-- formalization: skip-end -->

## Assemblies, TTE, and Domains Inside $\EffCat$ {#sec:tte-domains-eff-subcategories}

\begin{mathmeta}
  \vars{a,b,e,r,s}{Nat}
  \vars{t}{Fun(Nat,Nat)}
\end{mathmeta}

An \termforward{assembly} $A=\Pair{\UnderlyingSet{A}}{\Vdash_A}$ assigns a nonempty set
$E_A(x):=\{e:e\Vdash_A x\}\IncludedIn\NN$ to each $x\in\UnderlyingSet{A}$. A morphism $f:A\to B$ is a function on the
underlying sets for which one index $r$ satisfies
$$e\in E_A(x)\quad\Longrightarrow\quad r\cdot e\text{ is defined and belongs to }E_B(f(x)).$$
Only the function is part of the morphism; the tracker is required to exist. Identity and composition of functions
are tracked by the identity program and composition of the two tracking programs. This gives the category of assemblies.
The associated realizer-valued relation is
$$
x\sim_A y=
\begin{cases}
E_A(x), & x=y,\\
\emptyset, & x\ne y.
\end{cases}
$$

\begin{proposition*}[Assembly PER calculation]
The displayed relation is symmetric and transitive pointwise.
\end{proposition*}

\begin{proof}[Proof]
If $e$ realizes $x\sim_A y$, then $x=y$, so the same $e$ realizes $y\sim_A x$. If $e$ realizes $x\sim_A y$ and $e'$
realizes $y\sim_A z$, then $x=y=z$, so $e$ realizes $x\sim_A z$.
\end{proof}

The identity operation tracks symmetry, and the first projection from $\NatPair{e}{e'}$ tracks transitivity.
Thus this is a realizer-valued PER. The passage to morphisms requires the following additional argument.

\begin{theorem*}[\termdefineas{fully faithful assembly embedding}{Fully faithful assembly embedding}]
Sending $A$ to the displayed PER and $f:A\to B$ to the graph relation
$$\Gamma_f(x,y):=E_A(x)\land(f(x)\sim_B y)$$
defines a fully faithful functor from assemblies to $\EffCat$.
\end{theorem*}

\begin{proof}[Proof]
A tracker for $f$ also sends each realizer of $x\sim_A x'$ to one of $f(x)\sim_B f(x')$.
The graph construction in §{sec:effective-topos-finite-limits} therefore gives a functional relation.
For the identity, projecting the second entry sends $\Gamma_{\mathrm{id}}(x,y)$ into $x\sim_A y$.
For composition, a realizer of the composite graphs contains realizers of $E_A(x)$, $f(x)\sim_B y$, and
$g(y)\sim_C z$ for some $y$. Apply the equality tracker for $g$ to the middle component and then transitivity
in $C$; pair the result with the input extent. This uniformly realizes $\Gamma_{g\circ f}(x,z)$.
The one-inclusion criterion in §{sec:effective-topos-subobjects-truth-values} turns both inclusions into equivalences,
proving the functor laws.

For faithfulness, $\Gamma_f(x,y)$ is nonempty exactly when $y=f(x)$. The forward implication follows from the diagonal
relation in $B$. For the reverse implication, choose a realizer of $x$ and apply a tracker for $f$; pair the input
and output. Thus equivalent graph relations determine the same underlying function.

For fullness, let $F:A\to B$ be any functional relation between the displayed PERs. Given $x$, choose an element of
$E_A(x)$ and apply totality of $F$. This proves that $F(x,y)$ is nonempty for some $y$.
Single-valuedness and the diagonal relation in $B$ make this $y$ unique; define $f(x)=y$.
If $u_F$ tracks totality and $r_F$ extracts the output extent from strictness, then
$$a\longmapsto r_F(u_F(a))$$
tracks $f$. Indeed, $u_F(a)\in F(x,y)$ for some $y$, and uniqueness gives $y=f(x)$.
The program computes a numerical realizer, not a representative $y$ of the underlying set.
Finally, if $b\in F(x,y)$, uniqueness gives $y=f(x)$, and the two strictness projections produce
$$\NatPair{\ell_F(b)}{r_F(b)}\in\Gamma_f(x,y).$$
This is a uniform inclusion $F\le\Gamma_f$; the same one-inclusion criterion gives $F\equiv\Gamma_f$.
Hence every arrow between embedded assemblies comes from an assembly morphism.
\end{proof}

In particular, this embeds \termforwardas{modest set}{modest} assemblies, in which each realizer realizes at most
one element. We next construct the assembly associated with a represented space and the numerical tracker induced
by a Type-Two realizer.

\begin{mathmeta}
  \forward{LambdaSyntaxCode,LambdaOutputSearch,LambdaNumeralCodeProgram,LambdaTaggedCode}
\end{mathmeta}

\begin{lemma*}[\termdefineas{name-to-index transformation}{From name transformers to index transformers}]
Let a closed term $P$ compute a Type-Two map $F:D\to\BaireSpace$ on $D\IncludedIn\BaireSpace$.
There is a total lambda-computable function $t:\NN\to\NN$ such that
$$\varphi_e=p\in D\quad\Longrightarrow\quad\varphi_{t(e)}=F(p).$$
The function $t$ is defined even for indices which do not compute a name in $D$.
\end{lemma*}

\begin{proof}[Proof]
Put $U:=\LambdaOutputSearch$, the universal evaluator from §{sec:lambda-output-search}, and choose
fixed named representatives of $P,U$. The term $U\ChurchNumeral{e}$ computes the same numerical partial function
as index $e$. Define
$$t(e):=\LambdaSyntaxCode{P(U\ChurchNumeral{e})}.$$
This is a computation of finite syntax. More explicitly, put $c(a,b):=3\NatPair{a}{b}+1$, the application-code
constructor. Then
$$t(e)=c\bigl(\LambdaSyntaxCode{P},c(\LambdaSyntaxCode{U},\LambdaSyntaxCode{\ChurchNumeral{e}})\bigr).$$
The closed programs $\LambdaNumeralCodeProgram$ and $\LambdaTaggedCode{1}$, together with constant programs and
composition, compute this formula on every input $e$. No name is executed during this code construction.

Suppose now that $\varphi_e=p\in D$. Substitute the closed numerical program $U\ChurchNumeral{e}$ for the oracle
in the computation of $P$ on $p$. Each oracle query at $n$ is replaced by its finite beta reduction to
$\ChurchNumeral{p(n)}$. The substitution argument in §{sec:lambda-input-composition} gives
$$P(U\ChurchNumeral{e})\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{F(p)(n)}.$$
The term whose code is $t(e)$ is closed. Decoding that code therefore gives precisely this program, proving the
claimed equality of total names.
\end{proof}

\begin{mathmeta}
  \scopebegin
  \vars{X}{Set(Point)}
  \vars{x}{Point}
  \vars{p}{Name}
  \vars{e}{Nat}
  \vars{\delta}{PartialFun(Name,Point)}
  \vars{\varphi_*}{PartialFun(Nat,Nat)}
  \vars{A_\delta}{Assembly(Point)}
\end{mathmeta}

For a representation $\delta$ of $X$, let $A_\delta$ have underlying set
$$\UnderlyingSet{A_\delta}:=\{x\in X:\exists p\in\DomainOf\delta\ \exists e\in\NN\ (\delta(p)=x\ \land\ \varphi_e=p)\}$$
and realization relation
$$e\Vdash_{A_\delta}x\quad\Longleftrightarrow\quad
  \exists p\in\DomainOf\delta\ (\delta(p)=x\ \land\ \varphi_e=p).$$
These are exactly the \termforwardas{computable point in represented space}{computable points} for $\delta$.
Every such point has a realizer by definition. For a computable Polish space, take $\delta=\rho_X$.

Here $e$ is a numerical program index, $p$ is a total natural-number-valued name, and $x$ is a point of $X$.
The equality $\varphi_e=p$ requires the partial function $\varphi_e$ to be defined at every natural number and
agree with $p$ there. The representation $\delta$ is partial; the condition $p\in\DomainOf\delta$ makes
$\delta(p)$ defined.

\begin{mathmeta}
  \scopeend
\end{mathmeta}

\begin{proposition*}[Computable-point assemblies]
The assembly $A_\delta$ is modest. If $f:X\to Y$ has a Type-Two computable realizer for $\delta_X,\delta_Y$,
then its restriction to computable points is a morphism $A_{\delta_X}\to A_{\delta_Y}$.
This construction preserves identity maps and composition.
\end{proposition*}

\begin{proof}[Proof]
If an index realizes both $x$ and $y$, uniqueness of numerical outputs makes the two names equal coordinatewise.
Applying $\delta$ gives $x=y$, proving modesty. Let $F$ realize $f$, and let $t$ be the index transformer in the
preceding lemma. If $e$ realizes $x$ via a name $p$, then $t(e)$ computes the valid name $F(p)$, and
$$\delta_Y(F(p))=f(\delta_X(p))=f(x).$$
Thus $f(x)$ is a computable point, and one index computing $t$ tracks the restricted function for every input
realizer. The underlying functions of the induced identity and composite are the identity and composite of the
restricted functions. Assembly morphisms are determined by these functions, so the two functor laws follow.
\end{proof}

<!-- formalization: skip-begin (external/internal comparison and recursive-tree warning) -->

The following are translations into computable-point assemblies. They do not assert an equivalence between
TTE and $\EffCat$. In particular, internal existential quantification over the Baire object ranges over realized
sequences. A recursive tree can have an external infinite branch without any recursive branch, so its external
projection cannot in general be replaced by that internal quantifier.

| External language | Internal language in $\EffCat$ |
|-------------------|--------------------------------------|
| Index of a total recursive Cauchy name for $x$ | realizer of an element $x$ |
| TTE-computable map | induced morphism on computable-point assemblies |
| semidecidable open set | subobject classified by a realized predicate |
| relativization to a real parameter | changing the available realizer structure |

<!-- formalization: skip-end -->

\begin{mathmeta}
  \define{LambdaRationalDouble}
  \forward{LambdaMul,LambdaNumericPair,LambdaNumericProjection,LambdaSucc,LambdaRationalAdd}
\end{mathmeta}

\begin{construction*}[Doubling computable reals]
Use the rational codes of §{sec:tte-polish-as-represented}: if $i=\RationalCode{a}{b}{c}$, put
$$q_i:=\frac{a-b}{c+1},\qquad
\mathrm{dbl}(\RationalCode{a}{b}{c}):=\RationalCode{2a}{2b}{c}.$$
Every rational has such a code, so this sequence is dense in $\R$. Its Cauchy representation is $\rho_{\R}$.
Let $A=A_{\rho_{\R}}$ be the assembly of computable reals constructed above. Thus $e\Vdash_A x$ means that
$\varphi_e$ is a total Cauchy name for $x$. We will track the function $d(x)=2x$.

There is a closed program $\LambdaRationalDouble$ computing $\mathrm{dbl}$ on every numerical input.
Write $\pi_1,\pi_2$ for the closed numerical projection programs
$\LambdaNumericProjection{1},\LambdaNumericProjection{2}$.
Recover the two numerator parts by $\pi_1(\pi_1z)$ and $\pi_2(\pi_1z)$, multiply each by $\ChurchNumeral{2}$ using
$\LambdaMul$, and pair these outputs and the unchanged denominator code $\pi_2z$ using $\LambdaNumericPair$.
Composition of these closed programs gives $\LambdaRationalDouble$. Their finite beta reductions prove
$$\LambdaRationalDouble\ChurchNumeral{i}\to_\beta^*\ChurchNumeral{\mathrm{dbl}(i)}.$$
The value equation is
$$q_{\mathrm{dbl}(i)}=\frac{2a-2b}{c+1}=2q_i.$$
No normalization or search for another rational code is needed.

Now put
$$P:=\lambdaab{p}{\lambdaab{n}{\LambdaRationalDouble\,(p(\LambdaSucc\,n))}},\qquad
\psi_e(n):=\mathrm{dbl}(\varphi_e(n+1)).$$
The term $P$ is closed. With input name $p$, two beta contractions expose the query at $n+1$, and the preceding
numerical reduction returns $\mathrm{dbl}(p(n+1))$. The following calculation shows why the shift is necessary.
\end{construction*}

\begin{lemma*}[Shifted doubling preserves Cauchy names]
If $\varphi_e\in\DomainOf{\rho_{\R}}$ and $\rho_{\R}(\varphi_e)=x$, then
$\psi_e\in\DomainOf{\rho_{\R}}$ and $\rho_{\R}(\psi_e)=2x$.
\end{lemma*}

\begin{proof}[Proof]
For $m\ge n$, the pairwise Cauchy-name bound gives
$$
\begin{aligned}
d(q_{\psi_e(n)},q_{\psi_e(m)})
&\le 2d(q_{\varphi_e(n+1)},q_{\varphi_e(m+1)})\\
&\le 2\cdot 2^{-(n+1)}=2^{-n}.
\end{aligned}
$$
Thus $\psi_e$ satisfies the defining pairwise condition for $\DomainOf{\rho_{\R}}$. Moreover,
$q_{\varphi_e(n+1)}\to x$, so $q_{\psi_e(n)}=2q_{\varphi_e(n+1)}\to2x$. Hence $\rho_{\R}(\psi_e)=2x$.
\end{proof}

\begin{theorem*}[\termdefineas{tracked doubling of computable reals}{Tracked doubling}]
The function $d(x)=2x$ gives an assembly morphism $d:A\to A$ and hence a morphism in $\EffCat$.
There is a total lambda-computable index transformer $t$ satisfying
$$\varphi_{t(e)}(n)=\mathrm{dbl}(\varphi_e(n+1))$$
whenever the right-hand side is defined. Its associated functional relation can be presented as
$$D(x,y)=
\begin{cases}
\{e:e\Vdash_A x\ \text{and}\ t(e)\Vdash_A y\}, & y=2x,\\
\emptyset, & y\ne 2x.
\end{cases}$$
\end{theorem*}

\begin{proof}[Proof]
Let $U=\LambdaOutputSearch$. The code construction used for the name-to-index transformation above gives
$$t(e):=\LambdaSyntaxCode{P(U\ChurchNumeral{e})}.$$
This function is computed by a closed numerical program on every $e$, without executing $\varphi_e$.
If $\varphi_e(n+1)=m$, two outer beta contractions, the successor reduction, universal evaluation, and the rational
program give
$$\begin{aligned}
P(U\ChurchNumeral{e})\ChurchNumeral{n}
&\to_\beta^*\LambdaRationalDouble\,
  ((U\ChurchNumeral{e})(\LambdaSucc\ChurchNumeral{n}))\\
&\to_\beta^*\LambdaRationalDouble\ChurchNumeral{m}
 \to_\beta^*\ChurchNumeral{\mathrm{dbl}(m)}.
\end{aligned}$$
Only this one input value is needed; the indexed program may be partial elsewhere.
For a valid Cauchy name, the preceding lemma proves that the transformed name represents $2x$.
Thus $t$ tracks $d$ on computable points.

We verify all four conditions for $D$. Strictness is tracked by
$$e\longmapsto\NatPair{e}{t(e)}.$$
The two components realize the input and output extents. For extensionality, the equality realizers imply that the
input representatives are equal and the output representatives are equal. Retain the middle relation realizer:
$$\NatPair{\NatPair{r}{e}}{s}\longmapsto e.$$
For single-valuedness, if $e\in D(x,y)$ and $e'\in D(x,y')$, then $y=y'=2x$, and $t(e)$ realizes $y\sim_A y'$.
Thus its tracker is
$$\NatPair{e}{e'}\longmapsto t(e).$$
For totality, keep the input realizer $e$. The element $2x$ supplies the semantic witness, and $e\in D(x,2x)$
because $t(e)$ realizes $2x$. These are fixed numerical programs made from projections, pairing, the program for $t$,
and the identity; none takes an underlying real number as an extra input.

Finally, $e\mapsto\NatPair{e}{t(e)}$ also sends $D(x,y)$ into the graph relation
$\Gamma_d(x,y)=E_A(x)\land(d(x)\sim_A y)$. Both are functional relations, so the one-inclusion criterion gives
$D\equiv\Gamma_d$. Thus this presentation represents exactly the morphism obtained from the assembly embedding.
\end{proof}

§{sec:domains-tte-equivalence} proves continuous equivalence between Cauchy-name streams and domain chains.
It does not assert a computable equivalence for arbitrary presentations. If computable translators in both
directions are additionally supplied, the induced index transformations give inverse assembly morphisms on
computable points and hence isomorphic objects in $\EffCat$. Mere Scott continuity or topological admissibility
does not supply those translators.

<!-- formalization: skip-begin (computational evidence versus external topology) -->
For Polish spaces this does not invent a new topology. The ordinary topology still determines continuity and Borel
structure externally. What changes is the evidence supplied for computational use. To use membership in an open set
computationally, one must supply a semidecision procedure on names; choices must be tracked, and functions must
transform names uniformly.

<!-- formalization: skip-end -->

## Basic Constructions on Assemblies {#sec:effective-topos-basic-constructions}

Products organize the input to a binary operation, while function objects organize the input to an operation on
functions. The following constructions make both kinds of evidence explicit before they are used in internal analysis.

### Products and Addition {#sec:effective-topos-products-addition}

\begin{mathmeta}
  \vars{p,q}{Name}
  \vars{e,f}{Nat}
  \vars{s,t}{Fun(Nat,Nat)}
  \vars{r}{Name}
  \vars{z}{Nat}
\end{mathmeta}

To interpret a binary operation internally, we must relate a pair of realized points to a computable name of a
pair. We first make this passage explicit.

\begin{proposition*}[\termdefineas{products of assemblies}{Products of assemblies}]
For assemblies $A,B$, put
$$\UnderlyingSet{A\times B}:=\UnderlyingSet{A}\times\UnderlyingSet{B},\qquad
E_{A\times B}(x,y):=\{\NatPair{e}{f}:e\in E_A(x),\ f\in E_B(y)\}.$$
This is their categorical product. Its image under the assembly embedding is the product of the embedded objects
in $\EffCat$.
\end{proposition*}

\begin{proof}[Proof]
Each pair has a realizer because each coordinate does. The two numerical projections track the coordinate maps.
If $g:C\to A$ and $h:C\to B$ have trackers $a,b$, the program
$$\lambdaab{z}{\LambdaNumericPair\,((U\ChurchNumeral{a})z)\,((U\ChurchNumeral{b})z)}$$
tracks $c\mapsto\Pair{g(c)}{h(c)}$, where $U:=\LambdaOutputSearch$. Both evaluations terminate on every realizer of $c$.
Composing with the projections recovers $g,h$. Every map with these two coordinates has this underlying
function, so uniqueness follows from the definition of assembly morphisms.
For the embedding, a number $z$ realizes equality between $\Pair{x}{y}$ and $\Pair{x'}{y'}$ precisely when
$$x=x',\quad y=y',\quad
\pi_1(z)\in E_A(x),\quad\pi_2(z)\in E_B(y).$$
The product of the two embedded PERs has exactly the same equality realizers. The product construction in
§{sec:effective-topos-finite-limits} therefore identifies these objects, including their projection maps.
\end{proof}

\begin{lemma*}[\termdefineas{pairing name indices}{Pairing name indices}]
There is a total lambda-computable function $s:\NN\to\NN$ such that
$$\varphi_e=p,\quad\varphi_f=q
\quad\Longrightarrow\quad
\varphi_{s(\NatPair{e}{f})}=\NamePair{p}{q}.$$
Here $\NamePair{p}{q}(n)=\NatPair{p(n)}{q(n)}$, as in §{sec:tte-represented-constructions}.
\end{lemma*}

\begin{proof}[Proof]
For $z=\NatPair{e}{f}$, construct the code
$$s(z):=\LambdaSyntaxCode{\lambdaab{n}{\LambdaNumericPair\,((U\ChurchNumeral{e})n)\,((U\ChurchNumeral{f})n)}}.$$
Fix named representatives of $U$ and numerical pairing. Numerical projections extract $e,f$ from $z$;
numeral-code, application-code, and abstraction-code construction then produce the displayed finite syntax.
Every stage terminates on every $z$, independently of whether either index computes a total name.
If the two indices compute $p,q$, applying the constructed term to $\ChurchNumeral{n}$ first substitutes $n$,
then evaluates the two names, and finally pairs their outputs. These finite beta reductions return
$\ChurchNumeral{\NatPair{p(n)}{q(n)}}$ for every $n$.
\end{proof}

\begin{theorem*}[\termdefineas{products of computable-point assemblies}{Products of computable-point assemblies}]
For any representations $\delta_X,\delta_Y$, the coordinate identification gives an isomorphism
$$A_{\delta_X}\times A_{\delta_Y}\cong A_{\delta_{X\times Y}}.$$
\end{theorem*}

\begin{proof}[Proof]
Given computable names of $x,y$, the preceding lemma produces a computable paired name of $\Pair{x}{y}$. The total
function $s$ tracks this map on the product assembly. Conversely, the two TTE coordinate projections induce
assembly maps by the computable-point construction above. Pair these maps using the assembly product. The two
composites are identity functions on the underlying points, hence identity assembly morphisms. This proves the
claimed isomorphism without identifying a pair of name indices with an index of a paired name.
\end{proof}

\begin{theorem*}[\termdefineas{tracked addition of computable reals}{Tracked addition}]
For the computable-real assembly $A=A_{\rho_{\R}}$, addition is an assembly morphism
$$+:A\times A\longrightarrow A$$
and hence a morphism between the corresponding objects in $\EffCat$.
One total lambda-computable transformation sends $\NatPair{e}{f}$ to an index of a Cauchy name of $x+y$ whenever
$e,f$ realize $x,y$.
\end{theorem*}

\begin{proof}[Proof]
Let $p_1,p_2$ be Cauchy names of $x,y$. Using the rational addition program of
§{sec:lambda-rational-arithmetic}, define $a(p_1,p_2)(n)$ to be a code for
$$q_{a(p_1,p_2)(n)}=q_{p_1(n+1)}+q_{p_2(n+1)}.$$
For $m\ge n$, the two input bounds give
$$\begin{aligned}
\Abs{q_{a(p_1,p_2)(n)}-q_{a(p_1,p_2)(m)}}
&\le \Abs{q_{p_1(n+1)}-q_{p_1(m+1)}}
   +\Abs{q_{p_2(n+1)}-q_{p_2(m+1)}}\\
&\le 2^{-(n+1)}+2^{-(n+1)}=2^{-n}.
\end{aligned}$$
Both summands converge to their respective represented reals. Thus $a(p_1,p_2)$ is a valid Cauchy name of $x+y$;
the one-coordinate shift supplies exactly the required precision.
For a paired input name $r=\NamePair{p_1}{p_2}$, the following closed terms implement the construction:
$$\begin{aligned}
S&:=\lambdaab{o}{\LambdaSucc},\\
Q&:=\lambdaab{o}{\lambdaab{n}{o(Son)}},\\
P&:=\lambdaab{o}{\lambdaab{n}{\LambdaRationalAdd(Qon)}}.
\end{aligned}$$
The first term computes the successor independently of the supplied name. The second queries $r(n+1)$, which is
already the numerical pair of the two rational codes. The third adds those coded rationals. Beta contraction,
one name query, and the terminating rational computation prove that $P$ produces $a(p_1,p_2)$ at every
coordinate.
Now let $s$ be the pairing-index function and let $t$ be the name-to-index transformation for $P$. The composite
$z\mapsto t(s(z))$ is total and lambda-computable on every numerical input. On $z=\NatPair{e}{f}$ realizing
$\Pair{x}{y}$, it returns an index for $a(\varphi_e,\varphi_f)$, hence a realizer of $x+y$. This is a tracker on
$A\times A$. The assembly embedding and its product calculation above then give the asserted morphism in
$\EffCat$.
\end{proof}

### Function Objects and Their Realizers {#sec:effective-topos-assembly-functions}

\begin{mathmeta}
  \vars{e}{Nat}
  \vars{a,b}{Nat}
  \vars{t}{Fun(Nat,Nat)}
\end{mathmeta}

A procedure selecting a zero takes a function as input. We therefore specify the evidence that represents a
function before comparing name-based computation with internal analysis. Write $\mathsf{Asm}$ for the category
of assemblies defined above.

\begin{theorem*}[\termdefineas{assembly exponential}{Function objects of assemblies}]
For assemblies $A,B$, define
$$\UnderlyingSet{\funcspace{A}{B}}:=\HomSet{\mathsf{Asm}}{A}{B},$$
$$E_{\funcspace{A}{B}}(f):=
\{e\in\NN:\forall x\in\UnderlyingSet{A}\ \forall a\in E_A(x)\ \exists b\in E_B(f(x))\ (e\cdot a=b)\}.$$
Here $e\cdot a=b$ asserts that the partial application is defined and has value $b$.
Evaluation is an assembly morphism
$$\evalMap:\funcspace{A}{B}\times A\longrightarrow B,\qquad \evalMap\Pair{f}{x}=f(x),$$
and there is a natural bijection
$$\HomSet{\mathsf{Asm}}{C\times A}{B}\cong\HomSet{\mathsf{Asm}}{C}{\funcspace{A}{B}}.$$
Together with the products above and the singleton terminal assembly, these objects make the category of
assemblies cartesian closed. If $B$ is modest, then $\funcspace{A}{B}$ is modest.
\end{theorem*}

\begin{proof}[Proof]
Every assembly morphism has a tracker, so every element of the proposed function object has a realizer.
For evaluation, an input realizer has the form $\NatPair{e}{a}$ with $e\in E_{\funcspace{A}{B}}(f)$ and
$a\in E_A(x)$. The closed term
$$V:=\lambdaab{z}{U(\LambdaNumericProjection{1}z)(\LambdaNumericProjection{2}z)},\qquad
U:=\LambdaOutputSearch,$$
returns a member of $E_B(f(x))$. The two projections terminate, and the tracking condition on $e$ supplies the
terminating universal evaluation. The same program works for all $f,x$.

Let $h:C\times A\to B$ have tracker $d$. For a realizer $a$ of $z\in\UnderlyingSet{C}$, construct
$$c(d,a):=\LambdaSyntaxCode{\lambdaab{b}{U\ChurchNumeral{d}(\LambdaNumericPair\,\ChurchNumeral{a}\,b)}}.$$
The code factory in §{sec:effective-topos-construction} computes this number on every input $a$, without evaluating
$h$. On an argument realizer $b\in E_A(x)$, the resulting program has exactly the outputs of
$d\cdot\NatPair{a}{b}$, so it returns a member of $E_B(h(z,x))$. Hence each section $x\mapsto h(z,x)$ is an
assembly morphism, and the total code factory tracks
$$\widehat h:C\longrightarrow\funcspace{A}{B},\qquad \widehat h(z)(x)=h(z,x).$$
The chosen underlying point $z$ is never an input to this factory; only its numerical realizer $a$ is supplied.

Conversely, evaluate a morphism $k:C\to\funcspace{A}{B}$ after pairing it with the argument projection.
This gives $\Pair{z}{x}\mapsto k(z)(x)$. Evaluation after currying returns $h$, and currying after evaluation returns
$k$, since assembly morphisms are determined by their underlying functions. Replacing the parameter by
$\ell:D\to C$ gives
$$\widehat{h\circ(\ell\times\mathrm{id}_A)}=\widehat h\circ\ell,$$
which proves naturality. The singleton with every natural number as a realizer is terminal: the identity program
tracks the unique underlying map into it. Thus the displayed product and function objects give the claimed
cartesian closed structure.

Finally, suppose $B$ is modest and $e$ realizes both $f$ and $g$. For each $x\in\UnderlyingSet{A}$, choose
$a\in E_A(x)$. Numerical output uniqueness makes the outputs of $e\cdot a$ used for $f$ and $g$ equal.
This common output realizes both $f(x)$ and $g(x)$, so modesty gives $f(x)=g(x)$. Extensionality gives $f=g$.
\end{proof}

Now let $\delta_{\mathcal C}$ be the representation of $\RepresentedFunctionSpace{\mathbf X}{\mathbf Y}$ from
§{sec:tte-represented-constructions}, and put $F:=A_{\delta_{\mathcal C}}$.
An element of $F$ is an external function with a computable function name; a realizer of this element is an
index computing such a name. This differs from a realizer in $\funcspace{A_{\delta_X}}{A_{\delta_Y}}$, which
acts directly on indices of computable input names.

\begin{proposition*}[\termdefineas{restriction of TTE functions to assemblies}{Restriction of TTE functions}]
Restriction to computable points defines an assembly morphism
$$J:F\longrightarrow\funcspace{A_{\delta_X}}{A_{\delta_Y}},\qquad J(f)(x)=f(x).$$
There is one total lambda-computable function $t:\NN\to\NN$ such that
$$e\in E_F(f)\quad\Longrightarrow\quad t(e)\in E_{\funcspace{A_{\delta_X}}{A_{\delta_Y}}}(J(f)).$$
Evaluation commutes with this restriction.
\end{proposition*}

\begin{proof}[Proof]
The computable TTE evaluator and the computable-point product isomorphism give an assembly morphism
$$H:F\times A_{\delta_X}\longrightarrow A_{\delta_Y},\qquad H(f,x)=f(x).$$
In detail, the pairing-index map $s$ from §{sec:effective-topos-products-addition} combines a function-name index
and an argument-name index. Apply the name-to-index compiler for the fixed TTE evaluation program to $s$'s
output. The composite is total on numerical inputs and tracks $H$ on valid realizers. Fix one index $d$ for
this composite. Currying $H$ gives $J$, and
$$t(e):=c(d,e)$$
is the total compiler in the statement. For every $a\in E_{A_{\delta_X}}(x)$, its defining reduction gives
$$t(e)\cdot a\simeq d\cdot\NatPair{e}{a}\in E_{A_{\delta_Y}}(f(x)).$$
The underlying section is exactly the restriction of $f$ to computable points, and the evaluation identity is the
uncurrying identity already proved.
\end{proof}

For real analysis, we may now take $A:=A_{\rho_{\R}}$ and use $\funcspace{A}{A}$ as a specified function assembly.
Its embedding is a specified object of $\EffCat$, with evaluation induced by the assembly embedding and its product
calculation. The proposition supplies a comparison from computably named external functions to this object.
It does not assert an inverse comparison, nor convert an arbitrary tracker into a Type-Two program on names.
The finite-query argument in §{sec:effective-topos-zero-selection} concerns function names; the self-reference
argument in §{sec:effective-topos-index-zero-selection} separately rules out zero selection on function trackers.

## Computable Principles Inside $\EffCat$ {#sec:effective-topos-internal-logic}

\begin{mathmeta}
  \vars{e,n}{Nat}
  \vars{a,b,k,m,r}{Nat}
  \vars{F}{Fun(Name,Nat)}
  \vars{\alpha,\beta}{Name}
\end{mathmeta}

<!-- formalization: skip-begin (internal-logic reading of the tripos clauses) -->

The internal logic of $\EffCat$ is \termdefine{intuitionistic higher-order logic} with explicit computational force. The
realizability clauses in §{sec:effective-topos-construction} give the reading:
<!-- formalization: skip-end -->

*   a proof of $\varphi\land\psi$ is a pair of realizers;
*   a proof of $\varphi\lor\psi$ is a tag and a realizer for the chosen side;
*   a proof of $\varphi\to\psi$ is an index transforming realizers of $\varphi$ into realizers of $\psi$;
*   a realizer of $\exists x\,\varphi(x)$ lies in the union of the realizer sets over possible witnesses,
    with existence evidence included when quantifying over a PER object. It need not encode an arbitrary
    base-set witness as a natural number.

<!-- formalization: skip-begin (introduction to imported internal computability principles) -->
This logic validates the following computability principles in their internal forms.

<!-- formalization: skip-end -->

<!-- formalization: skip-begin (Church's Thesis, Markov's Principle, and continuity are imported standard K1
realizability results, cited in the chapter scope) -->

\begin{statement*}[\termdefineas{Church's Thesis in effective topos}{Church's Thesis in $\EffCat$}]
For a fixed universal partial-recursive evaluator $U(e,n)$ on natural numbers,
$$
\EffCat \models
\forall f\in\funcspace{\NN}{\NN}\;\exists e\in\NN\;\forall n\in\NN\;
U(e,n)\downarrow = f(n).
$$
\end{statement*}

The convergence assertion is part of the displayed equality: internally, every total function $\NN\to\NN$ is represented
by some recursive index. Accordingly, the Baire object $\BaireSpace$ in the internal continuity
principle below is the internal function object, whose global elements are total recursive sequences.
It is not the full external Baire space.

\begin{statement*}[\termdefineas{Markov's Principle in effective topos}{Markov's Principle in $\EffCat$}]
For every internal predicate $P$ on $\NN$,
$$
\EffCat \models
\bigl(\forall n\in\NN\, (P(n)\vee\neg P(n))\bigr)
\to
\bigl(\neg\neg\exists n\in\NN\,P(n)\to \exists n\in\NN\,P(n)\bigr).
$$
\end{statement*}

The realizer is the usual unbounded search procedure. Decidability supplies a decision for each test, and the double
negation rules out the possibility that the search runs forever without finding a witness.

\begin{statement*}[\termdefineas{Continuity Principle in effective topos}{Continuity Principle in $\EffCat$}]
For every internal function $F:\BaireSpace\to\NN$,
$$
\EffCat \models
\forall \alpha\in\BaireSpace\;\exists k\in\NN\;\forall \beta\in\BaireSpace\;
\bigl(\restrict{\alpha}{k}=\restrict{\beta}{k}\to F(\alpha)=F(\beta)\bigr).
$$
\end{statement*}

This is an internal continuity statement about morphisms in $\EffCat$. Externally, such a morphism is tracked by a
recursive operation on indices of total recursive sequences. The Kreisel--Lacombe--Shoenfield/Ceitin
effective-operations theorem says that every extensional operation of this kind is continuous and supplies the finite
prefix information needed at a given input. This substantive $K_1$ theorem is part of the realizability semantics
imported in the chapter scope; it is not the elementary finite-use argument for Type-Two stream realizers.

<!-- formalization: skip-end -->

\begin{lemma*}[\termdefineas{undecidability of diagonal halting}{Undecidability of diagonal halting}]
Put $K:=\{e\in\NN:\varphi_e(e)\text{ is defined}\}$, where defined means that evaluation returns a Church numeral.
There is no closed lambda program computing the total function that returns $0$ on $K$ and $1$ outside $K$.
\end{lemma*}

\begin{proof}[Proof]
Suppose that a closed program $D$ computes this function. Use the first numerical projection to form
$$T:=\lambdaab{z}{D(\LambdaNumericProjection{1}\,z)}.$$
On input $\NatPair{e}{k}$, this total test returns $0$ if $e\in K$ and $1$ otherwise, independently of $k$.
Apply the parameterized numerical search of §{sec:lambda-rational-ball-programs} to $T$.
The resulting closed term $S_T$ searches for the least $k$ with a nonzero test answer, and consequently
$$S_T\ChurchNumeral{e}\text{ has a numeral output}\quad\Longleftrightarrow\quad e\notin K.$$
Choose an index $d$ of $S_T$ in the fixed enumeration of closed programs. On input $d$, the definition of $K$ gives
$$d\in K\quad\Longleftrightarrow\quad
  S_T\ChurchNumeral{d}\text{ has a numeral output}\quad\Longleftrightarrow\quad d\notin K,$$
a contradiction. Both the search and the evaluation use ordinary beta reduction.
\end{proof}

We now retain the input extent explicitly. Let $N$ be the natural-number assembly with $E_N(e)=\{e\}$, and put
$$H(e):=\{\NatPair{e}{m}:\varphi_e(e)=m\}.$$
Then $H(e)$ is nonempty exactly when $e\in K$. The first projection uniformly gives $H(e)\le E_N(e)$.
An equality realizer in $N$ forces equality of the represented natural numbers, so the second projection gives
$$(e\sim_N e')\land H(e)\le H(e').$$
Thus $H$ is a strict extensional predicate and defines a subobject of $N$ by
§{sec:effective-topos-subobjects-truth-values}. This predicate keeps the index available as part of its realizer.

\begin{proposition*}[\termdefineas{halting predicate has no complement}{The halting predicate has no complement}]
There is no family $Q(e)\IncludedIn\NN$ for which both reductions
$$E_N\le H\lor Q,\qquad H\land Q\le\bot$$
hold uniformly in $e$.
\end{proposition*}

\begin{proof}[Proof]
Let $r$ track the first reduction and $s$ the second. Since $e\in E_N(e)$, the computation $r\cdot e$ always returns
an element of $H(e)\lor Q(e)$. Write $U:=\LambdaOutputSearch$ and form the closed program
$$D:=\lambdaab{z}{\LambdaNumericProjection{1}\bigl((U\ChurchNumeral{r})z\bigr)}.$$
If $r\cdot e=\NatPair{0}{a}$ with $a\in H(e)$, then $e\in K$, and $D$ returns $0$.
If $r\cdot e=\NatPair{1}{b}$ with $b\in Q(e)$, then $e\notin K$: otherwise there would be an $a\in H(e)$,
and $s\cdot\NatPair{a}{b}$ would have to belong to the empty truth value $\bot$.
In this second case $D$ returns $1$. Universal evaluation followed by numerical projection therefore makes $D$
a total decider of the function excluded by the preceding lemma. This contradiction proves the proposition.
\end{proof}

\begin{corollary*}[Failure of excluded middle]
There is no uniform realizer for $\forall e\in N\,(H(e)\lor\neg H(e))$. In particular, $\EffCat$ is not Boolean.
\end{corollary*}

\begin{proof}[Proof]
Take $Q:=H\to\bot$. Applying an implication realizer to a realizer of $H$ always tracks $H\land Q\le\bot$.
A uniform realizer of the displayed formula would also track $E_N\le H\lor Q$, contrary to the proposition.
More generally, the strict-predicate description of subobjects would make a complement of the subobject defined by
$H$ satisfy exactly the two reductions in that proposition. This subobject has no complement,
so the topos is not Boolean.
The obstruction is uniformity; it does not deny the external classical alternative $e\in K$ or $e\notin K$ for each $e$.
\end{proof}

<!-- formalization: skip-begin (Diaconescu's external theorem) -->

The full axiom of choice fails because, in an elementary topos, it implies excluded middle by
Diaconescu's theorem.

<!-- formalization: skip-end -->

\begin{mathmeta}
  \forward{LambdaOutputCandidate,LambdaAdd,LambdaDyadic}
\end{mathmeta}

We can also make the obstruction to real comparison explicit. Use the rational enumeration $q_i$ and the
computable-point assembly $A=A_{\rho_{\R}}$ from the doubling construction. Put $c_e(k)=1$ if the finite certificate
candidate $k$ for $\varphi_e(e)$ is accepted, and put $c_e(k)=0$ otherwise. This is the total test computed by
$\LambdaOutputCandidate$. There is an accepted candidate exactly when $e\in K$.
Let $d_k:=\RationalCode{1}{0}{2^{k+2}-1}$, so $q_0=0$ and $q_{d_k}=2^{-(k+2)}$. Define a numerical name by
$$\begin{aligned}
p_e(0)&:=0,\\
p_e(n+1)&:=\begin{cases}
p_e(n),&p_e(n)\ne0,\\
d_n,&p_e(n)=0\text{ and }c_e(n)=1,\\
0,&\text{otherwise}.
\end{cases}
\end{aligned}$$

This recurrence is computed by a closed lambda program $P$ on input $\NatPair{e}{n}$. For its step, the numerical
projections read $e,n,r$ from $\NatPair{e}{\NatPair{n}{r}}$. A zero test preserves $r$ when it is nonzero. Otherwise,
another zero test on $\LambdaOutputCandidate\ChurchNumeral{e}\ChurchNumeral{e}\ChurchNumeral{n}$ selects zero or
$\LambdaDyadic(\LambdaAdd\ChurchNumeral{n}\ChurchNumeral{2})$.
The parameterized recursor of §{sec:lambda-primitive-recursion}, with zero initial value, implements the recurrence.
Every step terminates, including when the original indexed program diverges. Thus
$$P\ChurchNumeral{\NatPair{e}{n}}\to_\beta^*\ChurchNumeral{p_e(n)}.$$

\begin{lemma*}[\termdefineas{halting-coded computable reals}{Computable reals encoding halting}]
Every $p_e$ is a Cauchy name. Writing $x_e:=\rho_{\R}(p_e)$, we have
$$x_e\ne0\quad\Longleftrightarrow\quad e\in K.$$
Moreover, one total closed lambda program computes an index $t(e)$ of $p_e$ from $e$.
\end{lemma*}

\begin{proof}[Proof]
If there is no accepted candidate, induction gives $p_e(n)=0$ for every $n$, so the name represents zero.
Otherwise let $k$ be the least accepted candidate. Induction on the recurrence gives
$$p_e(n)=\begin{cases}0,&n\le k,\\d_k,&n>k.\end{cases}$$
Thus the rational sequence $q_{p_e(n)}$ is eventually constant at the positive value $2^{-(k+2)}$.
For $n\le m$, the only case in which its values differ is $n\le k<m$, and in that case
$$\Abs{q_{p_e(n)}-q_{p_e(m)}}=2^{-(k+2)}\le2^{-n}.$$
This proves both the required pairwise Cauchy bound and the asserted value of the limit.

For the uniform index construction, put
$$C:=\lambdaab{z}{\lambdaab{n}{P(\LambdaNumericPair\,z\,n)}},\qquad
  t(e):=\LambdaSyntaxCode{C\ChurchNumeral{e}},$$
using a fixed named representative of $C$. Numeral-code and application-code construction compute this finite syntax
from $e$, without running the indexed program. The resulting closed term computes $p_e$ by beta contraction,
numerical pairing, and the preceding recursion calculation. Therefore $t(e)\Vdash_A x_e$ for every $e$.
\end{proof}

\begin{theorem*}[\termdefineas{undecidability of computable-real equality}{Undecidability of computable-real equality}]
No closed lambda program, given an arbitrary index for a total Cauchy name of a computable real $x$, always terminates
and returns $0$ when $x=0$ and $1$ when $x\ne0$. No behavior is required on invalid name indices.
\end{theorem*}

\begin{proof}[Proof]
Suppose such a program existed. Given $e$, first compute $t(e)$ and apply the proposed test to this valid name index.
It returns $1$ exactly when $e\in K$, and $0$ otherwise. A final zero test exchanges the two answers, giving the
halting decider excluded above. In particular, equality of two computable reals cannot be decided from arbitrary name
indices: fixing the second input to a constant name of zero would give the forbidden test.
\end{proof}

\begin{corollary*}[Failure of real trichotomy]
There is no uniform realizer deciding $x<0$, $x=0$, or $0<x$ on the chosen computable-real object $A$.
Consequently, there is no uniform realizer of trichotomy for two arbitrary such reals.
\end{corollary*}

\begin{proof}[Proof]
Read the disjunction as $x<0\lor(x=0\lor0<x)$. A realizer of the outer left branch has the form $\NatPair{0}{a}$;
the other two branches have the forms $\NatPair{1}{\NatPair{0}{a}}$ and $\NatPair{1}{\NatPair{1}{a}}$.
Numerical projections and zero tests convert these to answer tags $0,1,2$, respectively. Soundness of the three
comparison predicates ensures that the middle tag occurs exactly when $x=0$; the other two tags imply $x\ne0$.
Testing whether the tag is the middle one gives the forbidden zero test. This only uses the supplied name index and
soundness of the comparison realizers, and does not assume a Type-Two operator on arbitrary nonrecursive names.
\end{proof}

## Zero Selection: Names and Indices {#sec:effective-topos-zero-selection-problems}

A function name supplies information through queries, whereas a function tracker is a natural number on which a
program can perform numerical computations. We keep the two selection problems separate: the first proof uses finite
query dependence, and the second uses finite certificate search and self-reference. Both distinguish the existence of
a zero from a uniform procedure that selects one from the specified input evidence.

### Selection from Function Names {#sec:effective-topos-zero-selection}

\begin{mathmeta}
  \vars{x}{Real}
  \vars{p,r}{Name}
  \vars{i,j}{Nat}
  \vars{f}{Fun(Real,Real)}
  \vars{w}{Name}
\end{mathmeta}

The intermediate value theorem guarantees existence, but does not supply one procedure for selecting an exact zero
from every named function. We prove this distinction with one explicit family. The input functions below are defined
on $\R$, so their names provide even more information than their restrictions to $\ClosedInterval{0}{1}$.

\begin{lemma*}[A computable family with a flat zero interval]
Put
$$f_a(x):=\max\{x-3/4,0\}-\max\{1/4-x,0\}+a.$$
The map $\Pair{a}{x}\mapsto f_a(x)$ is computable for the rational-code Cauchy representation.
Every $f_a$ is continuous, with the common modulus $\mu(n)=n+1$. If $\Abs{a}<1/4$, then
$$f_a(0)<0<f_a(1).$$
If $a>0$, every zero lies below $1/4$; if $a<0$, every zero lies above $3/4$.
\end{lemma*}

\begin{proof}[Proof]
Continuity follows from continuity of maximum, subtraction, and addition. The endpoints have values
$-1/4+a$ and $1/4+a$. If $a>0$ and $x\ge1/4$, the second maximum vanishes and $f_a(x)\ge a>0$.
If $a<0$ and $x\le3/4$, the first maximum vanishes and $f_a(x)\le a<0$. Also, since each maximum changes
by at most $\Abs{x-y}$,
$$\Abs{f_a(x)-f_b(y)}\le2\Abs{x-y}+\Abs{a-b}.$$
Setting $a=b$ gives the stated modulus. In particular,
$\Abs{x-y}\le2^{-(n+1)}$ implies $\Abs{f_a(x)-f_a(y)}\le2^{-n}$.

Here is a lambda realizer, including its precision bound. Let $Q$ be the closed numerical program obtained by
composing the rational subtraction, maximum, and negation routines in the expression defining $f_a(x)$.
It receives $\NatPair{i}{j}$ and returns a rational code for $f_{q_i}(q_j)$. The constants $1/4$ and $3/4$ have
codes $\RationalCode{1}{0}{3}$ and $\RationalCode{3}{0}{3}$. For the final addition, subtract the negated parameter.
The maximum routine compares the two rational codes and returns one of them, as in
§{sec:tte-polish-as-represented}. All these numerical computations terminate by
§{sec:lambda-rational-arithmetic}. On the paired name $w=\NamePair{p}{r}$, use
$$E:=\lambdaab{o}{\lambdaab{n}{Q\bigl(o(\LambdaSucc(\LambdaSucc n))\bigr)}}.$$
Thus its $n$-th output is a code for $f_{q_{p(n+2)}}(q_{r(n+2)})$. For $m\ge n$, the preceding estimate gives
$$\Abs{f_{q_{p(n+2)}}(q_{r(n+2)})-f_{q_{p(m+2)}}(q_{r(m+2)})}
\le3\cdot2^{-(n+2)}\le2^{-n}.$$
The output is therefore a valid Cauchy name, and its limit is $f_a(x)$ when $p,r$ name $a,x$.
Two beta contractions, the successor computations, one query, and the rational computation give each output of $E$.
\end{proof}

\begin{theorem*}[\termdefineas{nonexistence of uniform zero selection}{No uniform zero selection}]
There is no closed Type-Two lambda program which, from every computable function name of a continuous
$f:\R\to\R$ with $f(0)<0<f(1)$, produces a Cauchy name of some $x\in\ClosedInterval{0}{1}$ with $f(x)=0$.
This remains impossible if all input functions have the common modulus $\mu(n)=n+1$ and this modulus is
supplied as a second input name. Different names of the same function may lead to different selected zeros.
\end{theorem*}

\begin{proof}[Proof]
First suppose that a fixed program $S$, given any computable Cauchy name $p$ of $a$ with $\Abs{a}<1/4$,
outputs a Cauchy name of a zero of $f_a$. Run it on the constant-zero name $p_0(n)=0$ until output coordinate $3$
returns a code $c$. By finite use, there is $N$ such that every input agreeing with $p_0$ below $N$ admits the
same finite reduction to $\ChurchNumeral{c}$ at that coordinate.

Put $\varepsilon:=2^{-(N+4)}$, and choose rational codes $j_+,j_-$ for $\varepsilon,-\varepsilon$.
Define
$$p_\pm(n):=\begin{cases}0,&n<N,\\j_\pm,&n\ge N.\end{cases}$$
These are computable names: compare $n$ with the fixed numeral $N$ and return one of two fixed codes.
They are valid Cauchy names because $\varepsilon\le2^{-N}$, and they represent $\pm\varepsilon$.
Moreover, $0<\varepsilon\le1/16<1/4$. By finite use and confluence, both output names have code $c$ at coordinate $3$.
If their represented zeros are $x_+,x_-$, the Cauchy error bound yields
$$\Abs{x_+-q_c}\le1/8,\qquad \Abs{x_--q_c}\le1/8,\qquad \Abs{x_+-x_-}\le1/4.$$
But the lemma gives $x_+<1/4$ and $x_->3/4$, contradicting this last bound.

Finally, let $e$ be the syntax index of the evaluation program $E$ in the lemma. The computable exponential law
sends a name $p$ of $a$ to the function name $e\concat p$ of $f_a$. This name is computable whenever $p$ is.
Let $M:=\lambdaab{o}{\LambdaSucc}$, which produces the fixed modulus name, and put
$$T:=\LambdaPairOutputs{\LambdaNamePrefix{e}}{M}.$$
If a closed program $P$ selected a zero from the paired function and modulus names, then $C_{P,T}$ would be the
forbidden parameter-name program $S$. The prefixing, pairing, and input-substitution reductions establish this
composition on every valid input. All names used in the contradiction are computable.
\end{proof}

### Selection from Function Indices {#sec:effective-topos-index-zero-selection}

\begin{mathmeta}
  \vars{x}{Real}
  \vars{e,m,n,s,v}{Nat}
  \vars{g}{Fun(Real,Real)}
  \vars{k}{Nat}
\end{mathmeta}

We now treat numerical realizers of the function assembly from §{sec:effective-topos-assembly-functions}.
An index can be inspected as a natural number, so the preceding finite-query argument does not apply directly.
Instead, finite certificate search and the self-reference construction in §{sec:lambda-index-recursion}
produce an input whose zeros contradict the proposed selector's own output.

\begin{theorem*}[\termdefineas{nonexistence of indexed zero selection}{No zero selection on function indices}]
Put $A:=A_{\rho_{\R}}$. There is no closed lambda program which, from every tracker of a morphism
$f\in\UnderlyingSet{\funcspace{A}{A}}$ admitting a continuous extension $g:\R\to\R$ with
$g(0)<0<g(1)$ and modulus $\mu(n)=n+1$, returns a realizer of some $x\in\UnderlyingSet{A}$ such that
$x\in\ClosedInterval{0}{1}$ and $f(x)=0$. The extension and its properties are promises on the input;
they are not extra input data. Different trackers of the same function may lead to different selected zeros,
and no behavior is required on inputs violating the promises.
\end{theorem*}

\begin{proof}[Proof]
First suppose that a closed program $D$ takes any index $e$ of a Cauchy name $p$ of $a$ with $\Abs{a}<1/4$
and returns an index $d$ of a Cauchy name of a zero of the preceding function $f_a$.
Let $U:=\LambdaOutputSearch$, and fix an index $r$ of the closed program
$$R:=\lambdaab{z}{U(Dz)\ChurchNumeral{3}}.$$
Thus, whenever the selector returns a valid name index, $R$ computes coordinate $3$ of that name.

For each candidate $k=\NatPair{m}{s}$, let $b_r(e,k)$ be the finite certificate test for the computation
$\varphi_r(e)=m$, using certificate $s$. It is computed by $\LambdaOutputCandidate$ and always terminates.
Put $\varepsilon_k:=2^{-(k+4)}$ and choose the following explicit rational code:
$$j_k:=\begin{cases}
\RationalCode{0}{1}{2^{k+4}-1},&q_m<1/2,\\
\RationalCode{1}{0}{2^{k+4}-1},&q_m\ge1/2.
\end{cases}$$
Thus $q_{j_k}=-\varepsilon_k$ in the first case and $q_{j_k}=\varepsilon_k$ in the second.
The dyadic-code, rational comparison, and negation programs compute $j_k$ from $k$.

Define, for every numerical parameter $e$,
$$\begin{aligned}
p_e(0)&:=0,\\
p_e(n+1)&:=\begin{cases}
p_e(n),&p_e(n)\ne0,\\
j_n,&p_e(n)=0\text{ and }b_r(e,n)=1,\\
0,&\text{otherwise}.
\end{cases}
\end{aligned}$$
The parameterized recursor implements this recurrence by a closed program $P$ on input $\NatPair{e}{n}$.
Its step extracts $e,n,v$ from $\NatPair{e}{\NatPair{n}{v}}$. If $v\ne0$, it returns $v$; otherwise it runs
$\LambdaOutputCandidate\ChurchNumeral{r}\ChurchNumeral{e}\ChurchNumeral{n}$ and returns $0$ or $j_n$.
Every stage is a terminating numerical computation, whether or not $R\ChurchNumeral{e}$ terminates.

If no candidate is accepted, $p_e$ is the constant-zero name. Otherwise let $k$ be the first accepted candidate.
The code $j_k$ is nonzero, and induction gives
$$p_e(n)=\begin{cases}0,&n\le k,\\j_k,&n>k.\end{cases}$$
For $n\le k<m$, the only case in which two approximants differ, their distance is
$\varepsilon_k\le2^{-n}$. Thus every $p_e$ is a Cauchy name. Its value $a_e$ is either zero or $q_{j_k}$,
and always satisfies $\Abs{a_e}\le1/16<1/4$. This validity argument does not assume that the selector terminates.

Now apply self-reference to the closed binary program
$$H:=\lambdaab{z}{\lambdaab{n}{P(\LambdaNumericPair\,z\,n)}}.$$
It supplies an index $e$ with
$$\varphi_e(n)=p_e(n)\qquad\text{for every }n.$$
Indeed, the self-reference reductions give
$P_e\ChurchNumeral{n}\to_\beta^*H\ChurchNumeral{e}\ChurchNumeral{n}$,
and pairing followed by the computation of $P$ returns $\ChurchNumeral{p_e(n)}$.
Hence $e$ is an index of the valid name just constructed. The hypothesis on $D$ now forces
$D\ChurchNumeral{e}$ to return an index $d$ of a name $u$ of a zero $x$ of $f_{a_e}$.
Consequently $R\ChurchNumeral{e}$ returns $\ChurchNumeral{c}$ with $c=u(3)$.
Some certificate is accepted, and numerical output uniqueness implies that the output component of the
first accepted candidate $k$ is exactly $c$.

The Cauchy error bound gives $\Abs{x-q_c}\le1/8$. If $q_c<1/2$, our construction makes
$a_e=-\varepsilon_k<0$, so the plateau lemma gives $x>3/4$, whereas
$x\le q_c+1/8<5/8$. If $q_c\ge1/2$, it makes $a_e=\varepsilon_k>0$, so the lemma gives
$x<1/4$, whereas $x\ge q_c-1/8\ge3/8$. Both cases are impossible.

Finally, the computable map $\Pair{a}{x}\mapsto f_a(x)$ and the product construction induce an assembly morphism
$h:A\times A\to A$. By the explicit currying construction, one total numerical program $C$ sends every
name index $e$ of $a$ to a tracker $t(e)$ of the section $x\mapsto f_a(x)$.
For $\Abs{a}<1/4$, this section has the continuous extension and the common modulus required in the theorem.
If $S$ selected zeros from all such function trackers, then
$$D:=\lambdaab{z}{S(Cz)}$$
would satisfy the parameter-index selection hypothesis already contradicted. The beta reductions for composition
and the total code factory justify this passage on every valid name index.
\end{proof}

This excludes a tracked zero-selection morphism on the subassembly defined by these promises.
The index proof is stronger than that conclusion: it did not require the selected zero to depend only on the
underlying function. It also does not deny the existence of zeros for individual inputs, or identify this promise
subassembly with an unspecified internal space of all continuous functions.

<!-- formalization: skip-begin (two-register examples and constructive-analysis guidance) -->

A TTE construction can often be transported to a computable-point assembly by transforming indices of
recursive names. The converse requires care: an operation on indices need not give a Type-Two operator on
arbitrary names. An internal proof in $\EffCat$ must therefore be read with the chosen objects and their
realizers specified.

The addition construction in §{sec:effective-topos-products-addition} exhibits this passage explicitly: its name
transformer, index transformer, and assembly morphism describe the same operation at three levels. The internal
object used there is the specified computable-real assembly $A$.

For the function assembly specified in §{sec:effective-topos-assembly-functions},
§{sec:effective-topos-index-zero-selection} provides the separate index argument needed to exclude a zero-selection
tracker. The objects, promises on the inputs, and output realizers are all explicit in that statement.

<!-- formalization: skip-end -->



<!-- formalization: skip-begin (external research on oracles and realizability subtoposes) -->
The internal universe can also be varied by changing its local logic. A
\termdefine{Lawvere--Tierney topology} is an internal closure operator on the subobject classifier that
preserves finite meets; it determines a subtopos of sheaves. Kihara [@Kihara2023], building on Lee and
van Oosten, describes the lattice of these topologies on $\EffCat$ through computable reduction games
with imperfect information. The reduction notion extends both Turing reducibility and generalized
Weihrauch reducibility. In this description, local operators express ways of supplying additional
computational power to realizability. One consequence is that there is no minimal
\termuse{Lawvere--Tierney topology} strictly above the identity topology.

Kihara's related work [@Kihara2025Realizability] uses Weihrauch degrees to build Lifschitz-like relative
realizability interpretations of intuitionistic Zermelo--Fraenkel set theory. It separates principles such
as the intermediate value theorem and weak König's lemma without assuming countable choice. This supplies
a concrete route from comparisons of multivalued problems in §{sec:weihrauch-reducibility} to distinctions
between internal mathematical principles. These model constructions and separation results are external
to the fixed-assembly arguments proved in this chapter.
<!-- formalization: skip-end -->

<!-- formalization: skip (structural transition to the appendices) -->
\part{Outlook and Appendices}\label{part-outlook-appendices}
