# Tripos-to-Topos: Forcing and Realizability {#sec:effective-topos}
\index{forcing!categorical semantics}
\index{realizability!categorical semantics}
\index{effective topos}

<!-- formalization: skip-begin (chapter motivation, comparison with earlier effective frameworks, and proof scope) -->

Forcing and \termdefine{realizability} look different at first. Forcing starts with conditions and generic filters;
realizability starts with programs and indices. Their common shape is that truth is no longer a bare two-valued
assertion. A formula is interpreted by evidence: a condition may force it, or an index may realize it, and the logical
operations describe how evidence is transformed.

§{sec:forcing} used forcing to add generic points to Polish spaces and kept the set-theoretic machinery in Appendix
§{sec:appendix-forcing-background}. This chapter looks at the same method before passing to a generic extension. A
forcing notion assigns structured truth values to formulas, while a realizability model assigns sets of realizers to
formulas. A \termforward{tripos} packages such predicates, their substitution behavior, implication, and quantifiers.
The \termforward{tripos-to-topos construction} then turns this predicate semantics into a category that behaves like a
universe of sets.

Hyland's \termforward{effective topos} $\EffCat$ is the \termuse{realizability} instance of this passage.
Its realizers are natural-number program indices. This differs from TTE, where points may have arbitrary
infinite names. A computable name transformer induces a recursive transformer of indices for computable names,
so computable-point assemblies provide one precise connection. The construction does not identify all
represented spaces, with all their external points, with objects of the effective topos.

The \termdefine{categorical envelope} provided by $\EffCat$ is specific to natural-number realizability.
The lightface pointclasses of §{sec:effective-dst} are not identical to its internal predicates, and
\termuseas{Type-Two lambda realizer}{TTE realizers} from §{sec:computable-polish-tte} are not, without a
specified translation, the same as its morphisms. §{sec:inside-effective-topos} constructs the
computable-point translation
and separates it from the external theory of arbitrary names.

\begin{mathmeta}
  \define{SetCat,SetCatU}
  \forward{opcat,LambdaOutputSearch,LambdaSyntaxCode}
\end{mathmeta}

The construction below uses the universe convention of §{sec:inaccessible-universes}: $\SetCatU$ denotes the category of
$U$-small sets and functions, and in this chapter $\SetCat$ means $\SetCatU$. Appendix
§{sec:appendix-category-realizability} gives the general categorical definitions and tripos-to-topos construction.
The present chapter specializes that construction to $\EffCat$ and proves the structural facts needed later.
Standard references for the full realizability development are [@Hyland1982] and [@vanOosten2008].

Proof scope: this chapter proves the local realizability-predicate and PER calculations that
connect forcing, TTE, and $\EffCat$, while the general Hyland--Johnstone--Pitts tripos-to-topos theorem remains the
named external theorem. Appendix §{sec:appendix-category-realizability} supplies the categorical conventions needed to
read that boundary precisely.

<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

For the realizability construction, use numerical program indices from §{sec:lambda-indices} and the PCA and
assembly definitions in §{sec:realizability-pca} and §{sec:realizability-assemblies}. Read the categorical
vocabulary in §{sec:cat-basics}, finite limits and exponentials in §{sec:cat-ccc}, and internal logic in
§{sec:cat-internal-logic}. The tripos-to-topos theorem in §{sec:realizability-tripos} is an imported
structural result whose statement can be used first. The localic comparison additionally uses forcing names
and truth from §{sec:forcing-names-valuation} and §{sec:forcing-relation}; random-forcing calculations can be
skipped. The goal is to track the evidence for predicates and morphisms while distinguishing numerical indices
from arbitrary TTE names.

<!-- formalization: skip-end -->

## Predicate Semantics and Forcing {#sec:forcing-realizability-predicate-semantics}
\index{tripos-to-topos construction}
\index{forcing!tripos}
\index{realizability!tripos}

<!-- formalization: skip-begin (tripos roadmap and comparison table; the concrete
realizability tripos is constructed below) -->

A \termforward{tripos} separates the base sets and parameters from their predicates, substitution, and
quantifiers. The \termforward{tripos-to-topos construction} turns this \termdefine{predicate semantics} into a
category of partial equivalence relations and functional relations. Appendix §{sec:realizability-tripos} gives the
general definition and the construction over an arbitrary PCA; the present chapter follows the forcing and
numerical-realizability instances.

The forcing comparison comes first. We then construct the Kleene realizability predicates in
§{sec:effective-topos-construction} and their concrete PER category in
§{sec:effective-topos-objects-morphisms}. The finite-limit, classifier, and exponential proofs culminate in
§{sec:effective-topos-topos-theorem}. Thus the general categorical vocabulary stays in the appendix, while the
programs and uniformity arguments establishing the structure of $\EffCat$ stay here.

\begin{mathmeta}
  \forward{HeytAlgCat}
\end{mathmeta}

This single construction covers two different notions of evidence:

| Forcing semantics | Realizability semantics |
|-------------------|-------------------------|
| condition $p$ forces $\varphi$ | index $e$ realizes $\varphi$ |
| stronger conditions refine information | recursive operations transform evidence |
| dense sets express unavoidable requirements | inhabited realizer sets express witnessed assertions |
| Boolean-valued or sheaf-style predicates | realizability predicates |
| generic extension makes forced statements true | the effective topos makes realized statements internally true |

The analogy is structural, not literal. A forcing condition is not a program, and a generic filter is not an index. The
shared pattern is that predicates vary over parameters, reindex along functions, and carry the logical operations needed
to interpret first-order reasoning. Forcing toposes and realizability toposes therefore belong to the same categorical
family, even though their intended readings and technical details differ.

<!-- formalization: skip-end -->

### Localic Tripos and Forcing Extensions {#sec:localic-tripos-forcing-extensions}

\begin{mathmeta}
  \vars{p,q,r}{Seq}
\end{mathmeta}
\index{forcing!localic tripos}

The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
Define a predicate on a set $I$ to be a function
$$\varphi:I\to\Omega,$$
ordered pointwise. For $f:I\to J$, reindexing is pullback:
$$f^\ast(\psi)(i)=\psi(f(i)).$$
The logical operations are pointwise:
$$
(\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
\qquad
(\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
$$
and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
$$
(\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
\qquad
(\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
$$
The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
$\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.

<!-- formalization: skip-begin (localic topos identification and forcing background cited externally) -->
The standard
tripos-to-topos identification gives the localic topos associated with $\Omega$ [@vanOosten2008, Ch. 2].
<!-- formalization: skip-end -->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
未リンクの冒頭はlocalic triposをBoolean-valued modelとして読む命名・圏論上の位置付け。
直後のBoolean値の実際の構成、
forcing不等式および論理演算の再帰はForcingBooleanValuesとForcingBooleanRecursionに接続している。
一般の圏論的同定をこれらの定理が証明したとは扱わない。)
--> When $\Omega$ is a complete Boolean algebra $\mathbb B$, this is the categorical form of a
\termdefine{Boolean-valued model}. A formula $\varphi$ has a Boolean truth value
$$[\![\varphi]\!]\in\mathbb B.$$<!--
formalization: skip-end
-->
For set-theoretic formulas, use the recursively defined relation $p\forces^*\varphi$ from
§{sec:forcing-relation}. A condition $p\in\mathbb B^+$ satisfies this relation exactly when
$$p\le[\![\varphi]\!].$$
The recursive clauses for $[\![\varphi]\!]$ are the Boolean-algebra versions of the tripos operations: conjunction is
meet, disjunction is join, implication is Boolean implication, $\exists$ is a join over witnesses, and $\forall$ is a
meet over witnesses.

\begin{proof}[Construction of the Boolean values]
For the set-theoretic application, fix a transitive ground model $M$ of ZFC and a Boolean algebra
$\mathbb B\in M$ that is complete as computed in $M$. Completeness is required only for subsets
belonging to $M$. Given a formula $\varphi$ and its name parameters in $M$, forcing definability and
Separation give
$$S_\varphi:=\{p\in\mathbb B^+:p\forces^*\varphi\}\in M.$$
Define its Boolean value $b_\varphi$ to be the supremum of $S_\varphi$ computed in $M$.
The set $S_\varphi$ is downward closed and saturated under forcing density by §{sec:forcing-relation}.
Thus $p\in S_\varphi$ implies $p\le b_\varphi$.
Conversely, suppose $p\le b_\varphi$ but $p\notin S_\varphi$. Saturation gives a nonzero $q\le p$
such that no nonzero extension of $q$ belongs to $S_\varphi$. For every $s\in S_\varphi$, downward
closure then gives $q\land s=0$, so $s\le\neg q$. The supremum property gives
$b_\varphi\le\neg q$, contradicting $0<q\le p\le b_\varphi$. This proves the forcing inequality.

The condition-forcing recursion now gives the Boolean recursive clauses, since positive principal
ideals determine their Boolean elements. In particular, a Boolean element is below the value of
$\forall x\,\psi(x)$ exactly when it is below every value of $\psi(\tau)$ for a name $\tau$ in $M$;
the existential clause follows by complements.
The witness values also form an actual set in $M$. Indeed, the value relation is definable by
the displayed equivalence between forcing and the Boolean order. Applying Separation inside
$\mathbb B$ to the assertion that some name $\tau$ has value $b$ for $\psi(\tau)$ gives a set
$W_\psi\in M$. The existential value is the supremum of $W_\psi$ computed in $M$.
This uses an internally defined set of Boolean values, without requiring a set of all names in $M$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Boolean値の構成を振り返り、Cohenとrandomの既出の完備化を比較して、
直後の内部Cohen完備化とname翻訳・forcing保存の証明へ案内する段落。
円筒の稠密性はCohenRegularOpenCompletionに接続済みで、内部グラフ・generic
filter・再帰的および意味論的forcingの保存は後続の個別証明で対象に残す。ここでは新たなrandom完備化の構成を提示していない。)
--> This recovers the recursive forcing relation of §{sec:forcing-relation} before choosing a generic filter.
Cohen forcing uses the
regular-open completion of the tree of finite binary strings; random forcing uses the measure algebra of Borel sets
modulo null sets. After passing to these Boolean completions, conditions are nonzero elements of a complete
Boolean algebra.<!--
formalization: skip-end
-->
The original finite-string order for Cohen forcing embeds densely in its completion.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
Boolean値の構成を振り返り、Cohenとrandomの既出の完備化を比較して、
直後の内部Cohen完備化とname翻訳・forcing保存の証明へ案内する段落。
円筒の稠密性はCohenRegularOpenCompletionに接続済みで、内部グラフ・generic
filter・再帰的および意味論的forcingの保存は後続の個別証明で対象に残す。ここでは新たなrandom完備化の構成を提示していない。)
--> Under this embedding, recursive forcing agrees with the Boolean-value inequality, with names translated
as follows.<!--
formalization: skip-end
-->

\begin{proof}[Internal construction of the completion]
Let $P\in M$ be a forcing order whose order relation belongs to $M$ as well. Use the negative operation
from §{sec:random-forcing-detail} with conditions in $P$:
$$\ForcingNeg{U}=\{p\in P:\forall q\le p\ (q\notin U)\}.$$
The regular lower sets are the downward-closed subsets $U$ of $P$ satisfying
$U=\ForcingNeg{\ForcingNeg{U}}$. Take only those subsets that belong to $M$.
Their carrier is a set in $M$: apply Separation to the power set of $P$ computed inside $M$.
All quantifiers in the defining conditions are bounded by $P$, so transitivity makes these conditions
agree with their external meanings.

Order this carrier by inclusion. Intersection is meet, $\ForcingNeg{U}$ is complement, and the bottom
and top are $\varnothing$ and $P$. The double negative is precisely the set of conditions below which
$U$ is dense. It is an idempotent closure operation on lower sets, and its fixed points form a Boolean
algebra with these operations. Separation also puts the order, complement, and meet graphs in $M$.

For a family $\mathcal A\in M$ of regular lower sets, Union and Separation give
$$\bigvee\mathcal A=\ForcingNeg{\ForcingNeg{\bigcup\mathcal A}}\in M.$$
Each member of the family is contained in this regularization. Every regular upper bound contains
the union and therefore also its regularization. This proves the supremum property and hence
completeness for all families in $M$.
\end{proof}

\begin{proposition*}[Cohen completion and generic filters]
The finite binary-string order $P$ has a dense order embedding $e:P\to\mathbb B^+$ into its
internally computed regular-set completion, with the graph of $e$ belonging to $M$.
It induces a bijection between the $M$-generic filters on the two orders.
\end{proposition*}

\begin{proof}[Proof]
Put $e(p)=\{q\in P:q\le p\}$. If $q\not\le p$, the cylinder order embedding gives
$\neg(\cyl{q}\IncludedIn\cyl{p})$. Their nonempty clopen difference contains a cylinder $\cyl{r}$.
Thus $r\le q$ and $r$ is incompatible with $p$.
Thus the principal lower set $e(p)$ is regular. It is nonempty, and
$e(p)\IncludedIn e(q)$ holds exactly when $p\le q$. Every nonempty regular lower set contains
some $p$ and therefore contains $e(p)$. This proves density. The defining formula for the graph
has only bounded quantifiers over $P$, so Separation puts that graph in $M$.

To compare this construction with regular opens of Cantor space, send a regular lower set $U$ to
$$J(U)=\bigvee_{p\in U}\cyl{p},$$
where the join is computed in the external regular-open algebra, by regularizing the union.
Then $\cyl{p}\IncludedIn J(U)$ holds exactly when $p\in U$.
Indeed, if $p\notin U$, regularity supplies $q\le p$ with no extension in $U$.
Its cylinder is disjoint from every cylinder indexed by $U$, and therefore from their regular-open
join, contradicting $\cyl{p}\IncludedIn J(U)$. The converse follows from the definition of the join.
The inverse sends a regular open $V$ to $\{p\in P:\cyl{p}\IncludedIn V\}$; density of cylinders
makes this set regular and recovers $V$ as its join. Thus the external completions are Boolean
isomorphic. Restricting to internally coded lower sets gives a faithful Boolean representation,
and $J(e(p))=\cyl{p}$. Completeness of the internal carrier is still required only for families in $M$.

More generally, let $e:P\to Q$ be an internally represented dense order embedding, where both
orders and their order relations belong to $M$. For an $M$-generic filter $G$ on $P$, put
$$H=\{q\in Q:\exists p\in G\ (e(p)\le q)\}.$$
This is a filter. If $D\in M$ is dense in $Q$, then
$$T=\{p\in P:\exists d\in D\ (e(p)\le d)\}$$
belongs to $M$ and is dense in $P$: first refine $e(p)$ into $D$, then refine further into the image
of $e$. Meeting $T$ makes $H$ meet $D$. Hence $H$ is $M$-generic.

Conversely, let $H$ be $M$-generic on $Q$ and put $G=\{p\in P:e(p)\in H\}$.
For each $b\in H$, the set consisting of image conditions below $b$ together with all conditions
incompatible with $b$ is dense and belongs to $M$. A filter containing $b$ cannot meet the
incompatible part. Thus there is $p\in G$ with $e(p)\le b$.
This property makes $G$ nonempty and directed, and upward closure follows from monotonicity of $e$.
For every dense $D\in M$ in $P$, its image $e[D]$ is internal and dense in $Q$.
Meeting this image shows that $G$ is $M$-generic. The same refinement property, together with
order reflection, shows that the two filter constructions are inverse. No countability assumption
on $M$ enters this correspondence.
\end{proof}

\begin{proposition*}[Names and forcing under the dense embedding]
For the internally represented dense order embedding $e:P\to Q$, define translations of names by
$$\begin{aligned}
F(\tau)&=\{\Pair{F(\sigma)}{e(p)}:\Pair{\sigma}{p}\in\tau\},\\
R(\eta)&=\{\Pair{R(\delta)}{p}:\exists q\in Q
\ (\Pair{\delta}{q}\in\eta\land p\in P\land e(p)\le q)\}.
\end{aligned}$$
These send names in $M$ to names in $M$. For corresponding filters $G,H$ as above,
$$F(\tau)^H=\tau^G,\qquad R(\eta)^G=\eta^H.$$
Consequently, the two generic extensions are equal. Recursive forcing is preserved before choosing
any filter:
$$p\forces_P^*\varphi(\vec\tau)
\quad\Longleftrightarrow\quad
e(p)\forces_Q^*\varphi(F(\vec\tau)).$$
Here $F$ acts on each name parameter. In the Boolean completion this becomes
$$p\forces_P^*\varphi(\vec\tau)
\quad\Longleftrightarrow\quad
e(p)\le[\![\varphi(F(\vec\tau))]\!].$$
\end{proposition*}

\begin{proof}
The recursions are well founded because each child name has smaller rank. To verify internality,
retain at each set a table of the translated values of its hereditary members. The preceding tables
contain the values for every child name. The displayed pair collections are obtained by Separation
from products of sets bounding their ranges and the condition sets. Pairing and Union then adjoin the new table entry.
This gives an internally definable membership-recursion step closed in $M$. The comparison theorem in
§{sec:internal-transitive-bounds} puts the specified recursive translations in $M$.
Induction on names proves both valuation identities: in the forward direction a label belongs to $G$
exactly when its image belongs to $H$; in the reverse direction a label belongs to $H$ exactly when
some image of a condition in $G$ lies below it. Applying both translations gives equality of extensions.

For recursive forcing, define a matching relation between a $P$-name $\sigma$ and a $Q$-name $\tau$
by recursion on the rank of the source name. Require both of the following clauses:

* For $\Pair{\pi}{a}\in\sigma$ and $r\le a$, there are $s\le r$ and
  $\Pair{\delta}{b}\in\tau$ such that $e(s)\le b$ and the child names $\pi,\delta$ match.
* For $\Pair{\delta}{b}\in\tau$ and $e(r)\le b$, there are $s\le r$ and
  $\Pair{\pi}{a}\in\sigma$ such that $s\le a$ and the child names $\pi,\delta$ match.

The forward translation matches each name with its image. The reverse translation matches each
translated name with the original name, since it includes every refining source condition.
For matched pairs of name parameters, prove atomic forcing correspondence by induction on the pair
of source ranks, sorted in decreasing order. In the membership clause, refine a witnessing condition
into the image and use a matching child; the recursive equality assertion has smaller rank.
For equality, apply the induction hypothesis to the membership assertions for each child, in both
directions. Density supplies the image refinements, and downward closure preserves the forced assertions.

Now induct on formulas. Atomic formulas use the preceding argument. For implication, test image
conditions using the induction hypothesis; density and saturation extend the result to all target
conditions. For a universal quantifier, translate any target name back by $R$ in one direction, and
any source name forward by $F$ in the other. The translated names belong to $M$ and match, so the
induction hypothesis applies with the enlarged parameter tuple. This proves the forcing equivalence
without generic existence. The Boolean inequality follows from the construction of Boolean values above.
For the semantic relation $\forces$ of §{sec:forcing-relation}, quantify over corresponding generic filters
and use the valuation identities to obtain preservation as well.
\end{proof}

The forcing extension appears when one evaluates this structured truth through a generic filter. Let $\mathbb
B$ be the complete Boolean algebra as computed in the ground model $M$.
If $G\IncludedIn\mathbb B$ is $M$-generic, then
$$
M[G]\models\varphi
\quad\Longleftrightarrow\quad
[\![\varphi]\!]\in G,
$$
for formulas interpreted by names in the \termuse{Boolean-valued model}. The filter evaluates the truth values
of formulas whose names lie in $M$.

Indeed, the truth lemma in §{sec:forcing-relation} says that $\varphi$ holds in $M[G]$ exactly when
some $p\in G$ satisfies $p\forces^*\varphi$. The Boolean inequality and upward closure of $G$ make this equivalent to
membership of the Boolean value in $G$. Conversely, a Boolean value belonging to the proper filter
$G$ is itself a nonzero condition and forces the formula. No countability assumption on $M$ is needed
once the generic filter is given.

This is not an assertion that the ground-model locale has a point: an atomless complete Boolean algebra
has no completely prime filter in the ground model.

<!-- formalization: skip-begin (generic forcing interpretation and localic logical comparison) -->
The localic tripos is the pre-generic universe of truth
values; the forcing
extension is what results after choosing a sufficiently generic way to collapse those truth values back to ordinary
truth.

This is the precise connection with §{sec:forcing}: Cohen and random forcing were presented there as methods for
adjoining generic points to Polish spaces. Here the same forcings appear as localic triposes. The dense-set arguments in
§{sec:cohen-forcing-detail} and the null-set avoidance arguments in §{sec:random-forcing-detail} are exactly the
external shadows of joins, meets, and generic evaluation in the \termuse{localic tripos}.

The localic construction also explains the logical contrast with realizability. If $\Omega$ is Boolean, the associated
forcing semantics is classical. For a general locale, the sheaf topos is intuitionistic, and its
\termdefineas{double-negation sheaf}{double-negation sheaves} form a Boolean subtopos. Realizability goes in a different
direction: its truth values are not open sets or Boolean conditions but sets of computational witnesses, so its internal
logic is constructive for computational rather than localic reasons.

<!-- formalization: skip-end -->

## Kleene Realizability Tripos {#sec:effective-topos-construction}

\begin{mathmeta}
  \vars{e,n}{Nat}
  \vars{a,b,v}{Nat}
  \vars{\ell,r}{Fun(Nat,Nat)}
\end{mathmeta}
\index{realizability}

The underlying realizers are natural numbers. Use Kleene's first partial combinatory algebra $K_1$ with
$$e\cdot n\simeq\varphi_e(n),\qquad
\varphi_e(n)=m\quad\Longleftrightarrow\quad P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}.$$
Thus a realizer is an index in the fixed enumeration of closed lambda programs. The construction in
§{sec:realizability-pca} gives the combinators $\mathsf k,\mathsf s$, including their definedness properties:
the preliminary applications compute syntax codes, and the final S computation searches certificates for all
required partial applications.

For a set $I$, a \termdefine{realizability predicate} on $I$ is a function
$$\varphi:I\to\PowerSet{\NN}.$$
Read $a\in\varphi(i)$ as "$a$ realizes that $\varphi$ holds at $i$." Predicates are ordered by uniform reducibility:
$$
\varphi\le\psi
\quad\Longleftrightarrow\quad
\exists e\in\NN\;\forall i\in I\;\forall a\in\varphi(i)\;
e\cdot a\downarrow\in\psi(i).
$$
The witness $e$ is a single recursive operation converting every realizer of $\varphi(i)$ into a realizer of $\psi(i)$,
uniformly in $i$.

Let $\mathcal P_{K_1}(I)$ be this preorder, quotiented by mutual reducibility if one wants literal posets. For a
function $f:I\to J$, reindexing is pullback:
$$f^\ast(\psi)(i)=\psi(f(i)).$$
Thus
$$\mathcal P_{K_1}:\opcat{\SetCat}\to\HeytAlgCat$$
is contravariant on the base sets.

The Heyting operations are the realizability clauses for intuitionistic logic:
$$
\top(i)=\NN,\qquad \bot(i)=\emptyset,
$$
$$
(\varphi\land\psi)(i)=\{\Pair{a}{b}:a\in\varphi(i),\ b\in\psi(i)\},
$$
$$
(\varphi\lor\psi)(i)=
\{\Pair{0}{a}:a\in\varphi(i)\}
\cup
\{\Pair{1}{b}:b\in\psi(i)\},
$$
and
$$
(\varphi\to\psi)(i)=
\{e:\forall a\in\varphi(i),\ e\cdot a\downarrow\in\psi(i)\}.
$$


\begin{proposition*}[\termdefine{realizability propositional operations}]
Uniform reducibility is a preorder. For predicates $\theta,\varphi,\psi$ on the same set, the displayed operations
satisfy
$$
\begin{aligned}
\theta\le\varphi\land\psi
&\quad\Longleftrightarrow\quad\theta\le\varphi\ \text{and}\ \theta\le\psi,\\
\varphi\lor\psi\le\theta
&\quad\Longleftrightarrow\quad\varphi\le\theta\ \text{and}\ \psi\le\theta,\\
\theta\land\varphi\le\psi
&\quad\Longleftrightarrow\quad\theta\le(\varphi\to\psi),\\
\bot&\le\varphi\le\top.
\end{aligned}
$$
Every reindexing map preserves uniform reducibility.
\end{proposition*}

\begin{proof}[Proof]
Write $U=\LambdaOutputSearch$ for the universal evaluation term and $\pi_i=\LambdaNumericProjection{i}$ for the
numerical projections. An index of $\lambdaab{a}{a}$ tracks reflexivity. If $e$ tracks $\varphi\le\psi$ and $f$ tracks
$\psi\le\theta$, an index of
$$\lambdaab{a}{U\ChurchNumeral{f}(U\ChurchNumeral{e}a)}$$
tracks $\varphi\le\theta$: first run the $e$ computation, then the $f$ computation. The same index works for every
point of the base set. Thus reducibility is transitive. Reindexing changes only the base point in the membership
conditions, so it keeps the original tracker.

The indices of $\pi_1$ and $\pi_2$ track the two projections from $\varphi\land\psi$.
If $e,f$ track $\theta\le\varphi$ and $\theta\le\psi$, respectively, use an index of
$$\lambdaab{a}{\LambdaNumericPair\,(U\ChurchNumeral{e}a)(U\ChurchNumeral{f}a)}.$$
Both computations terminate on every realizer of $\theta$, so this term returns a pair realizing $\varphi\land\psi$.
Composing with the two projections proves the converse.

The injections into $\varphi\lor\psi$ are tracked by indices of
$$\lambdaab{a}{\LambdaNumericPair\,\ChurchNumeral{0}a},
\qquad\lambdaab{b}{\LambdaNumericPair\,\ChurchNumeral{1}b}.$$
If $e,f$ track $\varphi\le\theta$ and $\psi\le\theta$, use an index of
$$\lambdaab{z}{\LambdaZeroTest(\pi_1z)
  (U\ChurchNumeral{e}(\pi_2z))(U\ChurchNumeral{f}(\pi_2z))}.$$
On a realizer of $\varphi\lor\psi$, the tag is $0$ or $1$. The zero test selects the corresponding branch before
that branch is evaluated; the unused computation need not terminate. The selected computation returns a realizer
of $\theta$. Composing with the two injections proves the converse. The identity index tracks $\varphi\le\top$.
For $\bot\le\varphi$, any index works because there are no input realizers.

For implication, suppose $e$ tracks $\theta\land\varphi\le\psi$. Fix named representatives of $U$ and numerical
pairing and form the syntax code
$$c(e,a)=\LambdaSyntaxCode{\lambdaab{b}{U\ChurchNumeral{e}(\LambdaNumericPair\,\ChurchNumeral{a}b)}}.$$
Numeral-code, application-code, and abstraction-code programs give a closed total program $C$ computing $c$ on paired
inputs. Put
$$H=\lambdaab{e}{\lambdaab{a}{C(\LambdaNumericPair\,e\,a)}},\qquad
q(e)=\LambdaSyntaxCode{H\ChurchNumeral{e}},$$
using a fixed named representative of $H$. The code map $q$ is also computed by a total lambda program. For every
$e,a$, the application $q(e)\cdot a$ returns $c(e,a)$ without evaluating the program with that code. Moreover,
$$c(e,a)\cdot b\simeq e\cdot\NatPair{a}{b}.$$
Indeed, one beta contraction supplies $b$, numerical pairing computes $\NatPair{a}{b}$, and the universal evaluator
has exactly the numerical outputs of the indexed program. Confluence gives the converse direction as well.
Consequently $q(e)$ tracks $\theta\le(\varphi\to\psi)$. This remains valid when $\varphi(i)$ is empty: the code
$c(e,a)$ is still returned, and its membership in the implication imposes no computations on inputs from that empty set.

Conversely, if $e$ tracks $\theta\le(\varphi\to\psi)$, take an index of
$$\lambdaab{z}{U\bigl(U\ChurchNumeral{e}(\pi_1z)\bigr)(\pi_2z)}.$$
On an input $\NatPair{a}{b}$ realizing $\theta\land\varphi$, first compute the implication realizer $e\cdot a$,
then apply it to $b$. Both computations are defined by the tracking assumptions, and the final result belongs to
$\psi(i)$. This proves the implication adjunction using the same numerical application as all the other clauses.
\end{proof}


Quantifiers along $f:I\to J$ are
$$
(\exists_f\varphi)(j)=\bigcup_{f(i)=j}\varphi(i),
$$
and
$$
\begin{aligned}
(\forall_f\varphi)(j)
&=\left\{e\in\NN:
  \begin{array}{l}
    \forall i\in I,\ f(i)=j\Longrightarrow{}\\
    \qquad\forall n\in\NN,\ e\cdot n\downarrow\in\varphi(i)
  \end{array}
\right\}\\
&=\bigcap_{f(i)=j}\bigl(\top\to\varphi(i)\bigr).
\end{aligned}
$$
The empty union is $\emptyset$. On an empty fiber the condition defining $\forall_f\varphi$ is vacuous, so its value is
$\NN$. The guard $\top\to-$ is essential: it records that the output realizer must itself be defined on every natural
number whenever the fiber is nonempty.

\begin{lemma*}[\termdefine{uniform indices for realizability quantifiers}]
There are total lambda-computable maps $\ell,r:\NN\to\NN$ and $d:\NN^2\to\NN$ such that
$$
\begin{aligned}
u\cdot a=e,\ e\cdot 0=b&\quad\Longrightarrow\quad\ell(u)\cdot a=b,\\
r(v)\cdot a&=d(v,a),\\
d(v,a)\cdot n&\simeq v\cdot a.
\end{aligned}
$$
The second equality holds for every $v,a$, whether or not $v\cdot a$ is defined.
\end{lemma*}

\begin{proof}[Proof]
Put $U=\LambdaOutputSearch$, the closed universal evaluation term constructed in
§{sec:lambda-input-universal-evaluation}. Thus
$$U\ChurchNumeral{e}\ChurchNumeral{a}\to_\beta^*\ChurchNumeral{b}
\quad\Longleftrightarrow\quad e\cdot a=b.$$
Fix a named representative of $U$ and use it in the syntax codes
$$
\begin{aligned}
\ell(u)&=\LambdaSyntaxCode{\lambdaab{x}{U(U\ChurchNumeral{u}x)\ChurchNumeral{0}}},\\
d(v,a)&=\LambdaSyntaxCode{\lambdaab{n}{U\ChurchNumeral{v}\ChurchNumeral{a}}}.
\end{aligned}
$$
The numeral-code, application-code, and abstraction-code programs compute these two maps without evaluating the
coded applications. One beta contraction and two uses of the evaluator give the first implication. For the last
identity, applying the program with code $d(v,a)$ to any numeral removes the unused binder. The evaluator theorem
and confluence give exactly the same numeral outputs as $P_v\ChurchNumeral{a}$, including absence of output.

Choose a closed term $B$ computing $d$ on paired inputs and set
$$H=\lambdaab{v}{\lambdaab{a}{B(\LambdaNumericPair\,v\,a)}},\qquad
r(v)=\LambdaSyntaxCode{H\ChurchNumeral{v}}.$$
Here too, fix a named representative of $H$ before taking syntax codes. The map $r$ is computed by the
numeral-code and application-code programs. Since $B$ is total,
$$P_{r(v)}\ChurchNumeral{a}\to_\beta^*B\ChurchNumeral{\NatPair{v}{a}}
\to_\beta^*\ChurchNumeral{d(v,a)}$$
for every $v,a$. This computation returns a code and never evaluates $v\cdot a$.
\end{proof}

\begin{lemma*}[Realizability quantifier adjunctions]
With respect to uniform reducibility, the displayed clauses satisfy
$$
\exists_f\varphi\le\psi\quad\Longleftrightarrow\quad\varphi\le f^\ast\psi,
\qquad
f^\ast\psi\le\varphi\quad\Longleftrightarrow\quad\psi\le\forall_f\varphi.
$$
\end{lemma*}

\begin{proof}[Proof]
For the existential adjunction, the same tracker works in both directions: an element of
$(\exists_f\varphi)(j)$ is already an element of some $\varphi(i)$ with $f(i)=j$.

For the universal adjunction, use the maps $\ell,r,d$ from the preceding lemma. Suppose $u$ tracks
$\psi\le\forall_f\varphi$. If $f(i)=j$ and $a\in\psi(j)$, then $u\cdot a$ is an index that sends every
$n\in\NN$ to an element of $\varphi(i)$. Evaluating it at $0$ shows that $\ell(u)$ tracks
$f^\ast\psi\le\varphi$. Conversely, if $v$ tracks $f^\ast\psi\le\varphi$, then $r(v)\cdot a=d(v,a)$
is defined for every $a$. Whenever $f(i)=j$ and $a\in\psi(j)$, the value $v\cdot a$ belongs to $\varphi(i)$,
so $d(v,a)$ sends every $n$ to that value. Hence $r(v)$ tracks $\psi\le\forall_f\varphi$.
On an empty fiber, the outer application still returns $d(v,a)$, while the defining condition for the universal
quantifier imposes no requirement on its outputs.
\end{proof}

\begin{proposition*}[\termdefineas{realizability tripos}{Realizability tripos}]
The indexed Heyting algebra $\mathcal P_{K_1}$, with the reindexing maps and quantifiers defined above, is a tripos over
$\SetCat$.
\end{proposition*}

\begin{proof}[Proof]
First form the quotient in each fiber explicitly. Write $\varphi\equiv\psi$ when $\varphi\le\psi$ and
$\psi\le\varphi$. Reflexivity and transitivity make this an equivalence relation. If $\varphi\equiv\varphi'$ and
$\psi\equiv\psi'$, transitivity gives $\varphi\le\psi$ if and only if $\varphi'\le\psi'$. Thus reducibility defines
an order on equivalence classes, and this order is antisymmetric by the definition of $\equiv$.

The propositional universal properties give the variance rules
$$
\begin{aligned}
\varphi\le\varphi',\ \psi\le\psi'
&\Longrightarrow\varphi\land\psi\le\varphi'\land\psi',\\
\varphi\le\varphi',\ \psi\le\psi'
&\Longrightarrow\varphi\lor\psi\le\varphi'\lor\psi',\\
\varphi'\le\varphi,\ \psi\le\psi'
&\Longrightarrow(\varphi\to\psi)\le(\varphi'\to\psi').
\end{aligned}
$$
For the last implication, the assumptions give
$$(\varphi\to\psi)\land\varphi'\le(\varphi\to\psi)\land\varphi\le\psi\le\psi',$$
and the implication adjunction applies. Applying these rules in both directions shows that all operations are
independent of the representatives. The meet, join, top, and bottom universal properties therefore hold on classes,
as does the implication adjunction. This makes the quotient a Heyting algebra.

Reindexing preserves reducibility by keeping the same tracker. It therefore descends to classes. Its defining
formula commutes pointwise with $\land,\lor,\to,\top,\bot$, so the induced map is a Heyting homomorphism. Moreover,
$$\mathrm{id}^{\ast}=\mathrm{id},\qquad (g\circ f)^{\ast}=f^{\ast}\circ g^{\ast}.$$
Both identities already hold on predicates. Hence the quotient fibers and reindexing maps form the required
contravariant functor to $\HeytAlgCat$.

The quantifier adjunctions also pass to the quotient. To check independence of representatives, suppose
$\varphi\le\psi$. The unit and counit of the already proved adjunctions give
$$\varphi\le\psi\le f^{\ast}\exists_f\psi,\qquad
f^{\ast}\forall_f\varphi\le\varphi\le\psi.$$
Applying those adjunctions yields
$$\exists_f\varphi\le\exists_f\psi,\qquad\forall_f\varphi\le\forall_f\psi.$$
Thus both quantifiers preserve mutual reducibility and define monotone maps on the quotient fibers. Their
adjunction equivalences are unchanged on representatives, so
$$\exists_f\dashv f^{\ast}\dashv\forall_f$$
holds on the Heyting algebras themselves.

For Beck--Chevalley, take any pullback square
$$\begin{array}{ccc}
I'\! & \xrightarrow{g'} & I\\
{\scriptstyle f'}\downarrow & & \downarrow{\scriptstyle f}\\
J'\! & \xrightarrow{g} & J .
\end{array}$$
For each $j'\in J'$, the map $i'\mapsto g'(i')$ gives a bijection
$$\{i'\in I':f'(i')=j'\}\longrightarrow\{i\in I:f(i)=g(j')\}.$$
Commutativity makes this map well defined. For each $i$ in the right-hand fiber, the pullback property gives a unique
$i'$ with $g'(i')=i$ and $f'(i')=j'$, proving bijectivity. Consequently, for every realizer $a$,
$$
\begin{aligned}
a\in(g^{\ast}\exists_f\varphi)(j')
&\Longleftrightarrow\exists i'\in I',\\
&\qquad f'(i')=j'\ \text{and}\ a\in\varphi(g'(i')),\\
a\in(g^{\ast}\forall_f\varphi)(j')
&\Longleftrightarrow\forall i'\in I',\ f'(i')=j'\Longrightarrow{}\\
&\qquad\forall n\in\NN,\ a\cdot n\downarrow\in\varphi(g'(i')).
\end{aligned}
$$
These are exactly the membership conditions for $\exists_{f'}g'^{\ast}\varphi$ and
$\forall_{f'}g'^{\ast}\varphi$. The guard quantifies over the same natural numbers on both sides; the argument also
covers empty fibers. Thus both Beck--Chevalley equalities hold already as equalities of predicates, and therefore
on their classes.

Finally, put $\Sigma=\PowerSet{\NN}$ and define the predicate
$$\sigma(S)=S\qquad(S\IncludedIn\NN).$$
For any representative $\varphi:I\to\PowerSet{\NN}$, its classifying map is $i\mapsto\varphi(i)$, and reindexing
$\sigma$ along this map gives $\varphi$ exactly. Given an element of the quotient fiber, choose a representative and
use this classifier. Thus the class of $\sigma$ is a generic predicate. Together with the functor, adjunctions, and
base-change equalities above, this proves all the tripos axioms.
\end{proof}

## Objects, Arrows, and Finite Limits {#sec:effective-topos-category}

### Objects and Morphisms of $\EffCat$ {#sec:effective-topos-objects-morphisms}

\begin{mathmeta}
  \define{EffCat}
  \vars{a,b,c,r,s}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
未リンク部分はKleene triposから得るtoposをSet[P_K1]と記す一般的なtripos-to-toposの同定・命名。
章のproof scopeと末尾のvan Oosten Ch.2への参照が、
一般Hyland–Johnstone–Pitts定理を外部理論として明示している。具体的なrealizer-valued
PERとuniform-equivalenceで割ったfunctional
relationsのcategoryはrealizabilityPERCategoryへ接続済み。
一般構成との圏同値を新たにLeanで証明済みとは扱わない。)
--> The \termdefine{effective topos} is the topos obtained from the Kleene \termuse{realizability tripos}:
$$
\EffCat:=\SetCat[\mathcal P_{K_1}].
$$<!--
formalization: skip-end
-->
Concretely, it is the category of realizability
\termdefineas{partial equivalence relation}{partial equivalence relations} and functional relations.

An \termdefineas{effective topos object}{object} is a pair
$$X=\Pair{\UnderlyingSet{X}}{\sim_X}$$
where $\UnderlyingSet{X}$ is a set and
$$\sim_X:\UnderlyingSet{X}\times \UnderlyingSet{X}\to\PowerSet{\NN}$$
is a realizability predicate satisfying symmetry and transitivity:

*   there is an index sending every realizer of $x\sim_X y$ to a realizer of $y\sim_X x$;
*   there is an index sending a pair of realizers of $x\sim_X y$ and $y\sim_X z$ to a realizer of $x\sim_X z$.

The \termdefineas{effective topos extent}{extent} of $x$ is
$$E_X(x):=(x\sim_X x).$$
Only elements with inhabited extent are internally present; an element whose extent is empty is a formal representative
with no evidence of existence.

A \termdefineas{effective topos morphism}{morphism} $F:X\to Y$ is represented by a realizability relation
$$F:\UnderlyingSet{X}\times \UnderlyingSet{Y}\to\PowerSet{\NN}$$
satisfying the following four conditions, each uniformly realized by some natural-number index:

1.  \termdefineas{strictness of effective topos morphism}{strictness}: $F(x,y)$ implies $E_X(x)$ and $E_Y(y)$.
2.  \termdefineas{extensionality of effective topos morphism}{extensionality}: $x\sim_X x'$, $F(x,y)$, and $y\sim_Y y'$
    imply $F(x',y')$.
3.  \termdefineas{single-valuedness of effective topos morphism}{single-valuedness}: $F(x,y)$ and $F(x,y')$ imply
    $y\sim_Y y'$.
4.  \termdefineas{totality on effective topos extent}{totality on the extent}: $E_X(x)$ implies $\exists y\,F(x,y)$.

Two such relations represent the same morphism if they are internally equivalent:
$$
F\equiv G
\quad\Longleftrightarrow\quad
F(x,y)\le G(x,y)\ \text{and}\ G(x,y)\le F(x,y)
\text{ uniformly in }x,y.
$$
Composition is relational:
$$
(G\circ F)\Pair{x}{z}
=
\bigcup_{y\in \UnderlyingSet{Y}}
\{\NatPair{a}{b}:a\in F(x,y),\ b\in G(y,z)\}.
$$
The identity on $X$ is $\sim_X$ itself.

\begin{proposition*}[\termdefineas{realizability PER category}{Category of realizability PERs}]
The objects and equivalence classes of functional relations above form a category, with the stated identities and
composition.
\end{proposition*}

\begin{proof}[Proof]
Fix trackers for the PER and functional-relation conditions. Write $s_X(a)$ for the symmetry transformer and
$t_X(a,b)$ for the transitivity transformer applied to $\NatPair{a}{b}$. For $F$, let
$\ell_F(a),r_F(a)$ be the two projections of its strictness output. Write $q_F(r,a,s)$ for its extensionality
transformer applied to $\NatPair{\NatPair{r}{a}}{s}$, $v_F(a,b)$ for its single-valuedness transformer applied to
$\NatPair{a}{b}$, and $u_F(e)$ for its totality transformer. These are partial numerical functions evaluated by
lambda indices, with definedness guaranteed on the indicated realizers. Every expression below expands into a closed
lambda term by using $U=\LambdaOutputSearch$, numerical pairing, projections, and composition, as in
§{sec:effective-topos-construction}. In particular, no transformation is allowed to depend on an unprovided
representative of an underlying set.

First consider the identity relation. From $a\in(x\sim_X y)$, symmetry and transitivity compute extent realizers
$$t_X(a,s_X(a))\in E_X(x),\qquad t_X(s_X(a),a)\in E_X(y).$$
Pairing these proves strictness. Given $r\in(x\sim_X x')$, $a\in(x\sim_X y)$, and $s\in(y\sim_X y')$, the expression
$$t_X\bigl(t_X(s_X(r),a),s\bigr)\in(x'\sim_X y')$$
proves extensionality. From $a\in(x\sim_X y)$ and $b\in(x\sim_X y')$, the expression $t_X(s_X(a),b)$ proves
single-valuedness. An extent realizer already belongs to the identity relation at $\Pair{x}{x}$, so the identity lambda
term
proves totality.

Now take $F:X\to Y$ and $G:Y\to Z$. A composite realizer is a pair $\NatPair{a}{b}$ with
$a\in F(x,y)$ and $b\in G(y,z)$ for some $y$. The pair $\NatPair{\ell_F(a)}{r_G(b)}$ realizes strictness.
For extensionality, also suppose $r\in(x\sim_X x')$ and $s\in(z\sim_Z z')$. Then
$$\NatPair{q_F(r,a,r_F(a))}{q_G(\ell_G(b),b,s)}$$
belongs to $(G\circ F)\Pair{x'}{z'}$, using the same intermediate point $y$. The terms $r_F(a)$ and $\ell_G(b)$ both
supply evidence of $y\sim_Y y$, so each use of extensionality has all its required inputs.

For single-valuedness, let $\NatPair{a}{b}$ and $\NatPair{a'}{b'}$ realize the composite at $\Pair{x}{z}$ and
$\Pair{x}{z'}$, with intermediate points $y,y'$. Put
$$d=v_F(a,a'),\qquad c=q_G(d,b,r_G(b)).$$
Here $d\in(y\sim_Y y')$ and $c\in G(y',z)$. Thus $v_G(c,b')\in(z\sim_Z z')$ proves single-valuedness.
For totality, from $e\in E_X(x)$ compute
$$a=u_F(e),\qquad b=u_G(r_F(a)),\qquad \NatPair{a}{b}.$$
The first output belongs to $F(x,y)$ for some $y$; its strictness output $r_F(a)$ realizes $E_Y(y)$.
The second output therefore belongs to $G(y,z)$ for some $z$, proving totality of the composite. The program never
extracts or chooses $y$ or $z$: they occur only in the proof of membership of its numerical outputs.

Composition respects uniform equivalence. Indeed, if $e$ and $f$ track $F\le F'$ and $G\le G'$, respectively,
then
$$\NatPair{a}{b}\longmapsto\NatPair{e\cdot a}{f\cdot b}$$
tracks $G\circ F\le G'\circ F'$. The same intermediate point witnesses membership on both sides.
Applying this in both directions makes composition well defined on equivalence classes.

For associativity, the two bracketings have the same intermediate points and differ only in their numerical pairing.
The transformations
$$\NatPair{\NatPair{a}{b}}{c}\longmapsto\NatPair{a}{\NatPair{b}{c}},\qquad
\NatPair{a}{\NatPair{b}{c}}\longmapsto\NatPair{\NatPair{a}{b}}{c}$$
use only numerical projections and pairing and realize the two inequalities uniformly.

Finally, for $F\circ 1_X\equiv F$ the forward and reverse transformations are
$$\NatPair{r}{a}\longmapsto q_F(s_X(r),a,r_F(a)),\qquad
 a\longmapsto\NatPair{\ell_F(a)}{a}.$$
The forward map transports $F(x',y)$ along $r\in(x\sim_X x')$, while the reverse map uses $x$ as the intermediate
point. For $1_Y\circ F\equiv F$, use
$$\NatPair{a}{s}\longmapsto q_F(\ell_F(a),a,s),\qquad
 a\longmapsto\NatPair{a}{r_F(a)}.$$
These formulas require only strictness and extensionality of $F$ and symmetry of the source PER.
Thus associativity and both identity laws hold as literal equalities of equivalence classes.
\end{proof}

### Finite Limits {#sec:effective-topos-finite-limits}

\begin{mathmeta}
  \define{PERRestriction}
  \vars{a,b,u}{Nat}
\end{mathmeta}

\begin{lemma*}[\termdefineas{realizability predicate restriction}{Restriction by a realizability predicate}]
Let $X$ be a realizability PER and let $\varphi(x)\IncludedIn\NN$ satisfy, uniformly,
$$\varphi(x)\le E_X(x),\qquad (x\sim_X x')\land\varphi(x)\le\varphi(x').$$
On the same representatives define $\PERRestriction{X}{\varphi}$ by
$$x\sim_{\PERRestriction{X}{\varphi}}x':=(x\sim_X x')\land\varphi(x).$$
This is a PER, and the relation
$$J_\varphi(x,x'):=(x\sim_X x')\land\varphi(x)$$
defines a monomorphism $J_\varphi:\PERRestriction{X}{\varphi}\to X$.
If a functional relation $F:Z\to X$ satisfies $F(z,x)\le\varphi(x)$ uniformly in $z,x$, the same realizer sets define
a unique factorization of $F$ through $J_\varphi$.
\end{lemma*}

\begin{proof}[Proof]
For symmetry, from realizers of $x\sim_X x'$ and $\varphi(x)$ compute a realizer of $x'\sim_X x$ by symmetry and
one of $\varphi(x')$ by the second assumption. Transitivity combines the two $X$-equality realizers and retains
the first $\varphi$ realizer. Thus the displayed relation is a PER, with
$$E_{\PERRestriction{X}{\varphi}}(x)=E_X(x)\land\varphi(x).$$
The equality realizer in $J_\varphi(x,x')$ supplies both $X$-extents, while its second component supplies
$\varphi(x)$; this proves strictness. Symmetry, transitivity, and the second assumption give extensionality and
single-valuedness. The identity transformer on $E_{\PERRestriction{X}{\varphi}}(x)$ proves totality, using $x'=x$.

For the factorization, retain $F(z,x)$ as its value in $\PERRestriction{X}{\varphi}$. The assumed conversion to
$\varphi(x)$ supplies the extra extent component for strictness and the extra equality component for
single-valuedness. Extensionality discards the extra component of the target equality; totality is unchanged.
The relation $J_\varphi$ has exactly the same realizer sets as the identity on $\PERRestriction{X}{\varphi}$, so
the identity-law conversions from §{sec:effective-topos-objects-morphisms} prove that the composite represents $F$.
For any two arrows into $\PERRestriction{X}{\varphi}$, these same conversions turn an equivalence of their
composites with $J_\varphi$ into an equivalence of the original relations. Thus $J_\varphi$ is monic and the
factorization is unique.
\end{proof}

\begin{proposition*}[\termdefineas{finite limits in realizability}{Finite limits in realizability}]
The category of realizability PERs has a terminal object, binary products, and equalizers, and hence has all finite
limits.
\end{proposition*}

\begin{proof}[Proof]
We use the tracker notation from the proof in §{sec:effective-topos-objects-morphisms}.
For the terminal object, take $1=\{\ast\}$ with $(\ast\sim_1\ast)=\NN$. The relation
$$T_X(x,\ast)=E_X(x)$$
is functional: strictness pairs the input with any natural number, extensionality follows from equality in $X$,
single-valuedness has value $\NN$, and totality uses the same input. Any functional relation $F:X\to1$ reduces to
$T_X$ by strictness. Conversely, totality sends $E_X(x)$ into $F(x,\ast)$ because there is only one representative
in $1$. This proves uniqueness of the arrow to $1$.

For products, use representatives $\Pair{x}{y}\in\UnderlyingSet{X}\times\UnderlyingSet{Y}$ and equality
$$\Pair{x}{y}\sim_{X\times Y}\Pair{x'}{y'}=(x\sim_X x')\land(y\sim_Y y').$$
Symmetry and transitivity act on each component. The projection relations are
$$\begin{aligned}
P_X(\Pair{x}{y},x')&=E_{X\times Y}(x,y)\land(x\sim_X x'),\\
P_Y(\Pair{x}{y},y')&=E_{X\times Y}(x,y)\land(y\sim_Y y').
\end{aligned}$$
The extent factors ensure strictness even when a coordinate has empty extent. More generally, if a function $f$ on
representatives uniformly preserves equality, its relation
$$E_A(a)\land(f(a)\sim_B b)$$
is functional. Symmetry and transitivity give extensionality and single-valuedness. A realizer of $E_A(a)$, together
with its image under the equality-preserving tracker, proves totality at $b=f(a)$. Applying this observation to the two
coordinate functions gives the displayed projections.

Given $F:Z\to X$ and $G:Z\to Y$, define
$$H(z,\Pair{x}{y}):=F(z,x)\land G(z,y).$$
Strictness, extensionality, and single-valuedness follow componentwise; for totality, apply the two totality trackers
to the same extent realizer and pair their outputs. Projection of a composite realizer, followed by extensionality of
$F$, proves $P_X\circ H\le F$. Conversely, from $a\in F(z,x)$ compute $u_G(\ell_F(a))$; it belongs to $G(z,y)$
for some $y$. These two outputs and their strictness outputs supply a realizer of $(P_X\circ H)\Pair{z}{x}$.
Thus $P_X\circ H\equiv F$, and the same argument gives $P_Y\circ H\equiv G$.

For uniqueness, let $K:Z\to X\times Y$ be any functional relation. Its strictness outputs give
$$K(z,\Pair{x}{y})\le(P_X\circ K)\Pair{z}{x}\land(P_Y\circ K)\Pair{z}{y}.$$
For the reverse inequality, the two composite realizers supply intermediate points $p,p'$ with realizers of
$K(z,p)$ and $K(z,p')$, together with $p_1\sim_X x$ and $p'_2\sim_Y y$. Single-valuedness of $K$ gives
$p\sim_{X\times Y}p'$, hence $p_2\sim_Y p'_2$. Transitivity yields $p_2\sim_Y y$, and pairing it with
$p_1\sim_X x$ gives $p\sim_{X\times Y}\Pair{x}{y}$. Extensionality of $K$ now supplies $K(z,\Pair{x}{y})$.
Each step uses a fixed tracker on the given numerical realizers. Consequently $K$ is uniformly equivalent to the
pairing of its two projections, proving uniqueness.

For equalizers, choose functional relations $F,G:X\to Y$ representing the two arrows and put
$$D(x):=\bigcup_{y\in\UnderlyingSet{Y}}\bigl(F(x,y)\land G(x,y)\bigr).$$
Strictness of $F$ proves $D(x)\le E_X(x)$. Given realizers of $x\sim_X x'$ and $D(x)$, apply extensionality of
$F$ and $G$ at the common output $y$, using their strictness outputs to realize $y\sim_Y y$.
This proves $(x\sim_X x')\land D(x)\le D(x')$ uniformly. The restriction lemma therefore gives the PER
$Q=\PERRestriction{X}{D}$ and its monomorphism $J_D:Q\to X$.

To check the equalizing equation, suppose a realizer of $D(x)$ gives $u\in F(x,y_0)$ and $v\in G(x,y_0)$,
and let $a\in F(x,y)$. Single-valuedness of $F$ computes $v_F(u,a)\in(y_0\sim_Y y)$, so
$$q_G\bigl(\ell_G(v),v,v_F(u,a)\bigr)\in G(x,y).$$
Thus $D(x)\land F(x,y)\le G(x,y)$; swapping the two components of the agreement realizer proves the reverse
conversion with $F$ and $G$ interchanged. A realizer of $J_D(x,x')$ also supplies $D(x')$ by extensionality of $D$.
Applying the conversions at that intermediate point gives
$$F\circ J_D\equiv G\circ J_D.$$
Neither conversion needs to compute $y_0$ or $x'$.

For the universal property, let $H:Z\to X$ satisfy $F\circ H\equiv G\circ H$, and fix a tracker $c$ for the
forward reduction. From $a\in H(z,x)$ compute
$$\begin{aligned}
u&=u_F(r_H(a)),\\
\NatPair{a'}{b}&=c\cdot\NatPair{a}{u},\\
b^\ast&=q_G\bigl(s_X(v_H(a,a')),b,r_G(b)\bigr).
\end{aligned}$$
For some $y$, the first output lies in $F(x,y)$. The second line is defined because $\NatPair{a}{u}$ realizes
$(F\circ H)\Pair{z}{y}$; for some $x'$, its projections satisfy $a'\in H(z,x')$ and $b\in G(x',y)$.
Single-valuedness of $H$ gives $x\sim_X x'$, and symmetry and extensionality of $G$ give $b^\ast\in G(x,y)$.
Hence $\NatPair{u}{b^\ast}\in D(x)$. We have proved $H(z,x)\le D(x)$ uniformly, so the restriction lemma gives
a factorization through $J_D$. It is unique because $J_D$ is monic. These calculations establish the equalizer
universal property for any chosen representatives $F,G$; consequently different representatives yield canonically
isomorphic equalizers.

Finally, the standard finite-limit criterion recalled in Appendix §{sec:cat-ccc} gives all finite limits from
these terminal objects, binary products, and equalizers.
\end{proof}

## Subobjects, Function Objects, and the Topos Theorem {#sec:effective-topos-structure}

### Subobjects and Truth Values {#sec:effective-topos-subobjects-truth-values}

\begin{mathmeta}
  \vars{a,b,s,t}{Nat}
\end{mathmeta}

\begin{proposition*}[\termdefineas{realizability subobject presentation}{Predicate presentation of subobjects}]
Let $M:X\to Y$ represent a monomorphism in the category of realizability PERs. The predicate
$$\varphi_M(y):=\bigcup_{x\in\UnderlyingSet{X}}M(x,y)$$
is strict and extensional. The same relation $M$ gives an isomorphism
$$X\cong\PERRestriction{Y}{\varphi_M}$$
whose composite with $J_{\varphi_M}$ is the original monomorphism. Its inverse is represented by
$$R(y,x):=M(x,y).$$
Moreover, predicate inclusions that are isomorphic over $Y$ have uniformly equivalent predicates.
\end{proposition*}

\begin{proof}[Proof]
Use the tracker notation from §{sec:effective-topos-objects-morphisms}. We first extract uniform injectivity from
categorical monicity. On $X\times X$ put
$$\kappa(x,x'):=\bigcup_{y\in\UnderlyingSet{Y}}\bigl(M(x,y)\land M(x',y)\bigr).$$
Strictness of $M$ gives both coordinate extents. Applying extensionality of $M$ in each coordinate, while retaining
the same output, proves extensionality of $\kappa$. Thus the restriction
$$K:=\PERRestriction{(X\times X)}{\kappa}$$
is defined, and the two coordinate functions induce arrows $p,q:K\to X$ by the graph construction in
§{sec:effective-topos-finite-limits}.

The composites $M\circ p$ and $M\circ q$ are equivalent. Indeed, let $a\in M(x,y_0)$ and $b\in M(x',y_0)$
be a common-image realizer. Given $c\in M(x,y)$, the expression
$$q_M\bigl(\ell_M(b),b,v_M(a,c)\bigr)\in M(x',y)$$
transfers that output to the second coordinate. Swapping $a,b$ gives the converse; the equality components in the
projection graphs are handled first by extensionality of $M$. Monicity now gives $p=q$. Fix the uniform conversion
between these two projection relations supplied by that equality. From $a\in M(x,y)$ and $b\in M(x',y)$ we can
construct an extent realizer of $\Pair{x}{x'}\in K$, using their strictness outputs and $\NatPair{a}{b}$.
This gives a realizer of $p(\Pair{x}{x'},x)$. The fixed conversion returns one of $q(\Pair{x}{x'},x)$, whose equality
component
realizes $x'\sim_X x$. Symmetry therefore gives a single uniform transformer $i_M$ with
$$i_M(a,b)\in(x\sim_X x').$$
This is a transformer of realizer numbers; no preimage representative is computed.

The range predicate $\varphi_M$ is strict by strictness of $M$, and extensional by extensionality of $M$ on the
output coordinate. Every $M(x,y)$ reduces to $\varphi_M(y)$ by the identity transformer, so the restriction lemma
lifts $M$ to $\PERRestriction{Y}{\varphi_M}$. For the converse relation $R$, strictness uses the two strictness
outputs of $M$ and its input realizer as evidence of $\varphi_M(y)$. Extensionality uses extensionality of $M$
with the two coordinates exchanged. Single-valuedness is precisely the transformer $i_M$ just constructed, and
totality follows from the defining union in $\varphi_M(y)$. Thus $R$ is functional.

In $R\circ M$, the transformer $i_M$ converts a pair of common-image realizers into $X$-equality.
Conversely, from an $X$-equality realizer, totality of $M$ gives an output at the first input and extensionality
transfers it to the second input, producing a composite realizer. In $M\circ R$, single-valuedness of $M$ gives
$Y$-equality, and the first component also realizes $\varphi_M$ at the source. Conversely, a restricted equality
realizer supplies a preimage through its $\varphi_M$ component; extensionality transports the associated $M$ realizer
to the other output. These are uniform conversions in both directions, proving both inverse laws.
The factorization through $J_{\varphi_M}$ is the one in the restriction lemma.

For uniqueness of the predicate presentation, suppose an arrow $L$ satisfies $J_\psi\circ L=J_\varphi$.
A realizer of $\varphi(y)$ supplies $J_\varphi(y,y)$ by strictness. The equality of arrows converts it into a
composite realizer with some intermediate point $y'$. Its inclusion component contains $y'\sim_Y y$ and $\psi(y')$,
so extensionality of $\psi$ returns $\psi(y)$. This proves $\varphi\le\psi$ uniformly. Applying the same argument
to an inverse isomorphism proves $\psi\le\varphi$.
\end{proof}

\begin{mathmeta}
  \define{RealizabilityTruthValues}
\end{mathmeta}

\begin{proposition*}[\termdefineas{realizability truth-value object}{Truth values and characteristic relations}]
Define
$$\RealizabilityTruthValues:=\Pair{\PowerSet{\NN}}{\sim_\Omega},\qquad
S\sim_\Omega T:=(S\to T)\land(T\to S).$$
This is a realizability PER. Its predicate $\sigma(S):=S$ is strict and extensional. For each strict extensional
predicate $\varphi$ on $X$, the relation
$$\chi_\varphi(x,S):=E_X(x)\land\bigl(\varphi(x)\sim_\Omega S\bigr)$$
is functional. Conversely, for a functional relation $F:X\to\RealizabilityTruthValues$, put
$$D_F(x):=\bigcup_{S\IncludedIn\NN}\bigl(F(x,S)\land S\bigr).$$
This is strict and extensional, and $F\equiv\chi_{D_F}$. Finally,
$$\chi_\varphi=\chi_\psi\quad\Longleftrightarrow\quad
\varphi\le\psi\ \text{and}\ \psi\le\varphi$$
as arrows, with both predicate reductions uniform over $X$.
\end{proposition*}

\begin{proof}[Proof]
Symmetry exchanges the two implication realizers. Transitivity composes them in the appropriate directions, using the
implication adjunction proved in §{sec:effective-topos-construction}. Identity implications supply extent realizers
uniformly for every $S$, so $\sigma$ is strict. From $S\sim_\Omega T$ and a realizer in $S$, applying the first
implication realizer returns one in $T$, proving extensionality of $\sigma$.
For $\chi_\varphi$, an $X$-equality realizer gives a transformer from $\varphi(x)$ to $\varphi(x')$ by extensionality,
and symmetry gives the reverse transformer. Parameter abstraction turns these into the two implication codes,
so the representative map $x\mapsto\varphi(x)$ uniformly preserves equality. Its graph relation from
§{sec:effective-topos-finite-limits} is exactly the displayed $\chi_\varphi$.

We will use the following consequence of totality and single-valuedness: if $A\le B$ uniformly for two functional
relations with the same source and target, then $B\le A$ as well. Given a $B(x,y)$ realizer, strictness and totality
of $A$ produce an $A(x,y')$ realizer for some $y'$. The assumed reduction turns it into a $B(x,y')$ realizer.
Single-valuedness of $B$ gives $y'\sim y$, and extensionality of $A$ returns an $A(x,y)$ realizer.
All operations use the fixed trackers, so this is a uniform reverse reduction.

For a given $F$, strictness of $D_F$ follows by applying strictness of $F$ to the first component. For
extensionality, transport that $F$ realizer along equality in $X$ and retain the second component in the same $S$.
To prove $F\le\chi_{D_F}$, fix $a\in F(x,S)$. Strictness supplies $E_X(x)$. The transformation
$$s\longmapsto\NatPair{a}{s}$$
sends $S$ into $D_F(x)$. In the other direction, a realizer $\NatPair{b}{t}$ of $D_F(x)$ has
$b\in F(x,T)$ and $t\in T$ for some $T$. Single-valuedness applied to $a,b$ returns a realizer of
$S\sim_\Omega T$. Apply its second implication to $t$ to obtain an element of $S$.
These two transformations are uniform in $a$; parameter abstraction gives the implication codes witnessing
$D_F(x)\sim_\Omega S$. Pairing with the extent realizer proves $F\le\chi_{D_F}$, and the preceding observation
proves equivalence.

For $F=\chi_\varphi$, the construction recovers $\varphi$ up to uniform equivalence. A realizer of $D_{\chi_\varphi}(x)$
contains an $S$ realizer and an implication $S\to\varphi(x)$, which together give a $\varphi(x)$ realizer.
Conversely, a $\varphi(x)$ realizer gives the source extent by strictness. Pair it with an extent realizer of
$\varphi(x)$ in the truth-value PER to obtain a $\chi_\varphi(x,\varphi(x))$ realizer, and pair that output with the
original input. This realizes $D_{\chi_\varphi}(x)$. Hence
$$D_{\chi_\varphi}\equiv\varphi.$$
The sets of realizer numbers need not be literally equal.

If $\varphi\equiv\psi$, the two uniform reductions give implication codes between $\varphi(x)$ and $\psi(x)$.
Composing them with a realizer of $\varphi(x)\sim_\Omega S$ gives one of $\psi(x)\sim_\Omega S$ while preserving
the source extent. Thus $\chi_\varphi\equiv\chi_\psi$. Conversely, a uniform reduction between two functional
relations preserves their $D$ predicates: transform the relation realizer and retain the truth-value realizer.
Applying this to both directions of $\chi_\varphi\equiv\chi_\psi$, then using the recovery just proved, gives
$\varphi\equiv\psi$. This proves the asserted uniqueness.
\end{proof}

#### Classification by Pullback {#sec:effective-topos-classifier}

\begin{mathmeta}
  \define{RealizabilityTruthArrow}
  \vars{a}{Nat}
\end{mathmeta}

\begin{theorem*}[\termdefineas{realizability subobject classifier}{Subobject classifier in realizability}]
The functional relation
$$\RealizabilityTruthArrow\Pair{\ast}{S}:=S$$
represents a monomorphism $\RealizabilityTruthArrow:1\to\RealizabilityTruthValues$.
For each strict extensional predicate $\varphi$ on $X$, the square
$$\begin{array}{ccc}
\PERRestriction{X}{\varphi} & \xrightarrow{J_\varphi} & X\\
{\scriptstyle T_{\PERRestriction{X}{\varphi}}}\downarrow & & \downarrow{\scriptstyle\chi_\varphi}\\
1 & \xrightarrow{\RealizabilityTruthArrow} & \RealizabilityTruthValues
\end{array}$$
is a pullback. More generally, every monomorphism $m:U\to X$ has a unique arrow
$\chi_m:X\to\RealizabilityTruthValues$ for which the square with top edge $m$, left edge $T_U$, and bottom edge
$\RealizabilityTruthArrow$ is a pullback. Thus $\RealizabilityTruthArrow$ is a subobject classifier in the sense of
Appendix §{sec:cat-toposes}. If $M$ represents $m$, one may take $\chi_m=\chi_{\varphi_M}$.
\end{theorem*}

\begin{proof}[Proof]
First verify the four conditions for the truth relation. Strictness supplies an arbitrary natural number as the
terminal extent and uses the two identity implications for the extent of $S$.
Extensionality applies the forward implication in $S\sim_\Omega T$ to the input in $S$.
For single-valuedness, realizers $s\in S$ and $t\in T$ give constant programs with values $t$ and $s$, respectively;
parameter abstraction supplies codes realizing both implications. Totality uses $S=\NN$ and retains the input.
This proves that the relation is functional. It is monic because its domain is terminal.

This relation also agrees with the graph of the representative map $\ast\mapsto\NN$.
Indeed, from an input in $S$ one obtains an implication $\NN\to S$ by a constant program, while the reverse
implication has unrestricted output. These codes and the terminal extent give the graph realizer.
The uniform inclusion between the two functional relations is an equivalence by the preceding proof.

To check commutativity, take realizers of $J_\varphi(x,x')$ and $\chi_\varphi(x',S)$.
The first supplies $x\sim_X x'$ and $\varphi(x)$. Extensionality of the predicate gives $\varphi(x')$, and the
forward implication from the second realizer gives an element of $S$.
The first realizer also supplies $E_{\PERRestriction{X}{\varphi}}(x)$.
Pairing these outputs realizes $(\RealizabilityTruthArrow\circ T_{\PERRestriction{X}{\varphi}})\Pair{x}{S}$, using the
intermediate point $\ast$. This is a uniform reduction from $\chi_\varphi\circ J_\varphi$ to
$\RealizabilityTruthArrow\circ T_{\PERRestriction{X}{\varphi}}$. Again, an inclusion between functional relations
is an equivalence, so the square commutes.

For the universal property, suppose functional relations $H:Z\to X$ and $K:Z\to1$ satisfy
$$\chi_\varphi\circ H\equiv\RealizabilityTruthArrow\circ K$$
and fix a tracker $c$ for the forward reduction. Given $a\in H(z,x)$, strictness gives $E_X(x)$, and the two
identity implications give $\varphi(x)\sim_\Omega\varphi(x)$.
Together they form, uniformly in $a$, a realizer
$$g(a)\in\chi_\varphi(x,\varphi(x)).$$
Thus $\NatPair{a}{g(a)}$ realizes the left composite at $\varphi(x)$. Compute
$$\NatPair{b_0}{b_1}=c\cdot\NatPair{a}{g(a)}.$$
By the defining value of the truth relation, $b_1\in\varphi(x)$. Projecting this numerical pair proves
$H(z,x)\le\varphi(x)$ uniformly. The restriction lemma now gives a factorization $L:Z\to\PERRestriction{X}{\varphi}$
with $J_\varphi\circ L=H$. Its composite with the arrow to $1$ is $K$, by uniqueness of arrows to a terminal object.
The factorization is unique because $J_\varphi$ is monic. This proves the pullback property.

For a general monomorphism $m:U\to X$ represented by $M$, the predicate presentation already proved gives
an isomorphism $e:U\cong\PERRestriction{X}{\varphi_M}$ over $X$.
Transporting the preceding pullback along this isomorphism gives the classifying square for
$\chi_{\varphi_M}$. Suppose another arrow $f:X\to\RealizabilityTruthValues$ gives a pullback with the same $m$.
Write $f=\chi_\psi$ using the truth-value normal form. Its canonical pullback is $J_\psi$.
Uniqueness of pullbacks gives an isomorphism over $X$ between the two predicate restrictions.
The predicate-presentation result therefore gives $\varphi_M\equiv\psi$ uniformly.
By the uniqueness result for characteristic relations, $f=\chi_{\varphi_M}$.
This proves the universal property for every monomorphism, including uniqueness of its characteristic arrow.
\end{proof}

### Function Objects and Evaluation {#sec:effective-topos-function-objects}

\begin{mathmeta}
  \define{UniformTrackers,FunctionalRealizers,RealizabilityFunctionSpace}
  \forward{evalMap}
  \vars{e}{Nat}
  \vars{a,b,r,s,t,v}{Nat}
\end{mathmeta}

For families $\varphi,\psi:J\to\PowerSet{\NN}$, write
$$\UniformTrackers{\varphi}{\psi}:=
\{e\in\NN:\forall j\in J\ \forall a\in\varphi(j),\ e\cdot a\downarrow\in\psi(j)\}.$$
The index must work uniformly in the semantic parameter $j$; that parameter is not an input to the program.
For relations $R,S:\UnderlyingSet{X}\times\UnderlyingSet{Y}\to\PowerSet{\NN}$, use
$J=\UnderlyingSet{X}\times\UnderlyingSet{Y}$ in $\UniformTrackers{R}{S}$.

\begin{lemma*}[\termdefineas{uniform tracker abstraction}{Abstraction of uniform trackers}]
Let $\Gamma:I\to\PowerSet{\NN}$ and $\varphi,\psi:I\times J\to\PowerSet{\NN}$ be predicates.
Suppose one index $e$ transforms every pair of realizers of $\Gamma(i)$ and $\varphi(i,j)$ into a realizer of
$\psi(i,j)$, uniformly in $i,j$. From each $a\in\Gamma(i)$ one can uniformly compute an index in
$\UniformTrackers{\varphi(i,-)}{\psi(i,-)}$. Uniform trackers can also be applied and composed by fixed lambda programs.
\end{lemma*}

\begin{proof}[Proof]
Use the code factory from §{sec:effective-topos-construction}. On input $a$, it returns the code $c(e,a)$ of the
program that sends $b$ to $e\cdot\NatPair{a}{b}$, without running that program.
For every $j$, the hypothesis proves that this same code sends $\varphi(i,j)$ into $\psi(i,j)$.
Neither the code nor its construction depends on $j$. Application uses the universal evaluator.
For composition, abstract the numerical input after applying the first code and then the second; this again uses
one code for all semantic parameters. Identity programs supply the reflexive case.
\end{proof}

For an arbitrary relation $R:\UnderlyingSet{X}\times\UnderlyingSet{Y}\to\PowerSet{\NN}$, let $\FunctionalRealizers{R}$
be the set of numbers
$$\NatPair{s}{\NatPair{e}{\NatPair{v}{t}}}$$
whose four entries track strictness, extensionality, single-valuedness, and totality, respectively. Explicitly, they
must satisfy all of the following conditions, uniformly in the displayed representatives:
\begin{enumerate}
\item If $a\in R(x,y)$, then $s\cdot a\downarrow\in E_X(x)\land E_Y(y)$.
\item If $r\in(x\sim_X x')$, $a\in R(x,y)$, and $b\in(y\sim_Y y')$, then
$$e\cdot\NatPair{\NatPair{r}{a}}{b}\downarrow\in R(x',y').$$
\item If $a\in R(x,y)$ and $b\in R(x,y')$, then
$$v\cdot\NatPair{a}{b}\downarrow\in(y\sim_Y y').$$
\item If $r\in E_X(x)$, then
$$t\cdot r\downarrow\in\bigcup_{y\in\UnderlyingSet{Y}}R(x,y).$$
\end{enumerate}
The last output is a realizer in the union; it need not encode a representative $y$.

\begin{proposition*}[\termdefineas{realizability function object}{Function object and evaluation}]
On the set of all relations $\UnderlyingSet{X}\times\UnderlyingSet{Y}\to\PowerSet{\NN}$, define
$$\begin{aligned}
R\sim_{\RealizabilityFunctionSpace{X}{Y}}S
&:=\bigl(\FunctionalRealizers{R}\land\FunctionalRealizers{S}\bigr)\\
&\quad\land\bigl(\UniformTrackers{R}{S}\land\UniformTrackers{S}{R}\bigr).
\end{aligned}$$
This defines a realizability PER $\RealizabilityFunctionSpace{X}{Y}$.
A representative has inhabited extent exactly when it is a functional relation. The relation
$$\evalMap\Pair{\Pair{R}{x}}{y}:=E_{\RealizabilityFunctionSpace{X}{Y}}(R)\land R(x,y)$$
is functional and hence defines an arrow
$$\evalMap:\RealizabilityFunctionSpace{X}{Y}\times X\longrightarrow Y.$$
\end{proposition*}

\begin{proof}[Proof]
Symmetry exchanges the two data tuples and the two conversion indices. Transitivity retains the data at the first
and last endpoints and composes the conversion indices in the appropriate directions by the preceding lemma.
This proves the PER laws uniformly. Its extent projects to $\FunctionalRealizers{R}$. Conversely, a number in
$\FunctionalRealizers{R}$ can be duplicated and paired with two identity-conversion indices to realize the extent.
Thus the extent and $\FunctionalRealizers{R}$ are uniformly equivalent.
By the definition of that set, an element supplies the four tracking indices of a functional relation, and any
functional relation supplies such a tuple. This proves the assertion about inhabited extent.

For evaluation, an input realizer contains an extent realizer for $R$ and an element of $R(x,y)$.
Extract the strictness index $s$ from the former and apply it to the latter. Its output gives $E_X(x)$ and $E_Y(y)$;
together with the retained extent of $R$, this proves strictness of evaluation.
For single-valuedness, extract $v$ and apply it to the two relation realizers at the same $x$.
For extensionality, suppose the inputs also give $R\sim S$, $x\sim_X x'$, and $y\sim_Y y'$.
The index $e$ from the data for $R$ transforms the $R(x,y)$ realizer into one for $R(x',y')$.
The forward conversion in $R\sim S$ then gives an $S(x',y')$ realizer, and the PER laws give the extent of $S$.
Pairing these outputs proves extensionality of evaluation.

Finally, an extent realizer for $\Pair{R}{x}$ supplies the extent of $R$ and an $E_X(x)$ realizer $r$.
Extract $t$ from the relation data and compute $b=t\cdot r$. There is some $y$ with $b\in R(x,y)$.
Pairing $b$ with the retained extent of $R$ realizes $\evalMap\Pair{\Pair{R}{x}}{y}$.
The program computes that pair; the existence of $y$ proves membership in the union required for totality.
This verifies all four conditions for evaluation.
\end{proof}

#### Currying and the Exponential Universal Property {#sec:effective-topos-exponentials}

\begin{mathmeta}
  \define{CurriedRelation,UncurriedRelation}
  \forward{HomSet}
  \vars{a,b,c,d,r}{Nat}
\end{mathmeta}

\begin{lemma*}[\termdefineas{uniform realizability currying}{Uniform currying}]
Let $H:Z\times X\to Y$ be a functional relation, and set $R_z(x,y):=H(\Pair{z}{x},y)$.
One fixed program transforms every $a\in E_Z(z)$ into an element of $\FunctionalRealizers{R_z}$.
Moreover, the assignment $z\mapsto R_z$ uniformly preserves equality, so
$$\CurriedRelation{H}(z,R):=E_Z(z)\land(R_z\sim_{\RealizabilityFunctionSpace{X}{Y}}R)$$
is a functional relation from $Z$ to $\RealizabilityFunctionSpace{X}{Y}$.
\end{lemma*}

\begin{proof}[Proof]
Fix trackers for the four conditions on $H$, and use the notation $\ell_H,r_H,q_H,v_H,u_H$ from
§{sec:effective-topos-objects-morphisms}. Write $\pi_0,\pi_1$ for the numerical pair projections.
Given $a\in E_Z(z)$, the four required programs act as follows:
$$\begin{aligned}
 b&\longmapsto\NatPair{\pi_1(\ell_H(b))}{r_H(b)},\\
 \NatPair{\NatPair{r}{b}}{c}&\longmapsto q_H(\NatPair{a}{r},b,c),\\
 \NatPair{b}{c}&\longmapsto v_H(b,c),\\
 r&\longmapsto u_H(\NatPair{a}{r}).
\end{aligned}$$
The first program discards the $Z$-extent from strictness of $H$. The second uses $a$ to keep $z$ fixed while
transporting $x$ and $y$. The third is single-valuedness of $H$. The last supplies totality of $H$ with the
paired extent of $\Pair{z}{x}$. Uniform tracker abstraction computes all four indices from $a$ before any of these
programs is run, and pairs them to obtain an element of $\FunctionalRealizers{R_z}$.
The raw slice $R_z$ exists even when $E_Z(z)$ is empty; no functionality is asserted without an extent realizer.

Given $d\in(z\sim_Z z')$, the PER laws supply extents for $z,z'$, hence data for both slices.
For $b\in R_z(x,y)$, the program
$$b\longmapsto q_H(\NatPair{d}{\pi_1(\ell_H(b))},b,r_H(b))$$
produces an element of $R_{z'}(x,y)$. Abstracting $d$ yields one conversion index for every $x,y$.
Symmetry in $Z$ gives the reverse conversion. These two indices and the two data tuples realize $R_z\sim R_{z'}$.
The graph construction in §{sec:effective-topos-finite-limits} now proves that $\CurriedRelation{H}$ is functional.
\end{proof}

For a functional relation $F:Z\to\RealizabilityFunctionSpace{X}{Y}$, define its application relation by
$$\UncurriedRelation{F}(\Pair{z}{x},y):=
 \bigcup_{R\in\UnderlyingSet{\RealizabilityFunctionSpace{X}{Y}}}\bigl(F(z,R)\land R(x,y)\bigr).$$
Its realizers are numerical pairs $\NatPair{a}{b}$. The relation $R$ witnessing membership is not part of the code.

\begin{lemma*}[\termdefineas{realizability application relation}{Application relation}]
The relation $\UncurriedRelation{F}$ is functional, and as an arrow it equals
$$\UncurriedRelation{F}=\evalMap\circ(F\times\mathrm{id}_X).$$
Uniformly equivalent $F$ give uniformly equivalent application relations.
\end{lemma*}

\begin{proof}[Proof]
Suppose $a\in F(z,R)$ and $b\in R(x,y)$. Strictness of $F$ gives extents for $z,R$.
Extract the data for $R$ and apply its strictness program to $b$ to obtain extents for $x,y$.
This proves strictness of the application relation. For extensionality, transport $a$ along $z\sim_Z z'$ using
$F$, keeping $R$ fixed, and transport $b$ along $x\sim_X x'$ and $y\sim_Y y'$ using the data for $R$.
Pair the two outputs. For single-valuedness, two inputs may use different relations $R,S$.
Single-valuedness of $F$ gives $R\sim S$; convert the $S(x,y')$ realizer to $R(x,y')$, then use single-valuedness
from the data for $R$.

For totality, from extents for $z,x$ first compute $a\in F(z,R)$ for some $R$ by totality of $F$.
Strictness of $F$ supplies data for $R$, whose totality program gives $b\in R(x,y)$ for some $y$.
Return $\NatPair{a}{b}$. Neither $R$ nor $y$ has to be computed as a representative.
All programs are uniform over the semantic witnesses, so existential elimination preserves these trackers.

To compare with evaluation, the same $a,b$ and strictness outputs give a realizer of
$F\times\mathrm{id}_X$ at $\Pair{\Pair{z}{x}}{\Pair{R}{x}}$ and a realizer of evaluation at $\Pair{\Pair{R}{x}}{y}$.
Pairing them proves one uniform inclusion into the composite. Both relations are functional, so
§{sec:effective-topos-subobjects-truth-values} gives their uniform equivalence.
Finally, a fixed conversion $F(z,R)\to G(z,R)$ acts on the first entry of $\NatPair{a}{b}$ and leaves the
second entry unchanged. This proves preservation of uniform equivalence.
\end{proof}

\begin{theorem*}[\termdefineas{realizability exponential universal property}{Exponential universal property}]
For every arrow $h:Z\times X\to Y$, there is a unique arrow
$f:Z\to\RealizabilityFunctionSpace{X}{Y}$ with
$$\evalMap\circ(f\times\mathrm{id}_X)=h.$$
It is represented by $\CurriedRelation{H}$ for any functional relation $H$ representing $h$.
Consequently $Y^X=\RealizabilityFunctionSpace{X}{Y}$ is an exponential object.
\end{theorem*}

\begin{proof}[Proof]
First, a realizer of $\UncurriedRelation{\CurriedRelation{H}}(\Pair{z}{x},y)$ supplies some $R$, a realizer of
$R_z\sim R$, and a realizer of $R(x,y)$. Applying the reverse conversion gives a realizer of
$R_z(x,y)=H(\Pair{z}{x},y)$. The two relations are functional, so this inclusion proves
$$\UncurriedRelation{\CurriedRelation{H}}\equiv H.$$

Conversely, fix $a\in F(z,R)$ and put $S_z(x,y):=\UncurriedRelation{F}(\Pair{z}{x},y)$.
Strictness of $F$ gives data for $R$ and an extent for $z$; uniform currying applied to
$\UncurriedRelation{F}$ gives data for $S_z$.
The program $b\mapsto\NatPair{a}{b}$ sends every $R(x,y)$ into $S_z(x,y)$.
For the reverse direction, an input in $S_z(x,y)$ has the form $\NatPair{c}{b}$ with
$c\in F(z,T)$ and $b\in T(x,y)$ for some $T$.
Single-valuedness of $F$ applied to $c,a$ yields $T\sim R$; its forward conversion sends $b$ into $R(x,y)$.
Abstracting $a$ computes both conversion indices, uniformly in $x,y,T$.
Together with the two data tuples they realize $S_z\sim R$. Pair with the extent of $z$ to obtain
$\CurriedRelation{\UncurriedRelation{F}}(z,R)$. Again one inclusion suffices, giving
$$F\equiv\CurriedRelation{\UncurriedRelation{F}}.$$

If $H\equiv K$, their fixed conversion programs also convert the slices at every $z$.
Pairing these indices with the slice data computed from $E_Z(z)$ gives $R_z^H\sim R_z^K$ uniformly.
Transitivity then converts the two graph relations, so currying descends to arrows.
Together with the preceding lemma, the two identities give inverse bijections
$$\HomSet{\EffCat}{Z\times X}{Y}\ \cong
  \HomSet{\EffCat}{Z}{\RealizabilityFunctionSpace{X}{Y}}.$$
The inverse sends $f$ to $\evalMap\circ(f\times\mathrm{id}_X)$, proving existence and uniqueness.

For completeness, this bijection is natural in the parameter: for $k:W\to Z$,
$$\UncurriedRelation{f\circ k}=\UncurriedRelation{f}\circ(k\times\mathrm{id}_X).$$
This follows from the expression for the inverse map in terms of evaluation, together with functoriality of products.
Thus the bijection defines the right adjoint to $-\times X$; on a morphism $g:Y\to Y'$ it takes
the transpose of $g\circ\evalMap$. Product symmetry gives the right adjoint to $X\times-$ as well.
This supplies the cartesian closed structure on the category.
\end{proof}

### The Topos Theorem {#sec:effective-topos-topos-theorem}

\begin{theorem*} $\EffCat$ is an elementary topos.

\end{theorem*}

\begin{proof}[Proof]
Finite limits were constructed in §{sec:effective-topos-finite-limits}, the subobject classifier in
§{sec:effective-topos-classifier}, and exponentials with their universal property in
§{sec:effective-topos-exponentials}. These are precisely the defining structures of an elementary topos.
\end{proof}

<!-- formalization: skip-begin (reference for the general tripos-to-topos theorem) -->
This concrete construction is an instance of the general tripos-to-topos theorem; see [@vanOosten2008, Ch. 2].
<!-- formalization: skip-end -->

## Internal Logic: Classical Sheaves and Constructive Realizability {#sec:tripos-internal-logic-comparison}
\index{double-negation sheaf}
\index{effective topos!internal logic}

<!-- formalization: skip-begin (comparison and application guidance after the formalized quantifier calculation) -->

The \termdefine{internal logic} of a topos is the logic interpreted by its objects, morphisms, and subobjects. The
tripos-to-topos construction makes the logical difference between forcing and realizability visible. Both start with
nontrivial truth values, but they organize those truth values differently.
<!-- formalization: skip-end -->

For a complete Boolean algebra $\mathbb B$, forcing is classical. The Boolean operations decide every truth value by
$$
[\![\varphi\lor\neg\varphi]\!]=1_{\mathbb B}.
$$

After evaluating at an $M$-generic filter $G$, the Boolean-valued semantics collapses to the ordinary two-valued truth
of $M[G]$. Thus forcing changes the universe while retaining classical first-order logic.

<!-- formalization: skip-begin (general localic sheaf semantics and Booleanization background) -->
For a general locale $\Omega$, sheaf semantics is intuitionistic. A proposition may hold only locally, and the law of
excluded middle can fail because an open need not have an open complement. The double-negation topology extracts the
Boolean part: the subtopos of $\neg\neg$-sheaves is the Booleanization of the sheaf topos. In forcing language, this is
the passage from open-ended local truth to a classical quotient where dense truth is identified with truth.
<!-- formalization: skip-end -->

The effective topos is intuitionistic for a different reason. Its truth values are not opens in a space of conditions;
they are sets of realizers. A proof of $\varphi\lor\psi$ must choose a side and provide evidence for it. A proof of
$\varphi\to\psi$ must be a computable transformer from realizers of $\varphi$ to realizers of $\psi$. Excluded middle
would require a uniform algorithm deciding which side of every proposition has evidence, and the halting problem blocks
such a uniform decision.

<!-- formalization: skip-begin (internal logic comparison table and reading guidance) -->
The comparison is:

| semantics | truth values | internal logic | classical recovery |
|-----------|--------------|----------------|--------------------|
| Boolean forcing | complete Boolean algebra | classical | evaluate at a generic filter |
| localic sheaves | frame of opens | intuitionistic | pass to $\neg\neg$-sheaves |
| Kleene realizability | index sets | computationally intuitionistic | Booleanization loses computable content |

This is why the same tripos-to-topos pattern supports two different uses in this book. Forcing asks which classical
statements survive when the surrounding universe changes. Realizability asks which statements have computable evidence
when the universe itself is read constructively.

<!-- formalization: skip-end -->
