# Forcing and Polish Spaces {#sec:forcing}

<!-- formalization: skip-begin (chapter synthesis) -->
Forcing turns topology into a method for changing the set-theoretic universe. Cohen forcing is Baire category written as
finite-prefix extension; \termforward{random forcing} is measure theory written as positive-measure refinement.
This lets
one prove independence results about familiar Polish-space objects without leaving the language of dense open sets, null
ideals, Borel codes, and generic points.

The chapter also explains why regularity theorems have exact set-theoretic limits. ZFC proves regularity at the Borel
and analytic levels, but forcing shows that higher projective regularity depends on additional axioms. Thus forcing is
not an external detour from descriptive set theory; it is the mechanism that tells us which parts of the Polish-space
picture are absolute and which parts are contingent on the surrounding universe.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter overview and external forcing infrastructure) -->
The deepest interactions between Polish spaces and 20th-century set theory go through Paul Cohen's method of
**\termdefine{forcing}**, introduced in 1963 to prove the independence of the continuum hypothesis. Forcing builds a
controlled extension $M[G]$ of a ground model $M$ by adjoining a generic object. In Polish-space applications the
generic object is usually a point of a familiar space — a Cohen real in $\CantorSpace$, a random real in
$\ClosedInterval{0}{1}$, or a
branch through a tree — and the forcing conditions are finite or approximate pieces of information about that point.

The construction has two layers:

1.  **Combinatorial layer.** A partial order $P$ describes finite information. Dense subsets of $P$ describe
    requirements. A generic filter meets all requirements visible in the ground model.
\begin{mathmeta}
  \define{forces}
\end{mathmeta}

2.  **Semantic layer.** $P$-names describe objects in the future extension. The forcing relation $p \forces \varphi$
    says that the finite information $p$ already guarantees the truth of $\varphi$ in every generic extension containing
    $p$.

The general set-theoretic infrastructure for forcing — ground models, names, valuation, the forcing relation, the
forcing theorem, and generic extensions — is collected in Appendix §{sec:appendix-forcing-background}. This chapter
keeps only the Polish-space uses in view: forcing notions whose conditions are finite, topological, or measure-theoretic
approximations to points of Polish spaces, and the absoluteness and regularity consequences that
follow.\termref{absoluteness}

Throughout the concrete forcing subsections, $M$ denotes a countable transitive ground model of enough set theory and
$G$ denotes an $M$-generic filter in the surrounding universe. Statements such as "the generic real is new" or "the
generic real avoids every ground-model null set" are external statements about the extension $M[G]$ and the objects
coded in $M$, not internal assertions about all reals in the surrounding universe.

Whenever a meager or null Borel set is coded in $M$, smallness means the value computed in $M$ from that code. The
external interpretation agrees by the Borel-code absoluteness in §{sec:borel-codes-why}. If a new real is tested for
membership, the Borel set likewise means the interpretation of its code in the extension, not the ground-model set of
old reals obtained by evaluating its check name.

Proof scope: this chapter proves the local Polish-space facts about Cohen cylinders, positive-measure Borel
conditions, dense-set requirements, and null/meager avoidance. The basis theorem, generic absoluteness, and
Solovay's regularity theorem are explicitly cited external results. The forcing theorem, the truth lemma, and
the internal recursion defining $p\forces\varphi$ are external infrastructure from Appendix
§{sec:appendix-forcing-background}.

<!-- formalization: skip-end -->

For Polish-space applications, the main working principle is: to show that every generic extension satisfies a statement
about a named Polish-space object, it suffices to show that every condition has a stronger condition forcing that
statement. This is the forcing form of a dense-set argument.

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Begin with finite-prefix trees, Baire category, and Borel codes in §{sec:closed-sets-trees},
§{sec:baire-category}, and §{sec:borel-codes}. Random forcing also uses the measure-algebra results in
§{sec:measure-algebras-maharam}. Read the statements about names, valuation, and forcing truth in
§{sec:forcing-names-valuation} and §{sec:forcing-relation} before using generic extensions. To verify those
foundations, first study §{sec:internal-model-closure}; for the random case, continue through
§{sec:appendix-borel-absoluteness}, §{sec:appendix-measure-absoluteness}, and §{sec:appendix-random-forcing}.
These internal constructions can be deferred while learning the generic-point examples. The goal is to
separate topological genericity from the model-dependent assertion that all coded requirements have been met.

<!-- formalization: skip-end -->

## Cohen Forcing in Detail {#sec:cohen-forcing-detail}

\begin{mathmeta}
  \vars{c,x}{Name}
  \vars{n}{Nat}
  \vars{p,s,t,u}{Seq}
  \vars{c_G}{Name}
  \vars{s_*}{Seq(Nat)}
\end{mathmeta}

The poset called \termdefine{Cohen forcing} is
$$P=\finseq{2}$$
ordered by extension:
$$t \le s \quad\Longleftrightarrow\quad s \prefixOf t.$$
Thus stronger conditions are longer binary strings.

Two conditions are compatible iff one is an initial segment of the other.

For $s \in P$, the corresponding basic open set in Cantor space is the cylinder
$$\cyl{s}=\{x\in\CantorSpace:s\prefixOf x\}.$$
Stronger conditions correspond to smaller cylinders:
$$t \le s \quad\Longleftrightarrow\quad \cyl{t}\IncludedIn \cyl{s}.$$

For each $n$, put
$$D_n:=\{s\in\finseq{2}:\Length{s}>n\}.$$

\begin{lemma*}[Length requirements] The set $D_n$ is dense in Cohen forcing.
\end{lemma*}

\begin{proof}[Proof] Given $s\in\finseq{2}$, append enough zeroes to obtain an extension of length greater than $n$.
\end{proof}

A filter $G\IncludedIn P$ is nonempty, contains every condition weaker than one of its members, and contains a
common extension of any two of its members. We first construct its real using just these properties and the length
requirements; no forcing relation is needed for this construction.

\begin{lemma*}[\termdefineas{Cohen filter union lemma}{Cohen filter union}]
If a filter $G$ meets every $D_n$, there is a unique $c_G\in\CantorSpace$ extending every member of $G$.
Moreover, $G=\{s\in P:s\prefixOf c_G\}$.
\end{lemma*}

\begin{proof}[Proof]
For each $n$, choose $s_n\in G$ with $\Length{s_n}>n$ and set $c_G(n)=s_n(n)$. Given $t\in G$ and $n<\Length{t}$, take a
common
extension of $t$ and $s_n$ in $G$. Its $n$th coordinate shows that $t(n)=s_n(n)=c_G(n)$. Thus every $t\in G$ is a
prefix of $c_G$. The same coordinate argument proves uniqueness, so this sequence is precisely the union $\bigcup G$.
Conversely, let $t\prefixOf c_G$. Choose $s\in G$ longer than $t$. Both are prefixes of $c_G$, so $t\prefixOf s$.
Closure toward weaker conditions gives $t\in G$.
\end{proof}

\begin{lemma*}[\termdefineas{countable Cohen requirements lemma}{Countable Cohen requirements}]
Let $\Sequence{E_n}{n\in\NN}$ be any sequence of dense subsets of $P$, and let $p\in P$. There is a filter containing
$p$
that meets every $E_n$ and every length requirement $D_n$. Consequently there is $c\in\cyl{p}$ such that, for every
$n$, some prefix of $c$ belongs to $E_n$.
\end{lemma*}

\begin{proof}[Proof]
Put $p_0=p$. Given $p_n$, first extend it to a string of length greater than $n$, then use density to choose a
further extension $p_{n+1}\in E_n$. Put
$$G=\{s\in P:\exists n\ (s\prefixOf p_n)\}.$$
This set contains $p$ and is closed toward weaker conditions. If $s\prefixOf p_n$ and $t\prefixOf p_m$, then
$p_{\max(n,m)}\in G$ extends both, proving directedness. The condition $p_{n+1}$ meets both $E_n$ and $D_n$.
The preceding lemma supplies the required real. Lengthening before entering $E_n$ is deliberate: a dense set need
not contain every extension of its members, so lengthening afterwards could leave $E_n$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
可算dense族からの外的filter構成はpfilter_meets_countable_denseへ接続済み。残りは既出補題への参照と、
構成を外側の宇宙で行うという適用範囲の説明。filterがMに属するとの追加結論を主張しない。)
--> This is the Cohen-instance of the countable dense-set construction in §{sec:ground-models-forcing-notions}.<!--
formalization: skip-end
-->
Since $M$ is countable in the surrounding universe, enumerate there all its dense subsets of $P$ and apply the
lemma. It produces an $M$-generic filter through any prescribed condition. <!--
formalization: skip-begin (引用・背景説明・読書案内:
可算dense族からの外的filter構成はpfilter_meets_countable_denseへ接続済み。残りは既出補題への参照と、
構成を外側の宇宙で行うという適用範囲の説明。filterがMに属するとの追加結論を主張しない。)
--> The enumeration and the resulting filter
are constructed externally; they need not belong to $M$.<!--
formalization: skip-end
-->

For each ground-model real $x\in M\cap\CantorSpace$, put
$$D_x:=\{s\in\finseq{2}:s\notPrefixOf x\}.$$

\begin{lemma*}[Diagonal requirements] The set $D_x$ is dense in Cohen forcing.
\end{lemma*}

\begin{proof}[Proof] If $s\notPrefixOf x$, use $s$ itself. If $s\prefixOf x$, extend $s$ by the bit opposite to the
next bit of $x$.
\end{proof}

\begin{corollary*}[Newness from diagonal requirements]
If a filter $G$ meets every length requirement and also meets $D_x$, then $c_G\ne x$.
In particular, the real of an $M$-generic filter differs from every real in $M$.
\end{corollary*}

\begin{proof}[Proof]
Choose $s\in G\cap D_x$. The union lemma gives $s\prefixOf c_G$, whereas the definition of $D_x$ gives
$s\notPrefixOf x$. Hence $c_G\ne x$. For $x\in M\cap\CantorSpace$, the dense set $D_x$ belongs to $M$, so an
$M$-generic filter meets it.
\end{proof}

The forcing relation matches the cylinder interpretation. If $s\in\finseq{2}$ and $n<\Length{s}$, then
$$s\forces \dot c(n)=s(n).$$
If $n\ge \Length{s}$, neither value is forced by $s$, but first extend $s$ to a string $t$ of length $n$. The
refinements $t\concat(0)$ and
$t\concat(1)$ then force opposite values at coordinate $n$. In this sense \termuse{Cohen forcing} is the
model-theoretic version of the product topology on
$\CantorSpace$.

A binary sequence $x\in\CantorSpace$ is \termdefineas{disjunctive sequence}{disjunctive} if every finite binary word
occurs somewhere as a consecutive block in $x$.

Fix a finite word $u\in\finseq{2}$ in $M$. Let
$$D_u:=\{s\in\finseq{2}:u\text{ occurs as a consecutive block in }s\}.$$

\begin{lemma*}[Word-occurrence requirements] The set $D_u$ is dense in Cohen forcing.
\end{lemma*}

\begin{proof}[Proof] Given any condition $s$, the concatenation $s\concat u$ extends $s$ and belongs to $D_u$.
\end{proof}

\begin{corollary*}[Disjunctiveness from word requirements]
If a filter $G$ meets every length requirement and every word requirement $D_u$, then $c_G$ is disjunctive.
\end{corollary*}

\begin{proof}[Proof]
Given $u$, choose $s\in G\cap D_u$ and write $s=a\concat u\concat b$. For every $i<\Length{u}$, the union lemma gives
$c_G(\Length{a}+i)=s(\Length{a}+i)=u(i)$. Thus $u$ occurs in $c_G$ at position $\Length{a}$. Every finite binary word
and its dense
requirement belong to the transitive model $M$, so every Cohen real over $M$ is disjunctive.
\end{proof}

This is a useful calibration point. Disjunctiveness is a topologically generic property: the set of disjunctive
sequences is comeager in $\CantorSpace$, because for each word $u$ the union
$\bigcup_{s\in D_u}\cyl{s}$ is dense open and there are only countably many $u$.

<!-- formalization: skip (motivational comparison with computable disjunctive sequences) -->
It is much weaker than
measure-theoretic randomness, since many computable sequences are disjunctive. Cohen forcing therefore captures
Baire-generic behavior, not probabilistic typicality.

## Random Forcing in Detail {#sec:random-forcing-detail}

\begin{mathmeta}
  \vars{c,r}{Name}
  \vars{N,a,b,k,m,n,p}{Nat}
  \vars{s}{Seq}
  \vars{c_G,r_G}{Name}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
正測度Borel集合の実際の非零quotient
conditionとnull差による順序はrandomPositiveCondition/random_condition_orderに接続した。
未リンク部分はCohenの円筒との導入上の比較、random forcingの名称とSolovayへの歴史的帰属であり、
別の条件や定理を構成する箇所ではない。)
--> Cohen forcing approximates a generic real by finite open conditions on cylinders.
\termdefineas{random forcing}{Random forcing},
introduced by Solovay,<!--
formalization: skip-end
-->  approximates it by Borel conditions of positive measure: a condition is no longer "the generic
real begins with $s$" but "the generic real lies in $B$, where $B$ is a Borel set of positive measure". Stronger
conditions are smaller positive-measure subsets, with sets of measure zero ignored.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
非零classと正のmassの同値、null差の順序、正測度交叉による両立性、
全空間の最弱条件を実際のMeasureAlgebra.Positiveへ接続した。未リンク部分は既出の内部商と外的比較についての規約、
およびbinary expansion/Lebesgue空間の同型というMaharam分類を引用する標準的背景である。
旧実数の外部での可算性から内部測度を求める証明としては扱わない。)
--> For forcing over $M$, the following measure-algebra construction is performed inside $M$, and generic filters
are taken on its internal positive part. Measures in the displayed forcing calculations are the values computed
there from Borel codes. These agree with measures of the codes' external interpretations, not with measures of
the sets of old reals viewed as countable external sets.
Fix the fair-coin Bernoulli measure $\mu$ on $\CantorSpace$. The binary expansion gives the usual equivalence with
Lebesgue measure on $\ClosedInterval{0}{1}$; at the level needed here, this is also the simplest case of the Maharam
classification in
§{sec:measure-algebras-maharam}.<!--
formalization: skip-end
-->  Let
$$Q := \MeasureAlg{\CantorSpace}{\mu}$$
be the \termuse{measure algebra} of §{sec:measure-algebras-maharam}, and let
$Q_+ := \{[B] \in Q : \mu(B) > 0\}$ be the
*positive-measure* elements. The forcing notion is $Q_+$ under inclusion mod null:
$$[B'] \le [B] \quad\Longleftrightarrow\quad \mu(\SetDifference{B'}{B}) = 0.$$
Two conditions are compatible iff $\mu(B \cap B') > 0$; they are incompatible iff $\mu(B \cap B') = 0$. The weakest
condition is $1_Q := [\CantorSpace]$.


All Boolean operations in $Q$ are operations on equivalence classes modulo null sets:
$[B]\vee[C]=[B\cup C]$, $[B]\wedge[C]=[B\cap C]$, and $[B]\le[C]$ means $\SetDifference{B}{C}$ is null. With this
convention, we have the following two facts.

\begin{lemma*}[Completeness] The measure algebra $Q$ is a \termdefine{complete Boolean algebra}: every family
$\mathcal F\IncludedIn Q$, even an uncountable one, has a supremum.
\end{lemma*}

\begin{proof}[Proof] Choose Borel representatives for the elements of $\mathcal F$, and set
$$
\alpha:=\sup\{\mu(B_0\cup\cdots\cup B_{k-1}):[B_i]\in\mathcal F,\ k<\omega\},
$$
where the empty union is allowed. Choose finite unions $U_n$ from representatives in $\mathcal F$ whose measures
increase to $\alpha$; when
$\alpha=0$, take all of them empty. Put $U:=\bigcup_n U_n$. The sets $U_n$ need not be increasing, but their finite
partial unions are increasing and still belong to the family used to define $\alpha$. Their measures are bounded
above by $\alpha$ and below by $\mu(U_n)$. Continuity from below therefore gives
$$\mu(U)=\alpha.$$
If $[B]\in\mathcal F$, then
$$
\mu(U\cup B)=\lim_N\mu\bigl(B\cup U_0\cup\cdots\cup U_N\bigr)\le\alpha=\mu(U),
$$
so $\mu(\SetDifference{B}{U})=0$ and $[B]\le[U]$. Thus $[U]$ is an upper bound. If $[C]$ is any upper bound for
$\mathcal F$, then every representative from $\mathcal F$ is contained in $C$ modulo null, so each $U_n$ is contained in
$C$ modulo null. Hence $U\IncludedIn C$ modulo null, and $[U]\le[C]$. Thus $[U]$ is the supremum of $\mathcal F$.
\end{proof}

\begin{lemma*}[\termdefineas{countable chain condition}{Countable chain condition (ccc)}] Every antichain in $Q_+$ is
countable.
\end{lemma*}

\begin{proof}[Proof] Let $\{[B_i]:i\in I\}\IncludedIn Q_+$ be an antichain, and choose representatives with pairwise
null intersections. For each $n\ge1$, only finitely many $i$ can satisfy
$\mu(B_i)\ge1/n$, because the measures of any finite subfamily sum to at most $1$. Since every positive measure is at
least $1/n$ for some $n$, the antichain is countable.
\end{proof}

For a countable family of Borel sets, the supremum has the simpler form
$$\bigvee_n[B_n]=\left[\bigcup_n B_n\right].$$
Indeed, if each $B_n$ is contained in $C$ modulo null, their union is too, since a countable union of null sets is null.
Write $a^c$ for the Boolean complement of $a\in Q$.

\begin{lemma*}[\termdefineas{positive-condition recursion lemma}{Positive-condition recursion}]
For $p\in Q_+$ and $a,a_n\in Q$, the following equivalences hold:
$$p\le a^c\quad\Longleftrightarrow\quad
\neg\exists q\in Q_+\ (q\le p\land q\le a),$$
$$\begin{aligned}
p\le\bigvee_n a_n\quad\Longleftrightarrow\quad
&\forall q\in Q_+\ (q\le p\Longrightarrow{}\\
&\qquad\exists r\in Q_+\ \exists n\ (r\le q\land r\le a_n)).
\end{aligned}$$
\end{lemma*}

\begin{proof}[Proof]
For the first equivalence, $p\le a^c$ excludes a positive common lower bound of $p$ and $a$.
Conversely, if $p\not\le a^c$, then $p\wedge a\ne0$, and this intersection is such a common lower bound.
For the second equivalence, suppose $p\le\bigvee_n a_n$ and $0<q\le p$.
If all $q\wedge a_n$ were zero, distributivity over the countable supremum would give
$$q=q\wedge\bigvee_n a_n=\bigvee_n(q\wedge a_n)=0,$$
a contradiction. Thus $r=q\wedge a_n$ is positive for some $n$ and is the required refinement.
Conversely, if $p\not\le\bigvee_n a_n$, then $q=p\wedge(\bigvee_n a_n)^c$ is positive.
No positive refinement of $q$ lies below any $a_n$, so the asserted density fails.
\end{proof}

These equivalences give a recursive calculation on Borel codes using just the positive-condition order.
At a cylinder leaf, assign its equivalence class. At a complement node, take the Boolean complement of the child's
value;
at a countable-union node, take the supremum of the children's values.

\begin{lemma*}[\termdefineas{Borel code Boolean value lemma}{Boolean values of Borel codes}]
The value assigned to a Borel code by this recursion is the class of its interpreted Borel set.
Moreover, the positive conditions below that value satisfy the same recursion with complement interpreted as
having no stronger condition in the child's forcing set, and countable union as density of the union of the children's
forcing sets.
\end{lemma*}

\begin{proof}[Proof]
Induct on the well-founded code. The leaf case is the definition. The complement step follows because taking a
complement
of a representative induces Boolean complementation. At a union node, the class of the countable union is the supremum
of the children's classes, by the countable-union calculation above. The two assertions about positive conditions follow
at each step from the positive-condition recursion lemma. This also explains why a condition below a countable supremum
need not itself lie below one of its terms: the union clause requires such a term only after a further refinement.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のfilter realとBorel truthの証明への導入。固定した宇宙で明示的仮定を用いるという読み方の案内で、追加の数学的命題ではない。)
--> We now construct the real of a filter and prove Borel truth directly from countably many dense tests.
These arguments take place in a fixed universe, with the hypotheses on the filter stated explicitly.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefineas{random cylinder partition lemma}{Cylinder partitions}]
For each $n$, the cylinders of length $n$ form a maximal antichain
$$A_n := \{[\cyl{s}] : s \in \funcspace{n}{2}\}$$
in $Q_+$, and each cylinder has measure $2^{-n}$. The set
$$C_n:=\{p\in Q_+:\exists s\in\funcspace{n}{2}\ (p\le[\cyl{s}])\}$$
is dense and closed under strengthening.
\end{lemma*}

\begin{proof}[Proof]
A cylinder of length $n$ prescribes $n$ independent bits, each with probability $1/2$, so its measure is $2^{-n}$.
Distinct cylinders of that length are disjoint, and together they partition Cantor space.
Every positive-measure Borel set has positive-measure intersection with one cell of this finite partition.
Intersecting with that cell gives a condition in $C_n$ below the original condition, proving density and maximality.
The definition of $C_n$ also shows that it is closed under strengthening.
\end{proof}

\begin{lemma*}[\termdefineas{random filter union lemma}{Random filter union}]
Let $G$ be a filter on $Q_+$ meeting every $C_n$. There is a unique $r_G\in\CantorSpace$ such that, for every finite
binary string $s$,
$$r_G\in\cyl{s}\quad\Longleftrightarrow\quad[\cyl{s}]\in G.$$
At each length $n$, exactly one cylinder $[\cyl{s_n}]$ belongs to $G$, and $r_G=\bigcup_n s_n$.
This is the \termdefine{random real} associated with the filter when it satisfies the required genericity tests.
\end{lemma*}

\begin{proof}[Proof]
Put $H=\{s:\exists p\in G\ (p\le[\cyl{s}])\}$. It contains the empty string and every prefix of any of its members.
If $s,t\in H$, choose witnessing conditions in $G$ and a common strengthening in $G$.
This positive condition lies below both cylinder classes, so their intersection has positive measure and is nonempty.
A point in the intersection extends both strings; hence one is a prefix of the other. The longer string is a common
extension in $H$.
Thus $H$ is a Cohen filter. Meeting every $C_n$ gives strings of every length in $H$.
The Cohen filter union lemma yields a unique real whose prefixes are exactly $H$.
Upward closure of $G$ gives $s\in H$ iff $[\cyl{s}]\in G$, proving the displayed equivalence.
At each length the real has exactly one prefix, so the last assertions follow as well.
\end{proof}

For a Borel code $c$ with cylinder leaves, write $B_c$ for its interpreted set.
\begin{mathmeta}
  \define{CodeForcingSet,ForcingNeg,ForcingDecision}
\end{mathmeta}
Let $\CodeForcingSet{c}=\{p\in Q_+:p\le[B_c]\}$. The Boolean calculation above identifies its recursion:
at a complement node, no stronger condition belongs to the child's forcing set; at a union node, the union of the
children's forcing sets is dense below the condition.
For any set $S\IncludedIn Q_+$ define
$$\ForcingNeg{S}:=\{p\in Q_+:\forall q\le p\ (q\notin S)\},\qquad
\ForcingDecision{S}:=S\cup\ForcingNeg{S}.$$
The quantifier ranges over positive conditions. The decision set is dense: either a condition has a strengthening in
$S$, or it already belongs to $\ForcingNeg{S}$.
If $S$ is closed under strengthening, so is its decision set.

Associate dense tests to $c$ recursively. A leaf adds no tests. A complement node retains its child's tests and adds
$\ForcingDecision{\CodeForcingSet{d}}$, where $d$ is the child. A union node with children $d_n$ retains all their tests
and adds
$\ForcingDecision{\bigcup_n\CodeForcingSet{d_n}}$. There are only countably many tests: this follows by induction on the
code, taking a countable union at each union node.
Every test is dense and closed under strengthening.

\begin{lemma*}[\termdefineas{random Borel truth lemma}{Borel truth for a random filter}]
Suppose $G$ meets every $C_n$ and every test associated with a Borel code $c$. Then
$$r_G\in B_c\quad\Longleftrightarrow\quad
\exists p\in G\ (p\le[B_c]).$$
\end{lemma*}

\begin{proof}[Proof]
Induct on the code. For a cylinder leaf, the equivalence is the random filter union lemma and upward closure of the
filter.
At a complement node with child $d$, the filter meets $\ForcingDecision{\CodeForcingSet{d}}$.
The positive and negative alternatives cannot both occur in the filter: a common strengthening would belong to the
child's forcing set and also exclude every such strengthening.
By the induction hypothesis, absence of a positive witness is exactly $r_G\notin B_d$.
The decision test supplies a negative witness in that case, and the complement calculation identifies it with a
condition below the complement class.

At a union node with children $d_n$, put $S=\bigcup_n\CodeForcingSet{d_n}$.
If $r_G$ belongs to one child's interpreted set, induction supplies a condition in that child's forcing set, hence one
below the union class.
Conversely, suppose $p\in G$ lies below the union class. Then $S$ is dense below $p$ by the positive-condition recursion
lemma.
Choose $q\in G\cap\ForcingDecision{S}$. If $q\in\ForcingNeg{S}$, a common strengthening of $p$ and $q$ can be further
strengthened into $S$, a contradiction.
Thus $q\in S$, so it belongs to some child's forcing set. Induction puts the real in that child's interpreted set and
hence in the union.
\end{proof}

\begin{corollary*}[Local null-set avoidance]
Under the hypotheses of the Borel truth lemma, if $\mu(B_c)=0$, then $r_G\notin B_c$.
\end{corollary*}

\begin{proof}[Proof]
Otherwise the truth lemma supplies a positive condition below $[B_c]=0$, which is impossible.
For a singleton, a code is given by the intersection of the cylinders of all finite prefixes of the point.
Their measures tend to zero, so the singleton is null. Meeting its tests therefore excludes that point.
\end{proof}

\begin{lemma*}[\termdefineas{countable random requirements lemma}{Countable random requirements}]
Given a countable family of dense subsets of $Q_+$, a countable family of cylinder-based Borel codes, and $p\in Q_+$,
there is a filter containing $p$ that meets every prescribed dense set, every $C_n$, and every test associated with
those codes.
Its real therefore satisfies Borel truth for all those codes and avoids every null set among their interpretations.
\end{lemma*}

\begin{proof}[Proof]
The combined family of dense requirements is countable. Enumerate it, adding the whole order if necessary to handle an
empty family.
Start at the prescribed condition and successively choose a stronger condition in the next dense set.
Take the upward closure of the resulting descending chain. Two members of this closure have a common strengthening
farther along the chain,
so it is a filter. The chosen condition in each dense set belongs to the filter itself; no closure assumption on the
prescribed dense sets is needed.
The length tests construct its real, and the Borel truth and null-set avoidance lemmas give the conclusions.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部商・正条件・比較写像およびfilterの輸送を構成する付録節への明示的参照。新しい局所証明を提示せず、以後で用いる構成を指定している。)
--> For forcing over $M$, use the internal quotient map $q$, its positive classes $P$, and the comparison map $\eta$
constructed in §{sec:internal-null-quotients}.
The construction in §{sec:internal-random-filter-valuation} distinguishes a filter on these internal classes
from its image in the external measure algebra.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \forward{InternalBitCell,FilterTransport,InternalRandomLength,InternalCylinder}
\end{mathmeta}

Let $G$ be a filter on $P$ meeting every internal length requirement $\InternalRandomLength{M}{n}$, and put
$H:=\FilterTransport{\eta}{G}$. Then $H$ meets the external length tests, so it determines a binary sequence $r_H$.
The canonical name records the internal bit decisions:
$$\dot r := \{\Pair{\check{\Pair{n}{i}}}{q(\InternalBitCell{M}{n}{i})} :
 n\in\omega,\;i\in\{0,1\}\}.$$
Each condition has internal measure $\tfrac12$.
The construction in §{sec:internal-null-quotients} places the entire decision table and its name in $M$.
By §{sec:internal-random-filter-valuation}, valuation gives the graph of $r_H$, which therefore belongs to $M[G]$.
Identifying a binary sequence with its graph, we write $r_G:=r_H$ and $\dot r^G=r_G$.

For an $M$-generic filter $G$, the internal length tests belong to $M$ and are dense in $P$, as proved in
§{sec:internal-random-filter-valuation}. Thus genericity supplies the length hypothesis, and the valuation
identity above holds for every such generic filter.

\begin{mathmeta}
  \define{BorelInterpretation,BorelCodeName}
\end{mathmeta}
Let $c\in M$ be a Borel code, and write $\BorelInterpretation{c}{K}$ for its interpretation in a transitive model $K$
containing $c$. The construction in §{sec:internal-random-union-tests} gives a ground-model name
$\BorelCodeName{c}$ with
$$\bigl(\BorelCodeName{c}\bigr)^G=\BorelInterpretation{c}{M[G]}$$
for every $M$-generic filter $G$.
It first constructs a name for all binary point graphs in the extension, then applies the uniform
Borel membership formula by Separation. This is the convention of §{sec:borel-codes-why};
unlike $\check{\BorelInterpretation{c}{M}}$, the valuation of $\BorelCodeName{c}$ may contain new reals.

For countable unions, §{sec:internal-random-union-tests} constructs the required decision sets inside $M$.
A generic filter contains a condition below the class of an internal union exactly when it contains a condition
below the class of one term. At a Borel union node, the entire sequence of child interpretations is constructed
from the code, so this statement applies without assuming that sequence as an additional parameter.

The node induction in §{sec:internal-random-borel-truth} combines the union test with the complement decision.
It applies to the actual real constructed from the generic filter and gives
$$r_G\in\BorelInterpretation{c}{M[G]}
\quad\Longleftrightarrow\quad
\exists p\in G\ (p\le q(\BorelInterpretation{c}{M})).$$
For $p=q(B')$, the order condition is exactly $\mu(\SetDifference{B'}{\BorelInterpretation{c}{M}})=0$.
Here $\mu$ denotes the decoded internal measure, whose value agrees with the external measure of the coded set.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部Borel truthとnull差による順序判定は対応する証明に接続済み。未リンク末尾だけは次の回避結果と後続のforcing
relationの説明への案内。)
--> This argument proves the following avoidance result directly. The identification with the forcing relation
is discussed afterwards.<!--
formalization: skip-end
-->

\begin{proposition*}[Null-set avoidance] Let $c_N\in M$ code a Borel set with
$M\models\mu(\BorelInterpretation{c_N}{M})=0$. Then
$$
r_G\notin \BorelInterpretation{c_N}{M[G]}.
$$
\end{proposition*}

\begin{proof}[Proof]
By the internal Borel truth theorem of §{sec:internal-random-borel-truth}, membership would give a
positive condition below $q(\BorelInterpretation{c_N}{M})$.
The measure is zero, so this class is zero, a contradiction.
\end{proof}

\begin{lemma*}[\termdefine{Random forcing calculation}] For every condition $[B']\in P$,
$$[B'] \forces \dot r \in \BorelCodeName{c}
\quad\Longleftrightarrow\quad
\mu(\SetDifference{B'}{\BorelInterpretation{c}{M}}) = 0.
$$
\end{lemma*}

\begin{proof}[Proof]
Apply the forcing theorem of §{sec:internal-random-borel-truth} to the two constructed names.
It identifies forcing with the condition $[B']\le q(\BorelInterpretation{c}{M})$.
The internal order criterion gives exactly the displayed null-difference condition.
\end{proof}


In particular, $M[G]$ sees that $r_G$ is not equal to any ground-model real. For each
$x \in M \cap \CantorSpace$, the singleton $\{x\}$ is a Borel null set coded in $M$, ruling out $r_G = x$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
正規化円筒測度の表示は、実際のbinary trace cylinderを使うbinary_cylinderDensityへ接続した。
未リンク部分は後続の密度点命題への導入とBorel codeをMで取るという適用範囲の指定だけで、
密度定理そのものは次段落でKechrisに引用する外部入力として分離している。)
--> Random forcing also turns the Lebesgue density theorem into a forcing statement. Let $A\IncludedIn\CantorSpace$
be
Borel and coded in $M$.<!--
formalization: skip-end
-->  Write $\mu_s$ for normalized measure inside the cylinder $\cyl{s}$:
$$
\mu_s(B):=\frac{\mu(B\cap\cyl{s})}{\mu(\cyl{s})}.
$$

<!-- formalization: skip-begin (external input or explanatory background) -->
The cylinder form of the Lebesgue density theorem [@Kechris1995, Thm. 17.9] says that the exceptional set
$$
N_A:=\{x:\lim_{s\prefixOf x}\mu_s(A)\text{ fails to exist or differs from }1_A(x)\}
$$
is null.
<!-- formalization: skip-end -->

\begin{proposition*}[Lebesgue-point property] For every Borel $A$ coded in the ground model,
$$
r_G\in A\quad\Longrightarrow\quad
\lim_{s\prefixOf r_G}\mu_s(A)=1,
$$
and
$$
r_G\notin A\quad\Longrightarrow\quad
\lim_{s\prefixOf r_G}\mu_s(A)=0.
$$
\end{proposition*}

\begin{proof}[Proof]
For $b\in\{0,1\}$ and $k,N\in\omega$, form the open cylinder union
$$\begin{aligned}
U^b_{k,N}&:=\bigcup_{\substack{s\in\finseq{2},\ N\le \Length{s}\\ (k+1)^{-1}\le \Abs{\mu_s(A)-b}}}\cyl{s},\\
E_b&:=\bigcup_{k\in\omega}\bigcap_{N\in\omega}U^b_{k,N}.
\end{aligned}$$
A point lies in $E_b$ exactly when some fixed positive reciprocal tolerance is violated arbitrarily late.
Thus a point lies outside $E_b$ exactly when its cylinder densities converge to $b$.

We construct the entire codes in $M$. Use the standard numbering of finite natural words; nonbinary words
have empty Cantor traces. For a cylinder trace, put $\nu=\mu(A\cap\cyl{s})$ and $\delta=\mu(\cyl{s})$.
The density-zero deviation test is
$$\delta>0\ \land\ \neg\bigl((k+1)\nu<\delta\bigr),$$
and the density-one test is $\neg\bigl(k\delta<(k+1)\nu\bigr)$. These formulas also handle empty traces if their
normalized density is set to zero. For nonnegative $x,y$ and $m,n\in\omega$ with $n>0$, rational density gives
$$mx<ny\quad\Longleftrightarrow\quad
\exists a,b\in\omega\ \bigl[b>0\land\neg(a/b<x)\land ma/(nb)<y\bigr].$$
Indeed, a rational margin at or above $x$ proves the reverse direction; in the forward direction choose it
strictly between $x$ and $ny/m$ when $m>0$, and use any rational above $x$ when $m=0$.
The lower-cut formula of §{sec:internal-borel-measure-cut} therefore expresses both tests internally. Its
cylinder parameter is uniform: an internal point graph belongs to a cylinder exactly when it contains the
corresponding finite-word graph, so bounded Separation constructs the required intersections. Integer
multiplication and the finite-word length test have their existing internal graph definitions.

Separation on $\omega\times(\omega\times\omega)$ collects each whole deviation-comparison relation, indexed
by $\Tuple{k,N,s}$. The union, complement, selected-leaf, and empty-leaf cases give a bounded description of every
label in the nested Borel expressions above. The shared graph-collection construction puts the entire label
graphs and the required sequences of label graphs in $M$. The internal Boolean constructors then give a code
in $M$ for
$$N_A=(A\cap E_1)\cup(A^c\cap E_0).$$

The cited cylinder density theorem makes this exceptional set null. Since $r_G$ avoids every null Borel
set whose code belongs to $M$, it lies outside $N_A$. If $r_G\in A$, it consequently lies outside $E_1$, and its
cylinder densities converge to one. If $r_G\notin A$, it lies outside $E_0$, and those densities converge to zero.
\end{proof}

<!-- formalization: skip-begin (external input or explanatory background) -->
The random real is not only outside all old null sets; it is a Lebesgue density point for every ground-model
coded Borel set it
belongs to, and a density-zero point for every ground-model coded Borel set it avoids. This is the
measure-theoretic analogue of a
Cohen real lying in every old dense open set.

These two forcing notions stand in a measure-theoretic/category-theoretic duality:

| | Cohen | Random |
|---|---|---|
| conditions | $\finseq{2}$ | positive-measure Borel sets mod null |
| order | extension | inclusion mod null |
| weakest condition | $\emptySeq$ | $1_Q = [\CantorSpace]$ |
| compatibility | one extends the other | positive-measure intersection |
| canonical generic | $c_G \in \CantorSpace$ | $r_G \in \CantorSpace$ |
| generic avoids | every ground-model meager Borel set | every ground-model null Borel set |
| $\sigma$-ideal | meager sets | null sets |
| chain condition | ccc | ccc |

The duality is not a literal isomorphism. Their Boolean completions are not isomorphic, and the
$\sigma$-ideals of meager and null sets are not symmetric under ZFC. The rest of this chapter uses only the
regularity-theoretic side of that asymmetry.
<!-- formalization: skip-end -->


## Absoluteness {#sec:forcing-absoluteness}
\index{absoluteness}

For cylinder codes on Baire space, the basic membership comparison is supplied by the explicit construction
in §{sec:internal-borel-sets}. Given the label and basis graphs in a transitive model $M$, one fixed formula
selects the point graphs satisfying the code from the model's internal function space.
This constructs $\BorelInterpretation{c}{M}\in M$ rather than merely deciding membership separately for each point.
For a second transitive model $N$ containing $M$ and the same inputs, external well-foundedness of the code gives
$$\BorelInterpretation{c}{N}\cap(\BaireSpace\cap M)=\BorelInterpretation{c}{M}.$$
Both models test each common point against the same external evaluation. This argument does not require
the models to have the same ordinals. Transfer of the measure of a coded set is a further assertion.

For the binary cylinders used in random forcing, §{sec:internal-cantor-borel-sets} restricts this construction
to the internal Cantor space. Inverse images under the inclusion into Baire space commute with every node equation,
including complements. Consequently, for Cantor-space codes the corresponding identity is
$$\BorelInterpretation{c}{N}\cap(\CantorSpace\cap M)=\BorelInterpretation{c}{M}.$$
Here again points are identified with their function graphs. This proves membership agreement on old binary points;
it does not identify the measure of an internal set of points with the external measure of that set.

The measure comparison can now be made at the level of entire real codes. Let $M$ and $N$ be transitive
models of ZFC containing the same externally valid Borel code $c$. Write $A$ for its full external
Cantor-space interpretation and $F_M,F_N$ for the models' usual fair-coin probability measure graphs,
using the fraction-cut representation of real values from §{sec:internal-borel-measure-cut}.

\begin{mathmeta}
  \forward{MeasureValueCode,NonnegativeRealCut}
\end{mathmeta}

\begin{theorem*}[\termdefine{Absoluteness of coded Borel measure}]
The two internal value codes agree:
$$\begin{aligned}
\MeasureValueCode{F_M}{\BorelInterpretation{c}{M}}
&=\NonnegativeRealCut{\mu(A)}\\
&=\MeasureValueCode{F_N}{\BorelInterpretation{c}{N}}.
\end{aligned}$$
Hence the decoded measure values are equal. In particular, the code defines a null set in one model
if and only if it does in the other. The models need not have the same ordinals.
\end{theorem*}

\begin{proof}[Proof]
Work first in $M$. Finite additivity and the fair-coin cylinder values give the measure of every finite
union of cylinders. Internal countable additivity gives continuity from above for the decreasing
finite-level approximations to a closed tree. §{sec:internal-finite-measure-laws} verifies
that the entire families used here belong to $M$, and identifies their closed-set value codes with the
external closed measures.

For an arbitrary $\varepsilon>0$, the internal approximation theorem in
§{sec:internal-approximation-errors} supplies closed trees $T,S$ whose entire codes lie in $M$, with
$$\TreeBody{T}\IncludedIn A\IncludedIn\TreeBody{S}^c,\qquad
1-\mu(\TreeBody{S})-\mu(\TreeBody{T})<\varepsilon.$$
The construction includes the transfer of the coded inclusions to all external points from
§{sec:internal-closed-inclusions}. Restricting them back to the internal points, monotonicity and
complementation place the decoded internal measure between
$\mu(\TreeBody{T})$ and $1-\mu(\TreeBody{S})$.
The external value $\mu(A)$ lies between the same endpoints, so the values are equal.
Uniqueness of fraction-cut coding identifies the whole code, as detailed in
§{sec:internal-borel-measure-identification}. Apply the same argument in $N$.
The common code is empty exactly when its decoded value is zero.
\end{proof}

This compares the measures of the two interpretations of a shared code. It does not assign external
probability measure to the set of old points. In particular, the result applies to a transitive forcing
extension $N=M[G]$ without asserting that the two interpretations have the same elements.


<!-- formalization: skip-begin (external input or explanatory background) -->
Forcing extends a ground model $M$ of ZFC to a larger model $M[G]$ by adjoining a "generic" filter $G \IncludedIn P$ for
some partial order $P \in M$. Whether a given statement $\varphi$ is *absolute* — having the same truth value in $M$ and
in $M[G]$ — depends sharply on its descriptive complexity:

*   \termforwardas{Shoenfield absoluteness theorem}{Shoenfield absoluteness}. Every $\bSigma^1_2$ and $\bPi^1_2$
    statement with real parameters from a transitive
    ground model is absolute between that model and its forcing extensions. In particular, no forcing extension can
    change the truth value of an analytic or coanalytic statement about ground-model parameters.\termref{absoluteness}
*   **Beyond $\bSigma^1_2$**, absoluteness fails in general, already for $\bSigma^1_3$ statements.
    A standard sufficient hypothesis for absoluteness of all projective formulas under arbitrary set forcing is
    that there is a proper class of Woodin cardinals. Under this hypothesis, Woodin's generic-absoluteness theorem
    preserves truth with ground-model real parameters [@Welch2014, Theorem 3.20]. This is a separate theorem from
    Martin--Steel determinacy in §{sec:determinacy}; the forcing and large-cardinal hypotheses must be specified
    when invoking it.\termref{absoluteness}

The descriptive complexity of a statement and the forcings under which it is invariant track each other closely.
<!-- formalization: skip-end -->

\begin{theorem*}[\termdefineas{Shoenfield absoluteness theorem}{Shoenfield absoluteness}] If $M\IncludedIn N$ are
transitive models of enough ZFC with the same ordinals, then $\bSigma^1_2$ and $\bPi^1_2$ formulas are
\termuseas{absoluteness}{absolute} between $M$ and $N$ on real parameters from $M$. A forcing extension $M[G]$ has the
same ordinals as $M$ by §{sec:generic-extension}, so the theorem applies to the pair $M\IncludedIn M[G]$.
\end{theorem*}

\begin{proposition*}[Analytic/coanalytic absoluteness]\termref{absoluteness}
Let $M\IncludedIn N$ be transitive models of enough ZFC with the same ordinals, and let $T\in M$ be a subtree of
$\finseq{\omega}$ or of $\finseq{\omega\times\omega}$. Then "$T$ has an infinite branch" is absolute between $M$ and
$N$. Consequently, analytic and coanalytic truth with parameters in $M$ is absolute between $M$ and $N$.
\end{proposition*}

\begin{proof}[Proof] If $M$ has a branch, its function graph belongs to $M$ and therefore to $N$.
Conversely, suppose $M$ has no branch through $T$. The internal dependent-choice argument in
§{sec:internal-tree-branches} shows that the strict-extension relation on its nodes satisfies the internal
subset-minimum condition: a nonempty internal subset without a minimum would produce a branch in $M$.
The construction in §{sec:internal-rank-existence} therefore gives an ordinal $\alpha\in M$ and a function graph
$\rho:T\to\alpha$ in $M$ that strictly decreases along proper extensions. We use this decreasing-rank property;
no choice of a canonical least rank is needed. §{sec:internal-rank-certificates} transfers the same
ordinal and graph to $N$. An infinite branch in $N$ would give an infinite decreasing sequence of ordinals,
which is impossible. For trees on $\omega\times\omega$, use the same fixed numerical pairing to code nodes and
branches in both models.

For the analytic case, use the closed-projection characterization in §{sec:analytic-sets} and a synchronized
pair tree $U$ coded in $M$. For a real parameter $a\in M$, put
$$T_a:=\{t:\Pair{\restrict{a}{\Length{t}}}{t}\in U\}.$$
This section is coded in $M$. Indeed, code each finite word $s$ by its function graph $e(s)$, and code the nodes
of $U$ by pairs of these graphs. From the internal set of all finite-word graphs, Separation selects $e(t)$
when there is a finite-word graph $e(s)$ contained in the graph of $a$ such that the coded pair
$\Pair{e(s)}{e(t)}$ belongs to the code of $U$. Synchronization forces $\Length{s}=\Length{t}$, so this test says
exactly that $t\in T_a$. Branches through $T_a$ are precisely the witnesses in the closed projection.
Applying the branch result to $T_a$ proves analytic absoluteness, and negation gives coanalytic absoluteness.
This proves the $\bSigma^1_1/\bPi^1_1$ case directly. The next argument deduces the
$\bSigma^1_2/\bPi^1_2$ case from the cited basis theorem.
\end{proof}

\begin{proof}[Proof from cited results]
<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限の算術的formationとactual lambda atomic decidersから、同じパラメータaのpair treeを実際に構成し、
そのsectionの判定器はaとxの双方を保持する。coanalytic性と真のwell-founded strict
extensionとの同値をForcingArithmeticKernelsへ接続し、任意のtree
specificationを入力にして代用していない。未リンクの冒頭は後続のKondo–Addisonとrelative
constructibility agreementを外部入力として使うという証明方針の案内だけである。)
--> We prove the $\bSigma^1_2$ case; the $\bPi^1_2$ case follows by negation. We use the
Kondo--Addison basis theorem and the cited agreement of relative constructible hierarchies as external inputs.<!--
formalization: skip-end
-->
Put the formula in normal form
$$
\exists x\,\forall y\,\psi(x,y,a),
$$
where $a$ is the real parameter and $\psi$ is arithmetic. For fixed $x$ and $a$, the assertion $\forall y\,\psi(x,y,a)$
is coanalytic. Equivalently, there is a tree $T_{x,a}$, recursive from $x\oplus a$, such that
$$
\forall y\,\psi(x,y,a)
\quad\Longleftrightarrow\quad
T_{x,a}\text{ is well-founded}.
$$

<!-- formalization: skip-begin (external input or explanatory background) -->
The only new issue beyond the analytic/coanalytic proof is this: $N$ might satisfy the displayed formula using a real
$x\notin M$. The standard way to remove that witness is the following basis theorem.

\begin{theorem*}[\termdefine{Kondo--Addison basis theorem}]
For every real parameter $a$, every nonempty coanalytic set coded with parameter $a$ contains a real constructible from
$a$.
\end{theorem*}

In the present notation, if
$$
A_a:=\{x:T_{x,a}\text{ is well-founded}\}
$$
is nonempty, then $A_a\cap L[a]\ne\emptyset$.

The assertion that a witness belongs to the relative constructible universe is the substantive content of this
basis theorem. Coanalytic ranks and their boundedness, developed in §{sec:effective-dst-ranks}, do not by
themselves justify selecting a constructible witness: one must first know that an appropriate rank section
meets that universe. We use the basis theorem as an external result, with the background supplied in
[@Kechris1995, §35; @Moschovakis2009, Ch. 4]. The argument below is a deduction from that theorem, not an
independent proof of the basis theorem.

<!-- formalization: skip-end -->

Assuming these cited inputs, suppose $N\models \exists x\,\forall y\,\psi(x,y,a)$. Then $A_a$ is nonempty in
$N$. By the basis theorem inside $N$, choose $x\in A_a\cap L[a]^N$. Since $M$ and $N$ have the same ordinals and both
contain $a$, the relative constructible hierarchy is the same in the two models [@Kunen1980]:
$$
L[a]^M=L[a]^N.
$$
Thus $x\in M$. The statement $x\in A_a$ is coanalytic, so by the analytic/coanalytic absoluteness proved above, $M$ also
sees $x\in A_a$. Hence\termref{absoluteness}
$$
M\models \exists x\,\forall y\,\psi(x,y,a).
$$
The converse direction is easier: if $M$ has such an $x$, then $x\in N$, and coanalytic absoluteness transfers $\forall
y\,\psi(x,y,a)$ from $M$ to $N$. Therefore $\bSigma^1_2$ formulas are \termuseas{absoluteness}{absolute} between $M$
and $N$ on parameters from $M$. Applying this result to the negation proves $\bPi^1_2$
absoluteness.\termref{absoluteness}
\end{proof}

<!-- formalization: skip-begin (explanatory consequence) -->
This is why the ZFC regularity theory of analytic sets is robust under forcing, while higher projective levels are
sensitive to the surrounding universe.
<!-- formalization: skip-end -->


<!-- formalization: skip-begin (external forcing-axiom and determinacy outlook) -->
\begin{mathmeta}
  \define{MartinMaximumPlusPlus,PmaxForcing}
\end{mathmeta}
A further connection comes from forcing axioms. Martin's Maximum is a forcing axiom for partial orders
preserving stationary subsets of $\omegaOneOrd$, and $\MartinMaximumPlusPlus$ is a strengthening that also
controls stationary-set names. Woodin's axiom $(*)$ asserts that AD holds in $L(\R)$ and that there is a
filter $g$ generic over $L(\R)$ for his forcing $\PmaxForcing$ such that every subset of $\omegaOneOrd$ belongs
to $L(\R)[g]$. Asperó--Schindler [@AsperoSchindler2021] prove that $\MartinMaximumPlusPlus$ implies $(*)$,
linking forcing axioms with this determinacy-based construction. The forcing and its proof are external to
the present discussion; this result illustrates how the absoluteness program extends beyond the projective
statements considered above.
<!-- formalization: skip-end -->

## Genericity Is Topological {#sec:forcing-genericity-topological}

\begin{mathmeta}
  \vars{c}{Name}
  \vars{i,n}{Nat}
  \vars{p,s,t}{Seq}
  \vars{s_*}{Seq(Nat)}
\end{mathmeta}

<!-- formalization: skip-begin (topological characterizations of Cohen and random genericity) -->
The standard forcing notions on Polish spaces are exactly the elementary topological and measure-theoretic notions of
"generic" in disguise:

<!-- formalization: skip-end -->

*   \termuse{Cohen forcing} $P = \finseq{2}$ (finite binary sequences ordered by extension) adds a *Cohen real* $c \in
    \CantorSpace$. Each dense open subset $D \IncludedIn P$ determines the dense open set $\bigcup_{s \in D} \cyl{s}
    \IncludedIn \CantorSpace$, and a Cohen real is precisely a point lying in every such dense open set coded in the
    ground model — equivalently, a real avoiding every meager Borel set coded in the ground model. This is a
    *Baire-generic* point of $\CantorSpace$.
*   \termuseas{random forcing}{Random forcing}, the nonzero part of the Boolean algebra of Borel sets modulo
    Lebesgue-null sets,
    ordered by inclusion modulo null sets, adds a
    *random real*: one that avoids every null Borel set coded in the ground model — a *Lebesgue-generic* point.

<!-- formalization: skip-begin (topological characterizations of Cohen and random genericity) -->
The whole vocabulary of forcing and genericity is the model-theoretic shadow of Baire category and Lebesgue measure on
Polish spaces.
<!-- formalization: skip-end -->

For Cohen forcing, any real $c$ determines the filter of its finite prefixes
$$G_c := \{s \in \finseq{2} : s \prefixOf c\}.$$
It contains the empty string and every shorter prefix of each member. Any two members have a common extension
in $G_c$, namely the prefix of $c$ whose length is the maximum of their lengths. Thus it is indeed a filter.

\begin{lemma*}[\termdefineas{Cohen dense-open correspondence}{Cohen dense-open correspondence}]
For a dense set $D\IncludedIn P$, the set $U_D=\bigcup_{s\in D}\cyl{s}$ is open and dense in $\CantorSpace$.
Conversely, if $U\IncludedIn\CantorSpace$ is open and dense, the set $D_U=\{s\in P:\cyl{s}\IncludedIn U\}$ is
dense in $P$. A prefix filter $G_c$ meets $D$ exactly when $c\in U_D$.
\end{lemma*}

\begin{proof}[Proof]
The set $U_D$ is open as a union of cylinders. Every nonempty open set contains a cylinder $\cyl{s}$. Density of
$D$ gives an extension $t\in D$ of $s$, so the nonempty cylinder $\cyl{t}$ lies in both that open set and $U_D$.
Conversely, density of $U$ gives a point of $\cyl{s}\cap U$. Since this intersection is open, it contains a
cylinder $\cyl{t}$ about that point. Cylinder inclusion gives $s\prefixOf t$, and $t\in D_U$.
Finally, $c\in U_D$ means exactly that some $s\in D$ is a prefix of $c$.
\end{proof}

\begin{corollary*}[Countable dense-open requirements]
For every sequence $\Sequence{U_n}{n\in\omega}$ of dense open subsets of Cantor space and every $p\in P$, there is a
point of
$\cyl{p}\cap\bigcap_n U_n$.
\end{corollary*}

\begin{proof}[Proof]
Apply the countable Cohen requirements lemma to $(D_{U_n})$ and $p$. Its real $c\in\cyl{p}$ has, for each $n$,
a prefix $s\in D_{U_n}$, so $c\in\cyl{s}\IncludedIn U_n$.
\end{proof}

\begin{lemma*}[Ground-model Cohen conditions]
Let $M$ be a transitive model of ZFC. Represent each finite binary word by its finite function graph.
Then $P=\finseq{2}$ belongs to $M$. For every $D\in M$ with $D\IncludedIn P$, the assertion that $D$ is dense
in $P$ has the same truth value in $M$ and in the surrounding universe. Moreover,
$$E:=\{t\in P:\exists s\in D\ (s\prefixOf t)\}$$
belongs to $M$ and satisfies $U_E=U_D$.
Under this representation, the forcing definition of $M$-genericity agrees with meeting every such dense
family of finite words.
\end{lemma*}

\begin{proof}[Proof]
The model contains $\omega$, all finite binary function graphs, and their set $P$. For these graphs,
$s\prefixOf t$ means $s\IncludedIn t$. Thus density is expressed by the bounded formula
$$\forall s\in P\ \exists t\in D\ (s\IncludedIn t).$$
Transitivity makes this formula absolute. Bounded separation inside $P$ constructs $E$ in $M$.
Since $D\IncludedIn E$, we have $U_D\IncludedIn U_E$. Conversely, if $t\in E$, choose $s\in D$ with
$s\prefixOf t$. Then $\cyl{t}\IncludedIn\cyl{s}\IncludedIn U_D$, proving the reverse inclusion.
Every element of the internal set $P$ is the graph of a unique finite binary word. Thus every internal
subset of $P$ corresponds to a family of words, with the same extension order and density test.
Applying this correspondence to all dense subsets belonging to $M$ gives the assertion about genericity.
\end{proof}

\begin{lemma*}[Internal closed codes from dense conditions]
If $D\in M$ is a dense subset of $P$, then $M$ contains a Borel code for $U_D$ and a Borel code for
$\SetDifference{\CantorSpace}{U_D}$. The latter set is closed and nowhere dense.
\end{lemma*}

\begin{proof}[Proof]
Use the standard cylinder coding of §{sec:internal-cantor-borel-sets}. Choose $s_*\in D$, put
$k=\FiniteSequenceCode{s_*}$, and let $s_n\in\finseq{\omega}$ be the word with $\FiniteSequenceCode{s_n}=n$.
Define
$$
\ell_n:=
\begin{cases}
n,&s_n\in D,\\
k,&s_n\notin D.
\end{cases}
$$
Every selected word belongs to $D$, and each word in $D$ is selected at its own index. Hence
$$
a:=\BorelUnionCode{\Sequence{\BorelLeafCode{\ell_n}}{n\in\omega}},
\qquad
b:=\BorelComplementCode{a}
$$
interpret respectively as $U_D$ and its complement in Cantor space.

The finite-word decoding graph belongs to $M$. The displayed case distinction is bounded, so Replacement
collects the entire index sequence in $M$. The leaf constructor has a uniform bounded description;
another application of Replacement collects the entire sequence of leaf label graphs.
The internal union and complement constructors then give the label graphs of $a$ and $b$ in $M$.
Thus the construction uses an internal sequence, not merely separately internal leaves.
Finally, $U_D$ is dense and open by the Cohen dense-open correspondence, so its complement is closed and nowhere
dense. The same argument applies inside $M$, using the absolute density test of the preceding lemma.
\end{proof}

\begin{mathmeta}
  \forward{BorelValue}
\end{mathmeta}
Write $\BorelValue{c}$ for the full Cantor-space interpretation of a code $c$.

\begin{lemma*}[Transfer of internally coded Borel covers]
Let $c$ and $\Sequence{d_n}{n\in\omega}$ be Borel codes interpreted on Cantor space.
Suppose the label graph of $c$ and the entire sequence of label graphs of $d_n$ belong to $M$.
If every binary point coded in $M$ that lies in $\BorelValue{c}$ lies in some $\BorelValue{d_n}$, then
$$\BorelValue{c}\IncludedIn\bigcup_n\BorelValue{d_n}.$$
In particular, the cover also contains all new points of $\BorelValue{c}$.
\end{lemma*}

\begin{proof}[Proof]
The internal union constructor gives a code $d=\BorelUnionCode{\Sequence{d_n}{n\in\omega}}$ in $M$.
The internal Boolean constructors give a code $e$ in $M$ for $\SetDifference{\BorelValue{c}}{\BorelValue{d}}$.
By hypothesis, no binary point coded in $M$ belongs to $\BorelValue{e}$.
Apply the transfer of closed disjointness from §{sec:internal-closed-inclusions} to the whole binary space
and the code $e$. It follows that $\BorelValue{e}=\emptyset$, which gives the required inclusion.
\end{proof}

For the internal calculations, identify binary sequences and finite words with their function graphs.
Put $Y:=\funcspace{\omega}{2}\cap M$ and $P:=\finseq{2}$. For an internal set $A\IncludedIn Y$, define
$$D_A:=\{s\in P:\forall g\in A\ \neg(s\IncludedIn g)\}.$$
The basis tests for closedness and nowhere density are
$$
\begin{aligned}
C(A)\quad\Longleftrightarrow\quad& A\IncludedIn Y\ \land\\
&\forall g\in\SetDifference{Y}{A}\ \exists s\in P\\
&\bigl(s\IncludedIn g\ \land\ s\in D_A\bigr),\\
N(A)\quad\Longleftrightarrow\quad&\forall s\in P\ \exists t\in P\\
&\bigl(s\IncludedIn t\ \land\ t\in D_A\bigr).
\end{aligned}
$$
Substituting the displayed definition of membership in $D_A$ makes both tests bounded formulas.
The first says that every point outside the set has a cylinder neighborhood disjoint from it;
the second says that every cylinder has a smaller cylinder disjoint from the set.

\begin{lemma*}[\termdefine{Internal avoiding conditions}]
If $A\in M$ satisfies $C(A)$ and $N(A)$ inside $M$, then $D_A\in M$ is dense in $P$.
There is a Borel code in $M$ whose internal Cantor interpretation is $A$ and whose external interpretation
is closed and nowhere dense. If $a$ is any internal Borel code with internal interpretation $A$, then
$$D_A=\{s\in P:\cyl{s}\cap\BorelValue{a}=\emptyset\}.$$
\end{lemma*}

\begin{proof}[Proof]
Bounded separation on $P$ constructs $D_A$ in $M$. Transitivity makes $N(A)$ absolute, so this same family
is dense externally. The preceding construction gives an internal code for the closed nowhere-dense set
$\SetDifference{\CantorSpace}{U_{D_A}}$.
A point of $A$ has no prefix in $D_A$. Conversely, $C(A)$ gives every internal point outside $A$ a prefix in
$D_A$. Thus this code has internal interpretation exactly $A$.
For an arbitrary code $a$ with that internal interpretation, membership in $D_A$ means that the cylinder
contains no internal point of $\BorelValue{a}$. Apply Borel-inclusion transfer to the cylinder code
and the complement code of $a$, as in the preceding cover lemma.
The cylinder is disjoint from the full external interpretation as well.
The reverse implication follows by restriction to internal points.
\end{proof}

To express that an internal set $A$ is meager, use the first-order assertion
$$
\exists R\ \exists F\quad
\begin{cases}
F:\omega\twoheadrightarrow R,\\
\forall B\in R\ \bigl(C(B)\land N(B)\bigr),\\
A\IncludedIn\bigcup R.
\end{cases}
$$
Here the function is represented by its graph, and the quantifiers over $R,F$ range over the model.
After these two quantifiers, all quantifiers can be bounded by the displayed parameters.

\begin{lemma*}[\termdefine{Internal meager-cover witnesses}]
The model satisfies this assertion exactly when there is a sequence $\Sequence{A_n}{n\in\omega}$ whose
whole graph belongs to $M$, each term satisfies the internal closedness and nowhere-density tests, and
$A\IncludedIn\bigcup_n A_n$ holds for the internal sets.
\end{lemma*}

\begin{proof}[Proof]
An internal witnessing function gives $A_n:=F(n)$; surjectivity identifies its range with $R$.
Conversely, the range of an internal sequence graph belongs to the model by Union and Separation.
Use that range as $R$ and the sequence graph as $F$.
The bounded interpretation principle identifies the model's tests with the same tests on these sets.
\end{proof}

The real $c$ is Cohen-generic over $M$ exactly when its prefix filter meets every dense subset of $\finseq{2}$
belonging to $M$, by the ground-model condition correspondence above.

\begin{proposition*}[Cohen genericity and Baire category] A real $c\in\CantorSpace$ is Cohen-generic over $M$ iff it
avoids every meager Borel set coded as meager in $M$.
\end{proposition*}

\begin{proof}[Proof]
Suppose first that $c$ is Cohen-generic, and let $a\in M$ code a set that the model judges to be meager.
Choose an internal closed nowhere-dense cover $\Sequence{A_n}{n\in\omega}$ using the preceding witness lemma.
The avoiding-condition lemma constructs each dense family $D_{A_n}$ inside $M$.
Genericity gives a prefix of $c$ in each such family, so $c$ avoids the external interpretation of every cover member.
The same lemma supplies an internal Borel code for each $A_n$.
Use §{sec:internal-borel-code-recognition} to choose the whole sequence of their codes inside $M$.
The Borel-cover transfer makes the internal covering inclusion valid at $c$ as well.
Thus $c\notin\BorelValue{a}$.

Conversely, let $D\in M$ be dense in $P$. The earlier construction supplies an internal code for the closed
nowhere-dense set $\SetDifference{\CantorSpace}{U_D}$. Its internal interpretation satisfies $C$ and $N$:
external closedness supplies the required finite neighborhoods, and density supplies the avoiding extensions.
Repeating this internal set gives an internal constant sequence witnessing its meagerness.
Avoidance therefore gives $c\in U_D$, so a finite prefix of $c$ belongs to $D$.
Since this holds for every such $D$, the prefix filter is $M$-generic.
\end{proof}

The converse for random forcing rests on a measure-theoretic reconstruction. We first make it explicit in the ambient
measure algebra $Q$.
A family of positive conditions is \termdefineas{predense family}{predense} if every positive condition is compatible
with a member of the family.

\begin{lemma*}[\termdefineas{random predense antichain lemma}{Predense antichains and conull covers}]
Every dense subset of $Q_+$ contains a countable predense antichain.
More generally, representatives of any countable predense family have a conull Borel union.
\end{lemma*}

\begin{proof}[Proof]
Fix a dense set and order its pairwise incompatible subfamilies by inclusion. The union of a chain of such subfamilies
is again pairwise incompatible:
any two members occur together in one subfamily of the chain. Zorn's lemma therefore gives a maximal such subfamily.
If a positive condition were incompatible with every member, strengthen it into the dense set and adjoin that
strengthening, contradicting maximality.
Thus the antichain is predense, and the ccc makes it countable.

For a countable predense family, form the Borel union of its representatives. If the complement had positive measure,
its class would be a positive condition incompatible with every member of the family. This contradicts predensity,
so the union is conull. The argument uses countability to obtain a Borel union, and does not require the representatives
to be literally disjoint.
\end{proof}

Let $A\IncludedIn Q$ be a countable Boolean subalgebra, and choose a Borel representative $B_a$ of each $a\in A$.
These choices need not preserve Boolean operations as literal set operations.
\begin{mathmeta}
  \define{SymmetricDifference}
\end{mathmeta}
Write $\SymmetricDifference{B}{C}$ for the symmetric difference of two sets. Define the defect set
$$\begin{aligned}
N_A:={}&B_0\cup B_1^c\\
&{}\cup\bigcup_{a,b\in A}\left(\SymmetricDifference{B_{a\wedge b}}{(B_a\cap B_b)}\right)\\
&{}\cup\bigcup_{a\in A}\left(\SymmetricDifference{B_{a^c}}{B_a^c}\right).
\end{aligned}$$

\begin{lemma*}[\termdefineas{coherent measure representatives lemma}{Coherent representatives}]
The set $N_A$ is Borel and null. At every point outside it, membership in the representatives preserves zero, one,
finite meets, and complements.
Consequently, for $r\notin N_A$,
$$G_r^A:=\{a\in\SetDifference{A}{\{0\}}:r\in B_a\}$$
is a filter on the positive part of $A$.
\end{lemma*}

\begin{proof}[Proof]
Each symmetric difference in the definition is null because its two sets represent the same element of the measure
algebra.
The sets representing zero and the complement of one are also null. All these sets are Borel, and there are only
countably many of them.
Outside their union, zero is false, one is true, membership in a meet is simultaneous membership, and membership in a
complement is nonmembership.
Thus the filter contains one. If two positive elements belong to it, their meet also contains the point and cannot be
zero, so it is a common strengthening in the filter.
If an element lies below another, its meet with that other element equals itself. Preservation of meets therefore makes
the filter upward closed.
\end{proof}

The construction is also independent of a second choice of representatives $C_a$, outside the additional Borel null set
$$\bigcup_{a\in A}\left(\SymmetricDifference{B_a}{C_a}\right).$$
Indeed, each symmetric difference is null, and outside their union the two membership tests agree for every element of
the algebra.

\begin{lemma*}[\termdefineas{point filter reconstruction lemma}{Point filters meeting prescribed families}]
Let $\Sequence{J_i}{i\in\NN}$ be families in the positive part of $A$, each predense in the full order $Q_+$.
Put
$$E:=N_A\cup\bigcup_i\left(\bigcup_{a\in J_i}B_a\right)^c.$$
Then $E$ is Borel and null. For every $r\notin E$, the filter $G_r^A$ meets every $J_i$.
\end{lemma*}

\begin{proof}[Proof]
Each family is countable because the algebra is countable. Its representatives have conull union by the predense-family
argument.
Thus the displayed set is a countable union of Borel null sets. A point outside it is outside the Boolean defects, so it
defines the filter already constructed.
For each family, it also lies in some representative of a member, placing that member in the filter.
\end{proof}

\begin{theorem*}[\termdefineas{conull random filter reconstruction theorem}{Conull reconstruction from dense
requirements}]
Let $\Sequence{D_i}{i\in\NN}$ be dense subsets of the full order $Q_+$. There is a Borel null set $N$ such that every
$r\notin
N$ is the real $r_G$ of a filter $G$ meeting every $D_i$ and every cylinder-length requirement $C_n$.
\end{theorem*}

\begin{proof}[Proof]
For each $i$, choose a countable predense antichain $J_i\IncludedIn D_i$. Let $A$ be the Boolean subalgebra generated by
all these antichains and all cylinder classes.
This algebra is countable: start with the countable generating set and zero, then repeatedly adjoin binary joins and
complements. Each stage is countable, and the union of the stages is exactly the generated Boolean subalgebra; finite
meets are obtained by De Morgan's law.

Choose representatives $B_a$ on $A$, and form the preceding exceptional set $E$ for the families $J_i$. To align these
representatives with the actual cylinders, also exclude
$$C:=\bigcup_{s\in\finseq{2}}\left(\SymmetricDifference{B_{[\cyl{s}]}}{\cyl{s}}\right).$$
Each symmetric difference is Borel and null because its two sets represent the same class. There are countably many
finite strings, so $N:=E\cup C$ is Borel and null.

For $r\notin N$, the point filter $G_r^A$ meets every $J_i$. Extend it to the full positive order by upward closure:
$$G:=\{p\in Q_+:\exists a\in G_r^A\ (a\le p)\}.$$
This is a filter: it is nonempty and upward closed, and a common strengthening in $G_r^A$ of two witnesses also
strengthens the two ambient conditions. Its restriction to the positive part of $A$ is exactly $G_r^A$, by upward
closure within that subalgebra. In particular, $G$ meets every $D_i$.

Since every cylinder class belongs to $A$ and $r$ avoids $C$, we have
$$[\cyl{s}]\in G\quad\Longleftrightarrow\quad r\in B_{[\cyl{s}]}\quad\Longleftrightarrow\quad r\in\cyl{s}.$$
For each length, the class of the cylinder containing $r$ therefore lies in $G$ and witnesses that it meets $C_n$. The
random filter union lemma now applies, and the displayed cylinder decisions identify its unique real with $r$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部conull列の構成はinternal_dense_conull_sequenceへ接続済み。残りはfull measure
algebraに対する仮定をcountable subalgebraへ弱めてはならないという適用範囲の注意。具体的反例の証明を提示する箇所ではなく、
局所証明の追加を免除するための除外ではない。)
-->
The predensity hypothesis concerns the full measure algebra. Maximality within an arbitrary countable subalgebra alone
does not rule out a positive condition outside that subalgebra which misses the family.<!--
formalization: skip-end
-->
For an internal forcing argument, §{sec:internal-random-point-filters} constructs finite approximate covers and their
entire sequence inside the ground model. Their union is conull when the family of representatives is dense.

Now suppose a real $r$ avoids every Borel null set coded in $M$.
The construction in §{sec:internal-random-point-filters} puts the complement, intersection, and symmetric-difference
codes in $M$ and uses their null defects to build a filter $G_r$ on the internal positive order.
For every ground-model coded representative $B$ of a condition $p$,
$$p\in G_r\quad\Longleftrightarrow\quad r\in B.$$
The filter is independent of the representatives. Applied to the real of an existing $M$-generic filter $G$,
the same construction recovers $G$ exactly.

To verify genericity, let $\Delta\in M$ be dense in the internal positive part. Apply the conull-sequence theorem
of §{sec:internal-random-point-filters} to obtain a whole internal sequence of sets $V_j$, each either empty
or a representative of a condition in $\Delta$, whose union is internally conull.

The selection theorem in §{sec:internal-borel-code-recognition} expresses the relation
$\BorelInterpretation{c}{M}=V_j$ by one formula on the internal set of valid label graphs.
Internal choice gives a selector on the range of the sequence $V_j$; reading that same selector along the
sequence gives the entire table of chosen label graphs in $M$. The internal union constructor therefore
produces a Borel code in $M$ for the cover.
Its complement is internally null, so measure absoluteness makes its full external interpretation null as well.
Thus $r$ belongs to a representative of a positive condition in $\Delta$, and $G_r$ meets $\Delta$.

For each finite binary word $s$, its one-leaf cylinder code belongs to $M$. Hence
$$q(\InternalCylinder{M}{s})\in G_r\quad\Longleftrightarrow\quad r\in\cyl{s}.$$
§{sec:internal-borel-code-recognition} uses these decisions to identify the valuation of the
random-real name with $r$. Together with null-set avoidance, this proves the random-genericity characterization.
The internally selected table supplies the conull code; the collection of all defects considered externally
need not itself have a code in $M$.

## Independence of Regularity Properties {#sec:forcing-independence-regularity}

<!-- formalization: skip-begin (constructibility and Solovay-model independence results) -->
Whether every set in a given projective class has Lebesgue measurability, the property of Baire, or the perfect set
property is decided not by ZFC alone, but by additional set-theoretic principles:

*   **At $\bSigma^1_1$**: all three regularity properties hold in ZFC, as recorded in
    §{sec:regularity-independence}.
*   **At $\bSigma^1_2$ and beyond**: independence sets in. In Gödel's constructible universe $L$ there is a
    $\bSigma^1_2$ well-ordering of $\R$, producing $\bSigma^1_2$ sets without the Baire property and without Lebesgue
    measurability [@Kunen1980]. Conversely, the consistency of an inaccessible cardinal yields Solovay's model of
    ZF + DC in which every set of reals is Lebesgue measurable and has the property of Baire.

<!-- formalization: skip-end -->

The mechanism behind the negative direction is simple once a definable well-order of the reals is available. A
projectively definable well-order lets one choose canonical representatives from equivalence classes that normally admit
no definable selector. For example, applying the first-in-the-well-order choice to the cosets of $\QQ$ in $\R$ gives a
projectively definable Vitali selector. Such a selector cannot be Lebesgue measurable and cannot have the Baire
property. Thus the definable well-order of $\R$ in $L$ turns set-theoretic constructibility into explicit projective
counterexamples to regularity.

<!-- formalization: skip-begin (constructibility and Solovay-model independence results) -->
The positive direction has the opposite flavor. Solovay's construction starts from an inaccessible cardinal $\kappa$,
forces with the Lévy collapse that makes $\kappa=\omegaOneOrd$, and then takes an inner model whose sets are
hereditarily definable from ordinals and reals [@Solovay1970]. Starting from a ground model with such an inaccessible,
the resulting Solovay model satisfies ZF + DC, and every set of reals is Lebesgue measurable, has the property of Baire,
and has the perfect set property.

The defining real parameters of a set in the Solovay model appear at a bounded stage of the collapse.
The set itself need not belong to that intermediate extension, since it may contain later reals. Solovay's
argument uses the parameters together with homogeneity of the remaining collapse to control the definition
and establish regularity. This is the substantial external part of the theorem, not a consequence of the
ccc alone.

Shelah proved that, for Lebesgue measurability under DC, the inaccessible strength in Solovay's theorem is not a
cosmetic assumption [@Shelah1984]. More precisely, the consistency of ZF + DC + "every set of reals is Lebesgue
measurable" implies the consistency of an inaccessible cardinal. The reverse direction supplied by Solovay and this
lower-bound direction supplied by Shelah make the theorem an equiconsistency result for universal Lebesgue measurability
with dependent choice. The property of Baire alone has lower consistency strength, so the three regularity properties
should not be conflated at the level of metamathematical cost.

Projective determinacy gives another route for projective sets specifically: games on $\omega$ impose enough structure
that projective sets regain regularity far beyond the analytic level.

<!-- formalization: skip-end -->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
coanalyticのBPはanalytic補集合の実際のBP定理から証明した。Lebesgue measurabilityの局所的な一歩は、
既出の文献概説で引用するanalytic measurabilityを明示的な入力とし、NullMeasurableSetの補集合閉包へ接続した。
Borel sigma algebra上のMeasurableSetで代用せず、analytic universal
measurability自体を新たに証明したとも扱わない。未リンクの結語とLにおけるcoanalytic
PSP失敗は構成可能性に関する外部結果の概説で、その独立性証明をこの段落では展開しない。)
--> Forcing therefore distinguishes the regularity properties that ZFC decides from those requiring further axioms.<!--
formalization: skip-end
-->
Their boundaries differ: coanalytic sets still have Lebesgue measurability and the Baire property in ZFC,
because both properties pass to complements, <!--
formalization: skip-begin (引用・背景説明・読書案内:
coanalyticのBPはanalytic補集合の実際のBP定理から証明した。Lebesgue measurabilityの局所的な一歩は、
既出の文献概説で引用するanalytic measurabilityを明示的な入力とし、NullMeasurableSetの補集合閉包へ接続した。
Borel sigma algebra上のMeasurableSetで代用せず、analytic universal
measurability自体を新たに証明したとも扱わない。未リンクの結語とLにおけるcoanalytic
PSP失敗は構成可能性に関する外部結果の概説で、その独立性証明をこの段落では展開しない。)
--> whereas their perfect set property can fail in the constructible
universe. Thus $\bSigma^1_1 / \bSigma^1_2$ is a useful comparison between additive levels, not a single boundary
shared by all three regularity properties.<!--
formalization: skip-end
-->

## Toward Algorithmic Randomness {#sec:forcing-algorithmic-randomness}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}
\index{Martin-Löf randomness}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
一つの閉lambda termによる全row/stageの列挙を持つUniformlyOpen、MLTest/MLRandomの定義と、
実際のnull交叉の証明へ接続した。未リンク部分は本章で既に証明したold null回避との動機上の比較、
およびeffective-open/measure algorithms/testを扱う既出節への読む順序だけである。)
--> Random forcing also motivates algorithmic randomness. A random real over a countable ground model avoids
every Borel null set coded in that model.<!--
formalization: skip-end
-->  Martin-Löf randomness instead restricts the tests effectively:
a test is a uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$, and a real
passes it when
it lies outside $\bigcap_n U_n$. The intersection is null; the individual open sets need not be null.
A Martin-Löf random real passes every such test. <!--
formalization: skip-begin (引用・背景説明・読書案内:
一つの閉lambda termによる全row/stageの列挙を持つUniformlyOpen、MLTest/MLRandomの定義と、
実際のnull交叉の証明へ接続した。未リンク部分は本章で既に証明したold null回避との動機上の比較、
およびeffective-open/measure algorithms/testを扱う既出節への読む順序だけである。)
--> Effective openness is developed in
§{sec:tte-effective-open-closed}; §{sec:tte-cantor-open-measure} supplies the measure algorithms, and
§{sec:computational-choice-randomness} develops the tests.<!--
formalization: skip-end
-->
