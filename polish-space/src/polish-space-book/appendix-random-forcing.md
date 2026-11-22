# Appendix: Internal Measure Algebras and Random Forcing {#sec:appendix-random-forcing}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
random forcing付録が使う測度絶対性とforcing基礎を明示する導入。具体的な構成は後続の各定理で別に対応済み。)
--> This appendix develops random forcing from internal measure algebras. It uses the internal measure values and
absolute comparisons proved in §{sec:appendix-measure-absoluteness}, together with the names, valuation, and forcing
machinery of §{sec:appendix-forcing-background}.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部商・random-real名・Borel真理・点からのgeneric回復を辿る章構成の案内。各結果をここで追加に証明する箇所ではない。)
-->
We first construct the quotient modulo null sets and a name for the generic point. We then compare internal Borel truth
with truth in generic extensions. Finally, we construct a filter from a null-avoiding point and prove genericity and
recovery of that point. §{sec:forcing} presents the resulting Polish-space applications.<!--
formalization: skip-end
-->

## Measure Algebras and Names for the Generic Point {#sec:random-measure-algebras}

### The Internal Measure Algebra {#sec:internal-null-quotients}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
全商写像を先に内部構成する理由と、有限測度則と可算加法性の依存関係の説明。relationClassMap_mem、
randomRealName_memは有限測度則のみを用い、外部Borel測度との同定は後続比較定理を使う。)
--> The random-real name uses measure-algebra elements as conditions. To obtain its decision table inside
the ground model, we first need the entire quotient map there. This construction uses only finite
measure laws; countable additivity enters the identification with Borel measure in
§{sec:internal-borel-measure-identification}.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
一般の内部商構成に使うモデル公理・同値関係の仮定を固定する文。
商の実定義は直後のrelationClass/relationClassMap/relationQuotientへ対応済み。)
--> Let $M$ be transitive and satisfy Pairing, Union, Separation, and Replacement. For an equivalence
relation $E\IncludedIn D\times D$, write<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{EquivalenceClass,SetQuotient}
\end{mathmeta}

$$\begin{gathered}
\EquivalenceClass{E}{a}:=\{b\in D:\Pair{a}{b}\in E\},\\
q:=\{\Pair{a}{\EquivalenceClass{E}{a}}:a\in D\},\qquad
\SetQuotient{D}{E}:=\GraphRange{q}.
\end{gathered}$$

\begin{theorem*}[\termdefine{Internal quotient maps}]
If $D,E\in M$, then $q\in M$ and $\SetQuotient{D}{E}\in M$. For $a,b\in D$,
$$\EquivalenceClass{E}{a}=\EquivalenceClass{E}{b}
\quad\longleftrightarrow\quad\Pair{a}{b}\in E.$$
\end{theorem*}

\begin{proof}[Proof]
Bounded Separation gives each class. A candidate class is specified as a subset of the carrier whose
members are exactly those related to the given input. The shared bounded-predicate interpretation
and definable-graph construction therefore collect the whole graph by Replacement. Taking its range
gives the quotient set. If two classes coincide, reflexivity puts the second representative in both
classes, so the representatives are related. Conversely, symmetry and transitivity show that related
representatives have the same class.
\end{proof}

Now also assume Power Set in $M$. Let $D,F\in M$ and let $F:D\to R$ satisfy the finite measure laws
of §{sec:internal-finite-measure-laws}. In particular, $D$ contains $\emptyset$ and is closed under
finite unions and differences. Let $\nu$ be the decoded value function. Define
$$E:=\{\Pair{A}{B}\in D\times D:
\nu(\SetDifference{A}{B})=0=\nu(\SetDifference{B}{A})\}.$$
This is equality modulo null differences.

\begin{theorem*}[\termdefine{Internal null quotients}]
The relation $E$ is an equivalence relation and belongs to $M$. Its quotient map and quotient set
belong to $M$, as does the set of positive conditions
$$P:=\SetDifference{\SetQuotient{D}{E}}{\{\EquivalenceClass{E}{\emptyset}\}}.$$
For every $A\in D$,
$$\EquivalenceClass{E}{A}\in P\quad\longleftrightarrow\quad\nu(A)>0.$$
\end{theorem*}

\begin{proof}[Proof]
The empty cut code represents zero, so for each $U\in D$,
$$\nu(U)=0\quad\longleftrightarrow\quad\Pair{U}{\emptyset}\in F.$$
Thus membership of $\Pair{A}{B}$ in the relation is expressed by bounded quantification over
$U,V\in D$, requiring
$$\begin{gathered}
U=\SetDifference{A}{B},\qquad V=\SetDifference{B}{A},\\
\Pair{U}{\emptyset}\in F,\qquad\Pair{V}{\emptyset}\in F.
\end{gathered}$$
The two difference equations use the shared bounded subset predicate. Closure under differences
supplies the witnesses, and bounded Separation on $D\times D$ gives $E\in M$.

Reflexivity and symmetry follow immediately from the zero law and the definition. For transitivity,
finite additivity applied to a disjoint decomposition gives
$$\nu(A\cup B)=\nu(A)+\nu(\SetDifference{B}{A})\le\nu(A)+\nu(B).$$
Combine this with
$$\SetDifference{A}{C}\IncludedIn
(\SetDifference{A}{B})\cup(\SetDifference{B}{C})$$
and monotonicity. If both differences on the right have value zero, nonnegativity forces the left
one to have value zero. Interchanging the first and third sets gives the reverse difference.
The preceding theorem now constructs the quotient map and quotient set. The empty-set class belongs
to the model, so a further bounded Separation gives the positive conditions. Finally, equality with
the empty-set class is equivalent to having value zero; nonnegativity gives the asserted positivity test.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部測度域の集合の商と、全外部Borel集合の測度代数を区別する適用上の注意。商の構成だけから比較写像やold
points上の外部測度を得たとは主張しない。)
--> These classes consist of sets in the internal measure domain. Comparing them with classes of full
external Borel sets requires the measure identification in §{sec:internal-borel-measure-identification}.
The quotient construction alone does not identify the model's set of old points with the full
external probability space.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
random-real名の構成に使うInfinity、公平なcylinder値、null関係・商写像・正条件の記号を固定する仮定。bit
cellの値と全判定表は後続で構成され、ここで仮定を証明済みの結果に変えない。)
--> Retain the transitive-model and finite measure assumptions of §{sec:internal-null-quotients}, and
assume Infinity as well. Let $Y_M$ be the internal Cantor space. Assume that all its basic cylinders
belong to $D$ and have the normalized value codes of §{sec:internal-finite-measure-laws}.
Write $E$ for null equivalence, $q$ for its entire quotient map, and $P$ for the positive quotient classes.<!--
formalization: skip-end
-->

For a family of sets and an input label, define its membership fiber by

\begin{mathmeta}
  \define{MembershipFiber,InternalBitCell}
\end{mathmeta}

$$\MembershipFiber{Y}{a}:=\{g\in Y:a\in g\}.$$
For binary point graphs, this gives the coordinate cells
$$\begin{gathered}
\InternalBitCell{M}{n}{i}:=\MembershipFiber{Y_M}{\Pair{n}{i}}
=\{g\in Y_M:g(n)=i\},\\
n\in\omega,\quad i\in2.
\end{gathered}$$
The integers in these graph pairs are represented by finite ordinals.

\begin{lemma*}[\termdefine{Internal coordinate cells}]
For every $n\in\omega$ and $i\in2$,
$$\InternalBitCell{M}{n}{i}\in D,\qquad\nu(\InternalBitCell{M}{n}{i})=\frac12.$$
Consequently, $q(\InternalBitCell{M}{n}{i})\in P$.
\end{lemma*}

\begin{proof}[Proof]
The coordinate cell is the disjoint union of the internal cylinders of length $n+1$ whose last bit
is $i$. Thus finite-union closure puts it in the measure domain. The finite-level value theorem
identifies its value with the ordinary fair-coin measure of $\{x:x(n)=i\}$: both are the same finite
sum of normalized cylinder values. The one-coordinate product calculation gives $1/2$.
The positivity criterion in §{sec:internal-null-quotients} then puts the class in the condition set.
\end{proof}

Set $I:=\omega\times2$ and form the entire decision table and its name:
$$\begin{gathered}
T:=\{\Pair{a}{q(\MembershipFiber{Y_M}{a})}:a\in I\},\\
\dot r:=\ForcingDecisionName{P}{I}{T}.
\end{gathered}$$

\begin{theorem*}[\termdefine{Internal random-real decision tables}]
The entire table $T$ belongs to $M$ and is a subset of $I\times P$. The set $\dot r$ is a $P$-name
belonging to $M$, with the explicit form
$$\dot r=\{\Pair{\check{\Pair{n}{i}}}{q(\InternalBitCell{M}{n}{i})}:
 n\in\omega,\ i\in2\}.$$
For any set $G$ meeting $P$, its valuation satisfies
$$\Pair{n}{i}\in\dot r^G
\quad\longleftrightarrow\quad q(\InternalBitCell{M}{n}{i})\in G.$$
\end{theorem*}

\begin{proof}[Proof]
The label set and internal Cantor space belong to the model. For each label, bounded Separation
constructs its membership fiber. A candidate output class is specified by a bounded existential
quantifier over the measure domain: the intermediate set must be that membership fiber, and its
pair with the output must belong to the already constructed quotient map. The shared subset
predicate and graph lookup express these tests. The coordinate-cell lemma supplies every intermediate
set in the measure domain, and the quotient construction supplies the unique output in the model.
Bounded-predicate interpretation and the shared definable-graph construction collect the whole table
by Replacement. This proves internality of the table, rather than only internality of each entry.

The coordinate-cell lemma also puts every table value in the positive condition set. Apply
§{sec:forcing-names-valuation} to the entire internal relation to obtain the name and its internality.
Its explicit form follows by writing each label as a coordinate-bit pair. The general evaluation
formula for decision names gives the displayed bit test, since the table has exactly one value at
each label. No genericity assumption is needed for this evaluation formula.
\end{proof}

\begin{corollary*}[\termdefine{Recovering the binary graph from its decisions}]
Suppose $x\in\CantorSpace$ and $G$ meets $P$. If, for every $n\in\omega$ and $i\in2$,
$$q(\InternalBitCell{M}{n}{i})\in G\quad\longleftrightarrow\quad x(n)=i,$$
then $\dot r^G$ is exactly the graph of $x$.
\end{corollary*}

\begin{proof}[Proof]
Every element of the valuation is a coordinate-bit label. For such a label, the theorem and the
assumed bit test identify membership in the valuation with membership in the binary graph.
Extensionality gives equality of the whole sets.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
比較定理に引き継ぐモデル公理、内部可算加法性、cylinder正規化と近似クラスの設定。比較写像の構成は後続定理で別に対応済み。)
--> To compare the internal random-real name with the filter construction, we must compare the conditions
on which they are based. Retain the model and measure assumptions of
§{sec:internal-borel-measure-identification}, including Choice, the internal countable-additivity
clause, and the fair-coin normalization. Write $E$ for null equivalence on $D$, $q$ for its quotient
map, and $P$ for the positive classes constructed in §{sec:internal-null-quotients}.
Use $\mathcal R_M$ for the sets with internal two-sided approximations from
§{sec:internal-finite-measure-bounds}.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Internal approximations under finite Boolean operations}]
If $A,B\in\mathcal R_M$, then $A\cup B$ and $\SetDifference{A}{B}$ belong to $\mathcal R_M$.
\end{lemma*}

\begin{proof}[Proof]
Given $\varepsilon>0$, choose closed inner and open outer approximants for each set with error less
than $\varepsilon/2$. For the union, take the union of the two closed approximants and the union of
the two open approximants. §{sec:internal-finite-measure-bounds} constructs their entire codes
in the model: finite unions of downward-closed trees represent unions of their bodies, and unions
of open word codes represent unions of their open sets. If the inner approximants are $F,K$ and the
outer approximants are $U,V$, then
$$\begin{aligned}
\mu(\SetDifference{(U\cup V)}{(F\cup K)})
&\le\mu(\SetDifference{U}{F})+\mu(\SetDifference{V}{K})\\
&<\varepsilon.
\end{aligned}$$
Thus the union has the required approximants. Complementation was proved in
§{sec:internal-finite-measure-bounds}; apply it twice to
$\SetDifference{A}{B}=(A^c\cup B)^c$.
\end{proof}

Let $A,B\in\mathcal R_M$ be measurable, and let $X,Y\in D$ be subsets of $Y_M$ with
$$\begin{aligned}
g_{i(x)}\in X&\quad\longleftrightarrow\quad g_{i(x)}\in M\land x\in A,\\
g_{i(x)}\in Y&\quad\longleftrightarrow\quad g_{i(x)}\in M\land x\in B.
\end{aligned}$$
Thus the internal sets contain exactly the old point graphs lying in the corresponding external
sets. Write

\begin{mathmeta}
  \define{MeasureClass}
\end{mathmeta}

$\MeasureClass{\mu}{A}$ for the class of a measurable set in the external measure algebra
$\MeasureAlg{\CantorSpace}{\mu}$.

\begin{theorem*}[\termdefine{Faithful comparison of internal measure classes}]
The internal and external differences have the same measure:
$$\nu(\SetDifference{X}{Y})=\mu(\SetDifference{A}{B}).$$
Consequently,
$$\begin{aligned}
\MeasureClass{\mu}{A}\le\MeasureClass{\mu}{B}
&\quad\longleftrightarrow\quad\nu(\SetDifference{X}{Y})=0,\\
\MeasureClass{\mu}{A}=\MeasureClass{\mu}{B}
&\quad\longleftrightarrow\quad q(X)=q(Y),\\
\MeasureClass{\mu}{A}\ne\bot&\quad\longleftrightarrow\quad\nu(X)>0.
\end{aligned}$$
\end{theorem*}

\begin{proof}[Proof]
The difference of the internal sets belongs to the measure domain by its finite closure laws.
The point-membership characterization passes to differences, and the preceding lemma supplies
internal approximations of the external difference. Apply the squeezing argument of
§{sec:internal-borel-measure-identification}; its closed-value hypothesis is supplied uniformly by
§{sec:internal-finite-measure-laws}. This proves the measure identity without constructing a
new difference code.

The external measure-algebra order is inclusion modulo a null difference. Since the measure is
finite, vanishing of its real value is equivalent to vanishing of its measure value. This gives the
order equivalence. Apply it in both directions and use the internal null-class criterion to obtain
the equality equivalence. Finally, the same squeezing theorem gives $\nu(X)=\mu(A)$.
Nonnegativity and the characterization of the zero measure class give the positivity equivalence.
\end{proof}

Now suppose every $X\in D$ is the internal interpretation of a valid Borel code whose entire label
graph belongs to $M$. This is the representation requirement for using the model's Borel domain;
finite measure laws alone do not supply Borel codes for its elements.

\begin{theorem*}[\termdefine{Embedding the internal Borel measure classes}]
There is an injective map
$$\eta:\SetQuotient{D}{E}\longrightarrow\MeasureAlg{\CantorSpace}{\mu}$$
with the following property. Let $X\in D$ be a subset of $Y_M$, and let $A\in\mathcal R_M$ be measurable.
If $g_{i(x)}\in X$ holds exactly when $g_{i(x)}\in M\land x\in A$, then
$$\eta(q(X))=\MeasureClass{\mu}{A}.$$
In particular, this identity holds for the internal and full external interpretations of every
valid internal Borel code. Moreover, for $X,Y\in D$ and $C\in\SetQuotient{D}{E}$,
$$\begin{aligned}
\eta(q(X))\le\eta(q(Y))&\quad\longleftrightarrow\quad\nu(\SetDifference{X}{Y})=0,\\
\eta(C)\ne\bot&\quad\longleftrightarrow\quad C\in P.
\end{aligned}$$
\end{theorem*}

\begin{proof}[Proof]
Choose a valid internal Borel code for each element of the measure domain, and take its full external
interpretation. §{sec:internal-approximation-errors} supplies internal two-sided approximations
for each of these measurable sets. Choose a representative of each internal null class and assign
the external measure class of the selected interpretation. These choices are made in the ambient
universe.

The faithful comparison theorem shows that any measurable set with internal approximations and the
same old-point membership gives the same external class. This proves the stated representative
identity and independence of the choices. The theorem also shows that equality of the assigned
external classes forces equality of the internal classes, proving injectivity. Its order and
positivity criteria give the remaining assertions.
\end{proof}

### Names, Filters, and Valuation {#sec:internal-random-filter-valuation}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
null差による順序と正条件のorder
embeddingはmeasureClassImage_le_iff/internalConditionEmbeddingへ対応済み。
残りは仮定の再掲とfilter transport補題を先に扱う旨の案内のみ。)
--> Retain the assumptions and notation of §{sec:internal-null-quotients}.<!--
formalization: skip-end
-->
Order the internal positive classes by $q(X)\le q(Y)$ if $\nu(\SetDifference{X}{Y})=0$.
The comparison theorem makes this well-defined and turns the restriction of $\eta$ to $P$ into an
order embedding into the external positive measure classes $Q_+$.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
null差による順序と正条件のorder
embeddingはmeasureClassImage_le_iff/internalConditionEmbeddingへ対応済み。
残りは仮定の再掲とfilter transport補題を先に扱う旨の案内のみ。)
--> We first record how filters pass through such an embedding.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{FilterTransport}
\end{mathmeta}

\begin{lemma*}[\termdefine{Transporting filters through an order embedding}]
Let $e:P_0\to Q_0$ be an order embedding and $G$ a filter on $P_0$.
Then the upward closure of its image,
$$\FilterTransport{e}{G}:=\{b\in Q_0:\exists a\in G\ (e(a)\le b)\},$$
is a filter on $Q_0$. For every $a\in P_0$,
$$e(a)\in\FilterTransport{e}{G}\quad\longleftrightarrow\quad a\in G.$$
\end{lemma*}

\begin{proof}[Proof]
The image is nonempty, and its upward closure is upward closed.
For two members of that closure, choose preimages in the filter below them. A common strengthening
of the preimages maps to a common strengthening in the closure, proving directedness.
If $e(a)$ belongs to the closure, some $b\in G$ satisfies $e(b)\le e(a)$.
Order reflection gives $b\le a$, so upward closure of $G$ gives $a\in G$.
The converse follows directly from the definition.
\end{proof}

\begin{lemma*}[\termdefine{Cylinder and bit conditions under comparison}]
The comparison map sends the internal cylinder and coordinate conditions to their external classes:
$$\begin{aligned}
\eta(q(\InternalCylinder{M}{s}))&=\MeasureClass{\mu}{\cyl{s}},\\
\eta(q(\InternalBitCell{M}{n}{i}))&=\MeasureClass{\mu}{\{x:x(n)=i\}}.
\end{aligned}$$
\end{lemma*}

\begin{proof}[Proof]
The internal sets contain exactly the old point graphs satisfying the indicated cylinder or bit test.
Basic cylinders have internal approximations by §{sec:internal-finite-measure-bounds}.
The bit set is the finite union of the cylinders of length $n+1$ whose last bit is $i$.
The finite-union lemma in §{sec:internal-null-quotients} therefore supplies its internal
approximations as well. Both external sets are measurable, so the representative identity for the
comparison map applies. Their measures are $2^{-\Length{s}}$ and $1/2$, respectively, so both identities
also hold in the positive condition orders.
\end{proof}

\begin{mathmeta}
  \define{InternalRandomLength}
\end{mathmeta}

For each $n\in\omega$, define the internal length requirement by
$$\InternalRandomLength{M}{n}:=
\{p\in P:\exists s\in\funcspace{n}{2}\ (p\le q(\InternalCylinder{M}{s}))\}.$$
We now construct these sets inside the model and prove their density.

\begin{mathmeta}
  \define{InternalMeasureCone}
\end{mathmeta}

\begin{lemma*}[\termdefine{Internal order and length tests}]
For each $X\in D$, the lower cone
$$\InternalMeasureCone{X}:=\{p\in P:p\le q(X)\}$$
belongs to $M$. The entire order relation
$$\mathcal O:=\{\Pair{p}{r}\in P\times P:p\le r\}$$
and every length requirement $\InternalRandomLength{M}{n}$ also belong to $M$.
\end{lemma*}

\begin{proof}[Proof]
The quotient map $q$ and the positive condition set $P$ already belong to $M$.
For $p\in P$, membership in the lower cone has the bounded description
$$\begin{aligned}
p\in\InternalMeasureCone{X}\quad\longleftrightarrow\quad
&\exists A\in D\ \exists U\in D\ \bigl(\Pair{A}{p}\in q\\
&\qquad{}\land U=\SetDifference{A}{X}\land\Pair{U}{\emptyset}\in F\bigr).
\end{aligned}$$
The last clause says that the difference has value zero, since the empty cut code represents zero.
Closure of the measure domain under differences supplies the intermediate set.
The comparison theorem identifies this null-difference test with the order on classes.
The shared bounded predicates for set difference and graph membership therefore give the whole
lower cone by Separation on $P$.

For the order relation, use the bounded description
$$\begin{aligned}
\Pair{p}{r}\in\mathcal O\quad\longleftrightarrow\quad
&p,r\in P\ \land\ \exists X\in D\ \bigl(\Pair{X}{r}\in q\\
&\qquad{}\land p\in\InternalMeasureCone{X}\bigr).
\end{aligned}$$
Substitute the preceding bounded description for the last membership test and apply Separation
on $P\times P$. This constructs the entire relation, rather than just its individual ordered pairs.
Finally,
$$\InternalRandomLength{M}{n}
=\bigcup_{s\in\funcspace{n}{2}}\InternalMeasureCone{\InternalCylinder{M}{s}}.$$
There are finitely many words of this length, and every corresponding cylinder belongs to $D$.
Each cone is therefore internal, and closure under finite unions puts their union in $M$.
\end{proof}

\begin{lemma*}[\termdefine{Density of internal length tests}]
For each $n\in\omega$, the set $\InternalRandomLength{M}{n}$ is dense in $P$ and closed under strengthening.
\end{lemma*}

\begin{proof}[Proof]
Take $p=q(A)\in P$, so $\nu(A)>0$.
The Borel representation assumption puts every member of $D$ inside $Y_M$.
The internal cylinders of length $n$ partition $Y_M$, and hence
$$A=\bigcup_{s\in\funcspace{n}{2}}\bigl(A\cap\InternalCylinder{M}{s}\bigr).$$
Each intersection belongs to $D$, since
$$A\cap B=\SetDifference{A}{(\SetDifference{A}{B})}.$$
If every intersection had value zero, finite subadditivity and nonnegativity would give $\nu(A)=0$.
Choose a word $s$ for which the intersection has positive value and set
$$r:=q(A\cap\InternalCylinder{M}{s}).$$
Then $r\in P$, $r\le p$, and $r\le q(\InternalCylinder{M}{s})$, proving density.
The two order inequalities follow because the corresponding differences are empty.
Transitivity of the order shows closure under further strengthening.
\end{proof}

\begin{theorem*}[\termdefine{Evaluation of the internal random-real name}]
Let $G$ be a filter on $P$ meeting every $\InternalRandomLength{M}{n}$, and put
$H:=\FilterTransport{\eta}{G}$.
Then $H$ meets every external length requirement $C_n$ of §{sec:random-forcing-detail}.
If $r_H$ is the binary sequence constructed there, the valuation of the internal name from
§{sec:internal-null-quotients} is its graph:
$$\dot r^G=g_{i(r_H)}.$$
\end{theorem*}

\begin{proof}[Proof]
A condition of $G$ below an internal cylinder of length $n$ maps to a condition of $H$ below the
corresponding external cylinder. Hence $H$ meets $C_n$, and the filter-union construction gives $r_H$.
For each coordinate, its bit is characterized by
$$r_H(n)=i\quad\longleftrightarrow\quad\MeasureClass{\mu}{\{x:x(n)=i\}}\in H.$$
Indeed, the cylinder determined by the first $n+1$ bits of $r_H$ belongs to $H$.
If its last bit is $i$, its class lies below the displayed bit class, which therefore belongs to $H$.
If its last bit differs from $i$, the cylinder and bit set are disjoint, so their classes cannot both
belong to a filter of positive conditions.

The image-membership equivalence and the preceding comparison lemma now give
$$\begin{aligned}
q(\InternalBitCell{M}{n}{i})\in G
&\quad\longleftrightarrow\quad\MeasureClass{\mu}{\{x:x(n)=i\}}\in H\\
&\quad\longleftrightarrow\quad r_H(n)=i.
\end{aligned}$$
Apply the graph-recovery corollary of §{sec:internal-null-quotients}.
\end{proof}

\begin{corollary*}[\termdefine{The filter real belongs to the valuation extension}]
Under the same hypotheses, $g_{i(r_H)}\in M[G]$.
\end{corollary*}

\begin{proof}[Proof]
The decision-table construction gives a $P$-name $\dot r\in M$.
Its valuation belongs to $M[G]$ by the definition of that extension, and the theorem identifies
this valuation with the graph of the filter real.
\end{proof}

\begin{corollary*}[\termdefine{The random-real name in a generic extension}]
Let $G$ be an $M$-generic filter on $P$, and put $H:=\FilterTransport{\eta}{G}$.
Then $H$ determines a binary sequence $r_H$ by its cylinder decisions, and
$$\dot r^G=g_{i(r_H)}\in M[G].$$
\end{corollary*}

\begin{proof}[Proof]
Each internal length test is dense and belongs to $M$, so genericity makes $G$ meet it.
The valuation theorem and its extension-membership corollary now apply.
\end{proof}

## Borel Truth in Generic Extensions {#sec:random-borel-truth}

### Dense Decisions and Borel Names {#sec:internal-random-union-tests}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部順序関係と全lower coneの所属はinternalNullOrder_mem/internalNullCone_memへ対応済み。
残りは測度域・商の記号と、可算加法性を全グラフがモデル内の族に限定する前提の再掲。)
--> Retain the internal measure domain $D$, measure graph $F$, quotient map $q$, and positive order $P$
from §{sec:internal-random-filter-valuation}. Write $\nu$ for the decoded internal measure.
Assume that it is countably additive on families whose entire sequence graph belongs to $M$, as in<!--
formalization: skip-end
-->
§{sec:internal-finite-measure-laws}. The order relation $\mathcal O$ and all lower cones
$\InternalMeasureCone{B}$ belong to $M$.

\begin{lemma*}[\termdefine{Internal decision tests}]
If $S\in M$ and $S\IncludedIn P$, then
$$\ForcingDecision{S}
=S\cup\{p\in P:\forall r\in P\ (r\le p\Longrightarrow r\notin S)\}$$
belongs to $M$ and is dense in $P$. Every $M$-generic filter therefore meets it.
For $E\in M$ with $E\IncludedIn D$, the set
$$S:=\bigcup_{B\in E}\InternalMeasureCone{B}$$
also belongs to $M$, so the same conclusion applies to its decision test.
\end{lemma*}

\begin{proof}[Proof]
Replace $r\le p$ by $\Pair{r}{p}\in\mathcal O$. The displayed condition is bounded,
so Separation constructs the decision test. Its density is the general decision lemma of
§{sec:random-forcing-detail}: either a condition has a strengthening in $S$, or it already
belongs to the negative alternative. For the family of lower cones, membership says
$\exists B\in E\ (p\in\InternalMeasureCone{B})$. Substitute the bounded lower-cone test from
§{sec:internal-random-filter-valuation} and apply Separation on $P$.
This constructs the whole union without choosing an enumeration of $E$.
\end{proof}

\begin{lemma*}[\termdefine{Positive intersections with an internal union}]
Let $B_n\in D$, assume that the graph of $\Sequence{B_n}{n\in\omega}$ belongs to $M$, and put $U:=\bigcup_n B_n$.
If $A\in D$, $\nu(A)>0$, and $\nu(\SetDifference{A}{U})=0$, then
$$\exists n\in\omega\quad\nu(A\cap B_n)>0.$$
\end{lemma*}

\begin{proof}[Proof]
Suppose every intersection has measure zero. Put
$$H_n:=\bigcup_{i<n}B_i,\qquad C_n:=\SetDifference{A}{H_n}.$$
The finite-union construction in §{sec:internal-finite-measure-laws} puts the entire sequence
$H_n$ in $M$. The bounded difference predicate and graph collection then put the entire sequence
$C_n$ in $M$. Explicitly, its output $C$ at index $n$ is characterized by
$\exists B\in\GraphRange{H}\ (\Pair{n}{B}\in H\land C=\SetDifference{A}{B})$,
where $H$ is the sequence graph. Each output is internal by Separation, so Replacement collects the graph.
Finite subadditivity gives $\nu(A\cap H_n)=0$, and finite additivity gives $\nu(C_n)=\nu(A)$.
But $C_n$ decreases to $\SetDifference{A}{U}$. Continuity from above in
§{sec:internal-finite-measure-laws} forces this constant positive sequence of values to tend to $0$,
a contradiction.
\end{proof}

\begin{theorem*}[\termdefine{Generic witnesses for internal unions}]
Let $B_n\in D$, let the graph of $\Sequence{B_n}{n\in\omega}$ belong to $M$, and suppose $U:=\bigcup_n B_n\in D$.
For every $M$-generic filter $G$ on $P$,
$$\begin{aligned}
&\exists p\in G\ (p\le q(U))\\
&\qquad\Longleftrightarrow\quad
\exists n\in\omega\ \exists r\in G\ (r\le q(B_n)).
\end{aligned}$$
\end{theorem*}

\begin{proof}[Proof]
The range $E:=\{B_n:n\in\omega\}$ belongs to $M$, so the first lemma puts
$S:=\bigcup_{B\in E}\InternalMeasureCone{B}$ and $\ForcingDecision{S}$ in $M$.
Suppose $p\in G$ and $p\le q(U)$. We claim that $S$ is dense below $p$.
Given any $q(A)\le p$, the order definition gives $\nu(\SetDifference{A}{U})=0$.
The preceding lemma supplies $n$ with $\nu(A\cap B_n)>0$.
The condition $q(A\cap B_n)$ lies below $q(A)$ and belongs to $\InternalMeasureCone{B_n}$,
proving the claim.

Choose a member of $G\cap\ForcingDecision{S}$. Its negative alternative is impossible:
a common strengthening with $p$ could be strengthened into $S$, contradicting that alternative.
Thus some $r\in G$ belongs to $S$, and its witnessing $B_n$ proves the forward implication.
Conversely, $B_n\IncludedIn U$ gives $q(B_n)\le q(U)$, so any witness on the right is also a witness on the left.
\end{proof}

\begin{corollary*}[\termdefine{Generic witnesses at Borel union nodes}]
Let $c$ be a well-founded Borel code whose whole label graph belongs to $M$.
Write $A_t$ for its internal Cantor interpretation at a node $t$, and assume these sets belong to $D$.
At every union node $s$, the preceding theorem applies with
$$B_n:=A_{s\concat\SingletonSeq{n}},\qquad U:=A_s.$$
In particular, the condition that the entire child sequence belongs to $M$ follows from the code.
\end{corollary*}

\begin{proof}[Proof]
The internal child-family construction of §{sec:internal-approximation-errors} gives the whole
sequence of Baire interpretations. Intersect each value with $Y_M$ to obtain the Cantor interpretations.
This operation preserves an internal whole graph: apply the fixed-difference construction twice,
using $A\cap Y_M=\SetDifference{Y_M}{(\SetDifference{Y_M}{A})}$.
The Borel node equation gives $A_s=\bigcup_n A_{s\concat\SingletonSeq{n}}$ exactly as sets of old point graphs.
The preceding theorem now applies to this constructed sequence.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
forcing notionを符号化したPと順序関係、必要なモデル公理を固定する文と、Gに依存しない名前をこれから作るという案内。
実定義separatedName/powerSetName/functionSpaceName/borelInterpretationNameはいずれ
もGを入力に持たず、値の同定は後続定理で別に対応。)
--> Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
Let $P,\mathcal O\in M$ code a forcing notion and its order.
We construct names in the ground model whose valuations give the function spaces and Borel sets
of every generic extension. The constructions are independent of the choice of generic filter.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{ForcingSeparationName,ForcingPowerSetName,ForcingFunctionSpaceName,CantorSpaceName}
\end{mathmeta}

Write $\ForcingSeparationName{\tau}{\varphi}{\vec\nu}$ for the name constructed in
§{sec:generic-separation}. For every $M$-generic filter $G$, it satisfies
$$\begin{aligned}
\bigl(\ForcingSeparationName{\tau}{\varphi}{\vec\nu}\bigr)^G
=\{z\in\tau^G:M[G]\models\varphi(\vec\nu^G,z)\}.
\end{aligned}$$
Thus a formula with ground-model parameter names selects a subset of the valuation of a fixed name.

For $\tau\in M^P$, the proof in §{sec:generic-power-set} constructs the ground-model sets
$$\begin{aligned}
B_\tau&:=\bigl(\bigcup\bigcup\tau\bigr)\times P,\\
C_\tau&:=\{\theta\in\InternalPowerSet{M}{B_\tau}:\theta\in M^P\},\\
\Pi_\tau&:=C_\tau\times P.
\end{aligned}$$
Every subset of $\tau^G$ belonging to the extension has a name in $C_\tau$.
Let $\psi(a,z)$ be the bounded formula $z\IncludedIn a$, and define
$$\ForcingPowerSetName{\tau}:=\ForcingSeparationName{\Pi_\tau}{\psi}{\tau}.$$
For $A,B\in M$, let $\chi(A,B,g)$ be the bounded formula saying that $g$ is a function graph
from $A$ to $B$, and define
$$\begin{aligned}
\rho_{A,B}&:=\ForcingPowerSetName{\check{(A\times B)}},\\
\ForcingFunctionSpaceName{A}{B}&:=
\ForcingSeparationName{\rho_{A,B}}{\chi}{\Pair{\check A}{\check B}}.
\end{aligned}$$

\begin{theorem*}[\termdefine{Uniform power-set and function-space names}]
These constructions give names in $M^P$. For every $M$-generic filter $G$,
$$\begin{aligned}
\bigl(\ForcingPowerSetName{\tau}\bigr)^G&=\InternalPowerSet{M[G]}{\tau^G},\\
\bigl(\ForcingFunctionSpaceName{A}{B}\bigr)^G&=\funcspace{A}{B}\cap M[G].
\end{aligned}$$
In the second equality, functions are identified with their graphs.
\end{theorem*}

\begin{proof}[Proof]
The bounded-name family and its all-conditions name belong to the ground model by
§{sec:generic-power-set}; internal Separation then constructs the power-set name.
Its valuation consists of those members of $\Pi_\tau^G$ included in $\tau^G$.
Every such member belongs to the extension. Conversely, every extension subset of $\tau^G$ has a
bounded name, so it lies in $\Pi_\tau^G$ and passes the subset test. This proves the first equality.

The checked product has value $A\times B$. Its power-set name therefore ranges over all extension
subsets of that product. The shared bounded function predicate is absolute in the transitive
extension, and the checked parameters have values $A$ and $B$. Applying the same Separation-name
construction selects exactly the function graphs belonging to the extension, proving the second equality.
\end{proof}

In particular, put
$$\CantorSpaceName:=\ForcingFunctionSpaceName{\omega}{2}.$$
Its value is $Y_{M[G]}$, the set of binary point graphs in the extension.
For a well-founded Borel code $c$ with its entire label graph in $M$, let $\vec a_c$ be the eight
parameters of the membership formula $\Phi$ in §{sec:internal-borel-sets}, using the standard cylinder
enumeration and the root node. The internal finite-word, label-slice, and canonical-basis constructions
put every parameter in $M$. Use their componentwise check names and define
$$\BorelCodeName{c}:=\ForcingSeparationName{\CantorSpaceName}{\Phi}{\check{\vec a_c}}.$$
The interpretation of the code in a model is the set denoted by $\BorelInterpretation{c}{M}$ in
§{sec:borel-codes-why}.

\begin{theorem*}[\termdefine{Names for interpreted Borel sets}]
The construction gives $\BorelCodeName{c}\in M^P$, and for every $M$-generic filter $G$,
$$\bigl(\BorelCodeName{c}\bigr)^G=\BorelInterpretation{c}{M[G]}.$$
Write $A_c$ for the full external interpretation of the code on Cantor space.
If $\tau\in M^P$ has value $\tau^G=g_{i(x)}$ for a binary sequence $x$, then
$$\tau^G\in\bigl(\BorelCodeName{c}\bigr)^G\quad\longleftrightarrow\quad x\in A_c.$$
\end{theorem*}

\begin{proof}[Proof]
Check-name closure and the internal Separation construction give the displayed name in $M^P$.
The preceding theorem supplies its ambient set of binary graphs. The extension is transitive and
satisfies the elementary axioms and Separation needed in §{sec:internal-borel-sets}.
Each checked parameter evaluates to the same ground-model set. Apply the uniform interpretation
formula there to the extension and to any binary point graph it contains. External well-foundedness
of the code identifies the truth set at all nodes, so $\Phi$ holds at the root exactly when the
binary point belongs to $A_c$. The Separation valuation identity therefore gives precisely the
internal interpretation in $M[G]$, proving equality of the whole sets.
For the final assertion, the value of any ground-model name belongs to the extension; apply this
membership characterization to the specified value of $\tau$.
\end{proof}

### Truth and the Forcing Relation {#sec:internal-random-borel-truth}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部random orderとmeasure graphを引き継ぎ、Y_Mと測度域の包含条件を仮定する導入。
負のdecisionを有限加法性から得る実証明は直後の補題で対応済み。)
--> Use the internal random order and measure of §{sec:internal-random-union-tests}.
Let $Y_M$ be the internal Cantor space, assume $Y_M\in D$, and assume every member of $D$ is a subset of $Y_M$.
We first identify the negative alternative in a decision test using finite additivity alone.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Internal complement decisions}]
For $B\in D$,
$$\ForcingNeg{\InternalMeasureCone{B}}
=\InternalMeasureCone{\SetDifference{Y_M}{B}}.$$
Consequently, for every $M$-generic filter $G$,
$$\begin{aligned}
&\exists p\in G\ (p\le q(\SetDifference{Y_M}{B}))\\
&\qquad\Longleftrightarrow\quad
\neg\exists p\in G\ (p\le q(B)).
\end{aligned}$$
\end{lemma*}

\begin{proof}[Proof]
A positive condition cannot lie below two disjoint internal sets $B,C$.
Indeed, if $q(A)$ did so, both $\SetDifference{A}{B}$ and $\SetDifference{A}{C}$ would have measure zero.
Their union is $A$, because $B\cap C=\emptyset$, so finite subadditivity would contradict $\nu(A)>0$.
It follows that every condition below $q(\SetDifference{Y_M}{B})$ has no strengthening below $q(B)$.

Conversely, let $p=q(A)$ have no strengthening below $q(B)$.
If $\nu(A\cap B)>0$, the condition $q(A\cap B)$ would be such a strengthening.
Thus $\nu(A\cap B)=0$. Since $A\IncludedIn Y_M$,
$$\SetDifference{A}{(\SetDifference{Y_M}{B})}=A\cap B,$$
and the order criterion gives $p\le q(\SetDifference{Y_M}{B})$.
This proves the set equality. By §{sec:internal-random-union-tests}, the filter meets
$\ForcingDecision{\InternalMeasureCone{B}}$.
The positive and negative alternatives cannot both occur in a filter, by directedness.
If no positive witness occurs, the decision test therefore supplies a negative one, proving the equivalence.
\end{proof}

\begin{theorem*}[\termdefine{Internal Borel truth at every node}]
Let $c$ be a valid Borel code whose entire label graph belongs to $M$.
For each node $s$, let $A_s$ be its full external Cantor interpretation and let $A_s^M$ be its internal
interpretation. Assume $A_s^M\in D$ for every node.
Let $G$ be $M$-generic and let $r_G$ be the real constructed from its cylinder decisions in
§{sec:internal-random-filter-valuation}. Then, at every node,
$$r_G\in A_s\quad\Longleftrightarrow\quad
\exists p\in G\ (p\le q(A_s^M)).$$
\end{theorem*}

\begin{proof}[Proof]
Induct along the well-founded child relation of the code.
An absent node has empty interpretation, and no positive condition lies below the empty class.
At a leaf, restrict the labeled Baire cylinder to binary points.
If its finite word contains a nonbinary entry, this restriction is empty.
Otherwise it is a binary cylinder, whose internal class is sent to the actual cylinder class by the
comparison map. The cylinder decisions of the transported filter therefore give the required equivalence.
This uses the already constructed filter real, rather than an assumed atomic truth relation.

At a union node, §{sec:internal-random-union-tests} constructs the entire internal child sequence and proves
that the filter selects the union exactly when it selects one term. Apply the induction hypothesis to
that child. Absent children contribute empty sets and may be included in the sequence.
At a complement node, validity gives exactly one present child. All other children have empty interpretation,
so the external set is the complement of that child's set and the internal set is its complement in $Y_M$.
The preceding complement lemma and the induction hypothesis prove the equivalence at this node.
These cases exhaust the labels, completing the induction.
\end{proof}

\begin{corollary*}[\termdefine{Internal random Borel truth}]
Under these assumptions,
$$\begin{aligned}
&r_G\in\BorelInterpretation{c}{M[G]}\\
&\qquad\Longleftrightarrow\quad
\exists p\in G\ (p\le q(\BorelInterpretation{c}{M})).
\end{aligned}$$
If $\nu(\BorelInterpretation{c}{M})=0$, then $r_G\notin\BorelInterpretation{c}{M[G]}$.
\end{corollary*}

\begin{proof}[Proof]
The random-real name evaluates to the graph of $r_G$, so this graph belongs to $M[G]$ by
§{sec:internal-random-filter-valuation}. The Borel interpretation in the extension consists exactly of
its point graphs satisfying the full external interpretation. Apply the theorem at the root to obtain the
identity. If the internal measure is zero, the comparison map sends its class to zero.
No positive condition can lie below that value, so the right-hand side is false.
\end{proof}

\begin{theorem*}[\termdefine{Forcing for the internal random-real name}]
Retain the assumptions of the internal Borel truth theorem, and suppose that $M$ is externally countable.
For every condition $p\in P$,
$$p\forces^*\dot r\in\BorelCodeName{c}
\quad\Longleftrightarrow\quad p\le q(\BorelInterpretation{c}{M}).$$
The same equivalence holds for semantic forcing $\forces$.
For $p=q(A)$, the right-hand side is equivalent to
$\nu(\SetDifference{A}{\BorelInterpretation{c}{M}})=0$.
\end{theorem*}

\begin{proof}[Proof]
Write $B:=\BorelInterpretation{c}{M}$.
The valuation identities of §{sec:internal-random-union-tests} and §{sec:internal-random-filter-valuation},
together with the internal Borel truth theorem, give for every $M$-generic filter $G$
$$\begin{aligned}
\dot r^G\in\bigl(\BorelCodeName{c}\bigr)^G
&\quad\Longleftrightarrow\quad r_G\in\BorelInterpretation{c}{M[G]}\\
&\quad\Longleftrightarrow\quad\exists t\in G\ (t\le q(B)).
\end{aligned}$$
If $p\le q(B)$, every generic filter containing $p$ satisfies this membership statement, with $p$ itself
as a witness. By the agreement with semantic forcing proved in §{sec:internal-generic-truth},
$p$ syntactically forces it.

Conversely, write $p=q(A)$ and suppose $p\not\le q(B)$.
The order criterion gives $\nu(\SetDifference{A}{B})>0$.
Hence $r:=q(\SetDifference{A}{B})$ is a condition below $p$.
No positive condition can lie below both $r$ and $q(B)$, since their representatives are disjoint,
as proved in the complement lemma above.
External countability supplies an $M$-generic filter $G$ containing $r$; upward closure also puts $p$ in $G$.
If the displayed membership statement held, the truth identity would supply a condition $t\in G$ below $q(B)$.
A common strengthening of $r$ and $t$ would contradict disjointness.
Thus this generic extension refutes membership, so $p$ does not force it.
Finally, the null-difference criterion for the internal order proves the last assertion.
\end{proof}

## Recovering Generic Filters from Random Points {#sec:random-point-recovery}

### Point Filters and Measure Covers {#sec:internal-random-point-filters}

\begin{mathmeta}
  \vars{i,j,k,n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
全内部Borel解釈を測度域Dとするこの節の設定とA_cの表記。
LeanのHasInternalBorelRepresentativesと全内部code解釈のdomain所属hcodeが両方向の要求を保持し、
これを有限測度則から導いたとは扱わない。)
--> Retain the transitive-model assumptions and the internal measure comparison of
§{sec:internal-random-borel-truth}. For a valid ground-model code $c$, write
$A_c:=i^{-1}(\BorelValue{c})$ for its full external Cantor interpretation.
In this section, $D$ consists of all sets $\BorelInterpretation{c}{M}$ for such codes.
Thus every internal class has a coded representative, and each constructed ground-model code again
has its internal interpretation in $D$.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Internal Boolean code constructors}]
If the entire label graphs of valid codes $c,d$ belong to $M$, then the codes for their complements,
finite unions, intersections, differences, and symmetric differences have entire label graphs in $M$.
For a sequence of valid codes $c_n$, let $\ell_n$ be the entire label graph of $c_n$.
If $H:=\{\Pair{n}{\ell_n}:n\in\omega\}\in M$, then the label graph of
$\BorelUnionCode{(c_n)}$ belongs to $M$ as well.
\end{lemma*}

\begin{proof}[Proof]
Use the finite-word graphs and the cons predicate of §{sec:internal-list-coding}.
For a fixed root label $a$ and child table $H$, the grafted labels are
$$g([])=a,\qquad g(n::s)=c_n(s).$$
The root case is a finite equality test. In the other case, bound $n$ by $\omega$, the tail by the internal
finite-word set, and the child graph by the range of $H$.
The cons predicate recognizes the input word, and two graph lookups recover the child graph and its label.
This is a bounded predicate. The shared reflection theorem and graph collection therefore put the whole
label graph of $g$ in $M$.

For a complement, take root label $2$, put $c$ at child $0$, and use the absent expression at every other child.
Its child table is defined by the two cases $n=0$ and $n\ne0$, so the same graph-collection principle constructs it.
For a union, take root label $1$ and use $H$ directly.
Finite unions use a two-valued child table; complements and finite unions then give intersections,
differences, and symmetric differences.
Their validity and interpretation equations follow from the complement and union equations
in §{sec:borel-codes-why}.
\end{proof}

\begin{lemma*}[\termdefine{Coded null defects}]
Every finite Boolean defect of coded representatives has a code in $M$.
When its two sides represent the same measure class, its full external interpretation is null.
A sequence of such null codes has a null union code in $M$ whenever its entire sequence of label graphs belongs to $M$.
If $r$ avoids every null Borel set coded in $M$, then for any ground-model codes $c,d$,
$$[A_c]\le[A_d]\quad\Longrightarrow\quad(r\in A_c\Longrightarrow r\in A_d).$$
In particular, $[A_c]=[A_d]$ implies that their membership tests at $r$ agree.
\end{lemma*}

\begin{proof}[Proof]
Apply the preceding constructors to the zero and one representatives, or to the symmetric differences
between the representative of an operation and that operation on representatives.
Equality of measure classes makes each symmetric difference null; the zero representative and the
complement of the one representative are null as well. Countable subadditivity makes the coded union null.
For the order assertion, the difference $\SetDifference{A_c}{A_d}$ has a code in $M$ and is null.
The point $r$ cannot belong to that difference. Applying this in both directions proves the equality case.
\end{proof}

\begin{theorem*}[\termdefine{Internal point filter from a null-avoiding real}]
Suppose that $r$ avoids every null Borel set coded in $M$. Write $\ell_c$ for the entire label graph of $c$. Put
$$\begin{aligned}
G_r:=\{p\in P:{}&\exists c\in\BorelCodes\;[\ell_c\in M\ \land\\
&r\in A_c\ \land\ q(\BorelInterpretation{c}{M})\le p]\}.
\end{aligned}$$
Then $G_r$ is a filter on the internal positive order.
For any coded representative of $p$, that is, any $c$ with $\eta(p)=[A_c]$,
$$p\in G_r\quad\Longleftrightarrow\quad r\in A_c.$$
Thus membership in the filter is independent of the chosen ground-model representative.
\end{theorem*}

\begin{proof}[Proof]
The fixed code for the whole space supplies a member of $G_r$.
Whenever $r\in A_c$, the class of its internal interpretation is positive: if it were zero, measure comparison
would make $A_c$ a coded null set containing $r$.
For two witnesses $c,d$, their intersection code is internal, and its external interpretation contains $r$.
Its positive class strengthens both conditions. Upward closure follows directly from the definition.

For the membership criterion, a witness $d$ for $p\in G_r$ satisfies $[A_d]\le\eta(p)=[A_c]$.
The preceding lemma therefore gives $r\in A_c$.
Conversely, if $r\in A_c$, the code $c$ itself is a witness. The equality case of the preceding lemma gives
independence of representatives.
\end{proof}

\begin{corollary*}[\termdefine{Recovery of an internal generic filter}]
Let $G$ be an $M$-generic filter on $P$ and let $r_G$ be the real obtained by evaluating the random-real name.
Then $r_G$ avoids every null Borel set coded in $M$, and $G_{r_G}=G$.
\end{corollary*}

\begin{proof}[Proof]
The random-real construction supplies the actual real and its cylinder decisions.
Every node of a ground-model code has an internal re-rooted code, so its interpretation belongs to $D$.
Thus §{sec:internal-random-borel-truth} applies to every such code and proves the asserted null-set avoidance.
For a condition $p$, choose a coded representative $c$. The point-filter criterion and Borel truth give
$$p\in G_{r_G}\ \Longleftrightarrow\ r_G\in A_c
\ \Longleftrightarrow\ \exists t\in G\ (t\le p)
\ \Longleftrightarrow\ p\in G.$$
The last equivalence is upward closure, with $p$ itself witnessing the reverse implication.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
dense集合からのconull coverと全符号列が必要になる理由の説明。外部可算性だけから内部列所属を結論しないという注意で、
コード選択の実証明は後続のinternal_borel_code_sequenceが与える。)
--> For an arbitrary null-avoiding real, genericity follows once dense sets supply conull coded covers.
§{sec:internal-random-point-filters} constructs internally chosen finite families whose union is conull.
To apply the internal union constructor, the entire sequence of representative codes' label graphs must also
belong to $M$. External countability of ground-model codes alone does not ensure this.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限cover補題に使う測度域・value graph・ambient Yと族Eの前提、および次に扱う構成の案内。)
--> Retain the finite measure domain $D$, cut range $R$, graph $F$, and decoded measure $\nu$ of
§{sec:internal-finite-measure-laws}. Let $Y\in D$ and let $E\IncludedIn D$ be a family of subsets of $Y$.
The following finite approximation will supply countable covers without a maximal-antichain construction.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Finite approximate covers}]
For every $\varepsilon>0$, there is a finite list $B_0,\ldots,B_{k-1}$ of members of $E$ such that, with
$U:=\bigcup_{i<k}B_i$,
$$\nu(\SetDifference{B}{U})\le\varepsilon\qquad(B\in E).$$
The empty list is allowed, with union $\emptyset$.
\end{lemma*}

\begin{proof}[Proof]
If no such list exists, every finite union $U$ of members of $E$ admits a further $B\in E$ with
$\nu(\SetDifference{B}{U})>\varepsilon$. Finite additivity gives
$$\nu(U\cup B)=\nu(U)+\nu(\SetDifference{B}{U}).$$
Starting with $U_0=\emptyset$, finite induction therefore gives a union $U_n$ of $n$ members of $E$ with
$\nu(U_n)\ge n\varepsilon$. But $U_n\IncludedIn Y$, so monotonicity gives $\nu(U_n)\le\nu(Y)$.
Choose $n>\nu(Y)/\varepsilon$ to obtain a contradiction.
\end{proof}

\begin{theorem*}[\termdefine{Internally chosen finite covers}]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, Replacement, and Choice.
Assume $D,R,F,E,Y\in M$. There are finite function graphs $f_n:k_n\to E$ and sets
$U_n=\bigcup_{i<k_n}f_n(i)\in D$ such that
$$\begin{gathered}
\{\Pair{n}{\Pair{f_n}{U_n}}:n\in\omega\}\in M,\\
\{\Pair{n}{f_n}:n\in\omega\}\in M,\qquad
\{\Pair{n}{U_n}:n\in\omega\}\in M,\\
\nu(\SetDifference{B}{U_n})\le\frac1{n+1}\qquad(n\in\omega,\ B\in E).
\end{gathered}$$
Assume further that $\nu$ satisfies the internal countable-additivity law of
§{sec:internal-finite-measure-laws} and that every $A\in D$ with $A\IncludedIn Y$ and $\nu(A)>0$
contains some $B\in E$ with $\nu(B)>0$. Then
$$C:=\bigcup_n U_n\in D,\qquad \nu(\SetDifference{Y}{C})=0.$$
\end{theorem*}

\begin{proof}[Proof]
For each $n$, apply the finite approximation lemma with $\varepsilon=1/(n+1)$.
The graph of the resulting finite list belongs to $M$ by §{sec:internal-borel-inputs}, and its finite union
belongs to $D$, hence to $M$. Thus its ordered pair with that union belongs to $M$.

To choose all these pairs internally, bound the candidate graph $f$ by
$K:=\InternalPowerSet{M}{\omega\times E}$ and its union $U$ by $D$.
Require $f:k\to E$ for some $k\in\omega$, require $U\IncludedIn Y$, and express the union by
$$x\in U\quad\longleftrightarrow\quad
\exists B\in E\;\exists i\in\omega\;(\Pair{i}{B}\in f\ \land\ x\in B)
\qquad(x\in Y).$$
For every $B\in E$, choose $W\in D$ and $V\in R$ with
$$W=\SetDifference{B}{U},\qquad\Pair{W}{V}\in F,\qquad\Pair{1}{n+1}\notin V.$$
The last condition is exactly $\nu(W)\le1/(n+1)$ because $V$ is the strict rational cut for $\nu(W)$.
Successor identifies $n+1$ inside $\omega$, and the difference equation is a bounded membership test.
All these conditions therefore form one bounded predicate on $n$ and the output pair.

Apply the shared reflection theorem and internal countable choice to this predicate. This produces the entire
sequence of pairs in $M$. Bounded projection and graph collection give both component sequences in $M$.

For the final assertion, first check $C\in D$ using only internal families.
Put $P_n:=\bigcup_{i<n}U_i$ and $W_n:=\SetDifference{Y}{P_n}$.
The partial-union and relative-complement constructions put both whole sequence graphs in $M$.
The sets $W_n\in D$ decrease. Internal continuity from above gives $\bigcap_nW_n\in D$, and taking its
complement in $Y$ gives $C\in D$.

If $\nu(\SetDifference{Y}{C})>0$, the density hypothesis supplies $B\in E$ with
$B\IncludedIn\SetDifference{Y}{C}$ and $\nu(B)>0$. Since every $U_n$ lies in $C$,
$$0<\nu(B)=\nu(\SetDifference{B}{U_n})\le\frac1{n+1}\qquad(n\in\omega),$$
which is impossible. Nonnegativity proves that the complement has measure zero.
\end{proof}

\begin{lemma*}[\termdefine{Internal dense representative families}]
Retain the model axioms above. Suppose $D,F,\Delta\in M$, let $q$ be the null-quotient map, and let
$\Delta$ be dense in its positive part. The order is characterized by
$$q(B)\le q(A)\quad\longleftrightarrow\quad\nu(\SetDifference{B}{A})=0.$$
Then the family
$$E:=\{B\in D:q(B)\in\Delta\}$$
belongs to $M$. Every $A\in D$ with $\nu(A)>0$ contains some $C\in E$ with $\nu(C)>0$.
\end{lemma*}

\begin{proof}[Proof]
The entire quotient map $q$ belongs to $M$ by §{sec:internal-null-quotients}. For $B\in D$, the condition
$\exists p\in\Delta\;(\Pair{B}{p}\in q)$ is bounded, so Separation gives $E\in M$.
For positive $A$, choose $p\in\Delta$ with $p\le q(A)$, and choose $B\in D$ with $q(B)=p$.
Put $C:=B\cap A$. Finite ring closure gives $C\in D$, and
$$\SetDifference{C}{B}=\emptyset,\qquad
\SetDifference{B}{C}=\SetDifference{B}{A},\qquad\nu(\SetDifference{B}{A})=0.$$
Thus $q(C)=q(B)=p$, so $C\in E$ and $\nu(C)>0$, while $C\IncludedIn A$ as an actual subset.
\end{proof}

\begin{lemma*}[\termdefine{Flattening internal finite rows}]
Retain the model axioms above except Choice. Let $E,d\in M$, and suppose the entire sequence graph
$H:=\{\Pair{n}{f_n}:n\in\omega\}$ belongs to $M$, where $f_n:k_n\to E$ and $k_n\in\omega$.
Using the numerical pairing of §{sec:internal-natural-arithmetic}, define
$$V_{\NatPair{n}{i}}:=\begin{cases}
f_n(i),&i<k_n,\\
d,&k_n\le i.
\end{cases}$$
Then
$$\{\Pair{j}{V_j}:j\in\omega\}\in M,\qquad
\{V_j:j\in\omega\}=\{d\}\cup\bigcup_n\GraphRange{f_n}.$$
In particular, for $d=\emptyset$,
$$\bigcup_jV_j=\bigcup_n\bigcup\GraphRange{f_n}.$$
\end{lemma*}

\begin{proof}[Proof]
The numerical pairing graph and $\GraphRange{H}$ belong to $M$. To read a row $f$ at column $i$, require
$$\Pair{i}{y}\in f\quad\lor\quad
\bigl(y=d\ \land\ \neg\exists z\in E\;(\Pair{i}{z}\in f)\bigr).$$
Since $f$ is a function with finite ordinal domain, this bounded predicate specifies exactly one output.
Given $j$, quantify $n,i$ over $\omega$ and $f$ over $\GraphRange{H}$, require
$j=\NatPair{n}{i}$ and $\Pair{n}{f}\in H$, and use the row predicate.
Bounded reflection and graph collection give the entire graph of $V$ in $M$.
Every output is either $d$ or an entry of a row, and every row entry occurs at its paired index.
The unused column $k_0$ in row $0$ also gives $V_{\NatPair{0}{k_0}}=d$, proving the range formula.
The union identity follows because adjoining $\emptyset$ does not change a union.
\end{proof}

\begin{theorem*}[\termdefine{Internal conull sequences for dense sets}]
Retain all the model axioms above, including Choice. Assume $D,R,F,Y,\Delta\in M$, $Y\in D$, and
$A\IncludedIn Y$ for every $A\in D$. Assume the internal countable-additivity law, and let $\Delta$ be dense
in the positive null quotient with the order described above. There is a sequence of sets $V_j$ such that
$$\begin{gathered}
\{\Pair{j}{V_j}:j\in\omega\}\in M,\qquad
V_j\in D,\qquad V_j=\emptyset\ \lor\ q(V_j)\in\Delta,\\
C:=\bigcup_jV_j\in D,\qquad\nu(\SetDifference{Y}{C})=0.
\end{gathered}$$
\end{theorem*}

\begin{proof}[Proof]
Form $E=\{B\in D:q(B)\in\Delta\}$ by the dense representative lemma. It belongs to $M$ and satisfies the
actual-subset density hypothesis of the finite-cover theorem. That theorem supplies the entire sequence of
finite graphs $f_n:k_n\to E$ in $M$, with $U_n=\bigcup\GraphRange{f_n}$ and internally conull union.
Flatten these rows with default value $\emptyset$. The flattening lemma gives the entire graph of $V$ in $M$,
identifies its nonempty entries as members of $E$, and preserves the union. All the assertions follow.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前に得た全内部集合列を、後続の内部Borel code選択へ渡す順序の案内。全code候補集合を先に構成する必要を説明する文で、
新しい選択原理を仮定していない。)
--> This constructs a whole internal sequence of sets. §{sec:internal-borel-code-recognition} lifts it to
a whole internal sequence of Borel label graphs, as required by the union constructor in
§{sec:internal-random-point-filters}. Its proof uses the internal candidate set constructed next.<!--
formalization: skip-end
-->

### Representatives and Genericity {#sec:internal-borel-code-recognition}

\begin{mathmeta}
  \vars{r}{Name}
  \vars{n}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部representative選択の目的、モデル公理、既出の有限語グラフ・即時拡大関係、全label graphの型を固定する設定。
実際の局所規則はlocalShapePredicate、全valid code集合はinternalValidCodes_memへ別に対応済み。)
--> To choose representative codes internally, we first construct the set from which they will be chosen.
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, Replacement, and Choice.
Use the finite-word set $T$, word graph $e(s)$, and immediate-extension relation $J(t,s)$ of
§{sec:internal-borel-inputs}. A label graph is a function $\ell:T\to\omega$.<!--
formalization: skip-end
-->

Let $L(\ell)$ assert the following local rules, with all node variables ranging over $T$:

* $\ell(e(\emptyset))\ne0$.
* If $J(t,s)$ and $\ell(t)\ne0$, then $\ell(s)\ne0$.
* If $\ell(s)\notin\{0,1,2\}$ and $J(t,s)$, then $\ell(t)=0$.
* If $\ell(s)=1$, there is $t$ with $J(t,s)$ and $\ell(t)\ne0$.
* If $\ell(s)=2$, there is exactly one such $t$.

These are bounded conditions: each label test is membership of an ordered pair in $\ell$, and the
immediate-extension test is bounded as well.

\begin{lemma*}[\termdefine{Local recognition of Borel label graphs}]
Every label graph determines a unique expression. More precisely, if $\ell:T\to\omega$, there is a unique
$c:\finseq{\omega}\to\omega$ such that
$$\ell=\{\Pair{e(s)}{c(s)}:s\in\finseq{\omega}\}.$$
The condition $L(\ell)$ is equivalent to the local labeling rules for $c$.
\end{lemma*}

\begin{proof}[Proof]
Read $c(s)$ from the unique value of $\ell$ at $e(s)$. Every element of $T$ is the graph of exactly one finite
word, so this recovers the entire graph, and the labels determine $c$ uniquely.
For word graphs, $J(e(t),e(s))$ means $t=s\concat\SingletonSeq{k}$ for some $k$.
Distinct $k$ give distinct children. Substituting this characterization into the five displayed rules gives
exactly the root, prefix, leaf, union, and complement clauses for the expression.
\end{proof}

Put
$$R_\ell:=\{\Pair{t}{s}\in T\times T:
J(t,s)\land\ell(t)\ne0\land\ell(s)\ne0\}.$$
The relation graph belongs to $M$ when $\ell\in M$. Let $W(T,R)$ be the internal subset-minimum formula
of §{sec:internal-rank-existence}: every nonempty subset of $T$ belonging to the model has an $R$-minimal
member. Define a first-order formula $\Phi(\ell)$ by requiring that $\ell:T\to\omega$, that $L(\ell)$ holds,
and that there exists a relation graph $R=R_\ell$ satisfying $W(T,R)$.
The relation equation is bounded, using a subset of $T\times T$ and tests on all pairs of nodes.
The well-foundedness clause uses the subset-minimum formula; we do not regard it as a local bounded test.

\begin{theorem*}[\termdefine{Internal recognition of Borel validity}]
For every $\ell\in M$, the assertion $M\models\Phi(\ell)$ holds if and only if $\ell$ is the label graph
of an externally valid Borel expression.
\end{theorem*}

\begin{proof}[Proof]
The bounded function and local-rule predicates have their actual meanings in the transitive model.
The preceding lemma therefore recovers the expression and its local rules. Bounded recognition of the relation
graph identifies $R$ with $R_\ell$, whose edges are exactly the live-child edges under the bijection $e$.
By §{sec:internal-rank-existence}, $M\models W(T,R_\ell)$ is equivalent to actual well-foundedness of this
relation. Pulling the relation back along $e$ gives precisely the remaining validity clause for the expression.
Conversely, an externally valid expression supplies the local rules and actual well-foundedness.
Its relation graph belongs to $M$, and actual well-foundedness supplies minima for all internal nonempty
subsets. Thus the same graph witnesses $\Phi(\ell)$ in $M$.
\end{proof}

\begin{corollary*}[\termdefine{Internal set of valid Borel codes}]
There is a set $\mathcal C\in M$ whose members are exactly the label graphs in $M$ of externally valid
Borel expressions.
\end{corollary*}

\begin{proof}[Proof]
Form the internal power set $P:=\InternalPowerSet{M}{T\times\omega}$ and apply Separation to $\Phi$ on $P$.
Every actual label graph in $M$ lies in $P$, since it is a subset of $T\times\omega$.
The recognition theorem identifies the resulting set exactly as claimed.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
モデル仮定と内部Cantor space・全valid code集合・canonical basisを固定する前提。
これらの所属は先行するinternalCantor_mem/internalValidCodes_mem/canonicalBasisWordGrap
h_memを利用し、新しい構成を主張しない。)
--> Retain the model axioms of §{sec:internal-borel-code-recognition}. Write $Y$ for the internal Cantor space
and $\mathcal C$ for the internal set of valid label graphs. The parameters for the canonical cylinder basis
belong to $M$ by §{sec:internal-borel-inputs}.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Uniform recognition of Borel representatives}]
There is one first-order formula $\Psi(A,\ell)$, with fixed parameters in $M$, such that for $A,\ell\in M$,
$$\begin{aligned}
&M\models\Psi(A,\ell)\\
&\quad\Longleftrightarrow\quad
\exists c\;[c\text{ is valid},\ \ell=\ell_c,\ A=\BorelInterpretation{c}{M}],
\end{aligned}$$
where $\ell_c$ is the entire label graph of $c$ and the interpretation is taken on Cantor space.
\end{lemma*}

\begin{proof}[Proof]
Require $\ell\in\mathcal C$. Quantify its live-child relation $R_\ell$ and the two slices of nodes labeled
$1$ and $2$, using their bounded graph-membership definitions. For these parameters, the evaluation formula
of §{sec:internal-borel-evaluations} recognizes membership of an internal point in the root interpretation.
Require that $A$ be precisely its fiber inside $Y$: for every $g$ in the model, $g\in A$ if and only if
$g\in Y$ and the root evaluation accepts $g$.

This is a single formula with $A$ and $\ell$ free. The validity test supplies a well-founded code, so the
point-evaluation theorem identifies its fiber with $\BorelInterpretation{c}{M}$.
Transitivity ensures that every element of either set is in the model; extensionality therefore identifies
the whole sets. Conversely, the relation and slices of any such code belong to $M$, and the same pointwise
comparison verifies the formula. We reuse the evaluation formula rather than a separate formula for each code.
\end{proof}

\begin{theorem*}[\termdefine{Internal selection of Borel code sequences}]
Suppose $H:=\{\Pair{n}{V_n}:n\in\omega\}\in M$ and each $V_n$ has a valid Borel representative
whose entire label graph belongs to $M$. Then there are valid codes $c_n$ such that
$$\BorelInterpretation{c_n}{M}=V_n\quad(n\in\omega),\qquad
\{\Pair{n}{\ell_{c_n}}:n\in\omega\}\in M.$$
\end{theorem*}

\begin{proof}[Proof]
The set $S:=\GraphRange{H}$ belongs to $M$. For each $A\in S$, the preceding formula defines the nonempty
set of all $\ell\in\mathcal C$ representing $A$. Apply internal definable choice to this relation to obtain
one function graph $f:S\to\mathcal C$ in $M$, with $M\models\Psi(A,f(A))$ for every $A\in S$.
For each $n$, let $c_n$ be the unique expression with label graph $f(V_n)$.

The whole output table $H'$ is obtained by two graph lookups:
$$\Pair{n}{\ell}\in H'\quad\Longleftrightarrow\quad
\exists A\in S\;(\Pair{n}{A}\in H\ \land\ \Pair{A}{\ell}\in f).$$
This bounded condition determines exactly one output for each $n\in\omega$.
Shared reflection and graph collection put the entire table in $M$.
The formula $\Psi$ gives the required interpretation identity at every entry.
In particular, the proof retains one internal selector throughout; it does not replace it by separate external choices.
\end{proof}

\begin{corollary*}[\termdefine{Internally coded conull covers}]
In the conull-sequence theorem of §{sec:internal-random-point-filters}, let $Y$ be the internal Cantor space
and assume every member of $D$ has a valid Borel representative with label graph in $M$.
There are valid codes $c_j$ whose whole label-graph sequence belongs to $M$, with
$$\BorelInterpretation{c_j}{M}=V_j.$$
The union code $u:=\BorelUnionCode{(c_j)}$ has label graph in $M$ and satisfies
$$\BorelInterpretation{u}{M}=\bigcup_j V_j\in D,\qquad
\nu(\SetDifference{Y}{\BorelInterpretation{u}{M}})=0.$$
\end{corollary*}

\begin{proof}[Proof]
Apply the selection theorem to the entire sequence supplied by the conull-sequence theorem.
Its conclusion is exactly the whole-table hypothesis of the union constructor in
§{sec:internal-random-point-filters}. Membership in the union interpretation is membership in some component
interpretation, so the displayed identities follow. The complement code also belongs to $M$ and is internally null.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
最終genericity定理へ引き継ぐmeasure比較、内部可算加法性、Choiceを含むモデル公理の前提の再掲。)
--> Retain the measure-domain and comparison assumptions of §{sec:internal-random-point-filters}, together with
internal countable additivity and the model axioms above, including Choice.<!--
formalization: skip-end
-->

\begin{theorem*}[\termdefine{Genericity of the null-avoiding point filter}]
If $r\in\CantorSpace$ avoids every Borel null set coded in $M$, then the filter $G_r$ constructed in
§{sec:internal-random-point-filters} is $M$-generic. Its cylinder decisions and random-real valuation satisfy
$$q(\InternalCylinder{M}{s})\in G_r\quad\Longleftrightarrow\quad r\in\cyl{s},\qquad
\dot r^{G_r}=r.$$
In the valuation identity, a point is represented by its function graph.
\end{theorem*}

\begin{proof}[Proof]
Let $\Delta\in M$ be dense in the internal positive order. The preceding corollary supplies codes $c_j$ and
a union code $u$ in $M$, with internally conull union, such that each internal interpretation $V_j$ is empty
or represents a condition in $\Delta$. Measure comparison makes the full external interpretation of the
complement of $u$ null. Since $r$ avoids it, $r\in A_{c_j}$ for some $j$.
The point-filter lemma makes $q(V_j)$ a positive condition in $G_r$.
Consequently $V_j\ne\emptyset$, so $q(V_j)\in\Delta$. This proves genericity.

For a finite binary word $s$, take its one-leaf cylinder code. Its root label is the basis index plus $3$,
and all other labels are $0$. Bounded graph collection puts this entire label graph in $M$.
Its external interpretation is exactly $\cyl{s}$, so the point-filter membership criterion proves the displayed
cylinder equivalence. The random-real valuation theorem now gives a point $y$ with these same cylinder decisions.
For each $n$, both points belong to $\cyl{\restrict{r}{n+1}}$, hence $y(n)=r(n)$.
Thus $y=r$, proving the valuation identity.
\end{proof}

