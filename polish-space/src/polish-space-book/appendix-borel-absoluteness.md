# Appendix: Absoluteness of Borel Codes {#sec:appendix-borel-absoluteness}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
付録全体の内容と、内部評価・rational measure bounds・finite-test
coding・包含移送・次のmeasure付録との依存関係を案内する導入。個々の構成と証明は後続の独立単位として対象に残す。)
--> This appendix compares the interpretation of a Borel code inside a transitive model with its external
interpretation. It builds on the bounded-formula and graph constructions of §{sec:internal-model-closure}.
The first part constructs internal evaluations and compares interpretations at old points. The second starts from
rational measure bounds and develops the ranked certificates needed to transfer closed inclusions. The third supplies
the internal arithmetic and finite-test coding used by those certificates. The final part combines this infrastructure
to transfer inclusions, including at new points. The rational bounds also prepare the measure comparison in
§{sec:appendix-measure-absoluteness}.<!--
formalization: skip-end
-->

## Internal Interpretation {#sec:appendix-borel-internal-interpretation}

### Internal Boolean evaluations {#sec:internal-borel-evaluations}

\begin{mathmeta}
  \vars{E,T}{Set}
\end{mathmeta}

For a fixed point, evaluating a Borel code amounts to marking its true nodes. We construct this set of nodes
inside a transitive model before comparing it with the external evaluation of §{sec:borel-codes}.
Let $T$ be a set of nodes and $R\IncludedIn T\times T$ a well-founded child relation, with
$\Pair{t}{s}\in R$ meaning that $t$ is a child of $s$. Let $U,C,L\IncludedIn T$ be parameters.
The sets $U$ and $C$ specify union and complement nodes; $L$ specifies the true leaves. Define
$$\begin{aligned}
\eta(E,s)&:\equiv\exists t\in T\;(\Pair{t}{s}\in R\land t\in E),\\
\theta(E,s)&:\equiv
\begin{cases}
\eta(E,s),&s\in U,\\
\neg\eta(E,s),&s\notin U,\ s\in C,\\
s\in L,&s\notin U,\ s\notin C.
\end{cases}
\end{aligned}$$
For an actual Borel code, each complement node has exactly one child. The construction below also allows
arbitrary child sets, with a complement node negating the disjunction of its children.

A partial evaluation consists of a domain $D$ and its true-node set $E$, satisfying the formula
$$\begin{aligned}
\sigma(D,E)\;:\equiv\;&D\IncludedIn T\land E\IncludedIn D\\
&{}\land\forall s\in D\;\forall t\in T\;
 (\Pair{t}{s}\in R\longrightarrow t\in D)\\
&{}\land\forall s\in D\;(s\in E\longleftrightarrow\theta(E,s)).
\end{aligned}$$
The parameters $T,R,U,C,L$ are suppressed in this notation. Expanding the subset and ordered-pair clauses
as in §{sec:zfc-absoluteness} makes $\sigma$ a bounded formula. Thus, for parameters and candidate sets in a
transitive model, its internal interpretation recognizes exactly the actual partial evaluations.

\begin{lemma*}[Agreement of partial Boolean evaluations]
If $\sigma(D,E)$ and $\sigma(D',E')$ hold, then
$$s\in D\cap D'\quad\Longrightarrow\quad(s\in E\longleftrightarrow s\in E').$$
\end{lemma*}

\begin{proof}[Proof]
Induct on the well-founded child relation. Every child of a node in both domains belongs to both domains.
The induction hypothesis therefore identifies its truth value in the two evaluations, so it also identifies
the existential child test $\eta$. Negation preserves this agreement, and a leaf uses the same parameter $L$.
The defining equations for the two partial evaluations now give the assertion at the parent.
\end{proof}

\begin{theorem*}[\termdefine{Internal Boolean evaluation}]
Let $M$ be transitive and satisfy Pairing, Union, and Separation. Suppose $T,R,U,C,L\in M$ and
$R$ is well-founded on $T$ in the surrounding universe. There is a unique $E\in M$ such that $\sigma(T,E)$.
Moreover, every external set satisfying $\sigma(T,E)$ is this same set.
\end{theorem*}

\begin{proof}[Proof]
Use Separation inside $M$ to form
$$\begin{aligned}
D_*&:=\{s\in T:M\models\exists D\,\exists E\;(\sigma(D,E)\land s\in D)\},\\
E_*&:=\{s\in T:M\models\exists D\,\exists E\;(\sigma(D,E)\land s\in E)\}.
\end{aligned}$$
These definitions quantify over partial evaluations belonging to $M$, not over all external subsets of $T$.
They use the two displayed first-order formulas with parameters $T,R,U,C,L$.
Transitivity and bounded absoluteness identify the witnesses with actual partial evaluations.

We first show $\sigma(D_*,E_*)$. Certainly $E_*\IncludedIn D_*\IncludedIn T$.
If $s\in D_*$, choose an internal partial evaluation $\Pair{D}{E}$ whose domain contains $s$.
Every child of $s$ belongs to $D$, hence to $D_*$.
On $D$, membership in $E_*$ agrees with membership in $E$: one direction follows by using $\Pair{D}{E}$ as a
witness, and the other by comparing it with any internal partial evaluation witnessing membership in $E_*$.
The same agreement holds at every child of $s$, so $\theta(E_*,s)$ agrees with $\theta(E,s)$.
The equation for $\Pair{D}{E}$ therefore proves the required equation at $s$.

Now prove $D_*=T$ by well-founded induction. Suppose every child of $s\in T$ is in $D_*$.
If $s\notin D_*$, extend the domain by $s$ and put
$$D':=D_*\cup\{s\},\qquad
E':=\begin{cases}E_*\cup\{s\},&\theta(E_*,s),\\E_*,&\neg\theta(E_*,s).\end{cases}$$
Both sets belong to $M$ by Pairing and Union. Old nodes retain their values, since their children already lie
in $D_*$; the new node satisfies its equation by construction. Thus $\sigma(D',E')$ holds.
This internal partial evaluation witnesses $s\in D_*$, a contradiction. Hence every node belongs to $D_*$.
The agreement lemma gives uniqueness even among external complete evaluations.
\end{proof}

Define the first-order truth formula
$$\tau(T,R,U,C,L,s)\;:\equiv\;\exists E\;(\sigma(T,E)\land s\in E).$$
For any external complete evaluation $E$ and any $s\in M$, the theorem and bounded absoluteness give
$$M\models\tau(T,R,U,C,L,s)\quad\Longleftrightarrow\quad s\in E.$$
Indeed, an internal witness must equal $E$ by uniqueness; conversely, the theorem puts $E$ in $M$, so it
itself witnesses the formula. Thus models containing the same parameters compute the same truth value.
This assertion concerns a fixed externally well-founded relation; it does not assert absoluteness of
well-foundedness for arbitrary relations.

\begin{corollary*}[Comparison with Borel-code evaluation]
Let $M$ be transitive and satisfy Pairing, Union, and Separation.
Let $c$ be an externally well-founded Borel expression with basic sets $V_n$, and fix a point $x$.
Write $c(s)$ for the numeric label at $s$, using $0$ for absent, $1$ for union, $2$ for complement,
and $n+3$ for leaf $n$. Suppose a set-coded presentation in $M$ supplies $T,R,U,C,L\in M$ and a bijection
$e:\finseq{\omega}\to T$ with
$$\begin{aligned}
\Pair{e(t)}{e(s)}\in R
&\longleftrightarrow c(s)\ne0\land\exists k\;(t=s\concat\SingletonSeq{k}\land c(t)\ne0),\\
e(s)\in U&\longleftrightarrow c(s)=1,\\
e(s)\in C&\longleftrightarrow c(s)=2,\\
e(s)\in L&\longleftrightarrow\exists n\;(c(s)=n+3\land x\in V_n).
\end{aligned}$$
The bijection only identifies the external word notation with the set-coded nodes. Then the set of nodes
whose interpreted sets contain $x$ belongs to $M$, and its membership relation is given internally by $\tau$.
In particular, the root test agrees with membership of $x$ in the external interpretation of $c$.
\end{corollary*}

\begin{proof}[Proof]
Let $E$ be the set of $e(s)$ such that $x$ belongs to the external set assigned to $s$.
At a union node, this holds exactly when it holds at some present child. At a complement node, it holds
exactly when it fails at the unique child. At a leaf, the condition is precisely $e(s)\in L$; absent nodes
are false. Thus $\sigma(T,E)$ holds. The bijection transports well-foundedness of the child relation to $R$.
The theorem puts this very set $E$ in $M$, and the truth-formula equivalence proves the assertion at every
node, including the root.
\end{proof}

### Set-coded Borel inputs {#sec:internal-borel-inputs}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{a,k,m,n}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
実際のomegaの内部所属はomegaOrdinal_memへ、有限語のgraph表示は既存wordGraphへ接続した。
残る127–129行は次にnode/leaf parametersを作るという案内、節で仮定する公理、自然数を有限von
Neumann順序数で表すという規約の宣言であり、新しい閉包や対応定理をここで証明しない。)
--> We now construct the node and leaf-test parameters required by §{sec:internal-borel-evaluations} for cylinder
codes on Baire space. Throughout this section, $M$ is transitive and satisfies Infinity, Pairing, Union,
Power Set, and Separation. Natural numbers are represented by their finite von Neumann ordinals.<!--
formalization: skip-end
-->
The earlier natural-number lemma gives the actual set $\omega\in M$.
For a finite word $s$, put
$$e(s):=\{\Pair{i}{s(i)}:i<\Length{s}\}.$$
Thus a word is represented by its graph, not by an additional object with unspecified membership properties.

\begin{lemma*}[Finite graphs in a transitive model]
Let $A\in M$ and $n\in\omega$. Every actual function graph $f:n\to A$ belongs to $M$.
\end{lemma*}

\begin{proof}[Proof]
Every value of $f$ belongs to $M$ by transitivity, as does every element of its finite domain.
Pairing therefore puts each ordered pair of the graph in $M$.
The empty graph belongs to $M$. Starting there, adjoin the finitely many graph entries one at a time,
using Pairing and Union to form each insertion. This gives the whole graph $f\in M$.
\end{proof}

\begin{lemma*}[\termdefine{Internal finite-word set}]
The actual set of all finite natural-number words, represented by their graphs, belongs to $M$:
$$T:=\{e(s):s\in\finseq{\omega}\}\in M.$$
\end{lemma*}

\begin{proof}[Proof]
The product and internal power-set constructions give
$$P:=\PowerSet{\omega\times\omega}\cap M\in M.$$
Apply Separation to the bounded function-graph predicate to obtain
$$T':=\{f\in P:\exists n\in\omega\;(f:n\to\omega)\}\in M.$$
Each word graph belongs to $P$ by the preceding lemma and satisfies the displayed predicate.
Conversely, a function on a finite ordinal is the graph of the word listing its values in domain order.
Thus $T'=T$. In particular, this construction retains every external finite word; it does not require
$M$ to contain every external subset of $\omega\times\omega$.
\end{proof}

Graph inclusion recognizes prefixes:
$$e(s)\IncludedIn e(t)\quad\Longleftrightarrow\quad s\prefixOf t.$$
Indeed, inclusion requires every coordinate of the first word to occur in the second with the same value,
and every shorter agreeing word has its graph included in the longer one. This also proves that $e$ is
injective, so it is a bijection from $\finseq{\omega}$ onto $T$.
Immediate extension is recognized by the bounded formula
$$\begin{aligned}
J(t,s)\;:\equiv\;\exists n,m\in\omega\;[&s:n\to\omega\land t:m\to\omega\\
&{}\land m=n\cup\{n\}\land s\IncludedIn t].
\end{aligned}$$
For word graphs,
$$J(e(t),e(s))\quad\Longleftrightarrow\quad\exists k\in\omega\;(t=s\concat\SingletonSeq{k}).$$
To see this, the function-graph clauses determine the two lengths, and inclusion gives a prefix.
Their lengths differ by exactly one, so the remaining suffix has one entry. The converse follows by
appending that entry to the graph.

Let $c$ be a Borel expression, let $b:\omega\to\finseq{\omega}$ specify its basic cylinders, and let
$x\in\BaireSpace$. Encode these three inputs by
$$\begin{aligned}
\ell&:=\{\Pair{e(s)}{c(s)}:s\in\finseq{\omega}\},\\
B&:=\{\Pair{n}{e(b(n))}:n\in\omega\},\\
g&:=\{\Pair{n}{x(n)}:n\in\omega\}.
\end{aligned}$$
Assume these input graphs belong to $M$. No surjectivity of $b$ is needed for evaluation of a fixed code;
when it enumerates all finite words, its cylinders are the usual base of Baire space.

The nonzero-label predicate and the live-child relation are
$$\begin{aligned}
A(s)&:\equiv\exists a\in\omega\;(\Pair{s}{a}\in\ell\land a\ne0),\\
R&:=\{\Pair{t}{s}\in T\times T:J(t,s)\land A(t)\land A(s)\}.
\end{aligned}$$
The two label sets are
$$U:=\{s\in T:\Pair{s}{1}\in\ell\},\qquad
C:=\{s\in T:\Pair{s}{2}\in\ell\}.$$
These sets belong to $M$ by Separation. The graph equations identify their external interpretations with
the child relation, union labels, and complement labels of the given expression.

For the leaves, cylinder membership is the finite graph test
$$x\in\cyl{b(n)}\quad\Longleftrightarrow\quad e(b(n))\IncludedIn g.$$
Consequently form
$$\begin{aligned}
L:=\{s\in T:\exists n,m\in\omega\;[&m=n+3\land\Pair{s}{m}\in\ell\\
&{}\land\exists w\in T\;(\Pair{n}{w}\in B\land w\IncludedIn g)]\}.
\end{aligned}$$
Here the offset relation is a first-order set-theoretic formula: with
$$S(a,b):\equiv b=a\cup\{a\},$$
replace $m=n+3$ by
$$\exists a\,\exists d\;(S(n,a)\land S(a,d)\land S(d,m)).$$
By transitivity, each successor equation recognizes the actual set operation. Hence any internal witnesses
must satisfy $a=n+1$, $d=n+2$, and $m=n+3$. Conversely, when $m=n+3$, choose $a=n+1$ and $d=n+2$;
these intermediate ordinals belong to $M$ by Pairing and Union. Thus the internal formula has exactly the
displayed meaning. Separation gives $L\in M$. By the input graph equations, these are exactly the leaf nodes
whose cylinders contain the fixed point.

\begin{theorem*}[\termdefine{Internal evaluation of cylinder codes}]
Suppose the Borel expression $c$ is externally well-founded and its input graphs $\ell,B,g$ above belong to
$M$. Then there is $E\in M$ such that, for every finite word $s$,
$$e(s)\in E\quad\Longleftrightarrow\quad x\in A_s,$$
where $A_s$ is the external set assigned to $s$ using the cylinders $\cyl{b(n)}$ at the leaves.
In particular, the test at $s=\emptyset$ agrees with membership in the interpreted Borel set.
\end{theorem*}

\begin{proof}[Proof]
The preceding constructions put $T,R,U,C,L$ in $M$ using just the stated axioms and input graphs.
The correspondence $s\mapsto e(s)$ is a bijection and identifies the live-child relations, so it transfers
external well-foundedness. The comparison theorem in §{sec:internal-borel-evaluations} now applies and
puts the actual external truth set in $M$. Its nodewise equations give the displayed equivalence.
\end{proof}

### Internal Borel sets and old points {#sec:internal-borel-sets}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
点のgraph表示はpointGraphへ接続し、
X_Mの内部所属と外部列との対応は既存のfunction-space構成とpointGraph認識へ接続済み。
残る233行は既存の仮定とcylinder presentationを保って点を変えるという段落の案内だけである。)
--> Keep the assumptions and cylinder presentation of §{sec:internal-borel-inputs}, but now vary the point.<!--
formalization: skip-end
-->
For $x\in\BaireSpace$, write
$$g_x:=\{\Pair{n}{x(n)}:n\in\omega\}.$$
The internal function-space construction gives
$$X_M:=\funcspace{\omega}{\omega}\cap M\in M,$$
where functions in this formula are sets of ordered pairs.
Every $g\in X_M$ is $g_x$ for a unique external sequence $x$: its value at the finite ordinal $n$
is a unique finite ordinal, which specifies $x(n)$. Conversely, every $g_x\in M$ belongs to $X_M$.
Thus $X_M$ consists exactly of the point graphs available in $M$.

Write $\lambda(\ell,B,g,t)$ for the leaf predicate defining $L$ in §{sec:internal-borel-inputs}.
Specify its entire truth set by the first-order formula
$$\begin{aligned}
\chi(\ell,B,g,L)\;:\equiv\;&L\IncludedIn T\\
&{}\land\forall t\in T\;
(t\in L\longleftrightarrow\lambda(\ell,B,g,t)).
\end{aligned}$$
The parameters $\omega,T$ are suppressed. For $g,L\in M$, this formula holds internally exactly when
$L$ is the actual leaf-truth set associated with $g$.
Indeed, transitivity makes the bounded quantifier range over every actual member of $T$, and the preceding
leaf calculation identifies the membership test. The subset clause excludes all other elements.

Now let $\sigma_L$ denote the partial-evaluation formula of §{sec:internal-borel-evaluations} with leaf parameter $L$.
Define
$$\begin{aligned}
\Phi(\ell,B,t,g)\;:\equiv\;\exists L\,\exists E\;
\bigl(&\chi(\ell,B,g,L)\\
&{}\land\sigma_L(T,E)\land t\in E\bigr).
\end{aligned}$$
Here $\omega,T,R,U,C$ are additional fixed parameters. This is one formula for all points and nodes;
it contains no external evaluation as a parameter.

\begin{theorem*}[\termdefine{Internal Borel interpretation}]
Suppose $c$ is externally well-founded and $\ell,B\in M$. For every finite word $s$, Separation gives
$$A_s^M:=\{g\in X_M:M\models\Phi(\ell,B,e(s),g)\}\in M.$$
For every external point $x$,
$$g_x\in A_s^M\quad\Longleftrightarrow\quad g_x\in M\ \text{and}\ x\in A_s,$$
where $A_s$ is the external cylinder-code evaluation.
At the root, $A_{\emptyset}^M$ is $\BorelInterpretation{c}{M}$ under the function-graph convention.
\end{theorem*}

\begin{proof}[Proof]
Fix $g_x\in X_M$. The leaf construction gives its actual set $L\in M$, and the internal-evaluation theorem
gives the actual truth set $E\in M$. These witness $\Phi(\ell,B,e(s),g_x)$ whenever $x\in A_s$.
Conversely, any internal witnesses must use that same leaf set by $\chi$; bounded absoluteness makes the
second witness a complete actual evaluation. Uniqueness of evaluations then gives $e(s)\in E$ exactly when
$x\in A_s$. All fixed parameters belong to $M$ by the preceding constructions, including $e(s)\in M$.
Separation on $X_M$ therefore constructs precisely the displayed set, with no requirement that all external
points belong to $M$.
\end{proof}

\begin{corollary*}[\termdefine{Restriction of Borel interpretations}]
Let $M\IncludedIn N$ be two transitive models satisfying the preceding axioms and containing the same input
graphs $\ell,B$. If $c$ is externally well-founded, then
$$A_s^N\cap X_M=A_s^M$$
for every finite word $s$. More generally, two such models agree on membership at every point whose graph
belongs to both models, without any inclusion assumption.
\end{corollary*}

\begin{proof}[Proof]
Every $g\in X_M$ has the form $g_x$ and also belongs to $X_N$. Apply the theorem in both models:
membership is equivalent to the same external condition $x\in A_s$. This proves both inclusions in the
set equality. The same equivalence proves agreement for a point shared by two arbitrary models.
The argument uses the common input graphs and external well-foundedness; it does not require the models to
have the same ordinals.
\end{proof}

### Cantor-space interpretations {#sec:internal-cantor-borel-sets}

\begin{mathmeta}
  \vars{w}{Seq}
  \vars{i}{Fun(Name,Name)}
  \vars{b}{Fun(Nat,Seq(Nat))}
\end{mathmeta}

The random-forcing presentation uses binary sequences rather than arbitrary natural-number sequences.
Let $i:\CantorSpace\to\BaireSpace$ be the coordinatewise inclusion, and let $b(n)$ be finite binary words.
Write $\widehat b(n)$ for the same words viewed as natural-number words. For a fixed externally well-founded
expression $c$, let $A_s$ be its evaluation on $\BaireSpace$ with leaf cylinders $\cyl{\widehat b(n)}$,
and let $D_s$ be its evaluation on $\CantorSpace$ with leaf cylinders $\cyl{b(n)}$.
The syntax and child relation are unchanged; only the leaf sets and the ambient space of complements change.

\begin{lemma*}[\termdefine{Cantor restriction of Borel evaluations}]
At every node $s$,
$$i^{-1}(A_s)=D_s.$$
\end{lemma*}

\begin{proof}[Proof]
For every finite binary word $w$, the coordinate test gives $i^{-1}(\cyl{\widehat w})=\cyl{w}$,
where $\widehat w$ is the same word over $\omega$. Inverse images preserve the empty set and countable unions,
and convert complements by
$$i^{-1}(\SetDifference{\BaireSpace}{A})=\SetDifference{\CantorSpace}{i^{-1}(A)}.$$
Thus $s\mapsto i^{-1}(A_s)$ satisfies exactly the node equations defining $D_s$.
Uniqueness of evaluation by well-founded induction gives the result.
\end{proof}

Keep the transitive-model assumptions of §{sec:internal-borel-sets}. Encode each bit by the finite ordinal
$0$ or $1$, so the graph $g_{i(x)}$ also represents the binary sequence $x$.
The internal function-space construction gives
$$Y_M:=\funcspace{\omega}{2}\cap M\in M.$$
Every member is the graph of a unique external binary sequence: each value lies in $2=\{0,1\}$.
Conversely, every such graph belonging to $M$ is in $Y_M$. In particular, $Y_M\IncludedIn X_M$.

\begin{theorem*}[\termdefine{Internal Cantor Borel interpretation}]
Assume $c$ is externally well-founded and the label graph and the basis graph for $n\mapsto\widehat b(n)$
belong to $M$. For every node $s$, the internal Baire interpretation $A_s^M$ gives
$$D_s^M:=A_s^M\cap Y_M\in M.$$
For each external binary sequence $x$,
$$g_{i(x)}\in D_s^M\quad\Longleftrightarrow\quad g_{i(x)}\in M\ \text{and}\ x\in D_s.$$
\end{theorem*}

\begin{proof}[Proof]
Both $A_s^M$ and $Y_M$ belong to $M$. Separation with the parameter $Y_M$ forms their intersection;
transitivity ensures that the internal membership predicate has its actual meaning.
The characterization of $Y_M$, the internal Baire interpretation theorem, and the preceding lemma give
$$\begin{aligned}
g_{i(x)}\in D_s^M
&\longleftrightarrow g_{i(x)}\in M\ \text{and}\ i(x)\in A_s\\
&\longleftrightarrow g_{i(x)}\in M\ \text{and}\ x\in D_s.
\end{aligned}$$
In particular, the complement clause uses the model's binary points as its ambient space.
\end{proof}

\begin{corollary*}[\termdefine{Restriction of Cantor Borel interpretations}]
For two such models $M\IncludedIn N$ containing the same input graphs,
$$D_s^N\cap Y_M=D_s^M.$$
More generally, the two interpretations agree at every binary point whose graph belongs to both models,
even without an inclusion assumption.
\end{corollary*}

\begin{proof}[Proof]
Every graph in $Y_M$ also belongs to $Y_N$. In either model the membership test is equivalent to the same
external condition $x\in D_s$, which proves the equality. The same argument applies to each common point
without an inclusion assumption.
\end{proof}

## Ranks and Inclusion Certificates {#sec:appendix-borel-rank-witnesses}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次のrational measure boundsからranked counterexample treesへ進む節順の説明。数値比較やtree
inclusionの具体的な定理はそれぞれのstatement/proof単位として対象に残す。)
--> We first state the rational bounds that reduce measure comparison to closed-tree inclusions. Ranked counterexample
trees then express these inclusions in a form that can be recognized and constructed inside the model.<!--
formalization: skip-end
-->

### Rational bounds for coded measures {#sec:coded-measure-bounds}

\begin{mathmeta}
  \vars{q,r}{Rat}
  \vars{a}{Real}
  \vars{s}{Seq}
\end{mathmeta}

We next isolate the numerical part of measure comparison. Let $\mu$ be fair-coin measure on $\CantorSpace$.
For a downward-closed binary tree $T$, put
$$\begin{aligned}
T_n&:=T\cap\funcspace{n}{2},\qquad C_n(T):=\bigcup_{s\in T_n}\cyl{s},\\
d_n(T)&:=\frac{\Card{T_n}}{2^n}\in\QQ.
\end{aligned}$$
We allow the empty tree and dead ends. The definition uses the entire finite level, not just nodes known to
extend to infinite branches.

\begin{lemma*}[\termdefine{Finite-level formula for closed measure}]
For every downward-closed binary tree $T$,
$$\mu(\TreeBody{T})=\inf_n d_n(T)=\lim_{n\to\infty}d_n(T).$$
\end{lemma*}

\begin{proof}[Proof]
Distinct words of length $n$ have disjoint cylinders, each of measure $2^{-n}$. Finite additivity gives
$\mu(C_n(T))=d_n(T)$. Downward closure makes $C_n(T)$ decrease with $n$, and the definition of a branch gives
$$\TreeBody{T}=\bigcap_n C_n(T).$$
Continuity from above in the probability space proves the formula. In particular, dead ends are harmless:
their cylinders disappear from the decreasing intersection.
\end{proof}

\begin{corollary*}[\termdefine{Rational cuts for closed and open measures}]
For every $q\in\QQ$,
$$\begin{aligned}
\mu(\TreeBody{T})<q
&\longleftrightarrow\exists n\;d_n(T)<q,\\
q\le\mu(\TreeBody{T})
&\longleftrightarrow\forall n\;q\le d_n(T),\\
q<\mu(\SetDifference{\CantorSpace}{\TreeBody{T}})
&\longleftrightarrow\exists n\;q<1-d_n(T).
\end{aligned}$$
The first equivalence, for all rational $q$, determines the real number $\mu(\TreeBody{T})$ uniquely.
\end{corollary*}

\begin{proof}[Proof]
The decreasing sequence $d_n(T)$ converges to the closed measure and never falls below it. Therefore a strict
upper bound holds exactly when it already holds at a finite stage. Negation gives the second equivalence,
and subtraction from $1$ gives the third. Two different real numbers have a rational strictly between them,
so they cannot have the same strict rational upper bounds.
\end{proof}

\begin{theorem*}[\termdefine{Closed-tree bounds for Borel measure}]
For every Borel set $A\IncludedIn\CantorSpace$ and every $\varepsilon>0$, there are downward-closed binary trees
$T,S$ such that
$$\begin{gathered}
\TreeBody{T}\IncludedIn A,\qquad
\TreeBody{S}\IncludedIn\SetDifference{\CantorSpace}{A},\\
1-\mu(\TreeBody{S})-\mu(\TreeBody{T})<\varepsilon.
\end{gathered}$$
In particular,
$$\mu(\TreeBody{T})\le\mu(A)\le1-\mu(\TreeBody{S}).$$
\end{theorem*}

\begin{proof}[Proof]
Closed-set regularity from §{sec:borel-measures-radon} gives a closed set $F$ and an open set $U$ with
$$F\IncludedIn A\IncludedIn U,\qquad\mu(\SetDifference{U}{F})<\varepsilon.$$
Take $T=\ClosedTreeCode{F}$ and $S=\ClosedTreeCode{U^c}$. Their bodies are $F$ and $U^c$, respectively, by the
closed-set coding theorem. Since $F\IncludedIn U$, finite additivity gives
$$\begin{aligned}
1-\mu(U^c)-\mu(F)&=\mu(U)-\mu(F)\\
&=\mu(\SetDifference{U}{F})<\varepsilon.
\end{aligned}$$
The two inclusions give the stated lower and upper bounds by monotonicity and complementation.
\end{proof}

\begin{corollary*}[\termdefine{Tree certificate for a rational measure bound}]
For a Borel set $A\IncludedIn\CantorSpace$ and $q\in\QQ$, the inequality $q<\mu(A)$ is equivalent to the existence
of a downward-closed binary tree $T$ and $r\in\QQ$ such that
$$\TreeBody{T}\IncludedIn A,\qquad q<r,\qquad\forall n\;r\le d_n(T).$$
\end{corollary*}

\begin{proof}[Proof]
If $q<\mu(A)$, apply the theorem with $\varepsilon=\mu(A)-q$. Its bounds give
$q<\mu(\TreeBody{T})$. Choose a rational $r$ strictly between these two numbers; then
$r\le d_n(T)$ for every $n$. Conversely, the finite-level lower bounds give
$r\le\mu(\TreeBody{T})\le\mu(A)$, and $q<r$ finishes the proof.
\end{proof}

\begin{proposition*}[\termdefine{Comparison by closed-tree bounds}]
Let $A\IncludedIn\CantorSpace$ be Borel and let $a\in\R$. Suppose that for every $\varepsilon>0$ there are trees
$T,S$ satisfying the theorem's inclusions and gap bound, and also
$$\mu(\TreeBody{T})\le a\le1-\mu(\TreeBody{S}).$$
Then $a=\mu(A)$.
\end{proposition*}

\begin{proof}[Proof]
Both $a$ and $\mu(A)$ lie in the same interval of length less than $\varepsilon$, so
$\Abs{a-\mu(A)}<\varepsilon$. If the two numbers differed, taking $\varepsilon=\Abs{a-\mu(A)}$ would be a contradiction.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
閉集合による上下界が揃えば数値が外部解釈の測度と一致するという条件付きの結論はmeasure_eq_of_closed_boundsへ接続した。
残る461–464行は、数値の解釈と新点を含むclosed-tree inclusionを別々に確かめるべきこと、
旧点でのmembership一致だけから包含を結論しないことを説明する適用上の注意である。
内部数値と測度の実際の一致をここで追加仮定なしに証明したとする判定ではなく、後の各移送・measure
identificationの証明は対象に保持する。)
--> For a comparison between transitive models, these formulas separate two obligations. The finite-level counts
and rational inequalities must have the same meaning in both models. The closed-tree inclusions must also hold
for the larger interpretation of the Borel set, including its new points. Agreement of membership on old points
alone does not establish those inclusions.<!--
formalization: skip-end
-->  Once both obligations are met, the comparison proposition identifies
the internal numerical value with the measure of the external interpretation, without treating the old points
as an external probability space.

### Ranked witnesses for closed inclusions {#sec:ranked-closed-inclusions}

\begin{mathmeta}
  \vars{y}{Name}
  \vars{q}{Rat}
  \vars{i,j,k,n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次のcounterexample tree構成の入力であるvalid expression・標準cylinder
basis・B_cという記号と前提を固定する導入。lambda programによるlabel計算を仮定しないこの集合論的構成の範囲を宣言している。
実際の有限row tests・tree・branch criterionは直後の構成と証明で扱い、この案内文を新たな計算可能性定理とはしない。)
--> We now replace the inclusion in the preceding measure certificate by a rank on an explicitly defined tree.
Fix a valid Borel expression $c$ on $\BaireSpace$, using the cylinders
$U_k=\cyl{\LambdaListDecode{k}}$ as its leaf sets, and write $B_c$ for its interpretation.
No computability assumption on $c$ is needed in this construction.<!--
formalization: skip-end
-->

Recall the finite certificate clauses of §{sec:edst-borel-validity}. A sequence $y\in\BaireSpace$ stores
$\NatPair{u_s}{j_s}$ at coordinate $\LambdaListCode{s}$: $u_s$ is the truth bit and $j_s$ selects a child when a union
node is true. For the row $i=\NatPair{\LambdaListCode{s}}{k}$, put $t=s\concat(k)$ and
$$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,\Length{\LambdaListDecode{k}}\}.$$
For $\varepsilon\in\{0,1\}$, let $P_i^\varepsilon(a,d)$ be the finite row test with prescribed root bit
$\varepsilon$. It checks $u_s\le1$, the absent-node, union, complement, and leaf clauses, and
$u_{\emptySeq}=\varepsilon$, reading the first word $a$ for the point and the second word $d$ for the certificate.
Its arguments have length $b(i)$, so every coordinate it reads is available. Write $P_i:=P_i^0$.
By the certificate theorem, all the tests $P_i$ with prescribed root bit $0$ hold on $\Pair{x}{y}$ exactly when
$y$ certifies $x\notin B_c$.
The tests $P_i^1$ instead characterize positive evaluation certificates for $x\in B_c$.

\begin{construction*}[Counterexample tree for a closed inclusion]
For a tree $T\IncludedIn\finseq{\NN}$, form a tree $Q(c,T)$ of finite words of paired natural numbers.
If a word $w$ of length $n$ has coordinate words $a,d$, put $w\in Q(c,T)$ exactly when, for every $j\le n$,
$$\begin{gathered}
\restrict{a}{j}\in T,\\
\forall i<j\;\bigl(b(i)\le j\ \Longrightarrow
P_i(\restrict{a}{b(i)},\restrict{d}{b(i)})\bigr).
\end{gathered}$$
\end{construction*}

\begin{proof}[Proof]
Write $Q^\varepsilon(c,T)$ for the same construction with $P_i^\varepsilon$ in place of $P_i$, so
$Q^0(c,T)=Q(c,T)$. Every condition concerns finite words and values of the parameters $c,T$.
There is no test for whether a
finite word extends to a point. Keeping the conditions for all $j\le n$ makes $Q(c,T)$ downward closed,
including when it is empty.
\end{proof}

\begin{theorem*}[\termdefine{Branches of the counterexample tree}]
The tree $Q(c,T)$ has an infinite branch if and only if $\SetDifference{\TreeBody{T}}{B_c}$ is nonempty.
Consequently,
$$\TreeBody{T}\IncludedIn B_c
\quad\Longleftrightarrow\quad Q(c,T)\text{ is well-founded}.$$
\end{theorem*}

\begin{proof}[Proof]
Decode a branch into two sequences $x,y$. The tree-membership tests at every length give $x\in\TreeBody{T}$.
For each row $i$, the test is performed by length $\max\{i+1,b(i)\}$, and truncation supplies exactly its prescribed
arguments. Thus all rows hold, and $y$ is a negative evaluation certificate for $x$.
Conversely, if $x\in\SetDifference{\TreeBody{T}}{B_c}$, choose such a certificate $y$
and pair their entries coordinatewise.
Every finite prefix passes all the required tests, giving a branch of $Q(c,T)$.
A downward-closed tree has no branch exactly when its strict-extension relation is well-founded, by the tree-rank
construction in §{sec:edst-boundedness}. This proves the last assertion as well.
\end{proof}

Now identify binary sequences with natural-number sequences whose entries are $0$ or $1$.
For a binary tree $T$, let $T^\uparrow$ contain the same words regarded as natural-number words, and put
$A_c:=B_c\cap\CantorSpace$, with the intersection understood through this identification.

\begin{corollary*}[\termdefine{Ranked certificate for closed inclusion}]
The inclusion $\TreeBody{T}\IncludedIn A_c$ holds if and only if there is an ordinal-valued function $\rho$ on
$Q(c,T^\uparrow)$ such that
$$u\properPrefixOf v\quad\Longrightarrow\quad\rho(v)<\rho(u)
\qquad\Pair{u}{v}\in Q(c,T^\uparrow).$$
\end{corollary*}

\begin{proof}[Proof]
The branches of $T^\uparrow$ are exactly the binary branches of $T$: every entry on a branch appears in a finite
word of the tree and hence is $0$ or $1$. Apply the theorem. If the counterexample tree is well-founded,
its ordinal rank gives $\rho$. Conversely, a branch would give the strictly decreasing sequence
$\rho(\restrict{z}{n})$ of ordinals, which is impossible.
\end{proof}

\begin{corollary*}[\termdefine{Ranked certificate for a rational measure bound}]
For $q\in\QQ$, the inequality $q<\mu(A_c)$ holds if and only if there are a downward-closed binary tree $T$,
a rational $r$, and an ordinal-valued function $\rho$ on $Q(c,T^\uparrow)$ satisfying
$$\begin{gathered}
q<r,\qquad\forall n\;r\le d_n(T),\\
u\properPrefixOf v\quad\Longrightarrow\quad\rho(v)<\rho(u)
\qquad\Pair{u}{v}\in Q(c,T^\uparrow).
\end{gathered}$$
\end{corollary*}

\begin{proof}[Proof]
Apply the tree certificate for a rational measure bound in §{sec:coded-measure-bounds} and replace its inclusion
condition by the preceding rank criterion. In the reverse direction, the rank gives the inclusion and
$q<r\le\mu(\TreeBody{T})\le\mu(A_c)$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
外部のrank criterionと、内部tree/rankを構成する義務を区別し、次節のrecognition・transferへ進む案内。
criterionだけから内部所属を推論できるという主張を避ける注意であり、非内部rankの反例や新たな存在定理をここで証明しない。)
--> The criterion identifies the data to be transferred. The next section proves that an internally recognized
rank excludes external counterexamples, including new points. Constructing the finite-test tree and a suitable
rank inside the model remains a separate step; their internal existence does not follow merely from the external
criterion.<!--
formalization: skip-end
-->

### Internal recognition and transfer of ranks {#sec:internal-rank-certificates}

\begin{mathmeta}
  \vars{q,r}{Rat}
\end{mathmeta}

A rank can be transferred as a fixed function graph with an ordinal bound. For sets $W,R,\alpha,f$, define
$$\begin{aligned}
\kappa(W,R,\alpha,f)\;:\equiv\;&\mathrm{Ord}(\alpha)\land(f:W\to\alpha)\\
&{}\land\forall x,y\in W\,\forall\beta,\gamma\in\alpha\\
&\quad\bigl[(\Pair{x}{y}\in R\land\Pair{x}{\beta}\in f\\
&\qquad{}\land\Pair{y}{\gamma}\in f)\longrightarrow\beta\in\gamma\bigr].
\end{aligned}$$
We orient $R$ from a smaller rank to a larger rank. The graph $f$ need not be injective or onto, and its values need
not be the least possible ranks. The ordinal, function, and pair predicates have the bounded expansions given in
§{sec:zfc-absoluteness}; every remaining quantifier is bounded by $W$ or $\alpha$. Thus $\kappa$ is
a $\Delta_0$ formula.

\begin{lemma*}[\termdefine{Internal recognition of rank certificates}]
Let $M$ be transitive and let $W,R,\alpha,f\in M$. Then $M\models\kappa(W,R,\alpha,f)$ if and only if $\alpha$ is an
actual ordinal and $f$ is an actual function graph from $W$ to $\alpha$ satisfying
$$\Pair{x}{y}\in R\quad\Longrightarrow\quad f(x)\in f(y)
\qquad\Pair{x}{y}\in W.$$
No set-theoretic axiom in $M$ is needed for this recognition.
\end{lemma*}

\begin{proof}[Proof]
The bounded ordinal and function predicates have their actual meanings in a transitive domain. Every member of
$W$ or $\alpha$ belongs to $M$, so the four bounded quantifiers range over all actual candidates. The ordered-pair
predicates recognize the same pairs and the same graph entries. Consequently the last clause says exactly that
the actual values at $R$-related arguments satisfy the displayed membership relation.
The argument also proves the converse.
\end{proof}

\begin{corollary*}[\termdefine{Transfer of a fixed rank certificate}]
If $M\IncludedIn N$ are transitive and $W,R,\alpha,f\in M$, then
$$M\models\kappa(W,R,\alpha,f)\quad\Longleftrightarrow\quad N\models\kappa(W,R,\alpha,f).$$
Moreover, either assertion implies that the actual relation $R$ restricted to $W$ is well-founded.
\end{corollary*}

\begin{proof}[Proof]
Apply the recognition lemma in both domains. Both sides express the same external condition on the same graph.
If an external descending sequence existed, applying $f$ to its entries would give a sequence of ordinal values
with each value a member of its predecessor. Foundation rules this out. Equivalently, pull back the well-founded
membership relation along $f$ and use that every $R$-step is a step in that pullback.
\end{proof}

We next connect this formula to the word trees used above. Code a finite word $s$ by its finite function graph
$e(s)$ from §{sec:internal-borel-inputs}, and for a tree $Q$ put
$$W_Q:=\{e(s):s\in Q\}.$$
Graph inclusion and injectivity of $e$ give
$$e(t)\IncludedIn e(s)\land e(t)\ne e(s)
\quad\Longleftrightarrow\quad t\properPrefixOf s.$$
For an arbitrary set $W$, define the descending relation
$$R_W:=\{\Pair{a}{b}\in W\times W:b\IncludedIn a\land b\ne a\}.$$
On $W_Q$ this is precisely strict word extension, with the longer word first.
For a rank certificate on $W_Q$ with relation $R_{W_Q}$, the comparison therefore reads
$$t\properPrefixOf s\quad\Longrightarrow\quad f(e(s))\in f(e(t))
\qquad\Pair{t}{s}\in Q.$$

\begin{lemma*}[\termdefine{Internal strict-extension relation}]
Suppose $M$ is transitive and satisfies Pairing, Union, Power Set, and Separation. If $W\in M$, then $R_W\in M$.
\end{lemma*}

\begin{proof}[Proof]
The product $W\times W$ belongs to $M$. Separate its elements using
$$\begin{aligned}
\eta(W,p)\;:\equiv\;\exists a,b\in W\,\bigl(&p=\Pair{a}{b}\\
&{}\land\bigl(\forall z\in b\;(z\in a)\bigr)\land b\ne a\bigr).
\end{aligned}$$
The ordered-pair equality has a bounded expansion, so $\eta$ is $\Delta_0$. Transitivity makes this predicate
recognize exactly the displayed relation, and Separation puts that relation in $M$. This construction does not
require a rank or an enumeration of branches.
\end{proof}

\begin{theorem*}[\termdefine{Internal tree ranks exclude external branches}]
Let $M$ be transitive, let $Q$ be a downward-closed tree, and suppose $W_Q,R_{W_Q},\alpha,f\in M$ and
$$M\models\kappa(W_Q,R_{W_Q},\alpha,f).$$
Then $Q$ has no external branch, including no branch newly present in a transitive extension of $M$.
\end{theorem*}

\begin{proof}[Proof]
The certificate gives actual well-foundedness on $W_Q$. Pull this relation back along $e:Q\to W_Q$.
The graph-inclusion equivalence identifies the pullback with strict word extension. Thus that extension relation
is well-founded. The successive prefixes of any branch would give a descending sequence, a contradiction.
\end{proof}

\begin{corollary*}[\termdefine{Borel measure bounds from internal ranks}]
Let $c$ be valid and let $T$ be a downward-closed binary tree. Apply the theorem to $Q=Q(c,T^\uparrow)$.
Under its internal-certificate hypotheses,
$$\TreeBody{T}\IncludedIn A_c$$
holds for the external interpretation. If $q,r\in\QQ$ also satisfy $q<r$ and $r\le d_n(T)$ for every $n$, then
$$q<\mu(A_c).$$
\end{corollary*}

\begin{proof}[Proof]
A failure of inclusion would give a branch in the counterexample tree, which the theorem excludes.
The finite-level lower bounds then give $q<r\le\mu(\TreeBody{T})\le\mu(A_c)$, exactly as in
§{sec:coded-measure-bounds}.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
与えられた内部rankの認識・移送から、subset minimaを用いたrank存在の構成へ進む案内。
存在とChoiceの用途は直後の定理の仮定・証明として別に対象に残す。)
--> The preceding statements recognize and transfer a given internal rank. We next construct such a rank from the
model's subset-minimum assertion, using its internal selection recursion and Hartogs bound.<!--
formalization: skip-end
-->

### Constructing ranks inside the model {#sec:internal-rank-existence}

\begin{mathmeta}
  \vars{q,r}{Rat}
\end{mathmeta}

Throughout this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation,
Replacement, and Choice. Let $W,R\in M$. The relation on $W$ coded by $R$ may be arbitrary. Use the subset-minimum
formula from the ordinal-representation argument:
$$\begin{aligned}
\chi(W,R)\;:\equiv\;\forall B\,\bigl[&
 (B\IncludedIn W\land B\ne\emptyset)\\
 &\longrightarrow\exists x\in B\,\forall y\in B\;
 \Pair{y}{x}\notin R\bigr].
\end{aligned}$$
In $M\models\chi(W,R)$, only subsets $B$ belonging to $M$ are quantified. Thus external well-foundedness is not
part of this hypothesis.

\begin{lemma*}[\termdefine{Internal selection of relation-minimal elements}]
Suppose $M\models\chi(W,R)$ and put
$$S:=\{U\in\InternalPowerSet{M}{W}:U\ne\emptyset\}.$$
There is a function graph $c\in M$ with domain $S$ and codomain $W$ such that
$$c(U)\in U,\qquad\forall y\in U\;\Pair{y}{c(U)}\notin R
\qquad(U\in S).$$
\end{lemma*}

\begin{proof}[Proof]
The internal subset-choice lemma in §{sec:internal-choice-recursion} gives $S\in M$ and a selector
$c_0:S\to W$ in $M$. For $U\in S$, define
$$m_R(U):=\{x\in U:\forall y\in U\;\Pair{y}{x}\notin R\}.$$
Its defining predicate is bounded, so Separation gives $m_R(U)\in M$. The assertion $M\models\chi(W,R)$ makes it
nonempty, and $m_R(U)\IncludedIn U\IncludedIn W$ gives $m_R(U)\in S$. Put
$$c(U):=c_0(m_R(U)).$$
To obtain the whole graph internally, separate from $S\times W$ the pairs $\Pair{U}{x}$ satisfying
$$\exists V\;\bigl(V=m_R(U)\land\Pair{V}{x}\in c_0\bigr).$$
The equality $V=m_R(U)$ is expressed by the bounded formula
$$V\IncludedIn U\;\land\;\forall x\in U\;
\bigl(x\in V\;\longleftrightarrow\;\forall y\in U\;\Pair{y}{x}\notin R\bigr).$$
Thus the separating formula has parameters in $M$, and its required witness $V=m_R(U)$ belongs to $M$.
The unique value of $c_0$ therefore makes
the separated set a total function graph on $S$. Its values belong to $m_R(U)$, proving both assertions.
\end{proof}

\begin{theorem*}[\termdefine{Internal enumeration respecting a relation}]
If $M\models\chi(W,R)$, there are an ordinal $\gamma\in M$ and a bijection $e:\gamma\to W$ whose graph belongs
to $M$, such that
$$\Pair{e(\alpha)}{e(\beta)}\in R
\quad\Longrightarrow\quad\alpha\in\beta
\qquad\Pair{\alpha}{\beta}\in \gamma.$$
\end{theorem*}

\begin{proof}[Proof]
Use the selector $c$ from the lemma and the internal Hartogs bound $H$ for $W$ from §{sec:internal-hartogs-bound}.
Run the internal selection recursion of §{sec:internal-choice-recursion} on $H$. At stage $\beta$, its remaining set is
$$r_\beta:=\SetDifference{W}{\GraphRange{\restrict{f}{\beta}}}.$$
The recurrence selects $c(r_\beta)$ if this set is nonempty and the empty set otherwise. Its graph $f$ belongs to
$M$. If every remainder were nonempty, the selected values would be distinct members of $W$, giving an internal
injection from $H$ into $W$, contrary to the Hartogs bound. Let $\gamma\in H$ be the first stage with empty remainder.
Then $\gamma\in M$ by transitivity and $e:=\restrict{f}{\gamma}\in M$ by graph restriction. As in
§{sec:internal-choice-enumerations}, every earlier remainder is nonempty, so $e$ is injective; the empty remainder
at $\gamma$ makes it onto $W$. This includes $W=\emptyset$, when $\gamma=0$.

It remains to check the relation. Suppose $x=e(\alpha)$, $y=e(\beta)$, and $\Pair{x}{y}\in R$.
The value $y=c(r_\beta)$ is $R$-minimal in $r_\beta$. Thus $x\notin r_\beta$ and $x$ already appears in the graph
$\restrict{f}{\beta}$. Let $\delta\in\beta$ be an index with $f(\delta)=x$. Since $\beta\in\gamma$, also
$\delta\in\gamma$, and injectivity of $e$ gives $\delta=\alpha$. Hence $\alpha\in\beta$, as required.
\end{proof}

\begin{corollary*}[\termdefine{Internal existence of a rank certificate}]
If $M\models\chi(W,R)$, there are $\gamma,g\in M$ such that
$$M\models\kappa(W,R,\gamma,g).$$
\end{corollary*}

\begin{proof}[Proof]
Take the ordinal enumeration $e:\gamma\to W$ from the theorem. Its inverse graph $g:W\to\gamma$ belongs to $M$:
separate from $W\times\gamma$ the reversed pairs of $e$. For $x,y\in W$, the enumeration property gives
$$\Pair{x}{y}\in R\quad\Longrightarrow\quad g(x)\in g(y).$$
Thus $g$ is a rank with ordinal bound $\gamma$. The recognition lemma of §{sec:internal-rank-certificates} gives
the asserted internal formula.
\end{proof}

\begin{corollary*}[\termdefine{Internal and actual well-foundedness}]
Under the axioms fixed in this section,
$$M\models\chi(W,R)\quad\Longleftrightarrow\quad
R\text{ restricted to }W\text{ is well-founded}.$$
\end{corollary*}

\begin{proof}[Proof]
In the forward direction, construct the internal rank graph and apply the preceding transfer theorem.
Conversely, actual well-foundedness gives a minimal element in every nonempty subset of $W$, hence in each such
subset belonging to $M$. Transitivity puts that element in $M$, and the interpretation of $\chi$ gives the result.
\end{proof}

\begin{corollary*}[\termdefine{Borel measure bounds from internal well-foundedness}]
Retain the valid code $c$, the downward-closed binary tree $T$, and the node and relation sets $W_Q,R_{W_Q}$ for
$Q=Q(c,T^\uparrow)$. Suppose these two sets belong to $M$ and
$$M\models\chi(W_Q,R_{W_Q}).$$
If $q,r\in\QQ$ satisfy $q<r$ and $r\le d_n(T)$ for every $n$, then $q<\mu(A_c)$ for the external interpretation.
\end{corollary*}

\begin{proof}[Proof]
The internal rank-existence corollary constructs the graph required by the Borel measure-bound corollary in
§{sec:internal-rank-certificates}. Apply that corollary with the given finite-level bounds.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次の節で、内部branchがないことからcoded treeのsubset-minimum assertionを導くという予告。
具体的なminima導出と内部rankの構成は後続の定理・証明として対象に残す。)
--> The preceding rank construction starts from the internal subset-minimum assertion. We now derive that assertion
for a coded tree from the absence of an internal branch.<!--
formalization: skip-end
-->

### Internal dependent choice and tree branches {#sec:internal-tree-branches}

\begin{mathmeta}
  \vars{k,n}{Nat}
  \vars{q,r}{Rat}
  \vars{t}{Seq}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
sequenceGraphの実際の表示は既存リンクで扱う。残る768行と770–771行は公理の仮定を保持する指示と、
点ごとの内部所属だけから外部sequenceのgraphの内部所属を結論しないという適用上の注意および次の構成への案内である。
任意の外部sequenceが内部にないことの反例をここで構成しない。)
--> Keep the transitive-model assumptions of §{sec:internal-rank-existence}.<!--
formalization: skip-end
-->  For a sequence of sets $s:\omega\to B$,
write its function graph as
$$G_s:=\{\Pair{n}{s(n)}:n\in\omega\}.$$
<!--
formalization: skip-begin (引用・背景説明・読書案内:
sequenceGraphの実際の表示は既存リンクで扱う。残る768行と770–771行は公理の仮定を保持する指示と、
点ごとの内部所属だけから外部sequenceのgraphの内部所属を結論しないという適用上の注意および次の構成への案内である。
任意の外部sequenceが内部にないことの反例をここで構成しない。)
-->
Having each $s(n)$ in $M$ does not by itself put $G_s$ in $M$. The following construction supplies the whole graph.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Internal iteration on natural numbers}]
For this lemma, assume only that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set,
and Separation. Let $B,d\in M$, where $d:B\to B$ is a function graph, and let $a\in B$. The sequence
$$s(0)=a,\qquad s(n+1)=d(s(n))$$
has its graph $G_s$ in $M$.
\end{lemma*}

\begin{proof}[Proof]
The actual set $\omega$ belongs to $M$, and so does $D=\omega\times B$. On subsets of $D$, use the operation
$$\begin{aligned}
\Phi(C):={}&\{\Pair{0}{a}\}\\
 &{}\cup\{\Pair{k}{y}:n,k\in\omega,\ x,y\in B,\ k=n+1,\\
 &\hspace{40mm}\Pair{n}{x}\in C,\ \Pair{x}{y}\in d\}.
\end{aligned}$$
It is monotone and takes values in $D$. The displayed predicate is first-order definable using the pair and
successor formulas, with all witnesses bounded by $\omega$ or $B$. Transitivity therefore identifies its internal
interpretation with the displayed operation. The internal least-fixed-point theorem in
§{sec:internal-model-fixed-points} uses only Separation once $D$ and the parameters belong to $M$.
It gives $C\in M$ with $C=\Phi(C)$. Thus this construction uses neither Replacement nor Choice.

Induction on $n$ proves
$$\Pair{n}{y}\in C\quad\Longleftrightarrow\quad y=s(n).$$
At $n=0$, only the initial pair can occur, since no natural number has successor $0$. At $n+1$, only the successor
clause can occur. Its predecessor index must be $n$, its preceding value must be $s(n)$ by induction, and the
function graph $d$ determines its next value uniquely. Conversely, that successor clause inserts precisely the
required pair. Since $C\IncludedIn\omega\times B$, these identities prove $C=G_s$.
\end{proof}

\begin{theorem*}[\termdefine{Internal dependent choice}]
Let $B,R\in M$ and suppose
$$\forall x\in B\;\exists y\in B\;\Pair{y}{x}\in R.$$
For every $a\in B$, there is a sequence $s:\omega\to B$ such that
$$s(0)=a,\qquad\Pair{s(n+1)}{s(n)}\in R\quad(n\in\omega),\qquad G_s\in M.$$
\end{theorem*}

\begin{proof}[Proof]
Take an internal choice function $c_0$ on the nonempty internal subsets of $B$. For $x\in B$, Separation gives
$$D_x:=\{y\in B:\Pair{y}{x}\in R\}\in M.$$
The hypothesis makes $D_x$ nonempty. Define $d(x)=c_0(D_x)$. Its graph belongs to $M$: separate from $B\times B$
the pairs $\Pair{x}{y}$ for which there is a set $V$ satisfying
$$V=D_x\quad\text{and}\quad\Pair{V}{y}\in c_0.$$
Expand $V=D_x$ by its membership clause. The set $D_x\in M$ supplies the witness internally, and the unique value
of $c_0$ makes this a function graph $d:B\to B$. Each value satisfies $\Pair{d(x)}{x}\in R$.
Apply the iteration lemma to $d$ and the specified starting point $a$.
\end{proof}

\begin{lemma*}[\termdefine{Internal union of an extension chain}]
Let $T\IncludedIn\finseq{\omega}$ be a tree, and let $t_n\in T$ satisfy
$$t_n\prefixOf t_{n+1},\qquad \Length{t_n}<\Length{t_{n+1}}.$$
If the sequence $\Sequence{e(t_n)}{n\in\omega}$ has its graph $G$ in $M$, then
$$g:=\bigcup\GraphRange{G}$$
is the graph of a branch $p\in\TreeBody{T}$ and belongs to $M$.
\end{lemma*}

\begin{proof}[Proof]
The range and union constructions give $g\in M$, and membership in $g$ means membership in some $e(t_n)$.
Induction gives $n\le \Length{t_n}$. In particular,
$$k<k+1\le \Length{t_{k+1}},\qquad
\Pair{k}{t_{k+1}(k)}\in e(t_{k+1})\IncludedIn g.$$
Thus every natural-number coordinate occurs in $g$. If two values for the same coordinate occur in $e(t_i)$
and $e(t_j)$, both pairs belong to $e(t_{\max(i,j)})$ and the values are equal. Thus $g$ is a function graph on
$\omega$ with values in $\omega$.
Write it as $g_p$ using the point-graph correspondence of §{sec:internal-borel-sets}.
For each $n$, the first $n$ values of $p$ agree with those of $t_n$:
$$\restrict{p}{n}=\restrict{t_n}{n}.$$
This prefix belongs to $T$ because $t_n\in T$ and $T$ is downward closed. Therefore $p\in\TreeBody{T}$.
\end{proof}

\begin{theorem*}[\termdefine{Internal absence of branches implies well-foundedness}]
Let $T\IncludedIn\finseq{\omega}$ be a tree, let $W=W_T$ and $R=R_W$, and suppose $W,R\in M$.
If no branch $p\in\TreeBody{T}$ has its graph $g_p$ in $M$, then $M\models\chi(W,R)$.
Consequently $T$ has no external branch either.
\end{theorem*}

\begin{proof}[Proof]
Otherwise, some nonempty $B\in M$ with $B\IncludedIn W$ has no $R$-minimal element. Every $x\in B$ then has
$y\in B$ with $\Pair{y}{x}\in R$. Choose $a\in B$ and apply internal dependent choice. It gives an internal
graph $G_s$ of a sequence in $B$ satisfying $\Pair{s(n+1)}{s(n)}\in R$. Each $s(n)$ is the finite graph
$e(t_n)$ of a unique node $t_n\in T$. The definition of $R_W$ says that $t_{n+1}$ strictly extends $t_n$.
The union lemma therefore produces a branch whose graph belongs to $M$, a contradiction.
Thus $M\models\chi(W,R)$. §{sec:internal-rank-existence} now constructs an internal rank, and
§{sec:internal-rank-certificates} excludes every external branch.
\end{proof}

\begin{corollary*}[\termdefine{Measure bounds from absence of internal counterexample branches}]
Retain the valid Borel code $c$, the downward-closed binary tree $T$, and the internal node and relation sets
$W_Q,R_{W_Q}$ for $Q=Q(c,T^\uparrow)$. Suppose no branch of $Q$ has its graph in $M$.
If $q,r\in\QQ$ satisfy $q<r$ and $r\le d_n(T)$ for every $n$, then $q<\mu(A_c)$ externally.
\end{corollary*}

\begin{proof}[Proof]
The theorem gives the internal subset-minimum assertion for $Q$. Apply the measure-bound corollary of
§{sec:internal-rank-existence}.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部branchがないことからminimaと内部rankを得る最後の数学的な主張はinternal_tree_minima_of_no_interna
l_branchとinternal_tree_rank_of_no_internal_branchへ接続した。後者は実際の内部rank
graphを構成するinternal_rank_certificateを適用し、存在仕様を追加で仮定していない。
残る868–874行前半はfinite tests、closed inclusions、measure bounds、clopen
approximation、general Borel approximation、measure
identificationの各節への参照と役割を列挙するroadmapであり、各参照先の証明をこの判定に含めない。)
--> §{sec:internal-finite-tests} constructs the finite-test node set internally, and
§{sec:internal-closed-inclusions} connects its internal branches with internal Borel counterexamples.
§{sec:internal-finite-measure-bounds} identifies internal counts and rational comparisons with the
finite-level bounds. §{sec:internal-finite-measure-bounds} constructs internal clopen approximations
for open codes. §{sec:internal-approximation-errors} extends these approximations to general Borel codes,
and §{sec:internal-borel-measure-identification} identifies their external measure with the value of the model's
measure under the stated measure axioms.<!--
formalization: skip-end
-->  Absence of internal branches supplies both the subset-minimum assertion
and the rank.

## Finite-Test Infrastructure {#sec:appendix-borel-finite-test-infrastructure}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
counterexample-treeのために次の内部算術・list coding・finite testsを準備するという構成順の案内。
各graphの内部所属やlambda計算との対応は後続の実際の構成・定理で扱う。)
-->
The counterexample trees use finite numerical tests. We now construct their arithmetic, list coding, and interpretation
inside the model, so that the final transfer argument can use the whole internal node set.<!--
formalization: skip-end
-->

### Internal arithmetic for finite tests {#sec:internal-natural-arithmetic}

\begin{mathmeta}
  \vars{a,i,j,k,m,n,x,y,z}{Nat}
\end{mathmeta}

The counterexample-tree tests use numerical pairing, its projections, and finite-list codes. Their lambda
implementations were given in §{sec:lambda-numerical-pairing} and §{sec:lambda-finite-lists}. To use these tests
inside a model, we must also construct their set-coded graphs internally. We begin with the arithmetic and
pairing operations. In this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set,
and Separation; Choice and Replacement are not needed for these constructions.

For a function graph $d:\omega\to\omega$, define the first-order formulas
$$\begin{aligned}
I(d,a,g)\;:\equiv\;&g:\omega\to\omega\land\Pair{0}{a}\in g\\
 &{}\land\forall n,k,x,y\in\omega\;\bigl[\bigl(k=n\cup\{n\}\\
 &\qquad{}\land\Pair{n}{x}\in g\land\Pair{k}{y}\in g\bigr)
 \longrightarrow\Pair{x}{y}\in d\bigr],\\
V(d,a,n,y)\;:\equiv\;&\exists g\;\bigl(I(d,a,g)\land\Pair{n}{y}\in g\bigr).
\end{aligned}$$
The parameter $\omega$ denotes the actual set constructed inside the model. Expand the function, pair-membership,
and successor predicates by their earlier definitions. In particular, the existential quantifier over $g$ in
$M\models V(d,a,n,y)$ ranges only over graphs belonging to $M$.

\begin{lemma*}[\termdefine{Internal recognition of numerical iteration}]
Suppose $d\in M$ is the graph of a function $f:\omega\to\omega$. For $a,n,y\in\omega$,
$$M\models V(d,a,n,y)\quad\Longleftrightarrow\quad y=f^n(a).$$
\end{lemma*}

\begin{proof}[Proof]
If an internal graph $g$ witnesses the left side, transitivity makes it an actual function on $\omega$ satisfying
$I(d,a,g)$. Induction gives $\Pair{n}{f^n(a)}\in g$: the initial clause gives the base case, and totality of
$g$ together with the successor clause and uniqueness of the value of $d$ gives the next value. Since $g$ also
contains $\Pair{n}{y}$, functionality gives $y=f^n(a)$.
Conversely, the iteration lemma of §{sec:internal-tree-branches} constructs the whole graph of
$n\mapsto f^n(a)$ inside $M$. It satisfies $I(d,a,g)$ and witnesses the value formula. Thus the converse does not
assume that an externally defined infinite graph is automatically internal.
\end{proof}

For a binary numerical operation $F$, encode its graph as
$$\Gamma_F:=\{\Pair{\Pair{m}{n}}{F(m,n)}:m,n\in\omega\}.$$
If a first-order formula recognizes $k=F(m,n)$ internally, Separation on
$$(\omega\times\omega)\times\omega$$
constructs $\Gamma_F\in M$. To expand the graph-membership formula, quantify $m,n,k\in\omega$, form the ordered
pair $r=\Pair{m}{n}$, and require that the candidate pair be $\Pair{r}{k}$ and that the value formula
hold. Pairing puts the intermediate set $r$ in $M$, and transitivity identifies all natural-number witnesses.

\begin{proposition*}[\termdefine{Internal addition graph}]
The graph $\Gamma_+$ of addition belongs to $M$.
\end{proposition*}

\begin{proof}[Proof]
Separation on $\omega\times\omega$ constructs the successor graph
$$S:=\{\Pair{n}{k}:n,k\in\omega,\ k=n\cup\{n\}\}\in M.$$
Its actual values are $n+1$. The iteration-recognition lemma gives
$$M\models V(S,m,n,k)\quad\Longleftrightarrow\quad k=m+n.$$
The graph construction above therefore gives $\Gamma_+\in M$.
\end{proof}

\begin{proposition*}[\termdefine{Internal multiplication graph}]
The graph $\Gamma_\times$ of multiplication belongs to $M$.
\end{proposition*}

\begin{proof}[Proof]
For each $m\in\omega$, separate the section
$$d_m:=\{\Pair{x}{y}\in\omega\times\omega:
\Pair{\Pair{x}{m}}{y}\in\Gamma_+\}.$$
This belongs to $M$ and is the graph of $x\mapsto x+m$. Induction on $n$ shows that its iteration from $0$ has
value $mn$:
$$\begin{aligned}
d_m^0(0)&=0=m\cdot0,\\
d_m^{n+1}(0)&=d_m^n(0)+m=mn+m=m(n+1).
\end{aligned}$$
To express this uniformly in $m$, let $D(A,m,d)$ assert that $d:\omega\to\omega$ and
$$\forall x,y\in\omega\;
\bigl(\Pair{x}{y}\in d\longleftrightarrow
\Pair{\Pair{x}{m}}{y}\in A\bigr).$$
Then
$$M\models\exists d\;\bigl(D(\Gamma_+,m,d)\land V(d,0,n,k)\bigr)
\quad\Longleftrightarrow\quad k=mn.$$
In the forward direction, the section clause fixes every next value and induction gives the product. In the
reverse direction, the internally constructed section supplies the witness. Separation now collects
$\Gamma_\times$.
\end{proof}

\begin{mathmeta}
  \forward{NatPair}
\end{mathmeta}
Write $p(i,j)=\NatPair{i}{j}$ for the numerical pairing of §{sec:lambda-numerical-pairing}. Its value is a natural
number; the pairs used to store function graphs above are set-theoretic ordered pairs.

\begin{proposition*}[\termdefine{Internal numerical pairing and projections}]
The pairing graph $\Gamma_p$ and the graphs of both inverse projections belong to $M$.
\end{proposition*}

\begin{proof}[Proof]
Use the formula
$$p(i,j)=\begin{cases}j^2+i,&i<j,\\i^2+i+j,&j\le i.\end{cases}$$
For finite ordinals, $i<j$ is exactly $i\in j$. In the first case, quantify a natural number equal to $j\cdot j$
using $\Gamma_\times$, then add $i$ using $\Gamma_+$. In the other case, quantify the intermediate values of
$i\cdot i$ and $i^2+i$, then add $j$. Every intermediate value is in the actual $\omega$, so the formula recognizes
the displayed pairing internally. Separation gives $\Gamma_p\in M$.

The inverse-projection graphs are separated from $\omega\times\omega$ as
$$\begin{aligned}
Q_1&:=\{\Pair{z}{i}:z,i\in\omega,\ \exists j\in\omega\;
\Pair{\Pair{i}{j}}{z}\in\Gamma_p\},\\
Q_2&:=\{\Pair{z}{j}:z,j\in\omega,\ \exists i\in\omega\;
\Pair{\Pair{i}{j}}{z}\in\Gamma_p\}.
\end{aligned}$$
The pairing bijection proved in §{sec:lambda-numerical-pairing} makes both graphs total and single-valued, and
identifies their values with the numerical projections used in the finite tests. The quantified witnesses are
natural numbers, so internal and external interpretations agree.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
既に構成した算術graphから、同じlambda番号付けを用いるlist encoding/decodingの内部graphへ進むという案内。
新しい番号付けや別の計算モデルを導入する主張ではなく、実際のgraph構成は次の定理として対象に残す。)
--> These arithmetic graphs supply the numerical operations for finite tests. We next construct the list-numbering
graph and its inverse, retaining the numbering already used by the lambda programs.<!--
formalization: skip-end
-->

### Internal finite-list coding {#sec:internal-list-coding}

\begin{mathmeta}
  \vars{a,i,j,l,n,v}{Nat}
  \vars{s,t}{Seq(Nat)}
  \vars{g,h}{ZFSet}
\end{mathmeta}

Keep the axioms of §{sec:internal-natural-arithmetic}, and let $F\in M$ be the set of all finite natural-number
function graphs constructed in §{sec:internal-borel-inputs}. For a finite word $s$, write $e(s)\in F$ for its graph.
We first express prepending an entry without invoking an external operation on lists. For $a\in\omega$ and
$g,h\in F$, put
$$\begin{aligned}
K(a,g,h)\;:\equiv\;\forall i,v\in\omega\;\bigl[\Pair{i}{v}\in h
\longleftrightarrow{}& (i=0\land v=a)\\
 &{}\lor\exists j\in\omega\;(i=j\cup\{j\}\land\Pair{j}{v}\in g)\bigr].
\end{aligned}$$
The coordinates of both finite graphs lie in $\omega$, so this condition determines every member of $h$.
The successor, pair-membership, and equality predicates have their previous first-order expansions.

\begin{lemma*}[\termdefine{Internal recognition of list cons}]
For finite words $s,t$ and $a\in\omega$,
$$K(a,e(s),e(t))\quad\Longleftrightarrow\quad t=a::s.$$
The same equivalence holds for the internal interpretation of $K$ in $M$.
\end{lemma*}

\begin{proof}[Proof]
At coordinate $0$, the graph of $a::s$ contains exactly the value $a$. At coordinate $j+1$, it contains precisely
the value at coordinate $j$ of $s$, if that coordinate is present. Thus its pair-membership condition is exactly
$K$. Conversely, $K$ identifies every pair of the two finite graphs, so their equality and injectivity of $e$
give $t=a::s$. All quantified indices and values lie in the actual $\omega$ inside the transitive model, which
also proves the assertion about internal interpretation.
\end{proof}

\begin{mathmeta}
  \forward{LambdaListCode,LambdaListDecode}
\end{mathmeta}
Use the numbering from §{sec:lambda-finite-lists}:
$$\LambdaListCode{[]}=0,\qquad
\LambdaListCode{a::s}=p(a,\LambdaListCode{s})+1,$$
where $p$ is the numerical pairing of the preceding section. Its inverse is $\LambdaListDecode{n}$.

\begin{theorem*}[\termdefine{Internal finite-list encoding graph}]
The graph
$$E:=\{\Pair{e(s)}{\LambdaListCode{s}}:s\in\finseq{\omega}\}$$
belongs to $M$.
\end{theorem*}

\begin{proof}[Proof]
Let $P=\Gamma_p\in M$ be the numerical pairing graph. On subsets $C$ of $F\times\omega$, use the monotone operation
$$\begin{aligned}
\Phi(C):={}&\{\Pair{e([])}{0}\}\\
 &{}\cup\{\Pair{h}{k}\in F\times\omega:\exists a,n,l\in\omega\;\exists g\in F\;[\\
 &\qquad K(a,g,h)\land\Pair{g}{n}\in C\\
 &\qquad{}\land\Pair{\Pair{a}{n}}{l}\in P\land k=l\cup\{l\}]\}.
\end{aligned}$$
Here $e([])=0$ as sets. The graph $P$ and the preceding lemma identify the step with adjoining
$\Pair{e(a::s)}{p(a,n)+1}$ whenever $\Pair{e(s)}{n}\in C$.
The displayed quantifiers are bounded by $F$ or $\omega$. The predicates $K$, successor, and nested
pair membership also have bounded expansions. Thus the step is defined by a $\Delta_0$ formula, and transitivity
makes its internal interpretation agree with the displayed operation. The internal least-fixed-point theorem in
§{sec:internal-atomic-forcing} gives $C\in M$ with $C=\Phi(C)$.

Induction on the finite list $s$ proves
$$\Pair{e(s)}{n}\in C\quad\Longleftrightarrow\quad n=\LambdaListCode{s}.$$
For the empty list, only the initial clause can apply, giving $n=0$. For $a::s$, the initial clause is impossible.
The cons lemma uniquely determines the head and tail in the step clause. The induction hypothesis fixes the tail
code, and the pairing graph and successor condition fix the new code. Conversely, the corresponding initial or
step clause inserts the required pair. Since every element of $C$ lies in $F\times\omega$, these equivalences
give $C=E$.
\end{proof}

\begin{corollary*}[\termdefine{Internal finite-list decoding graph}]
The inverse graph
$$D:=\{\Pair{n}{e(\LambdaListDecode{n})}:n\in\omega\}$$
belongs to $M$.
\end{corollary*}

\begin{proof}[Proof]
Separate from $\omega\times F$ the reversed pairs of $E$:
$$\{\Pair{n}{g}\in\omega\times F:\Pair{g}{n}\in E\}.$$
The identities
$$\LambdaListDecode{\LambdaListCode{s}}=s,\qquad
\LambdaListCode{\LambdaListDecode{n}}=n$$
proved in §{sec:lambda-finite-lists} identify this set with $D$. Thus decoding is the actual inverse numbering,
and its whole graph belongs to the model.
\end{proof}

\begin{corollary*}[\termdefine{Internal standard cylinder interpretation}]
For the standard cylinders $b(n)=\LambdaListDecode{n}$, the basis-word graph belongs to $M$ without a separate
input assumption. If a well-founded Borel expression has label graph $\ell\in M$, its interpretation on the
internal Baire space belongs to $M$ at every node.
\end{corollary*}

\begin{proof}[Proof]
The basis-word graph is exactly $D$. Apply the internal-interpretation theorem in §{sec:internal-borel-sets}
with this graph and the given label graph. The earlier membership comparison with the external evaluation is
unchanged.
\end{proof}

\begin{lemma*}[\termdefine{Internal numerical Borel labels}]
If the label graph $\ell$ of a Borel expression $c$ belongs to $M$, the following graph also belongs to $M$:
$$L_{\mathrm{num}}:=\{\Pair{n}{c(\LambdaListDecode{n})}:n\in\omega\}.$$
\end{lemma*}

\begin{proof}[Proof]
Separate from $\omega\times\omega$ the pairs $\Pair{n}{a}$ satisfying
$$\exists s\in F\;\bigl(\Pair{n}{s}\in D\land\Pair{s}{a}\in\ell\bigr).$$
The decoder forces $s=e(\LambdaListDecode{n})$, and the label graph then forces
$a=c(\LambdaListDecode{n})$. Conversely, that finite word graph belongs to $F$ and supplies the witness.
This identifies the separated set with $L_{\mathrm{num}}$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
算術・list graphsを使う有限テストの一様解釈原理を導入する案内。共通のbounded-predicate
compilerの意味保存・Delta0性・graph collectionは次の独立単位で対象に残す。)
--> The arithmetic and list graphs now provide the inputs for finite tests. The following uniform interpretation
principle avoids repeating the same internalization argument for every operation.<!--
formalization: skip-end
-->

### Uniform interpretation of finite tests {#sec:internal-finite-tests}

\begin{mathmeta}
  \vars{i,m,n,v,w}{Nat}
  \vars{j,k,p}{Nat}
  \vars{a,d}{Seq}
\end{mathmeta}

All predicates below use equality, membership, ordered-pair membership, function-graph conditions, successor,
and inclusion, combined by Boolean connectives and bounded quantifiers. After the bounded expansions of
§{sec:zfc-absoluteness}, each resulting formula $\varphi$ is $\Delta_0$. For parameters $\vec\eta$ in a transitive
set $M$, the absoluteness theorem in that section gives, uniformly,
$$M\models\varphi(\vec\eta)\quad\Longleftrightarrow\quad\varphi(\vec\eta).$$

Consequently, if $A\in M$ and the corresponding Separation instance holds, then
$$\{x\in A:\varphi(\vec\eta,x)\}\in M.$$
We use this consequence throughout the construction. It remains to check the ordinary mathematical meaning of
each finite-word predicate; its internal interpretation and the collection of its values then follow from the
same two principles.

\begin{lemma*}[\termdefine{Internal subsets from bounded recognition}]
Let $M$ be transitive, let $A\in M$, and let $B\IncludedIn A$. Suppose that a $\Delta_0$ formula
$\varphi(\vec\eta,x)$ with parameters $\vec\eta$ in $M$ satisfies
$$\forall x\in A\;\bigl(\varphi(\vec\eta,x)\longleftrightarrow x\in B\bigr).$$
If $M$ satisfies Separation for this formula, then $B\in M$.
\end{lemma*}

\begin{proof}[Proof]
Absoluteness identifies the internal and external interpretations of $\varphi$ on $A$.
Separation therefore gives $\{x\in A:\varphi(\vec\eta,x)\}\in M$. The recognition equivalence and
$B\IncludedIn A$ identify this set with $B$.
\end{proof}

This lemma applies equally to graphs of functions and sets of tree nodes. In each application, specify an
internal ambient set, verify that every parameter belongs to $M$, and prove the recognition equivalence
there. The internal interpretation and the collection step then follow from the lemma. For numerical
pairing and its inverse projections in §{sec:internal-natural-arithmetic}, the parameters are $\omega$ and
the previously constructed arithmetic graphs. No separate correspondence between internal and external
natural-number witnesses is needed for each operation.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部subsetを得る一般的補題の適用には有界記述・内部パラメータが必要であり、外部regularityから得たclosed
approximationだけでtree codeの内部所属を結論しないという注意。この段落で新たな反例やinternal
approximation存在を証明せず、その具体的な構成は後のmeasure付録に残す。)
--> The lemma does not assert that every externally defined subset of $A$ belongs to $M$.
The bounded description and its internal parameters are essential. In particular, applying external
regularity to obtain a closed approximation does not establish that its tree code belongs to $M$;
the existence of such internal approximations still requires a construction.<!--
formalization: skip-end
-->

We apply the principle to finite words. Continue to write $F$ for the internal set of finite word graphs and
$e(s)$ for the graph of $s$. For a word $s$ and $i\in\omega$, define
$$r(s,i):=\begin{cases}s(i),&i<\Length{s},\\0,&\Length{s}\le i.\end{cases}$$
For any $n\in\omega$, the word $\restrict{s}{n}$ consists of the first $\min(n,\Length{s})$ entries.
For $s,t\in F$ and $i,v,n,j\in\omega$, use the following predicate descriptions:
$$\begin{aligned}
L(s,n)&:\equiv s:n\to\omega,\\
R(s,i,v)&:\equiv\Pair{i}{v}\in s\\
 &\qquad{}\lor(v=0\land\forall w\in\omega\;\Pair{i}{w}\notin s),\\
T(s,n,t)&:\equiv\forall i,v\in\omega\;[\Pair{i}{v}\in t\\
 &\qquad\longleftrightarrow(i\in n\land\Pair{i}{v}\in s)],\\
J(s,j,t)&:\equiv\exists n,m\in\omega\;[L(s,n)\land L(t,m)\\
 &\qquad{}\land m=n\cup\{n\}\land s\IncludedIn t\land\Pair{n}{j}\in t].
\end{aligned}$$

\begin{proposition*}[\termdefine{Recognition of finite-word operations}]
For actual finite words $s,t$ and natural-number inputs, these predicates recognize the following operations:
$$\begin{aligned}
L(e(s),n)&\longleftrightarrow n=\Length{s},\\
R(e(s),i,v)&\longleftrightarrow v=r(s,i),\\
T(e(s),n,e(t))&\longleftrightarrow t=\restrict{s}{n},\\
J(e(s),j,e(t))&\longleftrightarrow t=s\concat\SingletonSeq{j}.
\end{aligned}$$
The same equivalences hold for their internal interpretations.
\end{proposition*}

\begin{proof}[Proof]
A function graph determines its domain, giving the length assertion. Lookup splits into the cases where the
coordinate is present and absent. Restriction retains exactly the pairs whose first coordinate is below the
cutoff; equality of all pairs gives equality of the finite words. For extension, the two function conditions
fix the lengths, inclusion fixes the prefix, and the last pair fixes the appended entry. These arguments prove
the external equivalences. The uniform interpretation principle gives all the internal equivalences at once.
\end{proof}

\begin{proposition*}[\termdefine{Internal finite-word operation graphs}]
Under the axioms of §{sec:internal-list-coding}, the following three graphs belong to $M$:
$$\begin{aligned}
\mathcal R&:=\{\Pair{\Pair{s}{i}}{v}\in(F\times\omega)\times\omega:R(s,i,v)\},\\
\mathcal T&:=\{\Pair{\Pair{s}{n}}{t}\in(F\times\omega)\times F:T(s,n,t)\},\\
\mathcal J&:=\{\Pair{\Pair{s}{j}}{t}\in(F\times\omega)\times F:J(s,j,t)\}.
\end{aligned}$$
\end{proposition*}

\begin{proof}[Proof]
The bounding products are internal by the product construction. The preceding proposition identifies the
internally interpreted predicates with the actual operations. Separation collects each whole graph. To encode
an input-output triple, form the intermediate ordered pair by Pairing; its two coordinates and the output are
bounded by the displayed factors. This is one graph-collection argument applied to the three predicates.
\end{proof}

\begin{lemma*}[\termdefine{Coordinatewise finite-word maps}]
Let $f:\omega\to\omega$ have an internal graph $G_f$. Define
$$\begin{aligned}
U(G_f,s,t):\equiv{}&\forall i,v\in\omega\;[\\
&\Pair{i}{v}\in t\longleftrightarrow\exists w\in\omega\;(\Pair{i}{w}\in s\\
&\hspace{8em}{}\land\Pair{w}{v}\in G_f)].
\end{aligned}$$
For finite words $s,t$, this predicate holds exactly when $t=f\circ s$, with the same finite domain as $s$.
Its internal interpretation has the same meaning.
\end{lemma*}

\begin{proof}[Proof]
At each coordinate of the source word, its unique value is the witness for the numerical graph, whose unique
output is the target value. Outside the source domain there is no such witness. Thus the pair-membership
conditions are precisely those of the coordinatewise image. Apply the uniform interpretation principle.
In particular, the two numerical projection graphs constructed in §{sec:internal-natural-arithmetic} give the
two projected words used by the counterexample tree.
\end{proof}

\begin{proposition*}[\termdefine{Internal child-code graph}]
The binary numerical operation
$$h(i,j):=\LambdaListCode{\LambdaListDecode{i}\concat\SingletonSeq{j}}$$
has its whole graph in $M$. On the two numerical components of a row index, it gives exactly the child code
used in the finite Borel-certificate test of §{sec:ranked-closed-inclusions}.
\end{proposition*}

\begin{proof}[Proof]
Use the decoder graph $D$ and the extension graph $\mathcal J$. The output equation $k=h(i,j)$ is equivalent to
$$\begin{aligned}
\exists s,t\in F\;[&\Pair{i}{s}\in D
\land\Pair{\Pair{s}{j}}{t}\in\mathcal J\\
&{}\land\Pair{k}{t}\in D].
\end{aligned}$$
Both witnesses are bounded by the internal set $F$. Expand the binary-graph condition by the bounded
ordered-pair predicate, so the displayed formula is $\Delta_0$. The decoder first fixes
$s=e(\LambdaListDecode{i})$; extension fixes the new word; its second use and the inverse-numbering identities
fix the output code. Conversely, those two finite graphs supply the witnesses. The uniform interpretation
principle gives the same equivalence internally, and the graph-collection argument uses Separation in
$(\omega\times\omega)\times\omega$ to obtain the graph. Substituting the numerical projections of the row index
recovers the child operation already computed by the lambda term in §{sec:lambda-recursive-borel-separation}.
\end{proof}

\begin{proposition*}[\termdefine{Bounded description of finite Borel tests}]
Suppose that the Borel label graph belongs to $M$. The finite row test $P_i(a,d)$ of
§{sec:ranked-closed-inclusions}, extended to arbitrary finite words by the default-zero lookup $r$, has a
bounded description using the internal graphs already constructed. The same is true of the predicate
$$V(e(a),e(d)):\equiv\forall i<\Length{a}\;\bigl(b(i)\le\Length{a}\ \Longrightarrow\ P_i(a,d)\bigr).$$
Their internal interpretations agree with the actual finite tests. The same assertions hold for
$P_i^\varepsilon$ and the corresponding predicate $V^\varepsilon$, uniformly for $\varepsilon\in\{0,1\}$.
\end{proposition*}

\begin{proof}[Proof]
Use the two projection graphs to write $i=\NatPair{p}{k}$, and use the child-code graph to obtain $t=h(p,k)$.
Read the labels at $p,t$ from $L_{\mathrm{num}}$, and read $r(d,0),r(d,p),r(d,t)$ using $R$.
Project these last three values to obtain the root bit, the two node bits, and the selected child index.
Every numerical auxiliary variable is bounded by $\omega$; the decoder supplies the leaf word in $F$.
For $P_i^\varepsilon$, the root bit must equal the finite ordinal $\varepsilon\in M$; all other conditions
are unchanged. In particular, root bit $0$ gives precisely the absent-node, union, complement,
and leaf clauses defining $P_i$.

Each numerical comparison is a bounded membership condition on finite ordinals. Addition uses its internal
graph, and the leaf condition is
$$\restrict{a}{\Length{\LambdaListDecode{k}}}=\LambdaListDecode{k}
\quad\Longleftrightarrow\quad e(\LambdaListDecode{k})\IncludedIn e(a).$$
An atomic binary-graph condition also has a bounded expansion: to express
$\Pair{\Pair{u}{v}}{z}\in G$, quantify over $p\in G$, $s\in p$, and $r\in s$, and require
$r=\Pair{u}{v}$ and $p=\Pair{r}{z}$. The Kuratowski pair supplies these witnesses.
Thus no unbounded quantifier is hidden in the auxiliary tuple notation.

For the row-selection condition, put $n=\Length{a}$ using $L$. The definition of $b$ gives
$$b(i)\le n\quad\Longleftrightarrow\quad
p<n\land t<n\land0<n\land\Length{\LambdaListDecode{k}}\le n.$$
The decoder and $L$ give the last length, so this too is a bounded predicate. Bind the row index by $i\in n$
and use implication to select the rows that fit. Finally, all lookups in row $i$ occur below $b(i)$, and its leaf
word has length at most $b(i)$. Hence
$$P_i(\restrict{a}{b(i)},\restrict{d}{b(i)})\quad\Longleftrightarrow\quad P_i(a,d).$$
This holds even for shorter words: default-zero lookup is unchanged by a cutoff above the queried coordinate,
and two successive restrictions compose by taking the smaller cutoff. Therefore $V$ is exactly the bounded
family of row tests used in the counterexample tree. The uniform interpretation principle applies to the
whole assembled predicates.
\end{proof}

\begin{proposition*}[\termdefine{Internal counterexample node set}]
Assume the axioms of §{sec:internal-list-coding}. Let $c$ have its label graph in $M$, and suppose that
$$W_T:=\{e(s):s\in T\}\in M.$$
Then the actual node set of the counterexample tree has its graph-coded copy in $M$:
$$W_{Q(c,T)}:=\{e(w):w\in Q(c,T)\}\in M.$$
This construction does not require $c$ to be valid or $T$ to be downward closed. For either
$\varepsilon\in\{0,1\}$, it also gives $W_{Q^\varepsilon(c,T)}\in M$: replace $V$ by $V^\varepsilon$ in
the bounded predicate below. The additional parameter $\varepsilon$ is an internal finite ordinal.
\end{proposition*}

\begin{proof}[Proof]
Let $G_1,G_2$ be the numerical projection graphs. For a candidate word graph $w\in F$, form the bounded
predicate
$$\begin{aligned}
\Theta(w):\equiv{}&\forall v\in F\;\bigl[v\IncludedIn w\ \Longrightarrow\quad
\exists a,d\in F\;[\\
&U(G_1,v,a)\land U(G_2,v,d)\\
&{}\land a\in W_T\land V(a,d)]\bigr].
\end{aligned}$$
For actual words, graph inclusion is exactly the prefix relation. The predicates $U$ force $a,d$ to be the two
coordinate words of that prefix, and the preceding proposition identifies $V$ with its required row tests.
Thus $\Theta(e(w))$ holds exactly when $w\in Q(c,T)$, including the empty-prefix test.
All parameters are internal. The uniform interpretation principle and Separation on $F$ now give
$\{w\in F:\Theta(w)\}\in M$, and this set is exactly $W_{Q(c,T)}$.
\end{proof}

## Transferring Closed Inclusions {#sec:internal-closed-inclusions}

\begin{mathmeta}
  \vars{j}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続のclosed-inclusion transferのために、モデル公理、標準cylinder basis、valid label graph、
内部tree-node set、外部/内部解釈の記号を固定する文脈設定。実際の包含移送は直後の定理・証明として対象に残し、
この仮定の宣言だけを対象外とする。)
--> We now connect the internal counterexample tree to the Borel interpretation. Throughout this section,
$M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation, Replacement, and Choice.
Use the standard cylinder basis, let $c$ be a valid Borel expression with its label graph in $M$, and let
$T\IncludedIn\finseq{\omega}$ have $W_T\in M$. Write $B_c$ for the external interpretation and
$\BorelInterpretation{c}{M}$ for its internal interpretation, whose elements are point graphs.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Internal coordinatewise maps}]
If $x,f:\omega\to\omega$ have their function graphs $g_x,G_f$ in $M$, then $g_{f\circ x}\in M$.
\end{lemma*}

\begin{proof}[Proof]
Separate from $\omega\times\omega$ the pairs $\Pair{n}{k}$ satisfying
$$\exists j\in\omega\;(\Pair{n}{j}\in g_x\land\Pair{j}{k}\in G_f).$$
This is a bounded predicate, so the uniform interpretation principle gives an internal set. The first graph
forces $j=x(n)$ and the second forces $k=f(x(n))$. Thus the separated set is exactly $g_{f\circ x}$.
In particular, both numerical projections can be applied to an internal sequence of paired entries.
\end{proof}

\begin{theorem*}[\termdefine{Internal counterexample branches}]
The counterexample tree $Q=Q(c,T)$ satisfies
$$\begin{gathered}
\exists z\in\TreeBody{Q}\;(g_z\in M)\\
\Longleftrightarrow\\
\exists x\in\TreeBody{T}\;
(g_x\in M\land g_x\notin\BorelInterpretation{c}{M}).
\end{gathered}$$
\end{theorem*}

\begin{proof}[Proof]
Given an internal branch $z$, project its entries onto their first coordinates to obtain $x$.
The lemma gives $g_x\in M$. The branch analysis of §{sec:ranked-closed-inclusions} gives
$x\in\TreeBody{T}$ and a negative evaluation certificate, hence $x\notin B_c$.
Agreement of the internal and external interpretations at $x$ gives
$g_x\notin\BorelInterpretation{c}{M}$.

Conversely, let $x$ satisfy the right-hand side. Agreement at this internal point gives $x\notin B_c$,
so §{sec:ranked-closed-inclusions} supplies an external branch of $Q$.
The node set $W_Q$ belongs to $M$ by §{sec:internal-finite-tests}, and the strict-extension relation
$R_{W_Q}$ belongs to $M$ by §{sec:internal-rank-certificates}. If there were no internal branch,
the theorem in §{sec:internal-tree-branches} would exclude every external branch, a contradiction.
Thus an internal branch exists. This argument does not require the resulting branch to project to the
originally chosen point $x$, and it does not assert computable selection of a certificate.
\end{proof}

\begin{corollary*}[\termdefine{Transfer of closed Borel inclusions}]
If every $x\in\TreeBody{T}$ with $g_x\in M$ satisfies
$g_x\in\BorelInterpretation{c}{M}$, then
$$\TreeBody{T}\IncludedIn B_c.$$
\end{corollary*}

\begin{proof}[Proof]
The theorem excludes internal branches of $Q$. The internal-branch theorem then excludes all external
branches as well, and the counterexample-tree criterion gives the inclusion. In particular, the inclusion
holds for new points in a larger transitive model. The proof uses the previously constructed internal rank
through the internal-branch theorem, rather than assuming that agreement on old points suffices.
\end{proof}

\begin{corollary*}[\termdefine{Transfer of closed disjointness}]
Under the same hypotheses, if every $x\in\TreeBody{T}$ with $g_x\in M$ lies outside $B_c$, then
$$\TreeBody{T}\cap B_c=\emptyset.$$
\end{corollary*}

\begin{proof}[Proof]
Use $Q^1(c,T)$, whose tests are $P_i^1$. The parameterized bounded-description and node-set propositions in
§{sec:appendix-borel-finite-test-infrastructure} put its whole node set in $M$.
A branch now gives a point in $\TreeBody{T}\cap B_c$,
and a point in that intersection has a positive evaluation certificate, hence gives an external branch.
If an external branch existed, the internal-branch theorem would supply an internal branch.
Its coordinate projection would be an internal point in the intersection, contrary to the hypothesis.
Thus there is no external branch, and the intersection is empty. This uses the same tree construction and
rank argument as closed inclusion; it does not require constructing a separate complement code.
\end{proof}

