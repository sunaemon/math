# Appendix: Foundations of Forcing {#sec:appendix-forcing-background}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
本付録がPolish空間上のgeneric pointsの背後にある集合論的forcingを扱うという導入。
新しい個別の数学的主張を証明する段落ではない。)
-->
This appendix develops the general forcing machinery used in §{sec:forcing}. The main text treats forcing as a source of
generic points in Polish spaces; here we record the set-theoretic construction behind that use.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
集合論付録・主章・本付録の役割と収録内容を案内する序文。定義可能性と真理補題を主章の正当化として使う依存関係の説明であり、
実際のforcing構成と証明は後続の独立単位として対象に残す。)
--> The set-theoretic prerequisites are collected in §{sec:appendix-set-theory}.
§{sec:forcing} is the user's manual: it shows how \termuse{Cohen forcing} and
\termuse{random forcing} act on Polish spaces and how dense-set arguments yield descriptive-set-theoretic consequences.
This appendix is the technical manual: it defines ground models, forcing notions, $P$-names, valuation, the forcing
relation, the \termforward{forcing theorem}, the \termforwardas{forcing truth lemma}{truth lemma}, and the construction
of $M[G]$. When the main text says that a condition forces a statement about a generic real, the justification is the
forcing theorem and truth lemma proved here.<!--
formalization: skip-end
-->

## Ground Models and Forcing Notions {#sec:ground-models-forcing-notions}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部モデル付録への参照と、各構成に必要な有限fragmentを満たす推移的基礎モデルを固定するという仮定の宣言。
ここで基礎モデルの新たな存在定理を主張しない。)
--> Transitive-model closure and recursion are developed in §{sec:appendix-internal-models}.
Throughout this appendix, fix a transitive ground model $M$ of the finite fragment needed for each construction.<!--
formalization: skip-end
-->

A \termdefine{forcing notion} in $M$ is a nonempty partially ordered set $\Pair{P}{\le} \in M$. Its elements are
\termdefineas{condition}{conditions}. The order is read as refinement:
$$q \le p \quad\text{means that } q \text{ is stronger than } p.$$
Two conditions $p,q$ are \termdefine{compatible}, written $p \parallel q$, if they have a common strengthening $r \le
p,q$; otherwise they are \termdefine{incompatible}, written $p \perp q$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のdense/open dense/predenseの三つの定義を導入する見出しだけの行。
各定義は標準IsCoinitial・IsLowerSet・共通強化の存在へ接続し、この案内行だけを対象外とする。)
--> A set $D \IncludedIn P$ is:<!--
formalization: skip-end
-->

*   \termdefine{dense} if every $p \in P$ has some $q \le p$ with $q \in D$;
*   \termdefine{open dense} if it is dense and downward closed: $p \in D$ and $q \le p$ imply $q \in D$;
*   \termdefine{predense below p} if every $q \le p$ is compatible with some element of $D$.

A \termdefine{filter} on $P$ is a nonempty set $G \IncludedIn P$ satisfying:

1.  $G$ is upward closed toward weaker conditions: if $p \in G$ and $p \le q$, then $q \in G$;
2.  $G$ is directed downward: if $p,q \in G$, then some $r \in G$ satisfies $r \le p,q$.

A filter $G$ is \termdefineas{M-generic}{$M$-generic} if it meets every dense set $D \IncludedIn P$ with $D \in M$.

\begin{lemma*}[\termdefine{Open dense test for genericity}]
Let $M$ be transitive and contain the condition set $P$ and its order relation $R$.
Suppose the Separation instance for the bounded predicate in the proof holds in $M$.
A filter $G$ on $P$ is $M$-generic if and only if it meets every open dense subset of $P$ belonging to $M$.
\end{lemma*}

\begin{proof}[Proof]
One implication is immediate. For the converse, let $D\IncludedIn P$ be dense and belong to $M$. Put
$$U:=\{q\in P:\exists p\in D\,(\Pair{q}{p}\in R)\}.$$
The displayed predicate is bounded, so Separation gives $U\in M$. Reflexivity gives $D\IncludedIn U$,
hence $U$ is dense; transitivity of the order makes $U$ downward closed.
Choose $q\in G\cap U$ and a witness $p\in D$ with $q\le p$.
Upward closure of the filter gives $p\in G$, so $G$ meets $D$.
\end{proof}

\begin{lemma*}[\termdefineas{Rasiowa--Sikorski lemma}{Rasiowa--Sikorski}]
If $M$ is externally countable, then every condition $p_{-1}\in P$ belongs to an $M$-generic filter.
\end{lemma*}

\begin{proof}[Proof]
The dense subsets of $P$ belonging to $M$ form a countable family. Adjoin $P$ if necessary to make the family nonempty.
Enumerate it as $\{D_n:n\in\omega\}$. Starting at the prescribed condition, choose
$$p_{-1}\ge p_0\ge p_1\ge\cdots,\qquad p_n\in D_n,$$
using density at each step, and put
$$G:=\{q\in P:\exists n\in\omega\,(p_n\le q)\}.$$
This set is upward closed. If $q,r\in G$ are witnessed by $n,m$, respectively, then $p_{\max\{n,m\}}$
belongs to $G$ and is stronger than both. Thus $G$ is a filter. It contains $p_{-1}$ because $p_0\le p_{-1}$,
and it meets every $D_n$ at $p_n$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Rasiowa–Sikorski構成が外部で行われること、filterのモデル内所属をこの構成から主張しないことと、
Baire-categoryの構成との類比を説明する背景。trivial forcingの場合との対比も例示で、
この段落で非内部性の反例や新しいgeneric存在定理を証明しない。)
--> The construction is external; the resulting filter need not belong to $M$. For trivial forcing, it may
already belong to $M$. The descending-chain argument is the forcing analogue of the Baire-category
construction that intersects countably many dense open sets in a Polish space.<!--
formalization: skip-end
-->

## Names and Valuation {#sec:forcing-names-valuation}

\begin{mathmeta}
  \vars{I}{Set}
  \vars{s}{Seq(Nat)}
  \vars{n,\varepsilon}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
名前による拡大の定義へ移るための説明。Gを加えて何らかの閉包を取る手続きとの不一致を数学的反例や独立定理として証明する箇所ではなく、
次の実際の名前・valuationの定義が対象となる。)
--> The extension $M[G]$ is not formed by simply adding $G$ as a new set and closing under ZFC operations.
Instead, names in $M$ specify the objects that will appear after forcing.<!--
formalization: skip-end
-->

For a set $P$ of conditions, define the class of \termdefineas{P-name}{$P$-names} recursively:
$$\tau \text{ is a } P\text{-name}
\quad\Longleftrightarrow\quad
\tau \IncludedIn \{\Pair{\sigma}{p} : \sigma \text{ is a } P\text{-name and } p \in P\}.$$
Use the usual ordered pair $\Pair{\sigma}{p}=\{\{\sigma\},\{\sigma,p\}\}$.
If $\Pair{\sigma}{p}\in\tau$, then
$$\sigma\in\{\sigma\}\in\Pair{\sigma}{p}\in\tau.$$
Thus the rank of $\sigma$ is strictly smaller than that of $\tau$, so the recursion is well founded.
Write $M^P$ for the class of all $P$-names belonging to $M$.

For $G\IncludedIn P$, the \termdefine{valuation} of a name is defined by the same rank recursion:
$$\tau^G := \{\sigma^G : \exists p \in G,\; \Pair{\sigma}{p} \in \tau\}.$$
The first coordinates occurring here form a subset of $\bigcup\bigcup\tau$, so Replacement makes the right-hand side
a set. This recursion determines the valuation uniquely: if two assignments satisfy the displayed equation,
induction on the rank of $\tau$ makes them agree on each contributing $\sigma$, hence on $\tau$ by Extensionality.
The generic extension is
$$M[G] := \{\tau^G : \tau \in M^P\}.$$
These definitions make sense even before imposing genericity on $G$.

For any set $x$, its \termdefine{check name} is defined by membership recursion:
$$\check{x} := \{\Pair{\check{y}}{p} : y \in x,\; p \in P\}.$$
We use this all-conditions convention below; it does not require a weakest condition.
When $P$ has a weakest condition $1_P$, the usual alternative is
$$\check{x} := \{\Pair{\check{y}}{1_P} : y \in x\}.$$
The two constructions need not give the same name, but they have the same valuation under every nonempty filter.

\begin{lemma*}[Check names in the ground model]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
If $P\in M$, then $\check{a}\in M$ for every $a\in M$.
\end{lemma*}

\begin{proof}[Proof]
With parameter $P$, use the step rule
$$C_P(a,g):=\GraphRange{g}\times P.$$
The range and product constructions above put its value in the model whenever its arguments belong to the
model. An internal defining formula is
$$\psi_P(a,g,b)\;:\equiv\;\exists r\,(r=\GraphRange{g}\land b=r\times P).$$
Use the range equality already displayed and expand the product equality as
$$\forall q\,\bigl(q\in b\leftrightarrow
 \exists v\in r\,\exists p\in P\,(q=\Pair{v}{p})\bigr).$$
All actual pairs from the two factors belong to the model by Pairing, so this internal formula recognizes
the actual product, not merely its intersection with the model.

For the external check-name function, the range of its graph on $a$ is
$\{\check{y}:y\in a\}$. Its product with the condition set is precisely the defining set of pairs for
$\check{a}$. Thus the check-name function satisfies this step equation.
Internal membership recursion and the comparison lemma now give $\check{a}\in M$.
No Choice axiom or generic filter is needed for this closure statement.
\end{proof}

\begin{lemma*}[Basic valuation calculations]
Let $\varnothing\ne G\IncludedIn P$. Every $\check{x}$ is a $P$-name and $\check{x}^G=x$.
More generally, let $I$ be a set, let $a_i$ be sets, and let $p_i\in P$ for $i\in I$. Then
$$\tau:=\{\Pair{\check{a_i}}{p_i}:i\in I\}$$
is a $P$-name and
$$\tau^G=\{a_i:i\in I,\;p_i\in G\}.$$
\end{lemma*}

\begin{proof}[Proof]
Membership induction shows that $\check{x}$ is a name, since its first coordinates are names $\check{y}$ with $y\in x$.
For its valuation, the same induction gives
$$\check{x}^G=\{\check{y}^G:y\in x,\;\exists p\,(p\in G)\}=\{y:y\in x\}=x.$$
Nonemptiness of $G$ is used in the middle equality. The name property of $\tau$ follows from that of the check names.
Its valuation formula follows by substituting $\check{a_i}^G=a_i$ into the defining recursion.
For the weakest-condition convention, the same argument uses $1_P\in G$, which holds for every nonempty filter
by upward closure.
\end{proof}

The filter itself has the canonical name
$$\dot G := \{\Pair{\check{p}}{p} : p \in P\}.$$
The lemma with labels $a_p=p$ gives $\dot G^G=G$.
For Cohen forcing $P=\finseq{2}$ ordered by extension, the canonical name for the generic real is
$$\dot c := \{\Pair{\check{\Pair{n}{\varepsilon}}}{s} : s \in \finseq{2},\; n<\Length{s},\; s(n)=\varepsilon\}.$$
Applying the same formula to the labels $\Pair{n}{\varepsilon}$ gives
$$\dot c^G=\{\Pair{n}{\varepsilon}:\exists s\in G,\;n<\Length{s},\;s(n)=\varepsilon\}=\bigcup G.$$
Directedness makes this union a function, and the dense length requirements make its domain all of $\omega$.
Thus the name evaluates to the generic real constructed in §{sec:cohen-forcing-detail}.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
これからcheck-nameの公理を保ってP,Aをパラメータに固定し、内部relationを用いる構成を行うという導入。具体的なdecision
relationと名前の内部所属は直後の定理と証明で別に扱う。)
--> We now construct these names inside the ground model, using a whole internal relation that records
which conditions activate which labels. Retain the axioms of
the check-name lemma, and let $P,A\in M$.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{CheckNameGraph,ForcingDecisionName}
\end{mathmeta}

Write
$$\CheckNameGraph{P}{A}:=\{\Pair{a}{\check a}:a\in A\}.$$
The parameter $P$ specifies the all-conditions convention for every check name.

\begin{lemma*}[\termdefine{Internal check-name graphs}]
The entire graph $\CheckNameGraph{P}{A}$ belongs to $M$.
\end{lemma*}

\begin{proof}[Proof]
Apply the internal recursive-value formula from §{sec:internal-model-closure} to the check-name
step rule. For $a,\sigma\in M$, it holds precisely when $\sigma=\check a$. The check-name closure lemma
supplies this unique value in $M$. The shared definable-graph construction now applies Replacement on
$A$ and collects the pairs $\Pair{a}{\check a}$ into one graph in $M$.
\end{proof}

\begin{theorem*}[\termdefine{Decision names from internal relations}]
Suppose $E\in M$ and $E\IncludedIn A\times P$. Define
$$\ForcingDecisionName{P}{A}{E}
:=\{\Pair{\check a}{p}:a\in A,\ p\in P,\ \Pair{a}{p}\in E\}.$$
This is a $P$-name belonging to $M$. For $\emptyset\ne G\IncludedIn P$,
$$\ForcingDecisionName{P}{A}{E}^{G}
=\{a\in A:\exists p\in G\ (\Pair{a}{p}\in E)\}.$$
Several conditions may be attached to the same label; no choice of a single condition is required.
\end{theorem*}

\begin{proof}[Proof]
Put $H=\CheckNameGraph{P}{A}$ and $R=\GraphRange{H}$. Both sets belong to $M$, as does $R\times P$.
For a candidate pair $z$, use the bounded condition
$$\begin{aligned}
&\exists a\in A\;\exists p\in P\;\exists\sigma\in R\\
&\qquad(\Pair{a}{\sigma}\in H\land\Pair{a}{p}\in E
\land z=\Pair{\sigma}{p}).
\end{aligned}$$
The common bounded interpretation theorem applies directly. Separation on $R\times P$ therefore
constructs exactly the displayed name in $M$. Every first coordinate is a check name and every second
coordinate belongs to $P$, which proves the name condition. Substituting $\check a^G=a$ into the
valuation equation gives the stated value.
\end{proof}

\begin{corollary*}[\termdefine{Generic-filter and union names in the ground model}]
The names
$$\dot G=\{\Pair{\check p}{p}:p\in P\},\qquad
\dot u=\{\Pair{\check a}{p}:p\in P,\ a\in p\}$$
belong to $M$. For $\emptyset\ne G\IncludedIn P$,
$$\dot G^G=G\in M[G],\qquad \dot u^G=\bigcup G\in M[G].$$
In particular, the Cohen-real name displayed above belongs to $M$ when its condition set belongs to $M$.
\end{corollary*}

\begin{proof}[Proof]
For $\dot G$, take $A=P$ and the diagonal relation
$$E_0=\{\Pair{p}{p}:p\in P\}.$$
It belongs to $M$ by bounded Separation on $P\times P$.
For $\dot u$, take $A=\bigcup P\in M$ and the relation
$$E_1=\{\Pair{a}{p}\in A\times P:a\in p\}.$$
This relation also belongs to $M$ by bounded Separation. Apply the theorem to each relation, and use
the previously proved valuation formulas. Membership in $M[G]$ follows from the definition of the
extension as the values of names in $M$. No genericity assumption is needed for these two membership
claims. For Cohen conditions represented by finite function graphs, $\dot u$ is exactly $\dot c$.
\end{proof}

\begin{lemma*}[Transitivity of the extension]
Let $M$ be transitive and $\varnothing\ne G\IncludedIn P$. Then $M[G]$ is transitive.
If $\check{x}\in M$ for every $x\in M$, then also $M\IncludedIn M[G]$.
\end{lemma*}

\begin{proof}[Proof]
Take $x=\tau^G\in M[G]$ and $y\in x$. Some pair $\Pair{\sigma}{p}\in\tau$ with $p\in G$ satisfies
$y=\sigma^G$. Since $\tau$ is a name, so is $\sigma$. Transitivity of $M$, applied successively along
$$\sigma\in\{\sigma\}\in\Pair{\sigma}{p}\in\tau\in M,$$
gives $\sigma\in M$. Thus $y\in M[G]$, proving transitivity.
Under the additional check-name closure hypothesis, each $x\in M$ equals $\check{x}^G$ for a name in $M$,
so $x\in M[G]$.
\end{proof}

For a transitive ground model satisfying the axioms in the check-name lemma, the closure hypothesis is
now established. Hence $M\IncludedIn M[G]$ whenever $P\in M$ and $\varnothing\ne G\IncludedIn P$.
This inclusion uses the concrete internal step rule and the comparison with external check names;
transitivity alone would not supply it.

## The Forcing Relation and the Forcing Theorem {#sec:forcing-relation}

For the following semantic definition, assume that $M$ is countable in the ambient universe, so that
a generic filter through each condition exists. The semantic definition is:
$$p \forces \varphi(\tau_0,\ldots,\tau_{k-1})$$
iff for every $M$-generic $G \IncludedIn P$ with $p \in G$,
$$M[G] \models \varphi(\tau_0^G,\ldots,\tau_{k-1}^G).$$
This definition uses generic filters outside $M$. The \termuse{forcing theorem} says that this external-looking relation
is actually definable in $M$ and satisfies the expected truth lemma.

\begin{theorem*}[\termdefine{forcing theorem}] Let $M$ be a countable transitive model of ZFC, $P \in M$, and $\varphi$
a formula in the forcing language. Then:

\begin{enumerate}
\item \termdefine{definability}. For each fixed $\varphi$, the relation $p \forces \varphi(\vec\tau)$ is
definable in $M$
from $P$ and the names $\vec\tau$. This is a schema, not a single truth definition uniform in all formula codes.
\item \termdefineas{forcing truth lemma}{Truth lemma}. If $G$ is $M$-generic, then
\end{enumerate}
    $$M[G]\models\varphi(\vec\tau^G)
    \quad\Longleftrightarrow\quad
    \exists p \in G\; (p \forces \varphi(\vec\tau)).$$

\end{theorem*}

\begin{proof}[Proof] Distinguish the \emph{semantic} forcing relation $p \forces \varphi$, defined externally by
quantifying over $M$-generic filters, from the \emph{syntactic} relation $p \forces^* \varphi$ given by the
atomic recursion and formula clauses below. The construction in §{sec:internal-atomic-forcing} defines the
atomic relations inside $M$. The construction in §{sec:internal-forcing-formulas} defines the names internally
and extends the definition through each fixed formula. Thus $\forces^*$ is $M$-definable.
The internal test sets constructed in §{sec:internal-generic-truth} allow the truth proof below to apply to
every $M$-generic filter. The equivalence
$p \forces^* \varphi \Leftrightarrow p \forces \varphi$ transfers this definition to the semantic relation,
and the same induction gives the truth lemma.

\textbf{Atomic clauses.} Define $p \forces^* \sigma \in \tau$ and $p \forces^* \sigma = \tau$ for $P$-names $\sigma,
\tau \in M^P$ by recursion on the lexicographic order $\prec$ on the rank-pair
$$\Pair{\sigma}{\tau} \;\longmapsto\; \Pair{\max(\mathrm{rank}\sigma, \mathrm{rank}\tau)}{\min(\mathrm{rank}\sigma,
\mathrm{rank}\tau)}.$$
This order is well-founded because pairs of ordinals are well-ordered lexicographically:

\begin{itemize}
\item $p \forces^* \sigma \in \tau$ iff the set
\end{itemize}
    $$\{q \le p \;:\; \exists \Pair{\pi}{r} \in \tau,\; q \le r \text{ and } q \forces^* \sigma = \pi\}$$
    is dense below $p$.
\begin{itemize}
\item $p \forces^* \sigma = \tau$ iff for every $\Pair{\pi}{r} \in \sigma$ the set
\end{itemize}
    $$\{q \le p : q \perp r \text{ or } q \forces^* \pi \in \tau\}$$
    is dense below $p$, \emph{and} the same condition holds with $\sigma,\tau$ swapped.

Each recursive call lies at a strictly smaller rank-pair. The call $q \forces^* \sigma = \pi$ inside the
$\sigma \in \tau$ clause uses $\mathrm{rank}\pi < \mathrm{rank}\tau$. Decreasing one coordinate of a pair while
fixing the other strictly decreases the pair sorted in descending order: either its maximum decreases,
or its maximum stays fixed and its minimum decreases. Thus the new rank-pair is $\prec$-smaller.
The call $q \forces^* \pi \in \tau$ inside the $\sigma = \tau$ clause uses $\mathrm{rank}\pi < \mathrm{rank}\sigma$,
with the same lexicographic decrease. This gives an external well-founded recursion.
The construction in §{sec:internal-atomic-forcing} produces its table in $M$ and supplies an explicit
defining formula interpreted in $M$.

\textbf{Connective and quantifier clauses.} Extend $\forces^*$ to all $L_\in$-formulas by recursion on formula
complexity:
$$\begin{aligned}
p \forces^* \varphi \land \psi
&\Longleftrightarrow p \forces^* \varphi \text{ and } p \forces^* \psi,\\
p \forces^* \neg\varphi
&\Longleftrightarrow \text{no } q \le p \text{ satisfies } q \forces^* \varphi,\\
p \forces^* \varphi \lor \psi
&\Longleftrightarrow \{q \le p : q \forces^* \varphi \text{ or } q \forces^* \psi\} \text{ is dense below } p,\\
p \forces^* \varphi \to \psi
&\Longleftrightarrow \forall q \le p\;(q \forces^* \varphi \Rightarrow q \forces^* \psi),\\
p \forces^* \exists x\,\varphi(x)
&\Longleftrightarrow \{q \le p : \exists \tau \in M^P,\; q \forces^* \varphi(\tau)\} \text{ is dense below } p,\\
p \forces^* \forall x\,\varphi(x)
&\Longleftrightarrow \forall \tau \in M^P\;\; p \forces^* \varphi(\tau).
\end{aligned}$$

One may take falsity, the atomic formulas, implication, and universal quantification as primitive.
No condition forces falsity. The other operations are given by
$$\begin{aligned}
\neg\varphi&:=\varphi\to\bot,\\
\varphi\land\psi&:=\neg(\varphi\to\neg\psi),\\
\varphi\lor\psi&:=\neg\varphi\to\psi,\\
\exists x\,\varphi&:=\neg\forall x\,\neg\varphi.
\end{aligned}$$
We verify below that these definitions give exactly the displayed forcing clauses, including the density clause
for the existential quantifier.

Two structural properties follow by induction on formula complexity (with the atomic cases checked from the clauses
above):

\begin{itemize}
\item \textbf{Monotonicity.} If $p \forces^* \varphi$ and $q \le p$, then $q \forces^* \varphi$. The atomic and density
clauses inherit denseness from $p$ down to $q$; the universal-style clauses ($\neg, \to, \forall$) inherit by reusing $q
\le p$ as a stronger universal hypothesis.
\item \textbf{Density-saturation.} If $\{q \le p : q \forces^* \varphi\}$ is dense below $p$, then $p \forces^*
\varphi$. For the atomic and density clauses, compose the two dense refinements. For conjunction, density
of conditions forcing both conjuncts gives density for each separately, and the induction hypothesis applies.
For negation, a condition forcing the positive formula would have a refinement forcing its negation, a contradiction.
For implication, fix a condition forcing the antecedent; the dense refinements force the consequent, so the
inductive saturation of the consequent applies. For universal quantification, apply inductive saturation
to each name instance.
\end{itemize}

Equality is symmetric directly from its two clauses. It is also reflexive, by induction on the rank of $\sigma$.
Fix $\Pair{\pi}{r}\in\sigma$ and $q\le p$. If $q\perp r$, the required alternative already holds.
Otherwise choose $t\le q,r$. The induction hypothesis gives $t\forces^*\pi=\pi$.
Every strengthening of $t$ is therefore a witness for the membership clause $\pi\in\sigma$,
so $t\forces^*\pi\in\sigma$. This verifies the dense requirement for every pair in $\sigma$ and proves
$p\forces^*\sigma=\sigma$.

A useful consequence of density-saturation is the following refinement rule: if $p$ does not force $\varphi$,
there is $q\le p$ such that no $r\le q$ forces $\varphi$. Otherwise the conditions forcing $\varphi$ would be dense
below $p$, and saturation would make $p$ force $\varphi$.

The primitive definition of negation gives its clause immediately. For conjunction, suppose $p$ forces both
$\varphi$ and $\psi$. No strengthening can force $\varphi\to\neg\psi$, by monotonicity and the implication clause.
Hence $p$ forces $\neg(\varphi\to\neg\psi)$. Conversely, if $p$ forces this negation but fails to force $\varphi$,
the refinement rule gives a strengthening with no further condition forcing $\varphi$;
that strengthening vacuously forces $\varphi\to\neg\psi$, a contradiction.
If instead $p$ fails to force $\psi$, a strengthening forces $\neg\psi$ and thus $\varphi\to\neg\psi$, again a
contradiction. This proves the conjunction clause.

For disjunction, if $p$ forces $\neg\varphi\to\psi$, take $q\le p$.
Either some strengthening of $q$ forces $\varphi$, or $q$ forces $\neg\varphi$ and therefore $\psi$.
Thus the union of the two forcing sets is dense below $p$.
Conversely, assume this density and take $q\le p$ forcing $\neg\varphi$.
Below each strengthening of $q$, the dense union supplies a condition forcing one of the disjuncts.
The first disjunct is impossible, so the conditions forcing $\psi$ are dense below $q$.
Saturation gives $q\forces^*\psi$, proving the implication clause for $\neg\varphi\to\psi$.
Finally, $p$ forces $\neg\forall x\,\neg\varphi(x)$ exactly when every $q\le p$ has a strengthening that forces
$\varphi(\tau)$ for some name $\tau$; this is precisely the existential density clause.

\textbf{Equivalence theorem and truth lemma — simultaneous induction.} We prove jointly, by induction on $\varphi$:

(†) $p \forces^* \varphi(\vec\tau) \;\Longleftrightarrow\; p \forces \varphi(\vec\tau)$,

(‡) For every $M$-generic $G$,
$M[G] \models \varphi(\vec\tau^G) \;\Longleftrightarrow\; \exists p \in G\;(p \forces^* \varphi(\vec\tau)).$

At each step, once (‡) is known, (†) follows in both directions. The forward direction applies (‡) to
every generic containing the condition. For the converse, if the condition does not syntactically force the
formula, density-saturation gives a stronger condition below which no condition forces it. Take a generic
through this stronger condition. If the formula held there, (‡) and directedness would yield a forcing condition
below it, a contradiction. We use this argument whenever (†) is said to follow from (‡).

The atomic cases are handled first by an inner induction on the rank-pair $\prec$.
We make the dense tests used in that induction explicit. For $\sigma,\tau\in M^P$, put
$$W(\sigma,\tau):=
\{q:\exists\Pair{\pi}{r}\in\tau,\;q\le r\text{ and }q\forces^*\sigma=\pi\}.$$
Then $p\forces^*\sigma\in\tau$ means that $W(\sigma,\tau)$ is dense below $p$.
The membership test is
$$W(\sigma,\tau)\;\cup\;
\{q:\forall s\le q,\;s\notin W(\sigma,\tau)\}.$$
It is dense: either a condition has a strengthening in $W(\sigma,\tau)$, or it belongs to the second part.
If $G$ meets this test and contains a condition below which $W(\sigma,\tau)$ is dense,
it cannot meet the second part;
a common strengthening of the two filter conditions would contradict that density. Thus $G$ meets
$W(\sigma,\tau)$ itself.

For equality, define the one-sided defect set and the test
$$\begin{aligned}
F(\sigma,\tau):=\{q:{}&\exists\Pair{\pi}{r}\in\sigma,\;q\le r,\\
&\forall s\le q,\;\neg(s\forces^*\pi\in\tau)\},\\
D(\sigma,\tau):={}&\{q:q\forces^*\sigma=\tau\}
\cup F(\sigma,\tau)\cup F(\tau,\sigma).
\end{aligned}$$
The set $D(\sigma,\tau)$ is dense. If $p$ fails the equality clause, one half has a pair
$\Pair{\pi}{r}$ whose dense requirement fails. There is then $q\le p$ such that no $s\le q$ is incompatible
with $r$ or forces the required membership. In particular $q$ is compatible with $r$.
Choose $t\le q,r$. No strengthening of $t$ forces that membership, so $t$ lies in the corresponding defect set.
These tests belong to $M$ by atomic definability.

\emph{Atomic, $\sigma \in \tau$, direction (‡).} If $p \in G$ has $p \forces^* \sigma \in \tau$, the dense set in the
clause meets $G$ at some $q \in G$, witnessed by $\Pair{\pi}{r} \in \tau$ with $q \le r$ and $q \forces^* \sigma
= \pi$. By the rank-pair induction (‡) applied to $\sigma = \pi$, $\sigma^G = \pi^G$. Since $r \in G$ and $\Pair{
\pi}{r} \in \tau$, the valuation gives $\pi^G \in \tau^G$, hence $\sigma^G \in \tau^G$. Conversely, if $\sigma^G
\in \tau^G$, the valuation of $\tau$ produces $\Pair{\pi}{r} \in \tau$ with $r \in G$ and $\pi^G = \sigma^G$.
Rank-pair induction (‡) applied to $\sigma = \pi$ gives some $q' \in G$ with $q' \forces^* \sigma = \pi$. Take $q \in G$
with $q \le q', r$ (using directedness of $G$). Then $q$ belongs to the witness set in the $\sigma \in \tau$ clause, and
every stronger condition below $q$ also belongs to that set by monotonicity. Hence the witness set is dense below $q$,
so $q \forces^* \sigma \in \tau$. Since $q \in G$, this supplies the forcing condition required by (‡).

\emph{Atomic, $\sigma = \tau$.} Suppose $p\in G$ and $p\forces^*\sigma=\tau$.
Take $\Pair{\pi}{r}\in\sigma$ with $r\in G$, and choose $q\in G$ with $q\le p,r$.
We first show $q\forces^*\pi\in\tau$. Given $s\le q$, the equality clause supplies $t\le s$ that is incompatible
with $r$ or forces $\pi\in\tau$. Since $t\le r$, incompatibility is impossible.
Thus the conditions forcing $\pi\in\tau$ are dense below $q$, and density-saturation gives
$q\forces^*\pi\in\tau$. Rank-pair induction now gives $\pi^G\in\tau^G$.
Every element of $\sigma^G$ has this form, so $\sigma^G\IncludedIn\tau^G$.
Swapping the two names gives the reverse inclusion.

Conversely, suppose $\sigma^G=\tau^G$ and let $G$ meet $D(\sigma,\tau)$.
A condition $q\in G\cap F(\sigma,\tau)$ would give a pair $\Pair{\pi}{r}\in\sigma$ with $q\le r$.
Upward closure puts $r$ in $G$, so $\pi^G\in\sigma^G=\tau^G$.
By the lower-rank truth lemma, some condition in $G$ forces $\pi\in\tau$.
A common strengthening with $q$ contradicts the definition of $F(\sigma,\tau)$.
The symmetric defect set is excluded in the same way. Hence $G$ contains a condition forcing $\sigma=\tau$.
This proves (‡) for equality, and the preceding general argument gives (†).

For atomic formulas, this induction only needs the two displayed tests for each pair of names in $M$.
It uses transitivity of $M$ to keep each child name in $M$, as proved in §{sec:forcing-names-valuation}.
If $M$ is countable, these tests form a countable family of dense sets. The descending-chain construction therefore
produces a filter meeting all of them through any prescribed condition.
Let $\mathcal G$ be the family of such filters. For either atomic formula $\varphi$, the argument also proves
$$p\forces^*\varphi
\quad\Longleftrightarrow\quad
\forall G\in\mathcal G,\;p\in G\Longrightarrow M[G]\models\varphi.$$
For the converse, if the condition does not force the formula, density-saturation supplies
$q\le p$ below which no condition forces $\varphi$.
Choose a test filter through $q$ and apply atomic truth; directedness then contradicts any forcing condition in that
filter. To pass from these explicit tests to the original model-theoretic statement, use their membership in $M$
and the existence of $M$-generic filters through every condition.

\emph{Conjunction.} If the conjunction is true in $M[G]$, induction gives conditions $p,q\in G$
forcing its two conjuncts. Choose $r\in G$ with $r\le p,q$. Monotonicity and the conjunction clause
show that $r$ forces the conjunction. Conversely, a condition forcing the conjunction forces each conjunct,
so induction makes both true in the extension. This proves (‡), and (†) follows by the general argument.

\emph{Negation.} By induction, $\varphi$ is false in $M[G]$ exactly when no condition in $G$ forces it.
Meet the dense decision set
$$D:=\{q:q\forces^*\varphi\}\cup\{q:q\forces^*\neg\varphi\}.$$
If $\varphi$ is false, the first alternative is impossible, so some condition in $G$ forces its negation.
Conversely, suppose $p\in G$ forces $\neg\varphi$. If $\varphi$ were true, induction would supply
$q\in G$ forcing $\varphi$. A common strengthening $r\in G$ of $p,q$ would force $\varphi$ by monotonicity,
contrary to the negation clause at $p$. This proves (‡), and hence (†), for negation.

\emph{Disjunction.} $\varphi \lor \psi \equiv \neg(\neg\varphi \land \neg\psi)$ reduces this to negation and
conjunction. Direct verification from the disjunction clause matches the same outcome.

\emph{Implication.} For the given parameters, let $A$ and $B$ be the forcing sets of $\varphi$ and $\psi$.
The useful dense test is
$$\{q:q\forces^*\varphi\to\psi\}
\;\cup\;\{q\in A:\forall r\le q,\;r\notin B\}.$$
To see density, if $p$ fails to force the implication, some $q\le p$ belongs to $A$ but not to $B$.
Apply the refinement rule to $B$ and use downward closure of $A$; a further strengthening lies in the second part.

If a condition in $G$ forces the implication and the antecedent is true, the induction hypothesis gives a condition
in $G$ forcing the antecedent. A common strengthening forces the consequent, so it is true by induction.
Conversely, suppose the implication is true in $M[G]$ and meet the displayed test.
Its second part would force the antecedent to be true and would prevent any condition in the filter from forcing
the consequent, contradicting induction and directedness. Hence the filter meets the first part.
This proves both directions of (‡) for implication.

\emph{Existential.} If $M[G]\models\exists x\,\varphi(x)$, choose a witness.
By the definition of the extension, it is $\tau^G$ for some $\tau\in M^P$.
Induction supplies $q\in G$ forcing $\varphi(\tau)$. Every strengthening of $q$ is therefore an existential witness
condition, so $q$ forces the existential formula.
Conversely, if $p\in G$ forces the existential formula, its witness conditions are dense below $p$.
Meet their decision test, just as in the membership case, to obtain $q\in G$ and a name $\tau$ with
$q\forces^*\varphi(\tau)$. Induction gives the witness $\tau^G$ in the extension.

\emph{Universal.} Write $C_\tau$ for the conditions forcing $\varphi(\tau)$.
Use the test
$$\{q:\forall\tau\in M^P,\;q\in C_\tau\}
\;\cup\;\bigcup_{\tau\in M^P}\{q:\forall r\le q,\;r\notin C_\tau\}.$$
It is dense: failure of the first part supplies a name for which forcing fails; the refinement rule then supplies
a condition in the corresponding part of the union.

If $p\in G$ forces the universal formula, it forces every name instance.
Every element of $M[G]$ is the valuation of a name in $M$, so induction makes the universal formula true in the
actual domain of the extension. Conversely, suppose every element satisfies the formula and meet the displayed test.
A condition in its second part would rule out every forcing condition for one name instance.
That instance is true by assumption, so induction and directedness give a contradiction.
Hence a condition in $G$ lies in the first part and forces the universal formula.
This proves (‡), including the passage between quantification over names and quantification over elements of $M[G]$.

The decision tests used for negation and existential quantification already follow from the primitive tests.
The implication test for $\varphi\to\bot$ is exactly the decision test for $\varphi$.
For the existential step, put $C_\tau:=\{p:p\forces^*\varphi(\tau)\}$ and apply the universal test to
$\neg\varphi$. Its first alternative says that no strengthening belongs to any $C_\tau$.
Its second supplies a name $\tau$ and a condition forcing $\neg\neg\varphi(\tau)$.
Such a condition forces $\varphi(\tau)$: otherwise the refinement rule would give a strengthening forcing
$\neg\varphi(\tau)$, contradicting double negation. Conversely, monotonicity excludes a negative strengthening
of a condition forcing $\varphi(\tau)$. Thus this universal test is precisely the decision test for
$\bigcup_{\tau\in M^P}C_\tau$, with its two alternatives interchanged.

The entire argument can be run with an explicit countable family of tests.
There are countably many finite formulas and, when $M$ is countable, countably many finite tuples of names in $M$.
Take the atomic tests and the implication and universal tests for every such formula and tuple.
The descending-chain construction meets this whole family through any prescribed condition.
The verified definitions of the other connectives reduce their truth to the primitive induction.
It therefore gives truth for every formula in these extensions, and the same saturation argument
identifies forcing with truth in all such extensions containing the condition.
For $M$-generic filters, each individual test belongs to $M$ by definability for its fixed formula and parameters.
No single internal truth definition for all formula codes is required.

This completes both inductions. (†) is the \termuse{definability} half of the forcing theorem: for each fixed
$\varphi$, the syntactic relation $\forces^*$ is $M$-definable from $P$, and equals the semantic relation
$\forces$. (‡) is the
\termuseas{forcing truth lemma}{truth lemma}: every formula true in $M[G]$ is forced by some condition in $G$, and every
formula forced by a condition in $G$ holds in $M[G]$.
\end{proof}

By construction, $\forces$ is **monotone**: $p \forces \varphi$ and $q \le p$ imply $q \forces \varphi$. The
truth lemma connects conditions to truth in $M[G]$: every true statement in the extension is
already forced by some condition in the generic filter. <!--
formalization: skip-begin (引用・背景説明・読書案内:
条件forcingの単調性はforce_iff_all_modelGenericと既存のforce_lowerへ、
真理補題の文はmodelGeneric_truthへ接続した。残る539行は条件をfinite objectsに限定しないという定義上の範囲の注意で、
無限条件の新しい具体例をここで証明していない。)
--> Conditions need not themselves be finite objects.<!--
formalization: skip-end
-->

### Internal atomic forcing tables {#sec:internal-atomic-forcing}

The rank-pair argument in §{sec:forcing-relation} constructs the atomic relations externally.
We now give their internal definitions, using the internal least-fixed-point construction in
§{sec:internal-model-fixed-points}. We show that the atomic recursion is the unique possible fixed table on each
suitable bound.

\begin{mathmeta}
  \define{ForcingTableEntry}
\end{mathmeta}
For the atomic clauses, let $P,R,W,m,e\in M$, where $R$ codes the forcing order, $W$ is transitive,
and $m\ne e$. The two tags distinguish membership from equality. Put
$$\begin{aligned}
\ForcingTableEntry{b}{p}{\sigma}{\tau}
&:=\Pair{b}{\Pair{p}{\Pair{\sigma}{\tau}}},\\
B&:=\{m,e\}\times(P\times(W\times W)),\\
T_b(p,\sigma,\tau)&\;:\Longleftrightarrow\;
 \ForcingTableEntry{b}{p}{\sigma}{\tau}\in T.
\end{aligned}$$
Pairing and the product construction give $B\in M$ under the closure axioms used above.
Transitivity of $W$ makes it closed under child names: if $\tau\in W$ and
$\Pair{\sigma}{r}\in\tau$, then $\sigma\in W$.
The atomic clauses make sense on arbitrary sets, so we use them throughout $W$ and restrict to names at the end.

All condition variables below range over $P$. For a candidate table $T$, define
$$\begin{aligned}
A_T(p,\sigma,\tau)\;:\Longleftrightarrow\;
&\forall q\le p\;\exists s\le q\;\exists\pi\in W\;\exists r\in P\\
&\bigl(\Pair{\pi}{r}\in\tau\land s\le r\land T_e(s,\sigma,\pi)\bigr),\\
E_T(p,\sigma,\tau)\;:\Longleftrightarrow\;
&\forall\pi\in W\;\forall r\in P\;\bigl(\Pair{\pi}{r}\in\sigma\\
&\longrightarrow\forall q\le p\;\exists s\le q\;
 (s\perp r\lor T_m(s,\pi,\tau))\bigr).
\end{aligned}$$
Define $\Phi(T)\IncludedIn B$ by the two clauses
$$\begin{aligned}
\ForcingTableEntry{m}{p}{\sigma}{\tau}\in\Phi(T)
&\Longleftrightarrow A_T(p,\sigma,\tau),\\
\ForcingTableEntry{e}{p}{\sigma}{\tau}\in\Phi(T)
&\Longleftrightarrow E_T(p,\sigma,\tau)\land E_T(p,\tau,\sigma)
\end{aligned}$$
for $p\in P$ and $\sigma,\tau\in W$.
Every lookup in $T$ occurs positively, while incompatibility is independent of $T$.
Thus enlarging $T$ preserves every witness and every universal requirement, proving monotonicity of $\Phi$.

Here is an explicit first-order definition of the step:
$$\begin{aligned}
\varphi(T,x)\;:\equiv\;&\exists p\in P\;\exists\sigma\in W\;\exists\tau\in W\\
&\bigl[(x=\ForcingTableEntry{m}{p}{\sigma}{\tau}\land A_T(p,\sigma,\tau))\\
&\quad\lor(x=\ForcingTableEntry{e}{p}{\sigma}{\tau}\land E_T(p,\sigma,\tau)\\
&\qquad\land E_T(p,\tau,\sigma))\bigr].
\end{aligned}$$
Expand $q\le p$ as $\Pair{q}{p}\in R$, and expand incompatibility as
$$s\perp r\quad\Longleftrightarrow\quad
 \neg\exists t\in P\,(\Pair{t}{s}\in R\land\Pair{t}{r}\in R).$$
For each record equality introduce the two intermediate pairs
$$u=\Pair{\sigma}{\tau},\qquad
v=\Pair{p}{u},\qquad x=\Pair{b}{v},$$
and use the previously verified formulas for ordered pairs and pair membership.
Pairing puts the intermediate pairs in the model. All remaining quantifiers range over $P$, $W$, or the candidate
table, so transitivity gives exactly the external step predicate. The internal fixed-point theorem therefore
constructs $C\in M$ with $\Phi(C)=C$, defined by the formula $\lambda_B$ above.

\begin{proposition*}[Agreement with the atomic recursion]
For $\sigma,\tau\in W$ and $p\in P$, every fixed table $C\IncludedIn B$ satisfies
$$\begin{aligned}
C_m(p,\sigma,\tau)&\Longleftrightarrow p\forces^*\sigma\in\tau,\\
C_e(p,\sigma,\tau)&\Longleftrightarrow p\forces^*\sigma=\tau.
\end{aligned}$$
Consequently the fixed table is unique, and the actual atomic table on this domain belongs to $M$.
\end{proposition*}

\begin{proof}[Proof]
Induct on the sorted rank-pair from §{sec:forcing-relation}, proving both equivalences together.
At a membership entry the fixed-point equation is $A_C(p,\sigma,\tau)$.
Every contributing child $\pi$ belongs to $W$, and its equality lookup has a strictly smaller rank-pair.
The induction hypothesis converts that lookup into $s\forces^*\sigma=\pi$, yielding exactly the atomic
membership clause in both directions. At an equality entry, apply the same argument to the two halves
$E_C(p,\sigma,\tau)$ and $E_C(p,\tau,\sigma)$; their membership lookups also have smaller rank-pairs.
Transitivity of $W$ ensures that restricting the child quantifiers to $W$ discards no witness.
The resulting equations are precisely the two equality clauses. Since all elements of $B$ are uniquely tagged
records, agreement at all entries gives uniqueness of the whole table.
\end{proof}

Finally remove the auxiliary parameters from the definition. For $b\in\{0,1\}$, put $t_0:=m$ and $t_1:=e$,
and define a fixed formula $\delta_b(P,R,p,\sigma,\tau)$ by
$$\begin{aligned}
\exists m\,\exists e\,\exists W\,\exists B\,\exists x\,\bigl[
&m\ne e\land\mathrm{Trans}(W)\\
&{}\land\sigma\in W\land\tau\in W\\
&{}\land B=\{m,e\}\times(P\times(W\times W))\\
&{}\land x=\ForcingTableEntry{t_b}{p}{\sigma}{\tau}\land\lambda_B(x)\bigr].
\end{aligned}$$
The parameters of $\lambda_B$ are $P,R,W,m,e,B$, all bound or displayed in this formula.
The product equality has an explicit expansion using the tag set and the two intermediate products, followed by
the product-equality formulas already verified. Thus $\delta_b$ is a formula of the pure membership language.

For any witnesses to $\delta_b$, the agreement proposition identifies the asserted entry with the appropriate
atomic forcing clause. Conversely, for $\sigma,\tau\in M$, Pairing gives $\{\sigma,\tau\}\in M$.
The internal transitive-bound construction supplies a transitive $W\in M$ containing this pair as an element,
hence containing both names. Choose $m=\emptyset$ and $e=\{\emptyset\}$; Infinity and Pairing put these distinct
tags in $M$. The record bound and the required record belong to $M$, so agreement supplies all the witnesses.
We have proved
$$\begin{aligned}
M\models\delta_0(P,R,p,\sigma,\tau)&\Longleftrightarrow p\forces^*\sigma\in\tau,\\
M\models\delta_1(P,R,p,\sigma,\tau)&\Longleftrightarrow p\forces^*\sigma=\tau.
\end{aligned}$$
This requires the ground-model axioms used for internal transitive bounds, but no generic filter or Choice axiom.

### Internal names and formula induction {#sec:internal-forcing-formulas}

The atomic definitions in §{sec:internal-atomic-forcing} extend to every fixed formula once the domain of
name quantification is defined internally. Throughout this construction, let $M$ be transitive and satisfy
Infinity, Pairing, Union, Power Set, Separation, and Replacement. Let $P,R\in M$, with $R$ coding the forcing order.
No generic filter is needed for the construction.

Choose a transitive $W\in M$. For each candidate $T$, define the positive step
$$\begin{aligned}
\psi(P,W,T,\tau)\;:\equiv\;&\forall z\in\tau\;\exists\sigma\in W\;\exists p\in P\\
&\bigl(z=\Pair{\sigma}{p}\land\sigma\in T\bigr),\\
\Psi(T)&:=\{\tau\in W:\psi(P,W,T,\tau)\}.
\end{aligned}$$
After expanding ordered-pair equality, $\psi$ is a bounded first-order formula with the displayed parameters.
Bounded absoluteness from §{sec:zfc-absoluteness} therefore identifies its internal interpretation with the
external condition. The only occurrence of $T$ is positive, so $\Psi$ is monotone.
The internal least-fixed-point construction gives
$$C\in M,\qquad C\IncludedIn W,\qquad \Psi(C)=C.$$
Its defining formula is
$$\begin{aligned}
\chi_{P,W}(T)&\;:\equiv\;\forall\rho\in W\,
 (\psi(P,W,T,\rho)\longrightarrow\rho\in T),\\
\lambda_{P,W}(\tau)&\;:\equiv\;\tau\in W\land
 \forall T\,(\chi_{P,W}(T)\longrightarrow\tau\in T).
\end{aligned}$$

We prove by induction on $\mathrm{rank}(\tau)$, for $\tau\in W$, that
$$\tau\in C\quad\Longleftrightarrow\quad\tau\in M^P.$$
The fixed-point equation says that every element of $\tau$ must be a pair $\Pair{\sigma}{p}$ with
$p\in P$ and $\sigma\in C$. Every such child has smaller rank.
By induction, membership of the child in $C$ is equivalent to its being a name, giving the forward implication.
Conversely, if $\tau$ is a name, every element has this pair form with a child name.
Transitivity of $W$ puts each child in $W$, so induction puts it in $C$ and the fixed-point equation gives
$\tau\in C$. The empty name satisfies the condition vacuously; a set containing an element that is not a
suitable pair fails it.

Thus $C=\{\tau\in W:\tau\in M^P\}$. If $V\in M$ is another transitive bound, the two fixed sets
agree on $W\cap V$, since both recognize precisely the names there. The choice of a transitive bound
therefore does not affect the name predicate.

Now define the formula with just $P$ and $\tau$ free by
$$\eta(P,\tau)\;:\equiv\;\exists W\,
 (\mathrm{Trans}(W)\land\tau\in W\land\lambda_{P,W}(\tau)).$$
For $P,\tau\in M$, any witnesses give a name by the rank induction.
Conversely, the internal transitive-bound construction supplies a suitable $W\in M$ containing $\tau$,
so every name satisfies this formula. Hence
$$M\models\eta(P,\tau)\quad\Longleftrightarrow\quad\tau\in M^P.$$
In particular, quantifying internally over this predicate ranges over exactly the actual names in the model.

\begin{theorem*}[Defining formulas for syntactic forcing]
For each fixed formula $\varphi(\vec x)$ there is a first-order formula
$\rho_\varphi(P,R,p,\vec\tau)$ such that, for $p\in P$ and any finite tuple of names $\vec\tau\in(M^P)^n$,
$$M\models\rho_\varphi(P,R,p,\vec\tau)
\quad\Longleftrightarrow\quad p\forces^*\varphi(\vec\tau).$$
The defining formula has no other free parameters.
\end{theorem*}

\begin{proof}[Proof]
Use falsity, atomic formulas, implication, and universal quantification as primitives.
Define the translation recursively, renaming bound variables to avoid capture:
$$\begin{aligned}
\rho_\bot(P,R,p,\vec\tau)&\;:\equiv\;\bot,\\
\rho_{x_i\in x_j}(P,R,p,\vec\tau)
 &\;:\equiv\;\delta_0(P,R,p,\tau_i,\tau_j),\\
\rho_{x_i=x_j}(P,R,p,\vec\tau)
 &\;:\equiv\;\delta_1(P,R,p,\tau_i,\tau_j),\\
\rho_{\varphi\to\theta}(P,R,p,\vec\tau)
 &\;:\equiv\;\forall q\in P\;\bigl(\Pair{q}{p}\in R\\
 &\qquad\longrightarrow(\rho_\varphi(P,R,q,\vec\tau)\\
 &\qquad\qquad\longrightarrow\rho_\theta(P,R,q,\vec\tau))\bigr),\\
\rho_{\forall x\,\varphi}(P,R,p,\vec\tau)
 &\;:\equiv\;\forall\sigma\;\bigl(\eta(P,\sigma)\\
 &\qquad\longrightarrow\rho_\varphi(P,R,p,\vec\tau,\sigma)\bigr).
\end{aligned}$$
The atomic formulas $\delta_0,\delta_1$ are those constructed in §{sec:internal-atomic-forcing}.
Ordered-pair membership is expanded by its first-order definition, so every displayed clause is in the
pure membership language and retains the parameters $P,R,p,\vec\tau$.

Induct on the input formula. Falsity is immediate, and the atomic cases are the previously proved equivalences.
For implication, transitivity ensures that the internal variables $q\in P$ run over all actual conditions;
the test $\Pair{q}{p}\in R$ is precisely $q\le p$.
The induction hypotheses therefore turn this clause into the defining implication clause of $\forces^*$.
For universal quantification, the equivalence for $\eta$ identifies the domain with $M^P$.
Apply the induction hypothesis to each extended tuple $\vec\tau,\sigma$ to obtain exactly the universal forcing
clause. These steps prove the displayed equivalence in both directions.
\end{proof}

\begin{corollary*}[The forcing set belongs to the ground model]
For each fixed formula and finite tuple of names as above,
$$\{p\in P:p\forces^*\varphi(\vec\tau)\}\in M.$$
\end{corollary*}

\begin{proof}[Proof]
Apply Separation in $M$ to $P$ using the formula $\rho_\varphi$ with parameters $P,R,\vec\tau$.
Every element of $P$ lies in $M$, and the theorem identifies the separating predicate on each such element.
Thus the internal separating set is exactly the displayed external set.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
fixed formulaごとのforcingTranslationと、構文的forcingからsemantic
forcingへの適用条件の違いを説明する注意。任意のformula code用の単一の内部truth
predicateをここでは主張していないという範囲の宣言であり、Tarskiの非定義可能性を証明したとみなす判定ではない。内部test
setsと真理補題の実際の構成は後続の定理で対象に残す。)
--> The construction associates a defining formula to each fixed input formula; it does not assert a single
internal truth predicate for arbitrary formula codes. Agreement with semantic forcing additionally uses the
truth argument in §{sec:forcing-relation}, including that the required dense test sets belong to the ground model.<!--
formalization: skip-end
-->

### From internal tests to generic truth {#sec:internal-generic-truth}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次の節で四つのdense testを共通の定義可能性からM内に置くこと、P,Rをパラメータとして保つことを案内する段落。
membershipTest_mem・equalityTest_mem・implicationTest_mem・universalTest_memから
modelGeneric_meets_testsへ至る個別の構成と証明は別単位として対象に残す。)
--> Retain the assumptions on $M,P,R$ from §{sec:internal-forcing-formulas}.
We now put every dense test used in §{sec:forcing-relation} into $M$ by one common definability argument.
This connects the truth proof there to the definition of an $M$-generic filter. All the formulas below retain
$P,R$ as parameters, even when these are suppressed in notation.<!--
formalization: skip-end
-->

\begin{proposition*}[Internal dense truth tests]
The membership and equality tests $W(\sigma,\tau)\cup W(\sigma,\tau)^-$ and $D(\sigma,\tau)$ from
§{sec:forcing-relation} belong to $M$. So do the implication and universal tests there, for each fixed formula
and finite tuple of names. Here $A^-:=\{q\in P:\forall s\le q,\;s\notin A\}$.
\end{proposition*}

\begin{proof}[Proof]
Use the defining-formula theorem of §{sec:internal-forcing-formulas}. In each test, replace a syntactic
forcing assertion by its defining formula $\rho_\varphi(P,R,q,\vec\tau)$; in atomic assertions use
$\delta_0$ or $\delta_1$. Expand order and pair membership by their verified first-order definitions.
Condition quantifiers range over $P$, and quantification over names uses the internal predicate $\eta$.
Transitivity and the defining-formula theorem identify these parts with the actual forcing clauses.

The only additional witnesses in the atomic tests are pairs $\Pair{\pi}{r}$ belonging to a given name.
The child-coordinate lemma in §{sec:forcing-names-valuation} puts $\pi$ in $M$, and transitivity puts $r\in P$
in $M$. Hence their internal existential quantifiers lose no external witness. Negating the existence of a
stronger condition is also exact, since the condition set and its order code are internal.
For the universal test, its second alternative is expressed by
$$\exists\sigma\,\bigl(\eta(P,\sigma)\land\rho_{\neg\varphi}(P,R,q,\vec\tau,\sigma)\bigr).$$
Thus it quantifies over exactly the names in $M$; it does not require their collection as an internal set.
All four test predicates are consequently first-order definitions with parameters in $M$. Separation on $P$
puts their actual sets in $M$. Their density was proved in §{sec:forcing-relation}.
\end{proof}

\begin{theorem*}[Truth for every generic filter]
Under the preceding model assumptions, let $G$ be any $M$-generic filter.
For every formula $\varphi$ and finite tuple of ground-model names $\vec\tau$,
$$M[G]\models\varphi(\vec\tau^G)
\quad\Longleftrightarrow\quad
\exists p\in G\;(p\forces^*\varphi(\vec\tau)).$$
External countability of the model is not needed for this implication from genericity.
\end{theorem*}

\begin{proof}[Proof]
Each of the four test sets is an actual dense subset of the condition set, as proved in §{sec:forcing-relation},
and the preceding constructions put it in the model. Genericity therefore makes the filter meet all of them.
The simultaneous rank induction proves atomic truth, and the induction on formulas proves implication and
universal quantification using the other two tests. The valuation map from names onto the extension identifies
quantification over names with quantification over its actual elements. These are exactly the hypotheses of the
truth proof in §{sec:forcing-relation}, so it applies to this arbitrary generic filter.
\end{proof}

If $M$ is externally countable, its actual dense subsets of $P$ form a countable family, because each is an element
of $M$. Apply the descending-chain construction from §{sec:ground-models-forcing-notions} to this entire family,
starting below any prescribed condition. The resulting filter is $M$-generic and contains that condition.
This existence argument uses all ground-model dense sets, including ones unrelated to the displayed truth tests.

\begin{corollary*}[Agreement with semantic forcing]
If the model is also externally countable, then for every condition and fixed formula with ground-model names,
$$p\forces^*\varphi(\vec\tau)\quad\Longleftrightarrow\quad p\forces\varphi(\vec\tau).$$
\end{corollary*}

\begin{proof}[Proof]
Apply the saturation argument from the simultaneous induction in §{sec:forcing-relation}, now using the truth
theorem for every $M$-generic filter. The preceding countability argument supplies a generic filter through
any stronger condition needed in that argument. This gives both implications without another induction.
\end{proof}

The construction in §{sec:internal-forcing-formulas} therefore gives, for each fixed formula,
a formula $\rho_\varphi(P,R,p,\vec\tau)$ that defines semantic forcing inside the model.
The proof separates internal definability, truth for an existing generic filter, and the countability assumption
that guarantees enough generic filters to characterize semantic forcing.

## The Generic Extension and the ZF Axioms {#sec:generic-extension}

### Basic Properties and Elementary Axioms {#sec:generic-extension-basic-properties}

\begin{mathmeta}
  \vars{n,t}{Nat}
\end{mathmeta}

If $M \models \mathrm{ZFC}$ and $G$ is $M$-generic for $P \in M$, then $M[G]$ is again a transitive model of ZFC,
contains $M$, and has $G$ as an element. More precisely:

*   $M \IncludedIn M[G]$ via $x=\check{x}^G$.
*   $G=\dot G^G \in M[G]$.
*   $M[G]$ is generated from $M\cup\{G\}$ by valuing the $P$-names in $M$; equivalently, any transitive ZFC model
    containing $M\cup\{G\}$ and closed under this name valuation contains $M[G]$.
*   $M$ and $M[G]$ have the same ordinals.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
順序数を追加しないという正の主張はfullZFC_extension_propertiesとordinal_mem_extension_iff_of_
axiomsへ接続した。残りは主章のCohen
forcingなどを背景に新しい実数や集合が加わりうることと基数算術との違いを説明する例示・読書上の位置付けで、
この段落で別のforcingや基数崩壊の反例を構成しない。すべてのforcingが新しい集合を加えるという主張としても扱わない。)
--> The last point is crucial. Forcing adds new sets, and in particular can add new reals, but<!--
formalization: skip-end
-->  it does not add new ordinals.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
順序数を追加しないという正の主張はfullZFC_extension_propertiesとordinal_mem_extension_iff_of_
axiomsへ接続した。残りは主章のCohen
forcingなどを背景に新しい実数や集合が加わりうることと基数算術との違いを説明する例示・読書上の位置付けで、
この段落で別のforcingや基数崩壊の反例を構成しない。すべてのforcingが新しい集合を加えるという主張としても扱わない。)
-->
Thus ordinals serve as the stable indexing spine across forcing extensions, while cardinal arithmetic may change because
new bijections can appear.<!--
formalization: skip-end
-->

\begin{lemma*}[Extensionality and Foundation in a transitive domain]
Every transitive set or class, interpreted with actual membership, satisfies Extensionality and Foundation.
In particular, these two axioms hold in $M[G]$ whenever $M$ is transitive, without any genericity assumption on $G$.
\end{lemma*}

\begin{proof}[Proof]
Let $N$ be transitive. If $x,y\in N$ have the same members in $N$, all their actual members lie in $N$,
so they have the same members externally. External Extensionality gives $x=y$.
For Foundation, let $x\in N$ have a member in $N$. It is externally nonempty, so external Foundation gives
$y\in x$ with $x\cap y=\emptyset$. Transitivity gives $y\in N$.
There is no $z\in N$ belonging to both $x$ and $y$, so this $y$ also witnesses the internal Foundation axiom.
The transitivity of $M[G]$ proved in §{sec:forcing-names-valuation} now gives the last assertion.
\end{proof}

\begin{proposition*}[Pairing in the extension]
Let $M$ be transitive and satisfy Pairing, Union, Power Set, and the bounded Separation instance for products
in §{sec:internal-model-closure}. Let $P\in M$ and $\varnothing\ne G\IncludedIn P$.
Then $M[G]$ satisfies Pairing.
Genericity is not needed for this assertion.
\end{proposition*}

\begin{proof}[Proof]
For $x,y\in M[G]$, choose names $\sigma,\tau\in M^P$ with $x=\sigma^G$ and $y=\tau^G$.
Put
$$\rho:=\{\sigma,\tau\}\times P.$$
Pairing and the product construction in $M$ give $\rho\in M$.
Every element of $\rho$ is an ordered pair whose first coordinate is one of the names $\sigma,\tau$ and whose
second coordinate belongs to $P$. Hence $\rho$ is a $P$-name.

The valuation equation gives
$$\begin{aligned}
\rho^G&=\{\pi^G:\pi\in\{\sigma,\tau\},\;\exists p\in G\,(p\in P)\}\\
&=\{\sigma^G,\tau^G\}=\{x,y\}.
\end{aligned}$$
The middle equality uses the nonemptiness of $G$ and $G\IncludedIn P$.
Thus the pair $\{x,y\}$ is the valuation of a name in $M$, so it belongs to $M[G]$.
Since the extension uses actual membership, this set witnesses its internal Pairing axiom.
\end{proof}

\begin{proposition*}[Union in the extension]
Let $M$ be transitive and satisfy Pairing, Union, Power Set, and the bounded Separation instances
for products and for the union-name predicate displayed below. Suppose $M$ contains $P$ and the relation
$$R=\{\Pair{q}{p}\in P\times P:q\le p\}$$
coding the refinement order. If $G$ is a filter on $P$, then $M[G]$ satisfies Union.
Genericity is not needed here either.
\end{proposition*}

\begin{proof}[Proof]
Fix a name $\tau\in M^P$ and form
$$A=\bigcup\bigcup\tau,\qquad D=\bigcup\bigcup\bigcup A.$$
Both sets belong to $M$ by repeated applications of its Union axiom.
Whenever $\Pair{\pi}{p}\in\tau$, we have $\pi\in A$.
If also $\Pair{\sigma}{r}\in\pi$, then
$$\sigma\in\{\sigma\}\in\Pair{\sigma}{r}\in\pi\in A,$$
so $\sigma\in D$. These bounds depend only on $\tau$, not on the filter.

Let $\rho$ be the subset of $D\times P$ consisting of the pairs $\Pair{\sigma}{q}$ for which
$$\begin{aligned}
\exists\pi\in A\,\exists p\in P\,\exists r\in P\,\bigl(
&\Pair{\pi}{p}\in\tau\land\Pair{\sigma}{r}\in\pi\\
&{}\land\Pair{q}{p}\in R\land\Pair{q}{r}\in R\bigr).
\end{aligned}$$
Thus $q$ simultaneously strengthens the two labels $p,r$.
Every quantifier is bounded by a set in $M$, and ordered-pair membership has the bounded expansion from
§{sec:zfc-absoluteness}. The product construction and bounded Separation give $\rho\in M$.
For a pair in $\rho$, the first coordinate is a name because $\tau$ is a name and the two displayed membership
relations lead to its successive first-coordinate names. The second coordinate belongs to $P$, so $\rho$ is a
$P$-name. Its definition does not require a separate test for being a name.

We verify that $\rho^G=\bigcup\tau^G$ in both directions.
If $x\in\rho^G$, take $\Pair{\sigma}{q}\in\rho$ with $q\in G$ and $x=\sigma^G$,
and choose $\pi,p,r$ from the defining predicate. Since $q\le p,r$, upward closure puts $p,r$ in $G$.
Consequently
$$x=\sigma^G\in\pi^G\in\tau^G,$$
so $x\in\bigcup\tau^G$.

Conversely, if $x\in\bigcup\tau^G$, the valuation equation applied twice gives
$\Pair{\pi}{p}\in\tau$ and $\Pair{\sigma}{r}\in\pi$ with $p,r\in G$ and $x=\sigma^G$.
Choose a common strengthening $q\in G$ with $q\le p,r$, using downward directedness.
The previously verified bounds give $\pi\in A$ and $\sigma\in D$, so $\Pair{\sigma}{q}\in\rho$.
It follows that $x\in\rho^G$.

Every set in $M[G]$ is some $\tau^G$, and the constructed name $\rho$ belongs to $M$.
Hence $\bigcup\tau^G=\rho^G\in M[G]$. Transitivity ensures that every member used in the union's defining
condition belongs to the extension, so this actual union witnesses the internal Union axiom.
The argument uses only the ground-model axioms needed for iterated unions, products, and the indicated bounded
Separation instances.
\end{proof}

\begin{lemma*}[Rank bound for name valuations]
For any $P$-name $\tau$ and any $G\IncludedIn P$,
$$\mathrm{rank}(\tau^G)\le\mathrm{rank}(\tau).$$
No filter or genericity assumption is needed.
\end{lemma*}

\begin{proof}[Proof]
Induct on $\mathrm{rank}(\tau)$. If $x\in\tau^G$, choose $\Pair{\sigma}{p}\in\tau$ with $p\in G$
and $x=\sigma^G$. The induction hypothesis and the rank decrease for first coordinates give
$$\begin{aligned}
\mathrm{rank}(x)&=\mathrm{rank}(\sigma^G)\\
&\le\mathrm{rank}(\sigma)<\mathrm{rank}(\tau).
\end{aligned}$$
A set has rank at most an ordinal $\beta$ exactly when each of its elements has rank less than $\beta$.
Apply this characterization to $\tau^G$ and $\beta=\mathrm{rank}(\tau)$.
\end{proof}

\begin{corollary*}[Internal bounds for sets and forcing tables]
Under the same axioms, each $x\in M$ satisfies
$$\begin{aligned}
\alpha&:=\mathrm{rank}(x)\in M,\\
x&\IncludedIn\InternalHierarchy{M}{\alpha}\in M.
\end{aligned}$$
Every $\InternalHierarchy{M}{\alpha}$ is transitive. If $\tau\in\InternalHierarchy{M}{\alpha}$ and
$\Pair{\sigma}{p}\in\tau$, then $\sigma\in\InternalHierarchy{M}{\alpha}$.
For $P\in M$ and an ordinal $\alpha\in M$, the sets
$$\begin{aligned}
B&:=P\times(\InternalHierarchy{M}{\alpha}\times\InternalHierarchy{M}{\alpha}),\\
\InternalPowerSet{M}{B}&=\PowerSet{B}\cap M
\end{aligned}$$
both belong to $M$.
\end{corollary*}

\begin{proof}[Proof]
The rank-ordinal lemma gives $\mathrm{rank}(x)\in M$. Every $z\in x$ belongs to $M$ and has rank less
than $\mathrm{rank}(x)$, proving the inclusion. If $z\in y\in\InternalHierarchy{M}{\alpha}$,
then $z\in M$ and $\mathrm{rank}(z)<\mathrm{rank}(y)<\alpha$, proving transitivity.
For a child name, the earlier pair-coordinate lemmas give $\sigma\in M$ and
$\mathrm{rank}(\sigma)<\mathrm{rank}(\tau)<\alpha$.
Finally, apply internal product closure twice to obtain $B\in M$, then apply Power Set internally.
\end{proof}

These sets bound tables of conditions and pairs of names from one internal stage, including all recursive
calls to child names. The internal power set collects only those subsets of $B$ that belong to $M$.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
条件・名前対のtable bounds、内部Power Set、child
namesの同じstageへの所属はinternal_forcing_table_boundsとchild_mem_internal_rank_seg
mentへ接続した。残る971–973行はboundの内部所属だけで外部tableの内部所属を結論しないという適用上の注意であり、
新たな非内部tableの反例を構成する箇所ではない。内部tableを実際に作る証明は別の定理として対象に残す。)
--> To obtain a particular forcing table in $M$, one must still give its internal defining formula and construction;
the existence of the bound alone does not establish membership of an externally specified table.<!--
formalization: skip-end
-->

<!-- lean-correspondence
{
  "scope": "ordinal-preservation",
  "lean": {
    "statement": "PolishSpaceBook.SetTheoryModels.ordinal_mem_extension_iff_of_axioms",
    "bound": "PolishSpaceBook.ForcingNames.ordinal_valuation_mem_ground"
  },
  "bindings": {
    "ground": ["M", "statement.M"],
    "conditions": ["P", "statement.P"],
    "collection": ["G", "statement.G"],
    "ordinal": ["\\alpha", "statement.α"],
    "name": ["\\tau", "bound.τ"],
    "rank-bound": ["\\beta", "bound.β"]
  }
}
-->
\begin{proposition*}[Ordinal preservation]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
Suppose $P\in M$ and $\varnothing\ne G\IncludedIn P$. Then
$$\mathrm{Ord}^{M[G]}=\mathrm{Ord}^M.$$
No genericity assumption is needed for this conclusion.
\end{proposition*}

\begin{proof}[Proof]
Write an ordinal $\alpha\in M[G]$ as $\alpha=\tau^G$ with $\tau\in M^P$.
Since an ordinal is its own rank, the valuation bound gives
$$\alpha\le\mathrm{rank}(\tau).$$
The rank-closure lemma supplies $\beta:=\mathrm{rank}(\tau)\in M$.
Either $\alpha=\beta$ or $\alpha\in\beta$, so $\alpha\in M$ by transitivity.
In the other direction, the check-name lemma and $\check{\alpha}^G=\alpha$ put every ground-model ordinal in $M[G]$.
The bounded ordinal predicate in §{sec:zfc-absoluteness} identifies the ordinals of each transitive domain
with its actual ordinal elements, so these two inclusions give the displayed equality.
\end{proof}
<!-- lean-correspondence-end: ordinal-preservation -->

The proof separates the external rank estimate from the internal closure constructions.
The latter have now been derived from the stated axioms. For a weaker ground theory, it is enough to supply
rank and check-name closure separately and then use the same ordinal comparison.

\begin{corollary*}[Infinity in the extension]
Under the hypotheses of the proposition, $M[G]$ satisfies the Infinity axiom.
\end{corollary*}

\begin{proof}[Proof]
The earlier natural-number construction gives the actual $\omega\in M$, and check-name closure gives
$M\IncludedIn M[G]$. Hence $\omega\in M[G]$. The extension is transitive, so it contains
$\emptyset\in\omega$ and, for each $n\in\omega$, the actual successor $n\cup\{n\}\in\omega$.
These sets satisfy the internal empty-set and successor clauses: their members already lie in the extension.
Thus the actual natural-number set witnesses the first-order Infinity sentence in the extension.
\end{proof}

The preceding arguments establish Extensionality, Foundation, Pairing, Union, and Infinity using transitivity,
concrete name valuations, and the internal closure constructions.
The construction in §{sec:generic-separation} proves the full Separation schema using the truth theorem.
The bounded supply of subset names in §{sec:generic-power-set} then proves Power Set.
The Collection argument in §{sec:generic-replacement} bounds output names and proves the full Replacement schema.
Finally, §{sec:generic-choice} combines the ground-set covers with internal ordinal enumerations and collects
least-preimage choice graphs inside the extension. This proves preservation of Choice without well-ordering
the proper class of all names.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のdense forcingのworking principleを導入し、Polish空間の応用での役割を説明する案内。working
principleそのものはmodelGeneric_truth_of_dense_semantic_forcingへ接続し、
この導入だけを対象外とする。)
--> For Polish-space applications, the most important consequence is not the full model-theoretic construction but the
following working principle:<!--
formalization: skip-end
-->

*To show that every generic extension satisfies a statement about a named Polish-space object, it suffices to show that
every condition has a stronger condition forcing that statement.*

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前の、各条件の下にforcing条件を得ればgeneric拡大で真になるという補題をdense-set argumentと呼ぶ一行の説明。
新しい局所主張ではない。)
--> This is the forcing form of a dense-set argument.<!--
formalization: skip-end
-->

### Separation in the generic extension {#sec:generic-separation}

The defining formulas and the truth theorem now let us build names for definable subsets.
The construction is uniform in the finite tuple of name parameters and does not depend on the generic filter.

\begin{theorem*}[\termdefine{Separation in generic extensions}]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
Let $P,R\in M$ code the forcing conditions and their order, and let $G$ be $M$-generic.
Then $M[G]$ satisfies every instance of the Separation schema, with arbitrary parameters from $M[G]$.
Neither external countability of the model nor its Choice axiom is required for this conclusion.
\end{theorem*}

\begin{proof}[Proof]
Fix a formula $\varphi(\vec a,z)$, a set $x\in M[G]$, and a finite tuple $\vec a$ of parameters from $M[G]$.
Choose names $\tau,\vec\nu\in M^P$ with $x=\tau^G$ and $\vec a=\vec\nu^G$.
Put $A:=\bigcup\bigcup\tau$, so every first-coordinate name occurring in $\tau$ belongs to $A$.
Union and the internal product construction give $A\times P\in M$.
Define a subset of this product by
$$\begin{aligned}
\theta:=\{\Pair{\sigma}{q}\in A\times P:{}&\exists r\in P\,
 (\Pair{\sigma}{r}\in\tau\land q\le r\\
 &{}\land q\forces^*\varphi(\vec\nu,\sigma))\}.
\end{aligned}$$
The stronger label is essential: it must preserve the old membership witness and force the selecting formula.

To put this specified name in the model, use the actual defining formula from §{sec:internal-forcing-formulas}:
$$\begin{aligned}
&\chi(z)\;:\equiv\;\exists\sigma\in A\;\exists q\in P\;\exists r\in P\,
 \bigl[z=\Pair{\sigma}{q}\\
&\qquad{}\land\Pair{\sigma}{r}\in\tau\land\Pair{q}{r}\in R\\
&\qquad{}\land\rho_\varphi(P,R,q,\vec\nu,\sigma)\bigr].
\end{aligned}$$
Its parameters are the finite tuple $\vec\nu$ and the sets $\tau,P,R,A$, all in $M$.
Whenever the pair-membership conjunct holds, the child-coordinate lemma puts $\sigma$ in the model and the name
property of $\tau$ makes it a name. Thus the defining-formula theorem applies to the entire extended tuple.
Transitivity identifies the bounded witnesses with the actual elements of their bounds, and the ordered-pair
formulas have their actual meanings. Consequently the internal interpretation of $\chi$ is exactly the predicate
used to define $\theta$. Separation in $M$ gives $\theta\in M$.
The defining formula need not be bounded, so this step uses the full Separation schema.
Every pair in $\theta$ has a child name as its first coordinate and a condition in $P$ as its second, so
$\theta$ is a name. This step uses the ground model's Separation, with no assumption that the extension already
satisfies it.

We verify the valuation identity
$$\theta^G=\{z\in\tau^G:M[G]\models\varphi(\vec\nu^G,z)\}.$$
Suppose $z\in\theta^G$. Choose $\Pair{\sigma}{q}\in\theta$ with $q\in G$ and $z=\sigma^G$, and take
$r$ from the defining predicate. Since $q\le r$, upward closure puts $r$ in $G$, so $z\in\tau^G$.
Also $q\forces^*\varphi(\vec\nu,\sigma)$. The truth theorem in §{sec:internal-generic-truth} gives
$M[G]\models\varphi(\vec\nu^G,z)$.

Conversely, let $z\in\tau^G$ satisfy $M[G]\models\varphi(\vec\nu^G,z)$.
The valuation equation supplies $\Pair{\sigma}{r}\in\tau$ with $r\in G$ and $z=\sigma^G$.
The child name belongs to the ground model. The truth theorem supplies $p\in G$ with
$p\forces^*\varphi(\vec\nu,\sigma)$.
Choose a common strengthening $q\in G$ with $q\le p,r$.
Monotonicity gives $q\forces^*\varphi(\vec\nu,\sigma)$, and the child bound gives $\sigma\in A$.
Thus $\Pair{\sigma}{q}\in\theta$, so $z\in\theta^G$. This proves the reverse inclusion.

Finally, $\theta\in M^P$ puts $y:=\theta^G$ in $M[G]$.
For every $z\in M[G]$, the valuation identity gives
$$z\in y\quad\Longleftrightarrow\quad z\in x\ \land\ M[G]\models\varphi(\vec a,z).$$
This is precisely the internal Separation instance for the original formula and parameters.
Every finite tuple of extension parameters has a tuple of ground-model names by the definition of the extension,
so the argument proves the whole schema.
\end{proof}

### Power Set in the generic extension {#sec:generic-power-set}

The bound in the Separation construction does not depend on the selecting formula or its parameters.
This gives a set of names large enough to represent every subset of a fixed extension set.
The name predicate from §{sec:internal-forcing-formulas} lets us form this supply inside the ground model.

\begin{theorem*}[\termdefine{Power Set in generic extensions}]
Under the hypotheses of §{sec:generic-separation}, the generic extension $M[G]$ satisfies Power Set.
More precisely, for every $x\in M[G]$,
$$\InternalPowerSet{M[G]}{x}=\{y\in M[G]:y\IncludedIn x\}\in M[G].$$
No Choice axiom in the ground model or external countability assumption is needed.
\end{theorem*}

\begin{proof}[Proof]
Write $x=\tau^G$ with $\tau\in M^P$, and put
$$A:=\bigcup\bigcup\tau,\qquad B:=A\times P.$$
Both sets belong to $M$. We first show that every $y\in M[G]$ with $y\IncludedIn x$ has a name
$\theta\in M^P$ satisfying $\theta\IncludedIn B$.
Choose $\nu\in M^P$ with $\nu^G=y$, and apply the construction in §{sec:generic-separation} to
$\varphi(a,z)\equiv z\in a$, with parameter name $\nu$. It gives
$$\begin{aligned}
\theta:=\{\Pair{\sigma}{q}\in B:{}&\exists r\in P\,
 (\Pair{\sigma}{r}\in\tau\land q\le r\\
 &{}\land q\forces^*\sigma\in\nu)\}\in M^P.
\end{aligned}$$
The valuation identity proved there yields
$$\theta^G=\{z\in\tau^G:z\in\nu^G\}=x\cap y=y.$$
Thus every required subset has a name contained in the same set $B$, even when its initially chosen name $\nu$
is not contained in $B$.

Now form the internal power set $\InternalPowerSet{M}{B}\in M$ and separate its name members:
$$C:=\{\theta\in\InternalPowerSet{M}{B}:M\models\eta(P,\theta)\}.$$
The defining-formula theorem identifies this predicate with being an actual $P$-name.
Separation in $M$ therefore gives $C\in M$, with
$$\theta\in C\quad\Longleftrightarrow\quad
 \theta\in M^P\ \land\ \theta\IncludedIn B.$$
Define
$$\Pi:=C\times P\in M.$$
Each first coordinate is a name and each second coordinate is a condition, so $\Pi\in M^P$.
For the nonempty filter $G$, its value is exactly
$$\Pi^G=\{\theta^G:\theta\in C\}.$$
Indeed, every member of the value has such a first coordinate; conversely, for any $\theta\in C$, choose
$p\in G$ and use $\Pair{\theta}{p}\in\Pi$.
In particular, every $y\in M[G]$ with $y\IncludedIn x$ belongs to $\Pi^G$.

The set $\Pi^G$ may also contain sets not included in $x$.
Apply the already proved Separation schema in $M[G]$ to $\Pi^G$, with parameter $x$ and formula
$$\psi(x,y)\;:\equiv\;\forall z\in y\,(z\in x).$$
Transitivity of the extension makes this formula equivalent to actual inclusion.
We obtain
$$p:=\{y\in\Pi^G:y\IncludedIn x\}\in M[G].$$
For $y\in M[G]$, the preceding bound gives
$$y\in p\quad\Longleftrightarrow\quad y\IncludedIn x.$$
Thus $p=\InternalPowerSet{M[G]}{x}$, proving the internal Power Set axiom.
The construction collects exactly the subsets that belong to the extension; it does not claim that every ambient
subset of $x$ belongs to $M[G]$.
\end{proof}

### Replacement in the generic extension {#sec:generic-replacement}

\begin{theorem*}[\termdefine{Replacement in generic extensions}]
Under the hypotheses of §{sec:generic-separation}, the generic extension $M[G]$ satisfies every instance of Replacement,
with arbitrary finite tuples of parameters from $M[G]$.
Neither Choice in the ground model nor external countability is required.
\end{theorem*}

\begin{proof}[Proof]
Fix $x\in M[G]$, a finite tuple $\vec p$ of parameters from $M[G]$, and a formula
$\varphi(\vec p,a,b)$ satisfying
$$M[G]\models\forall a\in x\,\exists!b\,\varphi(\vec p,a,b).$$
Choose names $\tau,\vec\xi\in M^P$ with $x=\tau^G$ and $\vec p=\vec\xi^G$.
Put
$$A:=\bigcup\bigcup\tau,\qquad D:=A\times P\in M.$$
For the internal Collection argument, define a relation on a coded input $d$ and an output name $\nu$:
$$\begin{aligned}
\Psi(d,\nu)\;:\equiv\;&\eta(P,\nu)\land\exists\sigma\,\exists q\in P\\
 &\bigl[d=\Pair{\sigma}{q}\land\eta(P,\sigma)\\
 &{}\land\rho_\varphi(P,R,q,\vec\xi,\sigma,\nu)\bigr].
\end{aligned}$$
Here $\eta$ and $\rho_\varphi$ are the actual first-order defining formulas from
§{sec:internal-forcing-formulas}; the parameters are $P,R,\vec\xi$.
For $\sigma,\nu\in M^P$ and $q\in P$, their interpretation is exactly
$$M\models\Psi(\Pair{\sigma}{q},\nu)
 \quad\Longleftrightarrow\quad q\forces^*\varphi(\vec\xi,\sigma,\nu).$$
The name clauses ensure that all possible output witnesses are actual names.

Apply §{sec:internal-collection} to $D$ and $\Psi$.
We obtain $W\in M$ such that, for every $\sigma\in A\cap M^P$ and $q\in P$,
$$\begin{aligned}
&\exists\nu\in M^P\;q\forces^*\varphi(\vec\xi,\sigma,\nu)\\
&\quad\Longrightarrow\exists\nu'\in W\cap M^P\;
 q\forces^*\varphi(\vec\xi,\sigma,\nu').
\end{aligned}$$
The condition $q$ and input name $\sigma$ are preserved: equality of their ordered-pair codes identifies
both coordinates. No uniform choice of $\nu'$ is needed.

Put $K:=\bigcup W\in M$ and repeat the bounded-name construction of §{sec:generic-power-set}:
$$\begin{aligned}
C&:=\{\nu\in\InternalPowerSet{M}{K}:M\models\eta(P,\nu)\}\in M,\\
\Pi&:=C\times P\in M^P.
\end{aligned}$$
Every name $\nu\in W$ is a subset of $K$, so $\nu\in C$ and $\nu^G\in\Pi^G$.
We show that this evaluated name contains every output of the given functional relation.

Suppose $a\in x$ and $M[G]\models\varphi(\vec p,a,b)$.
The valuation equation gives $\Pair{\sigma}{r}\in\tau$ with $r\in G$ and $\sigma^G=a$;
the child-name lemma puts $\sigma$ in $A\cap M^P$.
Choose a name $\nu\in M^P$ for $b$.
The truth theorem gives $q\in G$ with $q\forces^*\varphi(\vec\xi,\sigma,\nu)$.
Since $\Pair{\sigma}{q}\in D$, the property of $W$ supplies $\nu'\in W\cap M^P$ such that the same $q$ forces
this name to satisfy the same relation.
The truth theorem now gives $M[G]\models\varphi(\vec p,a,\nu'^G)$.
Uniqueness of the output in $M[G]$ implies $\nu'^G=b$, so $b\in\Pi^G$.
This is where functionality is used; the collected relation in $M$ was allowed to have many output names.

Finally apply Separation in $M[G]$ to the set $\Pi^G$, using the formula
$\exists a\in x\,\varphi(\vec p,a,b)$ with parameters $\vec p,x$. This gives
$$Y:=\{b\in\Pi^G:M[G]\models\exists a\in x\,\varphi(\vec p,a,b)\}\in M[G].$$
The preceding bound proves, for all $b\in M[G]$,
$$b\in Y\quad\Longleftrightarrow\quad M[G]\models\exists a\in x\,\varphi(\vec p,a,b).$$
This is the required Replacement instance. Every finite tuple of extension parameters has ground-model names,
so the argument proves the entire schema.
\end{proof}

## Evaluation Maps and the Axiom of Choice {#sec:forcing-evaluation-choice}

### Evaluation graphs and ground-set covers {#sec:forcing-evaluation-graphs}

To use the evaluation of names in an internal construction, its graph must belong to the extension.
We first construct this graph on any ground-model set of names, then restrict it to obtain a surjection
onto a given extension set. Neither construction uses Choice.

\begin{mathmeta}
  \define{ForcingUnorderedPairName,ForcingOrderedPairName,ForcingEvaluationName}
\end{mathmeta}
For names $\sigma,\tau$, define the unordered-pair and ordered-pair names by
$$\begin{aligned}
\ForcingUnorderedPairName{P}{\sigma}{\tau}&:=\{\sigma,\tau\}\times P,\\
\ForcingOrderedPairName{P}{\sigma}{\tau}
 &:=\ForcingUnorderedPairName{P}
 {\ForcingUnorderedPairName{P}{\sigma}{\sigma}}
 {\ForcingUnorderedPairName{P}{\sigma}{\tau}}.
\end{aligned}$$
Both are names. Whenever $\emptyset\ne G\IncludedIn P$, the valuation equation gives
$$\begin{aligned}
\ForcingUnorderedPairName{P}{\sigma}{\tau}^G&=\{\sigma^G,\tau^G\},\\
\ForcingOrderedPairName{P}{\sigma}{\tau}^G&=\Pair{\sigma^G}{\tau^G}.
\end{aligned}$$
The second identity uses the Kuratowski definition of an ordered pair.
If $P,\sigma,\tau\in M$, Pairing and product closure put both names in $M$.

\begin{theorem*}[\termdefine{Evaluation graphs in extensions}]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
Let $P,D\in M$, suppose that every member of $D$ is a $P$-name, and let $\emptyset\ne G\IncludedIn P$.
Then
$$\begin{aligned}
e_D&:=\{\Pair{\sigma}{\sigma^G}:\sigma\in D\}\in M[G],\\
Y_D&:=\{\sigma^G:\sigma\in D\}\in M[G].
\end{aligned}$$
Moreover, $e_D$ is a surjection from $D$ onto $Y_D$. Genericity is not required.
\end{theorem*}

\begin{proof}[Proof]
Define
$$\ForcingEvaluationName{P}{D}:=
 \{\ForcingOrderedPairName{P}{\check\sigma}{\sigma}:\sigma\in D\}\times P.$$
We must first show that this set belongs to $M$.
Let $\kappa(P,\sigma,c)$ be the first-order formula defining $c=\check\sigma$ by the internal recursion
in §{sec:forcing-names-valuation}. Define
$$\begin{aligned}
u(P,\sigma,\tau,\rho)\;:\equiv\;&\exists Q\,
 (Q=\{\sigma,\tau\}\land\rho=Q\times P),\\
o(P,\sigma,\tau,\rho)\;:\equiv\;&\exists s\,\exists t\,
 \bigl(u(P,\sigma,\sigma,s)\\
 &{}\land u(P,\sigma,\tau,t)\land u(P,s,t,\rho)\bigr),\\
\varepsilon(P,\sigma,\rho)\;:\equiv\;&\exists c\,
 (\kappa(P,\sigma,c)\land o(P,c,\sigma,\rho)).
\end{aligned}$$
The pair and product equalities abbreviate their previously constructed first-order formulas.
The closure lemmas and their interpretation identities show that, for $P,\sigma,\rho\in M$,
$$M\models\varepsilon(P,\sigma,\rho)
 \quad\Longleftrightarrow\quad\rho=\ForcingOrderedPairName{P}{\check\sigma}{\sigma}.$$
For each $\sigma\in D$, exactly one such $\rho$ belongs to $M$.
Replacement in $M$ therefore collects these values into a set in $M$, and product closure gives
$\ForcingEvaluationName{P}{D}\in M$. Its first coordinates are names, so it is itself a name.

The check-name identity and the ordered-pair valuation give
$$\ForcingOrderedPairName{P}{\check\sigma}{\sigma}^G
 =\Pair{\sigma}{\sigma^G}.$$
Every member of $\ForcingEvaluationName{P}{D}^G$ therefore belongs to $e_D$.
Conversely, choose $p\in G$. For each $\sigma\in D$, the name of the displayed pair occurs with condition $p$,
so that pair belongs to the value. Thus $\ForcingEvaluationName{P}{D}^G=e_D\in M[G]$.
Using the check name in the first coordinate preserves the original input name rather than evaluating it.

Similarly, $D\times P\in M$ is a name and $(D\times P)^G=Y_D$, so $Y_D\in M[G]$.
Check-name closure also gives $D\in M[G]$.
The definition of $e_D$ shows that it is a function on $D$ with image exactly $Y_D$.
\end{proof}

\begin{theorem*}[\termdefine{Ground-set covers of generic extensions}]
Under the hypotheses of §{sec:generic-separation}, for every $x\in M[G]$ there are
$D\in M$ and $U,F\in M[G]$ such that
$$U\IncludedIn D,\qquad F:U\twoheadrightarrow x.$$
The function $F$ itself belongs to the extension. The subset $U$ need not belong to the ground model.
\end{theorem*}

\begin{proof}[Proof]
Write $x=\tau^G$ with $\tau\in M^P$ and put
$$\begin{aligned}
A&:=\bigcup\bigcup\tau\in M,\\
D&:=\{\sigma\in A:M\models\eta(P,\sigma)\}\in M.
\end{aligned}$$
Here $\eta$ is the defining formula for names from §{sec:internal-forcing-formulas};
Separation in $M$ constructs $D$. Thus its elements are exactly the names in $A$.
For every $b\in x$, the valuation equation supplies $\Pair{\sigma}{r}\in\tau$ with
$r\in G$ and $\sigma^G=b$. The child-name lemma gives $\sigma\in A\cap M^P=D$.

The preceding theorem gives $e_D\in M[G]$, and check-name closure gives $D\in M[G]$.
Apply Separation in the extension to obtain
$$\begin{aligned}
U&:=\{\sigma\in D:\exists b\in x\ \Pair{\sigma}{b}\in e_D\}\\
 &=\{\sigma\in D:\sigma^G\in x\}\in M[G].
\end{aligned}$$
The first line uses an actual first-order formula with parameters $e_D,x$.
Transitivity and the graph identity justify the second line.
Restrict the graph to these inputs:
$$F:=e_D\cap\bigl(U\times\bigcup\bigcup e_D\bigr)\in M[G].$$
This graph restriction belongs to the extension by Union and Separation, as proved in
§{sec:internal-model-closure}. For each $\sigma\in U$, its unique output is $\sigma^G\in x$.
Conversely, each $b\in x$ has a name $\sigma\in D$ found above; this name belongs to $U$ and is mapped to $b$.
Thus $F:U\twoheadrightarrow x$. No selection of one name for each $b$ was needed.
\end{proof}

For the preservation of Choice, this reduces the problem to ordering inputs from a single ground-model set.
§{sec:internal-choice-enumerations} derives an internal ordinal enumeration from the ground model's
Choice axiom. §{sec:generic-choice} transports that enumeration to the extension and uses least
preimages to construct a choice graph there.

### Choice in the generic extension {#sec:generic-choice}

\begin{theorem*}[\termdefine{Choice in generic extensions}]
Under the hypotheses of §{sec:generic-separation}, suppose in addition that $M$ satisfies Choice.
Then $M[G]$ satisfies Choice.
\end{theorem*}

\begin{proof}[Proof]
Write $N:=M[G]$. The earlier constructions show that $N$ is transitive, contains $M$, and satisfies
Pairing, Union, and Replacement. Fix a family $A\in N$ whose members are nonempty, and put
$$X:=\bigcup A\in N.$$
The ground-set cover theorem supplies $D\in M$ and $U,F\in N$ with
$$U\IncludedIn D,\qquad F:U\twoheadrightarrow X.$$
§{sec:internal-choice-enumerations} supplies an ordinal $\gamma\in M$ and a bijection
$e:\gamma\to D$ with its graph in $M$.
Since $M\IncludedIn N$, the sets $\gamma,D,e$ belong to $N$.
They are the same actual ordinal, set, and function graph, so $e$ remains a bijection onto $D$ in the extension.
This transports the required enumeration; no ground-model membership of $U$ is needed.

For the fixed parameters $\gamma,e,F$, define the first-order formulas
$$\begin{aligned}
\theta(\alpha,x)&:\equiv\exists d\,
 (\Pair{\alpha}{d}\in e\land\Pair{d}{x}\in F),\\
C(y,\alpha)&:\equiv\exists x\in y\;\theta(\alpha,x),\\
\psi(y,x)&:\equiv\exists\alpha\in\gamma\,\bigl[
 x\in y\land\theta(\alpha,x)\\
 &\hspace{5em}{}\land\forall\beta\in\alpha\;\neg C(y,\beta)\bigr].
\end{aligned}$$
Thus $\psi(y,x)$ selects an output in $y$ at the least possible ordinal input.
All ordered-pair membership clauses use the previously verified first-order expansions.

These formulas have the intended meaning internally. If $\theta(\alpha,x)$ holds, its witness $d$ is a
coordinate of a pair in $e$, hence belongs to $\bigcup\bigcup e\in N$. Transitivity then puts it in $N$.
Conversely, an internal witness is an actual witness. The quantifiers bounded by $y$, $\gamma$, or
$\alpha\in\gamma$ range over their actual members, which also lie in $N$.
Thus, for parameters and arguments in $N$, internal satisfaction of $\theta$, $C$, and $\psi$ agrees with
the displayed set-theoretic conditions.

Fix $y\in A$. There is some $x\in y$, and surjectivity of $F$ gives $d\in U$ with $F(d)=x$.
Since $U\IncludedIn D$, surjectivity of $e$ gives $\alpha\in\gamma$ with $e(\alpha)=d$.
Hence $C(y,\alpha)$ holds for some $\alpha\in\gamma$.
The nonempty set of candidate ordinals has a least member $\alpha_y$.
The values $e(\alpha_y)$ and $F(e(\alpha_y))$ are unique, so there is a unique $x\in y$ satisfying $\psi(y,x)$.
More explicitly, two distinct candidate minima would be comparable by membership; the smaller would
contradict minimality of the larger. At the same ordinal input, functionality of $e$ and then of $F$ forces
both outputs to be equal. Since $x\in y\in N$, transitivity puts this unique output in $N$.

Apply the definable-graph construction in §{sec:internal-model-closure} inside $N$ to the selector
$$\rho(y,q)\;:\equiv\;\exists x\,
 (\psi(y,x)\land q=\Pair{y}{x}).$$
Pairing supplies its ordered-pair witnesses, and the Replacement instance for $\rho$ collects the whole graph
$$c:=\{\Pair{y}{x}:y\in A\land N\models\psi(y,x)\}\in N.$$
The uniqueness just proved makes $c$ a function on $A$, and each value belongs to its input set.
Consequently
$$c:A\to\bigcup A,\qquad c(y)\in y\quad(y\in A).$$
This is the Choice sentence in $N$. The same construction covers the empty family, when the graph is empty.
The only choice graph assumed at the outset was in the ground model, used to enumerate $D$.
No Choice axiom in the extension or ordering of the proper class of all names was used.
\end{proof}

