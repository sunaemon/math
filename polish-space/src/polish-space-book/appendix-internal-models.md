# Appendix: Transitive Models and Internal Constructions {#sec:appendix-internal-models}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
本付録がforcingとは独立に推移的モデル内の構成を展開し、forcing付録の前提を供給するという導入。新しい局所定理を主張しない。)
--> This appendix develops constructions inside transitive models, independently of forcing.
It supplies the model-theoretic prerequisites for §{sec:appendix-forcing-background}.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
三つの節の内容と依存関係を案内する段落。具体的な閉包、再帰、rank、Collection、
ChoiceとHartogsは各節の定理・証明として対象に残す。)
--> The development has three parts. §{sec:internal-model-closure} establishes closure under elementary set
operations, definable graphs, and membership recursion, then explains the passage to countable transitive models.
§{sec:internal-model-ranks-recursion} applies this machinery to ranks, cumulative stages, fixed points,
internal ordinal representations, and Collection. Finally, §{sec:internal-model-choice-enumerations} develops selection
and ordinal enumerations,
keeping the uses of Choice separate from the Choice-free Hartogs bound.<!--
formalization: skip-end
-->

## Closure and Internal Constructions {#sec:internal-model-closure}

### Transitivity and Elementary Closure {#sec:internal-transitive-closure}

Fix a transitive model $M$ of a sufficiently large finite fragment of ZFC. Here "sufficiently large" means: large enough
to include the particular ZFC axioms and schema instances used in the forcing construction under discussion. The finite
reflection theorem in §{sec:zfc-cumulative-hierarchy} justifies this convention. Given any prescribed finite fragment,
and any set of parameters that must be present, reflection gives some transitive $V_\alpha$ satisfying that fragment and
containing those parameters.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
到達不能kappaのV_kappaが全ZFCを満たす主張はinaccessible_stage_models_fullZFCへ、
有限量の真な公理文を満たす段階はfinite_true_sentences_reflectへ接続した。
残る冒頭の仮定の強さの位置付けだけを背景説明として対象外とし、相対的無矛盾性強度の厳密な比較を形式化済みとは扱わない。)
--> This is weaker than assuming an inaccessible cardinal.<!--
formalization: skip-end
-->  If $\kappa$ is inaccessible, then $V_\kappa$ is a transitive
model of full ZFC by §{sec:inaccessible-universes}. Reflection gives only the finite amount of ZFC needed for the
argument at hand, but it does so inside ordinary ZFC.

In independence arguments one often takes $M$ to be a \termdefine{countable transitive model} from the ambient universe
$V$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
可算推移モデルの定義は、
標準のCountableとIsTransitiveSetModelを組み合わせたIsCountableTransitiveSetModelへ接続した。
残りはcountabilityを外部で読むという約束と、推移性の定義を所属関係の解釈として説明する文であり、
新しい存在定理やモデルの内部可算性に関する反例をここで証明しない。)
--> Countability is external: $M$ itself need not believe that it is countable. Transitivity means that if $x \in y \in
M$, then $x \in M$, so membership facts about elements of $M$ are not distorted by hidden external elements.<!--
formalization: skip-end
-->

\begin{lemma*}[Elementary closure of a transitive model]
Let $M$ be transitive. Each closure assertion below requires only the indicated axiom to hold in $M$.
Infinity gives $\emptyset\in M$. Pairing gives $\{a,b\}\in M$ for $a,b\in M$, and hence
$\{a\}\in M$ and $\Pair{a}{b}\in M$.
Union gives $\bigcup x\in M$ for $x\in M$; together with Pairing it gives $a\cup b\in M$ for $a,b\in M$.
Power Set gives
$$\PowerSet{x}\cap M=\{z\in M:z\IncludedIn x\}\in M\qquad(x\in M).$$
It need not give $\PowerSet{x}\in M$.
\end{lemma*}

\begin{proof}[Proof]
The internal Infinity axiom supplies an element $e\in M$ with no member in $M$.
Every actual member of $e$ would lie in $M$ by transitivity, so $e=\emptyset$.

For Pairing, the internal witness $p\in M$ satisfies
$$z\in p\quad\Longleftrightarrow\quad z=a\lor z=b\qquad(z\in M).$$
Every element of $p$ lies in $M$, and both $a$ and $b$ lie in $M$.
Thus this equivalence also holds for arbitrary $z$, and external Extensionality gives $p=\{a,b\}$.
Taking $b=a$ gives the singleton, and repeating Pairing gives the Kuratowski pair
$\Pair{a}{b}=\{\{a\},\{a,b\}\}$.

For Union, let $u\in M$ be the internal union of $x\in M$.
If $z\in u$, transitivity puts $z$ in $M$, so the internal axiom supplies $y\in M$ with $z\in y\in x$.
Conversely, if $z\in y\in x$, transitivity applied twice puts $y$ and $z$ in $M$,
and the internal axiom gives $z\in u$. Hence $u=\bigcup x$.
Apply this to $\{a,b\}$ to obtain $a\cup b$.

Finally, let $p\in M$ be the internal power set of $x\in M$.
For $z\in M$, every member of $z$ belongs to $M$, so
$$M\models z\IncludedIn x\quad\Longleftrightarrow\quad z\IncludedIn x.$$
The internal Power Set axiom therefore says that $z\in p$ exactly when $z\IncludedIn x$, for $z\in M$.
Since every member of $p$ lies in $M$, this identifies $p$ with $\PowerSet{x}\cap M$.
It makes no assertion that an arbitrary external subset of $x$ belongs to $M$.
\end{proof}

\begin{lemma*}[Separation and definable images in a transitive model]
Let $M$ be transitive, let $x\in M$, and let $\vec p$ be a finite tuple from $M$.
Suppose the relevant Separation instance holds in $M$, and an external predicate $R$ satisfies
$$M\models\varphi(a,\vec p)\quad\Longleftrightarrow\quad R(a)\qquad(a\in x).$$
Then $\{a\in x:R(a)\}\in M$. In particular, this applies when $R$ is the external interpretation of a
$\Delta_0$ formula, by §{sec:zfc-absoluteness}.

Also let $f:x\to M$ be a function whose graph on $x$ is defined internally by a formula $\psi$:
$$M\models\psi(a,b,\vec p)\quad\Longleftrightarrow\quad b=f(a)
\qquad(a\in x,\ b\in M).$$
If the Replacement instance for $\psi$ holds in $M$, then $f[x]\in M$.
\end{lemma*}

\begin{proof}[Proof]
For Separation, take its internal witness $y\in M$. Every actual element of $y$ or $x$ lies in $M$ by
transitivity. Hence the internal characterization of $y$, together with the assumed equivalence, gives
$$a\in y\quad\Longleftrightarrow\quad a\in x\land R(a)$$
for all actual sets $a$. Thus $y=\{a\in x:R(a)\}$.

For the image, the graph condition and $f(a)\in M$ give exactly one internal output for each $a\in x$.
Replacement supplies $Y\in M$ such that, for $b\in M$, membership $b\in Y$ is equivalent to
$\psi(a,b,\vec p)$ holding internally for some $a\in x$.
Every member of $Y$ lies in $M$, so the graph condition identifies it with a value $f(a)$.
Conversely, each value $f(a)$ lies in $M$ and satisfies that condition, so it belongs to $Y$.
Thus $Y=f[x]$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前の内部image定理の適用条件を読み直す注意。valuesの内部所属と内部式によるgraphの定義が必要であることを明記し、
後の具体的name構成へ先送りする。この注意自体は任意の外部構成がモデル内に入らないことの独立した反例を構成しない。)
--> These conclusions distinguish internal definability from an arbitrary external construction.
To use the image argument for a recursively defined family of names, one must still show that its values
belong to $M$ and that one formula defines its graph inside $M$. Transitivity and external recursion alone
do not establish those two requirements.<!--
formalization: skip-end
-->

### Products and Function Graphs {#sec:internal-products-graphs}

\begin{mathmeta}
  \vars{x}{Nat}
\end{mathmeta}

\begin{lemma*}[Cartesian products in a transitive model]
Suppose $M$ is transitive and satisfies Pairing, Union, Power Set, and the Separation instance for the bounded
product predicate below. Then $x,y\in M$ implies $x\times y\in M$.
\end{lemma*}

\begin{proof}[Proof]
Use the elementary closure lemma to form the following sets in $M$:
$$A=x\cup y,\qquad B=\PowerSet{A}\cap M,\qquad C=\PowerSet{B}\cap M.$$
If $a\in x$ and $b\in y$, transitivity gives $a,b\in M$. Pairing puts
$\{a\}$, $\{a,b\}$, and $\Pair{a}{b}$ in $M$.
The first two sets are subsets of $A$, so they belong to $B$.
Hence $\Pair{a}{b}$ is a subset of $B$ and belongs to $M$, which puts it in $C$.
Thus $x\times y\IncludedIn C$.

The predicate $\exists a\in x\,\exists b\in y\,(q=\Pair{a}{b})$ is $\Delta_0$ after the bounded
ordered-pair expansion in §{sec:zfc-absoluteness}. Bounded Separation therefore gives
$$x\times y=\{q\in C:\exists a\in x\,\exists b\in y\,(q=\Pair{a}{b})\}\in M.$$
Both power sets used in the argument are internal power sets. No external power-set closure is assumed.
The required Separation instance can itself be obtained from Infinity and one Replacement instance by
§{sec:zfc-axioms}.
\end{proof}

\begin{lemma*}[Function spaces and definable graphs in a transitive model]
Let $M$ be transitive and satisfy Pairing, Union, Power Set, and the Separation instances for products and
for the bounded function predicate in §{sec:zfc-absoluteness}. For $x,y\in M$,
$\funcspace{x}{y}\cap M\in M$. This is the set of functions from $x$ to $y$ that belong to $M$.

Also suppose that $f:x\to M$ is internally defined by $\psi(a,b,\vec p)$ in the sense of the definable-image
lemma above. Define
$$\theta(a,q,\vec p)\;:\equiv\;\exists b\,\bigl(\psi(a,b,\vec p)\land q=\Pair{a}{b}\bigr).$$
If the Replacement instance for $\theta$ holds in $M$, then
$$\Gamma_f:=\{\Pair{a}{f(a)}:a\in x\}\in M.$$
Thus the entire graph, not just its individual pairs, belongs to $M$.
\end{lemma*}

\begin{proof}[Proof]
The product lemma gives $x\times y\in M$, so the internal Power Set axiom gives
$$B=\PowerSet{x\times y}\cap M\in M.$$
Every actual function from $x$ to $y$ is a subset of $x\times y$.
The bounded function predicate recognizes the actual function graphs in any transitive domain, as proved in
§{sec:zfc-absoluteness}. Separation therefore gives
$$\{g\in B:g:x\to y\}=\funcspace{x}{y}\cap M\in M.$$
This does not imply that every external function between those sets belongs to $M$.

For the second assertion, take $a\in x$. Transitivity gives $a\in M$, and the assumed internal definition
supplies the unique value $f(a)\in M$. Pairing puts $\Pair{a}{f(a)}$ in $M$.
The bounded ordered-pair formula identifies this actual pair, so $\theta(a,q,\vec p)$ holds internally exactly
when $q=\Pair{a}{f(a)}$. Apply the definable-image lemma to this pair-valued function to obtain
$\Gamma_f\in M$.
Every member of $\Gamma_f$ is one of these pairs, and each $a\in x$ occurs once, so
$\Gamma_f:x\to f[x]$. Uniqueness follows from injectivity of ordered-pair coding.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
部分的再帰assignmentを一つの内部setとして扱えるための既証明の前提と、後の内部再帰定理で示すべきことを区別する読書案内。
任意の外部assignmentの非内部性を新しい局所定理として証明する箇所ではない。)
--> These constructions let us treat a set-sized partial recursive assignment as one set in the model, once
its values and internal defining formula have been established. They do not assert that an arbitrary
externally given assignment belongs to the model. The existence and internal definability of recursive
assignments must still be proved by well-founded recursion inside the ground model.<!--
formalization: skip-end
-->

Restrictions of graphs can also be formed internally. Put $B=\bigcup\bigcup f$.
If $\Pair{a}{b}\in f$, then $b\in\{a,b\}\in\Pair{a}{b}\in f$, so $b\in B$.
Consequently
$$\restrict{f}{x}=\{q\in f:\exists a\in x\,\exists b\in B\,(q=\Pair{a}{b})\}.$$
For a function graph, this keeps exactly the pairs whose first coordinate lies in $x$.
If $f,x\in M$, two applications of Union put $B$ in $M$, and bounded Separation gives $\restrict{f}{x}\in M$.
No bound on the values external to the graph is needed.

### Membership Recursion {#sec:internal-membership-recursion}

\begin{mathmeta}
  \vars{a,x}{Nat}
\end{mathmeta}

\begin{definition*}[Partial solutions of membership recursion]
Fix a rule $H(a,g)$ assigning a set to each pair of sets. A
\termdefine{partial solution of membership recursion} is a function graph $f$ on a transitive domain $D$ such that
$$f(a)=H(a,\restrict{f}{a})\qquad(a\in D).$$
Transitivity ensures that every member of $a\in D$ belongs to the domain of $f$.
\end{definition*}

\begin{lemma*}[Agreement and gluing of recursive solutions]
Two partial solutions agree on the intersection of their domains. In particular, a solution on a fixed domain
is unique. If $(f_i:D_i\to V)_{i\in I}$ is a set-indexed family of partial solutions for the same rule, then
$$A:=\bigcup_{i\in I}D_i,\qquad F:=\bigcup_{i\in I}f_i$$
define a partial solution $F:A\to V$. Here $V$ denotes the ambient universe of sets, so no common set of
possible values is assumed in advance.
\end{lemma*}

\begin{proof}[Proof]
Let $f:D\to V$ and $g:E\to V$ be partial solutions. By membership induction on $a$, assume they agree at
every $z\in a$ belonging to both domains. If $a\in D\cap E$, transitivity puts all its members in both domains.
Thus $\restrict{f}{a}=\restrict{g}{a}$, and
$$f(a)=H(a,\restrict{f}{a})=H(a,\restrict{g}{a})=g(a).$$
This proves agreement. If the domains coincide, every pair in either graph occurs in the other, so the graphs
are equal.

For the gluing assertion, $A$ is transitive because each $D_i$ is transitive. Pairwise agreement makes $F$
a function with domain $A$: every input occurs in some graph, and two graphs cannot give it different values.
For $a\in A$, choose $i\in I$ with $a\in D_i$. Every $z\in a$ lies in $D_i$, and agreement gives
$\restrict{F}{a}=\restrict{f_i}{a}$. Hence
$$F(a)=f_i(a)=H(a,\restrict{f_i}{a})=H(a,\restrict{F}{a}),$$
as required. This includes an empty family, whose union is the empty solution.
\end{proof}

\begin{lemma*}[One-point extension of a recursive solution]
Let $f$ be a partial solution on $D$, and suppose that $a\notin D$ and $a\IncludedIn D$.
Put
$$\begin{aligned}
v&:=H(a,\restrict{f}{a}),\\
D'&:=D\cup\{a\},\qquad f':=f\cup\{\Pair{a}{v}\}.
\end{aligned}$$
Then $f'$ is a partial solution on $D'$.
\end{lemma*}

\begin{proof}[Proof]
The set $D'$ is transitive, since every member of the new input already belongs to $D$.
The new pair has a first coordinate outside $D$, so $f'$ remains a function.
If $z\in D$, then $a\notin z$: otherwise transitivity would give $a\in D$.
Also $a\notin a$ by Foundation. Thus adding the new pair changes none of the restrictions to the members of
an old or new input. All old recursive equations remain true, and the equation at $a$ holds by the definition
of $v$.
\end{proof}

For gluing inside a transitive model $M$, the two collections $\{D_i:i\in I\}$ and $\{f_i:i\in I\}$
must first belong to $M$. Union then puts $A,F$ in $M$, and the gluing lemma applies to their actual graphs.
For the one-point extension, if $D,f,a,v\in M$, Pairing and Union put $D',f'$ in $M$.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
モデル内のgluingとone-point
extensionの正の閉包主張は既存のrecursive_solution_iUnion_mem・recursive_solution_extend
_memへ接続済み。残る220–224行は次のpartial-solution式とReplacementによる存在証明の必要条件を案内する文で、
外部partial solutionの存在だけから内部所属を結論しないという適用上の注意である。後続の内部再帰の存在証明はこの判定から除外しない。)
--> These are the gluing and extension steps of internal membership recursion.
We now construct the internal formulas for partial solutions and their values.
The remaining existence argument must collect the required families by Replacement and establish closure
under the step rule; neither follows from the mere external existence of partial solutions.<!--
formalization: skip-end
-->

The restriction predicate can be written without an extra parameter bounding its values. Set
$$\chi(x,q)\;:\equiv\;\exists a\in x\,\exists u\in q\,\exists b\in u\,(q=\Pair{a}{b}).$$
The extra bound $u\in q$ loses no pair: for $q=\Pair{a}{b}$, use $u=\{a,b\}$.
Conversely, any witnesses to this formula exhibit a pair whose first coordinate lies in $x$.
Thus define
$$\begin{aligned}
\rho(f,x,g)\;:\equiv\;&\forall q\in g\,(q\in f\land\chi(x,q))\\
&{}\land\forall q\in f\,(\chi(x,q)\to q\in g).
\end{aligned}$$
Both formulas are $\Delta_0$ after expanding ordered-pair equality as in §{sec:zfc-absoluteness}.
In any transitive domain containing the parameters, the two clauses of $\rho$ give precisely the two inclusions
in $g=\restrict{f}{x}$. This recognition statement needs no closure axioms; the existence of the restriction
inside the model uses the closure argument above.

Fix a finite parameter tuple $\vec p\in M$ and a formula $\psi(a,g,b,\vec p)$ representing the step rule:
$$M\models\psi(a,g,b,\vec p)\quad\Longleftrightarrow\quad b=H(a,g)
\qquad(a,g,b\in M).$$
Define the partial-solution formula
$$\begin{aligned}
\sigma(D,f,\vec p)\;:\equiv\;&\mathrm{Trans}(D)\land\exists Y\,(f:D\to Y)\\
&{}\land\forall a\in D\,\exists g\,\exists b\,
 \bigl(\rho(f,a,g)\\
&\qquad{}\land\Pair{a}{b}\in f\land\psi(a,g,b,\vec p)\bigr).
\end{aligned}$$
The transitivity, function, and ordered-pair clauses are the explicit formulas already given above and in
§{sec:zfc-absoluteness}. All remaining quantifiers are displayed, so this is a single first-order formula
with the indicated finite tuple of parameters. No boundedness claim is made for $\sigma$ or for $\psi$.

\begin{lemma*}[Internal definition of partial solutions]
Suppose $M$ is transitive and satisfies Union and the bounded Separation instance used to restrict graphs.
For $D,f\in M$, the internal statement $\sigma(D,f,\vec p)$ holds exactly when $f$ is an actual partial solution
for $H$ on $D$.
\end{lemma*}

\begin{proof}[Proof]
From the internal formula, absoluteness of the transitivity and function predicates gives a transitive domain
and an actual function graph. For each input, the witness $g$ is the actual restriction by the preceding
calculation, and the witness $b$ is the graph's value. The defining equivalence for $\psi$ therefore gives the
required recursive equation.

Conversely, let $f$ be a partial solution on $D$ in the ambient universe. The set
$Y=\bigcup\bigcup f$ belongs to $M$ and contains all its values, so it witnesses the function clause.
For each $a\in D$, transitivity gives $a\in M$, and the restriction calculation puts
$g=\restrict{f}{a}$ in $M$. The value $b=H(a,g)$ occurs in a pair of $f$, so $b\in Y$ and hence $b\in M$.
These actual sets witness the two existential quantifiers, and the defining equivalence for $\psi$ gives
its internal truth. Thus $\sigma(D,f,\vec p)$ holds internally.
\end{proof}

Finally define the value predicate
$$\begin{aligned}
\nu(a,b,\vec p)\;:\equiv\;\exists D\,\exists f\,\bigl(
\sigma(D,f,\vec p)\\
{}\land a\in D\land\Pair{a}{b}\in f\bigr).
\end{aligned}$$
Internally, this says that some partial solution in the model assigns the proposed value to the input.
It is single-valued: two internal witnesses yield two actual partial solutions by the lemma, and the agreement
lemma makes their values equal at the common input. Thus this fixed formula supplies the uniqueness premise
needed for Replacement. Existence at each required input remains a separate step; the formula does not
postulate a solution on the whole ground model.

\begin{theorem*}[\termdefine{Internal membership recursion}]
Let $M$ be transitive and satisfy Pairing, Union, Power Set, Separation, and Replacement.
Suppose the rule $H$ has the internal defining formula $\psi$ above and
$H(a,g)\in M$ whenever $a,g\in M$. For every transitive $A\in M$, there is a unique function graph
$F\in M$ on $A$ satisfying
$$F(a)=H(a,\restrict{F}{a})\qquad(a\in A).$$
\end{theorem*}

\begin{proof}[Proof]
First fix the domain for each input. Put $B=\PowerSet{A}\cap M\in M$, and, for $a\in A$, define
$$D_a:=\{z\in A:\forall D\in B\,
 ((\mathrm{Trans}(D)\land a\in D)\to z\in D)\}.$$
The displayed predicate is bounded, so Separation gives $D_a\in M$.
It contains $a$, is a subset of $A$, and is transitive: if $z\in D_a$ and $w\in z$, then
$w\in A$, and every transitive candidate containing $a$ contains $z$ and hence $w$.
It is also minimal among internal transitive subsets of $A$ containing $a$:
$$D\in M,\quad D\IncludedIn A,\quad\mathrm{Trans}(D),\quad a\in D
\quad\Longrightarrow\quad D_a\IncludedIn D.$$

The equality $D=D_a$ is expressed internally by the bounded formula asserting $D\IncludedIn A$ and
that, for every $z\in A$, membership in $D$ is equivalent to the displayed selection predicate.
Combining this formula with $\sigma(D,f,\vec p)$ gives a fixed first-order formula
asserting that $f$ is a partial solution on $D_a$. Its parameters are $A,B,\vec p$.
The internal-definition lemma identifies its solutions with actual partial solutions, and the agreement
lemma makes the output graph unique. Hence, whenever these solutions exist for all inputs in a set
$X\in M$ with $X\IncludedIn A$, Replacement collects both $\{D_a:a\in X\}$ and
$\{f_a:a\in X\}$ inside $M$. Union then gives a partial solution on $\bigcup_{a\in X}D_a$ inside $M$.

We now prove by membership induction on $a\in A$ that a solution on $D_a$ belongs to $M$.
For every $b\in a$, the induction hypothesis supplies the unique solution $f_b\in M$ on $D_b$.
Since $a\in M$, the preceding collection and gluing argument gives
$$U:=\bigcup_{b\in a}D_b\in M,\qquad f:=\bigcup_{b\in a}f_b\in M,$$
where $f$ is a partial solution on $U$. Each $b\in a$ lies in $D_b$, so $a\IncludedIn U$.
Also $U\IncludedIn D_a$: transitivity of $D_a$ puts each such $b$ in $D_a$, and minimality gives
$D_b\IncludedIn D_a$.

If $a\in U$, minimality gives $D_a\IncludedIn U$, so $U=D_a$ and $f$ is the required solution.
Otherwise, the restriction belongs to $M$, and the step-rule closure assumption gives
$$v:=H(a,\restrict{f}{a})\in M.$$
The one-point extension lemma puts a solution on $W:=U\cup\{a\}$ in $M$.
Here $W$ is transitive, belongs to $M$, contains $a$, and satisfies
$W\IncludedIn D_a\IncludedIn A$. Minimality gives $D_a\IncludedIn W$, hence $W=D_a$.
This completes the induction, including the case of an empty predecessor set.

Finally apply the same collection formula to all $a\in A$ and take the union of the graphs.
Since $a\in D_a\IncludedIn A$ for every input, $\bigcup_{a\in A}D_a=A$.
The resulting graph $F\in M$ is therefore a solution on $A$, and the agreement lemma proves uniqueness.
\end{proof}

This theorem needs no Choice axiom in the model: each collected graph is uniquely specified by a formula.
It applies once an internal transitive domain and an internally defined step rule preserving membership in
$M$ have been supplied. <!--
formalization: skip-begin (引用・背景説明・読書案内:
Choiceを仮定せず、内部transitive domainと内部定義・value
closureを入力として一意のgraphを得る主張はinternal_membership_recursionの実際の仮定と証明で確認し接続した。
残る337–338行は後続のtransitive bound、rank、check-nameの構成への案内で、新たな一般的再帰閉包をここで主張しない。)
--> The next construction supplies a transitive domain containing any prescribed input.
The step rules for rank and check-name recursion are verified below.<!--
formalization: skip-end
-->

### Transitive Bounds and Recursive Values {#sec:internal-transitive-bounds}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{D,g}{Set}
\end{mathmeta}

\begin{lemma*}[Natural numbers in a transitive model]
Suppose $M$ is transitive and satisfies Infinity and the Separation instance for the bounded formula below.
Then the actual set $\omega$ of finite von Neumann ordinals belongs to $M$.
\end{lemma*}

\begin{proof}[Proof]
The Infinity axiom gives $I\in M$ that is internally inductive. Transitivity and Extensionality identify
its internal empty set and successors with the actual empty set and successors. Thus
$$\emptyset\in I,\qquad y\in I\ \Longrightarrow\ y\cup\{y\}\in I.$$
Ordinary induction gives $\omega\IncludedIn I$. To separate precisely its finite ordinals, put
$$\begin{aligned}
\mathrm{ZS}(y)&:\equiv y=\emptyset\lor\exists z\in y\,(y=z\cup\{z\}),\\
\mathrm{FinOrd}(y)&:\equiv\mathrm{Ord}(y)\land\mathrm{ZS}(y)
 \land\forall z\in y\,\mathrm{ZS}(z).
\end{aligned}$$
These are bounded formulas: emptiness says that there is no member, and the successor equality expands as
$$z\in y\land(\forall w\in z\,w\in y)
 \land\forall w\in y\,(w=z\lor w\in z).$$

Every finite ordinal satisfies $\mathrm{FinOrd}$. Conversely, use membership induction on an ordinal $y$
satisfying that formula. If $y=\emptyset$, it is finite. Otherwise write $y=z\cup\{z\}$ with $z\in y$.
Ordinalhood and the zero-or-successor conditions pass to $z$, so the induction hypothesis makes $z$ finite,
and then $y$ is finite as well. Bounded absoluteness therefore identifies the internal formula with actual
membership in $\omega$. Separation inside $I$ gives
$$\{y\in I:M\models\mathrm{FinOrd}(y)\}=\omega\in M.$$
\end{proof}

\begin{mathmeta}
  \define{GraphRange}
\end{mathmeta}
For a set of ordered pairs $g$, write $\GraphRange{g}$ for its range. More generally, for any set $g$ put
$$\GraphRange{g}:=\{b\in\bigcup\bigcup g:\exists a\,(\Pair{a}{b}\in g)\}.$$
Both coordinates of every pair in $g$ belong to $\bigcup\bigcup g$.
If $g\in M$, two unions put this bound in $M$, so transitivity puts both coordinates in $M$.
Consequently the internal existential formula recognizes exactly the actual range members, and Separation
gives $\GraphRange{g}\in M$. Its defining equality is the first-order formula
$$\forall b\,\bigl(b\in r\leftrightarrow\exists a\,(\Pair{a}{b}\in g)\bigr).$$
The same transitivity argument identifies internal unions and insertions with their actual set operations.

\begin{lemma*}[Internal transitive bounds]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
For every $x\in M$, there is a transitive $T\in M$ with $x\in T$.
\end{lemma*}

\begin{proof}[Proof]
Fix $x\in M$ and use the step rule
$$H_x(a,g):=\{x\}\cup\bigcup\bigcup\GraphRange{g}.$$
The preceding range construction, two unions, and insertion show that this rule has values in the model.
An internal defining formula is
$$\begin{aligned}
\psi_x(a,g,b)\;:\equiv\;\exists r\,\exists u\,\exists v\,\bigl(
 r=\GraphRange{g}\land u=\bigcup r\\
{}\land v=\bigcup u\land b=\{x\}\cup v\bigr).
\end{aligned}$$
Expand the range equality as above, the union equalities by their membership clauses, and the last equality
as $\forall z\,(z\in b\leftrightarrow z=x\lor z\in v)$.
All three intermediate sets belong to the model, so this formula defines exactly $H_x(a,g)$ internally.

By the preceding lemma, $\omega\in M$ is an actual transitive set.
Internal membership recursion therefore gives $F\in M$ with domain $\omega$ and
$$F(n)=\{x\}\cup\bigcup\bigcup\GraphRange{\restrict{F}{n}}\qquad(n\in\omega).$$
Set $T:=\bigcup\GraphRange{F}\in M$. Since $x\in F(0)$, we have $x\in T$.
To prove transitivity, suppose $z\in y\in T$. Choose $n\in\omega$ with $y\in F(n)$.
The pair $\Pair{n}{F(n)}$ belongs to $\restrict{F}{n+1}$, so
$$\begin{aligned}
F(n)&\in\GraphRange{\restrict{F}{n+1}},\\
z&\in\bigcup\bigcup\GraphRange{\restrict{F}{n+1}}\IncludedIn F(n+1).
\end{aligned}$$
Thus $z\in T$, as required. The construction collects the entire graph by the previously proved recursion
theorem; it does not infer that an externally chosen infinite sequence belongs to the model.
\end{proof}

\begin{corollary*}[Existence of internal recursive values]
Under the axioms of the last lemma, let $H$ have the internal defining formula $\psi$ and map pairs of
members of $M$ to members of $M$. Then the value formula $\nu(a,b,\vec p)$ defined above satisfies
$$M\models\forall a\,\exists!b\,\nu(a,b,\vec p).$$
\end{corollary*}

\begin{proof}[Proof]
For $a\in M$, choose a transitive $T\in M$ containing $a$, and apply internal membership recursion on $T$.
It gives a graph $F\in M$ assigning a value $b$ at $a$. Because $\Pair{a}{b}\in F$,
transitivity gives $b\in M$. The domain and graph witness $\nu(a,b,\vec p)$ internally.
Agreement of partial solutions gives uniqueness, independently of the chosen transitive bound.
\end{proof}

\begin{lemma*}[Comparison with an external recursion]
Under the hypotheses of the preceding corollary, suppose an externally definable class function $K$ satisfies
$$K(a)=H(a,\Gamma_{K,a}),\qquad
\Gamma_{K,D}:=\{\Pair{z}{K(z)}:z\in D\}.$$
Then $K(a)\in M$ for every $a\in M$.
\end{lemma*}

\begin{proof}[Proof]
Ambient Replacement makes $\Gamma_{K,D}$ a set for each set $D$.
When $D$ is transitive, restricting this graph to $a\in D$ gives $\Gamma_{K,a}$, so the assumed equation
makes it an actual partial solution. For $a\in M$, the preceding corollary supplies an internal partial
solution assigning a value at $a$. Compare it with the external graph on the same transitive domain.
Agreement of partial solutions identifies the internal value with $K(a)$, proving that $K(a)\in M$.
This argument proves membership of the specified recursive value, rather than merely producing some
unidentified internal solution.
\end{proof}

\begin{corollary*}[Defining the external recursive value]
Under the hypotheses of the comparison lemma, for $a,b\in M$,
$$M\models\nu(a,b,\vec p)\quad\Longleftrightarrow\quad b=K(a).$$
\end{corollary*}

\begin{proof}[Proof]
An internal partial solution witnessing the left side agrees with the external graph at $a$, so its value is
$K(a)$. Conversely, existence of an internal recursive value supplies some $c\in M$ satisfying the left side
with $c$ in place of $b$. The same comparison gives $c=K(a)=b$, yielding the desired instance of the formula.
\end{proof}

### Collapse and Countable Transitive Models {#sec:internal-countable-reduction}

\begin{mathmeta}
  \vars{A}{Set}
\end{mathmeta}

The countable-transitive convention is reached by starting from the reflected transitive set $V_\alpha$, then applying
downward Löwenheim--Skolem from §{sec:appendix-logic} and the Mostowski collapse below. Parameters are handled with
care: the collapse preserves actual parameters only when enough of their transitive closures is included in the
elementary submodel; in general it carries them to their collapsed images.

\begin{theorem*}[\termdefine{Mostowski collapse}]
Let $A$ be a set and let $E\IncludedIn A\times A$ be a well-founded relation that is
\termdefineas{extensional relation}{extensional}: two points with the same $E$-predecessors are equal.
Then there is a unique transitive set $M$ and a unique isomorphism
$$
\pi:\Pair{A}{E}\cong \Pair{M}{\in}.
$$

\end{theorem*}

\begin{proof}[Proof]
Define $\pi$ by well-founded recursion:
$$
\pi(a)=\{\pi(b): b\,E\,a\}.
$$
Since $A$ is a set, every predecessor collection is a set, and Replacement makes the recursive images sets.
In particular, $M=\{\pi(a):a\in A\}$ is a set. It is transitive, because every element of $\pi(a)$ is some
$\pi(b)$ with $b\,E\,a$.

To prove injectivity, use well-founded induction on $a$, keeping $a'$ arbitrary, to show that
$\pi(a)=\pi(a')$ implies $a=a'$. If $b\,E\,a$, the recursive equation gives some $c\,E\,a'$ with
$\pi(b)=\pi(c)$; the induction hypothesis at $b$ gives $b=c$, hence $b\,E\,a'$.
Conversely, if $b\,E\,a'$, there is some $c\,E\,a$ with $\pi(c)=\pi(b)$, and the induction hypothesis
at $c$ gives $c=b$, hence $b\,E\,a$. Extensionality now gives $a=a'$.
The recursive equation and injectivity show that $b\,E\,a$ iff $\pi(b)\in\pi(a)$, so $\pi$ is an
isomorphism onto $M$.

For uniqueness, let $\rho:\Pair{A}{E}\cong\Pair{N}{\in}$ be any isomorphism onto a transitive set.
Every element of $\rho(a)$ belongs to $N$ by transitivity, so surjectivity and preservation of the relation give
$$\rho(a)=\{\rho(b):b\,E\,a\}.$$
Well-founded induction in the two recursive equations gives $\rho(a)=\pi(a)$ for every $a\in A$.
Taking images gives $N=M$, proving uniqueness of both the transitive set and the isomorphism.
\end{proof}

\begin{theorem*}[\termdefine{Countable transitive reduction}]
Let $M_0$ be a nonempty transitive set, and let $T\IncludedIn M_0$ be a countable transitive set.
There is a countable transitive set $M$ containing every element of $T$ such that
$$M\models\varphi\quad\Longleftrightarrow\quad M_0\models\varphi$$
for every sentence $\varphi$ in the language of set theory.
\end{theorem*}

\begin{proof}[Proof]
By downward Löwenheim--Skolem from §{sec:appendix-logic}, choose a countable elementary submodel
$N\prec M_0$ containing every element of $T$. Its membership relation is well-founded by ambient
Foundation. Transitivity makes $M_0$ satisfy Extensionality, so elementarity makes $\Pair{N}{\in}$ extensional.
The Mostowski collapse gives an isomorphism $\pi:N\to M$ onto a transitive set $M$.
Surjectivity makes $M$ countable. Isomorphisms preserve satisfaction, and $N\prec M_0$, so $M$ and $M_0$
satisfy exactly the same sentences.

For $a\in T$, membership induction proves $\pi(a)=a$. Transitivity of $T$ ensures that every $b\in a$
belongs to $T$ and hence to $N$. The induction hypothesis therefore gives
$$\pi(a)=\{\pi(b):b\in a\cap N\}=\{b:b\in a\}=a.$$
Thus every $a\in T$ belongs to $M$, as required.
\end{proof}

For a finite fragment, choose a nonempty $M_0=V_\alpha$ by reflection and apply this theorem, taking
$T=\emptyset$ if no parameters need to be fixed. To preserve a parameter $a$, include $a$ and all its
iterated members in the seed $T$<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限反映からの可算推移モデルはfinite_fragment_countable_model_with_seedへ、
遺伝的可算なパラメータ族を保つcountable transitive
seedはparameterLayers・parameterSeedとそのcontains/transitive/subset/countableの各
証明およびfixed_parametersの縮約へ接続した。
任意の可算族を含めるLöwenheim–Skolemはexists_countable_elementarySubstructureへ、
全ZFCモデルから実際の自然演繹のConsistentを得る推論はnamedFullZFCTheory_consistent_of_modelへ接続し
た。残る、単にaを含むだけでは元のパラメータを固定したとみなせないという注意、崩壊で一般の対象が動きうるという背景説明、
全ZFCのCTM存在をこの有限反映から結論しないというメタ理論上の位置付けだけを対象外とする。
崩壊の反例やZFC上のモデル存在の不可能性を形式化済みとする判定ではない。)
--> ; merely requiring $a\in N$ is insufficient.<!--
formalization: skip-end
-->  A countable family of
hereditarily countable parameters admits such a countable transitive seed. Arbitrary countable collections
of objects may also be included in the Löwenheim--Skolem construction<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限反映からの可算推移モデルはfinite_fragment_countable_model_with_seedへ、
遺伝的可算なパラメータ族を保つcountable transitive
seedはparameterLayers・parameterSeedとそのcontains/transitive/subset/countableの各
証明およびfixed_parametersの縮約へ接続した。
任意の可算族を含めるLöwenheim–Skolemはexists_countable_elementarySubstructureへ、
全ZFCモデルから実際の自然演繹のConsistentを得る推論はnamedFullZFCTheory_consistent_of_modelへ接続し
た。残る、単にaを含むだけでは元のパラメータを固定したとみなせないという注意、崩壊で一般の対象が動きうるという背景説明、
全ZFCのCTM存在をこの有限反映から結論しないというメタ理論上の位置付けだけを対象外とする。
崩壊の反例やZFC上のモデル存在の不可能性を形式化済みとする判定ではない。)
--> , but the collapse can move those objects.
This is a metatheoretic reduction for finite fragments, not a theorem of ZFC asserting that countable
transitive models of full ZFC exist;<!--
formalization: skip-end
-->  such an assertion implies $\mathrm{Con}(\mathrm{ZFC})$.

## Ranks and Recursion {#sec:internal-model-ranks-recursion}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
既存の内部membership再帰をrank・累積段階・fixed point・Collectionへ使う、後続節の依存関係の案内。
各後続定理の証明とChoice不使用の確認は別単位として保持する。)
--> Internal membership recursion in §{sec:internal-membership-recursion} supplies values and defining formulas
inside the model. We now use it for ranks and cumulative stages, then derive fixed-point and Collection
constructions without adding Choice.<!--
formalization: skip-end
-->

### Internal Ranks and Cumulative Stages {#sec:internal-model-hierarchy}

\begin{lemma*}[Rank ordinals in the ground model]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
Then $\mathrm{rank}(a)\in M$ for every $a\in M$, where ranks are viewed as von Neumann ordinals.
\end{lemma*}

\begin{proof}[Proof]
Put $\rho(a):=\mathrm{rank}(a)$ and use the step rule
$$H(a,g):=R\cup\bigcup R,\qquad R:=\GraphRange{g}.$$
Range closure, Union, and binary-union closure put this value in the model.
An internal defining formula is
$$\begin{aligned}
\psi(a,g,b)\;:\equiv\;\exists r\,\exists u\,\bigl(
 r=\GraphRange{g}\\
{}\land u=\bigcup r\land b=r\cup u\bigr).
\end{aligned}$$
Expand the last equality as $\forall z\,(z\in b\leftrightarrow z\in r\lor z\in u)$.
The range and union predicates have already been verified, and transitivity identifies the internal
binary-union clause with the actual union. This defines the step even when the proposed preceding values
are not ordinals.

For the actual rank function, $R=\{\rho(y):y\in a\}$ consists of ordinals.
Every member of $R\cup\bigcup R$ is an ordinal, and for an ordinal $\beta$,
$$\begin{aligned}
\beta\in R\cup\bigcup R
&\Longleftrightarrow\exists y\in a\,(\beta\le\rho(y))\\
&\Longleftrightarrow\beta<\rho(a).
\end{aligned}$$
The last equivalence is the defining supremum property of rank.
Extensionality gives $\rho(a)=R\cup\bigcup R$, which is the required step equation.
The internal recursion and comparison lemmas therefore give $\rho(a)\in M$.
\end{proof}

\begin{mathmeta}
  \define{InternalPowerSet,InternalHierarchy}
\end{mathmeta}
For a transitive set $M$, write
$$\InternalPowerSet{M}{x}:=\PowerSet{x}\cap M.$$
The internal power set is defined by the first-order formula
$$\pi(x,p)\;:\equiv\;
\forall z\,\bigl(z\in p\leftrightarrow\forall w\in z\,(w\in x)\bigr).$$
For $x,p\in M$, transitivity gives
$$M\models\pi(x,p)\quad\Longleftrightarrow\quad p=\InternalPowerSet{M}{x}.$$
The symbol $M$ does not occur as a parameter in this formula: its quantifiers are interpreted in the model.
If the model satisfies Power Set, then $\InternalPowerSet{M}{x}\in M$ for each $x\in M$.
For $R\in M$, Replacement applied to $\pi$ therefore collects
$$S=\{\InternalPowerSet{M}{r}:r\in R\}\in M.$$
The corresponding image formula is
$$\chi(R,S)\;:\equiv\;
\forall p\,\bigl(p\in S\leftrightarrow\exists r\in R\,\pi(r,p)\bigr).$$
Its internal interpretation is exactly the displayed equality for $S$.

\begin{theorem*}[Internal cumulative stages]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
For every ordinal $\alpha$, put
$$\InternalHierarchy{M}{\alpha}:=V_\alpha\cap M.$$
If $\alpha\in M$, then $\InternalHierarchy{M}{\alpha}\in M$.
There is a first-order formula $\theta(\alpha,b)$, with no parameters, such that for every ordinal
$\alpha\in M$ and every $b\in M$,
$$M\models\theta(\alpha,b)
\quad\Longleftrightarrow\quad b=\InternalHierarchy{M}{\alpha}.$$
\end{theorem*}

\begin{proof}[Proof]
Use the step rule
$$H_M(a,g):=\bigcup\{\InternalPowerSet{M}{r}:r\in\GraphRange{g}\}.$$
Range closure, the preceding image construction, and Union show that $H_M(a,g)\in M$ whenever $a,g\in M$.
An internal defining formula is
$$\begin{aligned}
\psi(a,g,b)\;:\equiv\;\exists R\,\exists S\,\bigl(
 R=\GraphRange{g}\\
{}\land\chi(R,S)\land b=\bigcup S\bigr).
\end{aligned}$$
Expand the range equality as before and the union equality by its membership clause.
The intermediate sets belong to the model, and each clause has the required interpretation.
Thus this formula defines the step on all internal inputs, without assuming that $a$ is an ordinal or
that $g$ is a function.

In the ambient universe, membership recursion with parameter $M$ defines
$$K_M(a):=\bigcup_{z\in a}\InternalPowerSet{M}{K_M(z)}.$$
This is precisely the equation $K_M(a)=H_M(a,\Gamma_{K_M,a})$.
Internal recursion and comparison give $K_M(a)\in M$ for $a\in M$, and their value formula satisfies
$$M\models\nu(a,b)\quad\Longleftrightarrow\quad b=K_M(a)\qquad\Pair{a}{b}\in M.$$

We prove by induction on all ordinals $\alpha$ that
$$x\in K_M(\alpha)
\quad\Longleftrightarrow\quad x\in M\ \land\ \mathrm{rank}(x)<\alpha.$$
If $x\in K_M(\alpha)$, choose $\beta<\alpha$ such that $x\in\InternalPowerSet{M}{K_M(\beta)}$.
Then $x\in M$ and $x\IncludedIn K_M(\beta)$. By induction every $z\in x$ has rank less than $\beta$, so
$$\mathrm{rank}(x)\le\beta<\alpha.$$
Conversely, if $x\in M$ and $\mathrm{rank}(x)<\alpha$, put $\beta:=\mathrm{rank}(x)$.
For $z\in x$, transitivity gives $z\in M$, and $\mathrm{rank}(z)<\beta$ gives $z\in K_M(\beta)$ by induction.
Thus $x\in\InternalPowerSet{M}{K_M(\beta)}\IncludedIn K_M(\alpha)$.
The equivalence identifies $K_M(\alpha)$ with $\InternalHierarchy{M}{\alpha}$.
For $\alpha\in M$, the preceding closure and value formula give the theorem, with $\theta:=\nu$.
\end{proof}

### Internal Least Fixed Points {#sec:internal-model-fixed-points}

\begin{theorem*}[\termdefine{Internal least fixed points}]
Let $M$ be transitive and satisfy Separation, and let $B,\vec p\in M$.
Suppose an external operation $\Phi$ on sets satisfies $\Phi(T)\IncludedIn B$ and is monotone:
$$S\IncludedIn T\quad\Longrightarrow\quad\Phi(S)\IncludedIn\Phi(T).$$
Suppose also that a first-order formula $\varphi$ satisfies
$$M\models\varphi(T,x,\vec p)
\quad\Longleftrightarrow\quad x\in\Phi(T)
\qquad(T\in M,\ x\in B).$$
Then the set
$$C:=\{x\in B:\forall T\in M\,
 (\Phi(T)\IncludedIn T\Longrightarrow x\in T)\}$$
belongs to $M$ and satisfies $\Phi(C)=C$. Moreover, $C$ is contained in every $T\in M$ satisfying
$\Phi(T)\IncludedIn T$.
\end{theorem*}

\begin{proof}[Proof]
For internal variables define
$$\begin{aligned}
\chi_B(T)&\;:\equiv\;\forall y\in B\,
 (\varphi(T,y,\vec p)\longrightarrow y\in T),\\
\lambda_B(x)&\;:\equiv\;x\in B\land
 \forall T\,(\chi_B(T)\longrightarrow x\in T).
\end{aligned}$$
These are first-order formulas with parameters $B,\vec p$; the model itself is not a parameter.
Transitivity and the hypothesis on $\varphi$ identify the interpretation of $\lambda_B$ with membership in $C$.
Separation gives $C\in M$. It also gives $\Phi(S)\in M$ for every $S\in M$.
Minimality follows directly from the definition of $C$.

For any $T\in M$ with $\Phi(T)\IncludedIn T$, minimality and monotonicity give
$$\Phi(C)\IncludedIn\Phi(T)\IncludedIn T.$$
Since $\Phi(C)\IncludedIn B$, it follows that $\Phi(C)\IncludedIn C$.
Monotonicity then gives $\Phi(\Phi(C))\IncludedIn\Phi(C)$.
The set $\Phi(C)$ belongs to the model, so it is itself one of the closed candidates in the definition of $C$.
Minimality gives $C\IncludedIn\Phi(C)$, proving equality. Only internal candidates were intersected;
no closure under the external power set was used.
\end{proof}

### Internal Ordinal Representations {#sec:internal-ordinal-representations}

The ordinal representation theorem in §{sec:ordinals-representation} supplies external existence and uniqueness.
Here we prove the additional assertion that the ordinal and its whole isomorphism graph belong to the model.
The construction uses internal minimality and explicit Replacement instances, rather than assuming that an
external representing map is internal.

For use inside a transitive model, we need a formula that recognizes both the representing ordinal and
the entire isomorphism graph. Let $R$ code the relation on $W$, and define
$$\begin{aligned}
\iota(W,R,\alpha,f)\;:\equiv\;&\mathrm{Ord}(\alpha)\land(f:W\to\alpha)\\
 &{}\land\forall b\in\alpha\,\exists x\in W\,
   \Pair{x}{b}\in f\\
 &{}\land\forall x,y\in W\,\forall b,c\in\alpha\\
 &\quad\bigl[(\Pair{x}{b}\in f\land\Pair{y}{c}\in f)\\
 &\qquad\longrightarrow\bigl((x=y\leftrightarrow b=c)\\
 &\hspace{7em}{}\land(\Pair{x}{y}\in R\leftrightarrow b\in c)\bigr)\bigr].
\end{aligned}$$
The ordinal, function, and pair predicates are the bounded formulas spelled out in §{sec:zfc-absoluteness}.
Thus $\iota$ is a $\Delta_0$ formula; it does not quantify over arbitrary subsets to test well-ordering.

\begin{lemma*}[\termdefine{Internal recognition of ordinal representations}]
Let $M$ be transitive and $W,R,\alpha,f\in M$. Then
$$M\models\iota(W,R,\alpha,f)$$
if and only if $\alpha$ is an actual ordinal and $f$ is an actual order-isomorphism from $\Pair{W}{R}$ onto $\alpha$.
For fixed $W,R\in M$, at most one pair $\alpha,f\in M$ satisfies this formula.
No set-theoretic axiom in $M$ is required for these assertions.
\end{lemma*}

\begin{proof}[Proof]
Transitivity makes every bounded quantifier range over the actual members of its bounding set.
The first clauses therefore say that $\alpha$ is an ordinal and $f$ is a function from $W$ onto $\alpha$.
The equality clause makes it injective, and the relation clause preserves and reflects the order.
Conversely, an actual order-isomorphism satisfies each clause with witnesses already in $M$.
For uniqueness, two such representations have equal ordinal targets by the theorem, and their graphs agree
because an ordinal has no nonidentity order-automorphism.
\end{proof}

\begin{lemma*}[\termdefine{Internal restriction of ordinal representations}]
Let $M$ be transitive and satisfy Union and Separation. Suppose $W,R,\alpha,f\in M$ and
$M\models\iota(W,R,\alpha,f)$. For each $a\in W$, put
$$D_a:=\{x\in W:\Pair{x}{a}\in R\},\qquad
  \beta_a:=f(a),\qquad g_a:=\restrict{f}{D_a}.$$
Then $D_a,\beta_a,g_a\in M$ and
$$M\models\iota(D_a,R,\beta_a,g_a).$$
Moreover, $\beta_a$ and $g_a$ are the unique internal ordinal and graph satisfying this formula
for the fixed source $D_a$ and relation $R$.
\end{lemma*}

\begin{proof}[Proof]
The bounded pair-membership formula defines $D_a$ by Separation on $W$.
The recognition lemma makes $f$ an actual order-isomorphism onto the actual ordinal $\alpha$.
Thus $\beta_a\in\alpha\in M$, and transitivity gives $\beta_a\in M$.
Graph restriction in §{sec:internal-model-closure} puts $g_a$ in $M$ using Union and Separation.

For $x\in D_a$, preservation of the order gives $f(x)\in f(a)=\beta_a$.
Conversely, if $b\in\beta_a$, transitivity of $\alpha$ gives $b\in\alpha$.
Surjectivity supplies $x\in W$ with $f(x)=b$, and reflection of the order gives
$\Pair{x}{a}\in R$. Hence $x\in D_a$.
The restriction is therefore onto $\beta_a$, remains injective, and preserves and reflects the relation.
Since a member of an ordinal is an ordinal, the recognition lemma gives the displayed internal assertion.
Its uniqueness clause proves the last assertion.
\end{proof}

#### Constructing the Internal Representation

We now construct the representing ordinal and its graph inside the model.
For $W,R\in M$ and $a\in W$, retain $D_a=\{x\in W:\Pair{x}{a}\in R\}$ and define
$$\begin{aligned}
\psi(W,R,a,\beta)\;:\equiv\;&\exists D\,\exists g\,\bigl[
  \forall x\,(x\in D\leftrightarrow
     (x\in W\land\Pair{x}{a}\in R))\\
 &\hspace{6em}{}\land\iota(D,R,\beta,g)\bigr].
\end{aligned}$$
This is a first-order formula whose set witnesses range over the model.
Transitivity identifies $D$ with the actual predecessor segment.
The recognition lemma therefore gives at most one ordinal $\beta\in M$ satisfying this formula.

\begin{lemma*}[\termdefine{Gluing internal ordinal representations}]
Let $M$ be transitive and satisfy Pairing and Replacement. Suppose $W,R\in M$, the relation coded by $R$
is a strict linear order on $W$, and
$$M\models\exists\beta\,\psi(W,R,a,\beta)\qquad(a\in W).$$
Then there are unique $\alpha,F\in M$ such that $M\models\iota(W,R,\alpha,F)$.
\end{lemma*}

\begin{proof}[Proof]
Write $aRb$ for $\Pair{a}{b}\in R$.
Let $\beta_a$ be the unique ordinal selected by $\psi$, and let $f_a:D_a\to\beta_a$ be its representation.
If $aRb$, transitivity of the order gives
$$\{x\in D_b:xRa\}=D_a.$$
Restricting the actual order-isomorphism $f_b$ to this segment gives a representation of $D_a$ onto $f_b(a)$.
Uniqueness of ordinal representations gives
$$\beta_a=f_b(a)\in\beta_b.$$
Consequently $a\mapsto\beta_a$ is injective: for distinct points, linearity makes one image belong to the other,
so equal images would contradict Foundation.
The same comparison and asymmetry of membership show
$$\beta_a\in\beta_b\quad\Longleftrightarrow\quad aRb.$$

Replacement for $\psi$ collects the values, and Replacement for its ordered-pair selector collects the graph:
$$\alpha:=\{\beta_a:a\in W\}\in M,\qquad
  F:=\{\Pair{a}{\beta_a}:a\in W\}\in M.$$
The graph construction is the definable-graph lemma in §{sec:internal-model-closure}; Pairing supplies
its ordered-pair witnesses. These are explicit Replacement instances, so no external choice of a graph in $M$
is being assumed.
The set $\alpha$ is transitive. If $\delta\in\beta_a$, surjectivity of $f_a$ gives $xRa$ with
$f_a(x)=\delta$. The compatibility just proved gives $\beta_x=f_a(x)=\delta$, hence $\delta\in\alpha$.
Every member $\beta_a$ is an ordinal. The transitive-set-of-ordinals characterization therefore makes $\alpha$
an ordinal, and the membership equivalence makes $F$ an order-isomorphism onto it.
The recognition lemma supplies the internal assertion and uniqueness. This also covers $W=\emptyset$.
\end{proof}

The remaining well-order requirement is the following first-order formula:
$$\begin{aligned}
\chi(W,R)\;:\equiv\;\forall B\,\bigl[&
 (B\IncludedIn W\land\exists b\in B\;(b=b))\\
 &\longrightarrow\exists a\in B\,\forall b\in B\;
   \Pair{b}{a}\notin R\bigr].
\end{aligned}$$
When interpreted in $M$, the variable $B$ ranges only over sets belonging to $M$.
We do not assume that every external subset of $W$ belongs to $M$.

\begin{theorem*}[\termdefine{Internal ordinal representation theorem}]
Let $M$ be transitive and satisfy Pairing, Separation, and Replacement.
Suppose $W,R\in M$, the relation coded by $R$ is a strict linear order on $W$, and $M\models\chi(W,R)$.
Then there are unique $\alpha,F\in M$ such that $M\models\iota(W,R,\alpha,F)$.
\end{theorem*}

\begin{proof}[Proof]
Separation applied to $\neg\exists\beta\,\psi(W,R,a,\beta)$ gives the set of bad points
$$B:=\{a\in W:M\models\neg\exists\beta\,\psi(W,R,a,\beta)\}\in M.$$
If it is nonempty, $M\models\chi(W,R)$ gives a least bad point $b\in B$.
The predecessor set $D_b$ belongs to $M$ by Separation.
For every $x\in D_b$, minimality gives an internal ordinal representation of $D_x$.
Transitivity of the order identifies $D_x$ with the predecessor segment of $x$ inside $D_b$.
The gluing lemma applied to $D_b$ therefore constructs an ordinal representation of $D_b$ in $M$.
It witnesses $\exists\beta\,\psi(W,R,b,\beta)$, contradicting $b\in B$.
Thus no point is bad. Apply the gluing lemma once more, now to $W$, to obtain the required representation.
Uniqueness follows from the recognition lemma.
\end{proof}

### Collection inside the Ground Model {#sec:internal-collection}

Collection bounds witnesses to a relation that need not be single-valued.
The internal cumulative stages provide such a bound without choosing one witness for each input.

\begin{lemma*}[\termdefine{Collection in transitive models}]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, and Replacement.
For every formula $\varphi(\vec p,a,b)$, parameters $\vec p$ from $M$, and $x\in M$, there is $W\in M$ such that
$$\begin{aligned}
&\forall a\in x\,\bigl[(M\models\exists b\,\varphi(\vec p,a,b))\\
&\qquad\Longrightarrow(M\models\exists b\in W\,\varphi(\vec p,a,b))\bigr].
\end{aligned}$$
The ground model need not satisfy Choice.
\end{lemma*}

\begin{proof}[Proof]
First suppose that every $a\in x$ has a witness in $M$.
Let $\vartheta(\alpha,V)$ be the defining formula for the internal cumulative stage from
§{sec:internal-model-hierarchy}. With the fixed parameters understood, put
$$\begin{aligned}
\chi(a,\alpha)\;:\equiv\;&\mathrm{Ord}(\alpha)\land
 \exists V\,\bigl(\vartheta(\alpha,V)\\
 &{}\land\exists b\in V\,\varphi(\vec p,a,b)\bigr),\\
\mu(a,\alpha)\;:\equiv\;&\chi(a,\alpha)\land\forall\beta\in\alpha\,\neg\chi(a,\beta).
\end{aligned}$$
The defining-formula theorem and transitivity show that, for $a,\alpha\in M$,
$$\begin{aligned}
&M\models\chi(a,\alpha)\\
&\quad\Longleftrightarrow\mathrm{Ord}(\alpha)\land\exists b\in M\,
 \bigl(\mathrm{rank}(b)<\alpha\\
&\hspace{8em}{}\land M\models\varphi(\vec p,a,b)\bigr).
\end{aligned}$$
If $b\in M$ is any witness, rank closure and successor closure put $\mathrm{rank}(b)+1$ in $M$.
This ordinal satisfies the right side, so the set of ordinals of $M$ satisfying $\chi(a,\alpha)$ is nonempty.
Its least member $\alpha_a$ satisfies $\mu(a,\alpha_a)$ internally.
Conversely, ordinal comparison shows that any two internal solutions of $\mu(a,\alpha)$ are equal.
Thus the least stage is uniquely defined, although the witnesses themselves need not be unique.

The first-order formula
$$\zeta(a,V)\;:\equiv\;\exists\alpha\,\bigl(\mu(a,\alpha)\land\vartheta(\alpha,V)\bigr)$$
therefore defines the unique set $V=\InternalHierarchy{M}{\alpha_a}\in M$.
Apply Replacement in $M$ to this set-valued function and then Union:
$$Y:=\{\InternalHierarchy{M}{\alpha_a}:a\in x\}\in M,\qquad W:=\bigcup Y\in M.$$
For each $a\in x$, some witness belongs to $\InternalHierarchy{M}{\alpha_a}$ and hence to $W$.
We have collected entire stages; no choice of one witness per input was used.
For the general case, first separate
$$D:=\{a\in x:M\models\exists b\,\varphi(\vec p,a,b)\}\in M.$$
Apply the total case to $D$. Inputs outside $D$ impose no condition, so the same $W$ proves the displayed assertion.
\end{proof}

## Choice and Internal Enumerations {#sec:internal-model-choice-enumerations}

A choice graph supplies the step rule for selecting successive elements of a set. An internal Hartogs bound,
which does not require Choice, bounds the length of an injective selection. Combining the two gives an ordinal
enumeration whose entire graph belongs to the model.

### Choice and Internal Selection Recursion {#sec:internal-choice-recursion}

\begin{mathmeta}
  \vars{a}{Nat}
\end{mathmeta}

To construct an internal well-order, first obtain a single choice graph for all nonempty internal subsets.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
最初に全nonempty internal subsets用のchoice graphを得る主張はinternal_subset_choiceへ、
Choice sentenceの展開と内部unionの解釈は既存のchoiceSentence・models_choice_iffへ接続した。
残る866–868行のThroughout this section以降は、この節で仮定する公理を列挙する規約で、新しい数学的結論は含まない。)
--> Throughout this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation,
and Replacement, as well as Choice.<!--
formalization: skip-end
-->  The Choice sentence says that every family $A$ of nonempty sets admits a
function graph $c:A\to\bigcup A$ with $c(a)\in a$ for every $a\in A$.
In the membership language, quantify a set $U$ satisfying $U=\bigcup A$ and use the function-graph predicate
with codomain $U$. Union and transitivity identify this witness with the actual union.

\begin{lemma*}[\termdefine{Internal subset choice}]
For every $W\in M$, the set
$$S:=\{r\in\InternalPowerSet{M}{W}:\exists z\in r\;(z=z)\}$$
belongs to $M$, and there is a function graph $c\in M$ such that
$$c:S\to W,\qquad c(r)\in r\quad(r\in S).$$
\end{lemma*}

\begin{proof}[Proof]
Internal Power Set and Separation give $S\in M$. Transitivity makes internal nonemptiness equivalent to
actual nonemptiness, so Choice in $M$ supplies a graph $c:S\to\bigcup S$ belonging to $M$.
The function-graph and membership predicates are absolute. Since every $r\in S$ is a subset of $W$,
we have $\bigcup S\IncludedIn W$, and the same graph has codomain $W$.
Only subsets belonging to $M$ are inputs to this graph.
\end{proof}

Fix this graph $c$. For any proposed preceding graph $g\in M$, let
$$r_g:=\{z\in W:z\notin\GraphRange{g}\}.$$
The range-membership predicate and Separation give $r_g\in M$, even when $g$ is not a function graph.
Define the total step rule
$$H(a,g):=\begin{cases}
c(r_g),&r_g\ne\emptyset,\\
\emptyset,&r_g=\emptyset.
\end{cases}$$
The input $a$ does not enter this rule. In the nonempty case, $r_g\in S$, so $c(r_g)$ is uniquely defined
and belongs to $r_g\IncludedIn W$. In the empty case, Infinity gives $\emptyset\in M$.
Thus $H(a,g)\in M$ for every $a,g\in M$.

For parameters $W,c$, an internal defining formula for the step is
$$\begin{aligned}
\theta(W,c,a,g,b)\;:\equiv\;\exists r\,\bigl[&
 \forall z\,(z\in r\leftrightarrow
   (z\in W\land\neg\exists t\,\Pair{t}{z}\in g))\\
 &{}\land\bigl((b\in r\land\Pair{r}{b}\in c)
       \lor(r=\emptyset\land b=\emptyset)\bigr)\bigr].
\end{aligned}$$
Here $r=\emptyset$ means $\neg\exists z\,(z\in r)$, and similarly for $b$.
The range formula identifies the internal witness $r$ with $r_g$.
If $r_g$ is nonempty, the choice graph makes the first disjunct specify exactly one $b$ and rules out the second.
If $r_g$ is empty, the first disjunct is impossible and the second specifies $b=\emptyset$.
Consequently
$$M\models\theta(W,c,a,g,b)\quad\Longleftrightarrow\quad b=H(a,g).$$

\begin{lemma*}[\termdefine{Internal selection recursion}]
For every transitive $A\in M$, there is a unique function graph $f\in M$ on $A$ satisfying
$$f(a)=H(a,\restrict{f}{a})\qquad(a\in A).$$
Whenever $r_{\restrict{f}{a}}\ne\emptyset$, its value satisfies
$$f(a)\in \SetDifference{W}{\GraphRange{\restrict{f}{a}}}.$$
\end{lemma*}

\begin{proof}[Proof]
The step is internally defined and has values in $M$, so the internal membership-recursion theorem in
§{sec:internal-model-closure} supplies the unique graph on $A$.
If the remaining set is nonempty, its selected element belongs to that set, which gives the last assertion.
\end{proof}

When $A$ is an ordinal, this recursion selects a new element at every stage with a nonempty remainder.
The bound constructed in §{sec:internal-hartogs-bound} forces a remainder to become empty.
§{sec:internal-choice-enumerations} then cuts the graph at the first such stage to obtain an enumeration
of all of $W$.

### An Internal Hartogs Bound {#sec:internal-hartogs-bound}

\begin{theorem*}[\termdefine{Internal Hartogs bound}]
Let $M$ be transitive and satisfy Pairing, Union, Power Set, Separation, and Replacement.
For every $W\in M$, there is an ordinal $H\in M$ such that no injection from $H$ into $W$ has its graph in $M$.
This assertion requires no Choice axiom in $M$.
\end{theorem*}

\begin{proof}[Proof]
Use the internal ordinal-representation predicate $\iota$ from §{sec:internal-ordinal-representations} and define
$$\tau(q,\alpha)\;:\equiv\;\exists D\,\exists R\,\exists g\,
 \bigl(q=\Pair{D}{R}\land\iota(D,R,\alpha,g)\bigr).$$
If two pairs of witnesses represent the same $q$, injectivity of ordered-pair coding makes their domains
and relations equal. Uniqueness of ordinal representations then makes their ordinal targets equal.
Thus each $q\in M$ has at most one internal target $\alpha$ satisfying $\tau(q,\alpha)$.

Products and internal power sets give
$$C:=\InternalPowerSet{M}{W}\times\InternalPowerSet{M}{W\times W}\in M.$$
Separation and Replacement now give
$$\begin{aligned}
B&:=\{q\in C:M\models\exists\alpha\,\tau(q,\alpha)\}\in M,\\
T&:=\{\alpha_q:q\in B\}\in M,
\end{aligned}$$
where $\alpha_q$ is the unique internal ordinal specified by $\tau$.
Every member of $T$ is an actual ordinal, by the recognition lemma for $\iota$.
In particular, whenever $D,R,\alpha,g\in M$ satisfy
$$D\IncludedIn W,\qquad R\IncludedIn W\times W,\qquad
 M\models\iota(D,R,\alpha,g),$$
the code $\Pair{D}{R}$ belongs to $B$, so $\alpha\in T$.
The construction uses only internal power sets and a single-valued defining formula; it assumes neither
that every external subset belongs to $M$ nor that witnesses can be chosen uniformly in $M$.

Put
$$H:=T\cup\bigcup T\in M.$$
This is a transitive set of ordinals. Indeed, a member of $T$ is an ordinal, and a member of $\bigcup T$
is a member of such an ordinal. If $y\in H$ and $z\in y$, then either $y\in T$, which puts $z$ in $\bigcup T$,
or $y\in\alpha\in T$, in which case transitivity of $\alpha$ again puts $z$ in $\bigcup T$.
Thus $H$ is an ordinal. Also, every $\alpha\in T$ belongs to $H$, so $H$ strictly bounds all the represented
types just collected.

Suppose, toward a contradiction, that $j\in M$ is the graph of an injection $j:H\to W$.
Range closure gives $D:=\GraphRange{j}\in M$ and $D\IncludedIn W$.
Construct the transported relation and the inverse graph by
$$\begin{aligned}
R:=\{\Pair{x}{y}\in D\times D:\exists a\,\exists b\,
  (&\Pair{a}{x}\in j\land\Pair{b}{y}\in j\\
   &{}\land a\in b)\},\\
g:=\{\Pair{x}{a}\in D\times H:&\ \Pair{a}{x}\in j\}.
\end{aligned}$$
These sets belong to $M$ by product closure and Separation.
For complete first-order formulas, replace each displayed ordered pair by a variable $q$ and existentially
quantify its two coordinates, using the predicate $q=\Pair{x}{y}$ or $q=\Pair{x}{a}$.
Every coordinate of a pair in $j$ belongs to $\bigcup\bigcup j\in M$.
Transitivity therefore puts all witnesses in $M$, and the internal formulas define exactly these sets.

Injectivity of $j$ makes $g:D\to H$ a function, and every element of $H$ occurs as one of its values.
For $x,y\in D$, write $x=j(a)$ and $y=j(b)$ with the uniquely determined $a,b\in H$.
Then
$$x=y\quad\Longleftrightarrow\quad a=b,\qquad
 \Pair{x}{y}\in R\quad\Longleftrightarrow\quad a\in b.$$
Hence $g$ is an order-isomorphism and the recognition lemma gives $M\models\iota(D,R,H,g)$.
Since $R\IncludedIn D\times D\IncludedIn W\times W$, the collection property gives $H\in T\IncludedIn H$.
This contradicts $H\notin H$ and proves the bound.
\end{proof}

### From Choice to Internal Ordinal Enumerations {#sec:internal-choice-enumerations}

\begin{theorem*}[\termdefine{Internal ordinal enumeration from Choice}]
Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set, Separation, Replacement, and Choice.
For every $W\in M$, there are an ordinal $\gamma\in M$ and a bijection $e:\gamma\to W$ whose graph belongs to $M$.
Moreover, there are $R,g\in M$ such that $g$ is the inverse graph of $e$, $R\IncludedIn W\times W$, and
$$M\models\iota(W,R,\gamma,g).$$
Thus $R$ well-orders $W$, with its ordinal representation also in the model.
\end{theorem*}

\begin{proof}[Proof]
Take the choice graph $c$ from §{sec:internal-choice-recursion} and the internal Hartogs bound $H$ for $W$.
Internal selection recursion on $H$ gives a function graph $f\in M$.
Suppose the remaining set
$$r_\beta:=\{z\in W:z\notin\GraphRange{\restrict{f}{\beta}}\}$$
is nonempty for every $\beta\in H$. Then $f(\beta)\in W$ at every stage.
If $\alpha\in\beta\in H$, the earlier value $f(\alpha)$ belongs to
$\GraphRange{\restrict{f}{\beta}}$, whereas $f(\beta)$ does not.
The linearity of membership on ordinals therefore makes $f:H\to W$ injective.
Its graph belongs to $M$, contradicting the defining property of $H$.

There is consequently a least $\gamma\in H$ with $r_\gamma=\emptyset$.
Transitivity gives $\gamma\in M$, and graph restriction gives
$$e:=\restrict{f}{\gamma}\in M.$$
Every earlier remainder is nonempty. Thus all values of $e$ lie in $W$, and the same comparison of stages
shows that $e$ is injective. The equality $r_\gamma=\emptyset$ says that every element of $W$ already occurs
in this graph, so $e$ is onto $W$.
This proves the asserted internal ordinal enumeration, including the case of an empty set.

Finally, repeat the transported-relation and inverse-graph construction from the Hartogs proof with $j=e$.
Its range is now all of $W$, and its domain is $\gamma$.
It gives $R\IncludedIn W\times W$ and $g=e^{-1}$, both belonging to $M$.
The graph $g$ is an order-isomorphism from $\Pair{W}{R}$ onto $\gamma$; internal recognition gives the displayed
assertion. This connects the enumeration directly to the ordinal-representation predicate used in
§{sec:internal-ordinal-representations}.
\end{proof}

