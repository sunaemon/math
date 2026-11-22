# Appendix: Lambda Calculus and Computability {#sec:appendix-lambda-computability}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
本全体で採用する計算概念・用語の規約とChurch–Turing thesisを区別する導入。数値出力の実際の意味はnumericalValue、
有限arityの部分関数はComputesPartial/LambdaComputable、queryはOracleStepで定義し、
他モデルとの同値を本書内の局所証明とは扱わない。)
--> This appendix fixes the concrete \termdefine{computability} convention used in
§{sec:cauchy-representation-admissibility}, §{sec:effective-dst}, §{sec:domain-theory-quasi-polish}, and
§{sec:effective-topos}. The computational syntax throughout the book is \termdefine{lambda calculus}. A numerical
computation is a finite reduction of a lambda term to a numeral. Type-Two computation additionally permits queries to
the input name, passed as a function argument. The words "recursive," "computable," "partial recursive," and "realized
by a program" refer to lambda-definable partial functions in this convention. Comparisons with other formal models are
external background, not prerequisites for the constructions below. The Church--Turing thesis is the separate assertion
that a formal notion of computation captures intuitive effective calculability.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
3つの計算付録の依存順序と内容への案内。個々のlambda構成は後続の対応対象で、ここで別のrealizerを追加したとは扱わない。)
--> The three computational appendices share this convention. This appendix develops syntax, numerical data, program
indices, and universal evaluation. §{sec:appendix-type-two-computation} adds input names, query reduction,
and represented-space realizers. §{sec:appendix-effective-computations} collects the programs
used in effective descriptive set theory. The latter two appendices use the foundations established here; they do not
require §{sec:computable-polish-tte} as a prerequisite.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Turing完全性という古典的な他モデル比較を踏まえた動機付け。比較の文献は同章のBarendregt/Sipserで指定され、
本書のuniversal lambda評価や停止問題の実証明とは区別する。別の機械モデルへのsimulationを形式化済みとはしない。)
--> The untyped lambda calculus supplies Turing-complete partial computation and therefore supports
\termforwardas{universal program}{universal programs}, partiality, recursively enumerable sets, and the
\termforward{halting problem}.<!--
formalization: skip-end
-->

## Untyped lambda calculus {#sec:lambda-calculus}
\index{lambda calculus!untyped}

### Terms and Capture-Avoiding Substitution {#sec:lambda-terms-substitution}

Fix countably infinitely many variables $x,y,z,\ldots$ in an effective order. We use $M,N,P,\ldots$ as
metavariables ranging over lambda terms. The
\termdefineas{lambda term}{lambda terms} are defined recursively:

*   Every variable $x$ is a lambda term.
*   If $M$ and $N$ are lambda terms, then $(MN)$ is a lambda term, called
    \termdefineas{lambda application}{application}.
*   If $x$ is a variable and $M$ is a lambda term, then $(\lambdaab{x}{M})$ is a lambda term, called
    \termdefineas{lambda abstraction}{abstraction}.
*   Nothing else is a lambda term.

Equivalently, in EBNF summary form,
$$
\textit{Term} ::= \textit{Var} \mid (\textit{Term}\ \textit{Term}) \mid (\lambdaab{\textit{Var}}{\textit{Term}}).
$$

<!--
formalization: skip-begin (引用・背景説明・読書案内:
印刷されたlambda式の省略記法と優先順位・結合規約。実際の構文はTermのvar/app/lamで明示し、
パーサの正当性定理をこの記法の説明から要求しない。)
--> The formal grammar is fully parenthesized. In ordinary notation, lambda abstraction has lowest priority, while
application has higher priority and associates to the left. Thus $MNP$ means $((MN)P)$, not $(M(NP))$, while
$\lambdaab{x}{MN}$ means $(\lambdaab{x}{(MN)})$, not $((\lambdaab{x}{M})N)$.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \vars{x,y,z,M,N,P,A,B,R,S,V}{lambda-term}
  \inferbinder{\lambdaab}{lambda-term}
  \inferjuxtaposed{lambda-term}
  \define{FreeVarsLambda}
\end{mathmeta}

\begin{mathmeta}
  \define{SubstLambda}
\end{mathmeta}

Free variables are defined recursively by
$$\begin{aligned}
\FreeVars{x} &= \{x\},\\
\FreeVars{MN} &= \FreeVars{M}\cup\FreeVars{N},\\
\FreeVars{\lambdaab{x}{M}} &= \SetDifference{\FreeVars{M}}{\{x\}}.
\end{aligned}$$

We first define capture-avoiding substitution on named terms. For a term $N$ substituted for a variable $x$, the clauses
for $M\subst{x}{N}$ are:
$$\begin{aligned}
y\subst{x}{N}
&:=
\begin{cases}
N & \text{if } y=x,\\
y & \text{if } y\ne x,
\end{cases}\\
(MP)\subst{x}{N}
&:= (M\subst{x}{N})(P\subst{x}{N}),\\
(\lambdaab{y}{M})\subst{x}{N}
&:=
\begin{cases}
\lambdaab{y}{M}
    & \text{if } y=x,\\
\lambdaab{y}{(M\subst{x}{N})}
    & \text{if } y\ne x \text{ and } y\notin\FreeVars{N},\\
\lambdaab{z}{\bigl(M\subst{y}{z}\subst{x}{N}\bigr)}
    & \text{if } y\ne x \text{ and } y\in\FreeVars{N},
\end{cases}
\end{aligned}$$
where in the last case $z$ is the first variable not in $\FreeVars{M}\cup\FreeVars{N}\cup\{x\}$. The last clause is the
hygiene step: before $N$ is moved under a binder whose variable occurs free in $N$, that binder is renamed to the fresh
variable $z$.

\begin{lemma*}[\termdefineas{Termination of capture-avoiding substitution}{Termination of capture-avoiding
substitution}]
The displayed clauses define a total substitution operation on finite named terms. Replacing a variable by a variable
preserves the number of nodes in the syntax tree. A recursive depth bound equal to the original number of nodes
suffices, and every larger bound gives the same result.
\end{lemma*}

\begin{proof}[Proof]
First evaluate the clauses with a finite depth budget. At budget zero, temporarily return the input term; at a positive
budget, use the displayed clause and decrease the budget by one for each recursive call. In the renaming branch, both
the inner renaming call and the subsequent substitution call receive this smaller budget. This bounded procedure is
defined by ordinary recursion on the budget.

For a variable replacement, induction on the budget shows that the output has the same number of nodes as the input:
variables remain variables, applications retain their two branches, and abstractions retain one binder node. In the
renaming branch this assertion applies to both recursive calls. It holds even at budget zero.

Now compare two budgets that are each at least the number of nodes of the input term. Induct on the smaller budget. The
variable case is immediate, and each proper subterm of an application or abstraction has fewer nodes. In the renaming
branch, first apply the induction hypothesis to the body with a variable replacement. The resulting bodies agree and
have exactly the original body's node count. Apply the induction hypothesis again to this renamed body with the intended
replacement. Both calls have sufficient smaller budgets, so their results agree as well. Thus the bounded procedures
stabilize, and choosing the original node count gives a total operation satisfying precisely the displayed clauses. This
also explains why recursion merely on literal subterms would not justify the renaming branch.
\end{proof}

\begin{lemma*}[\termdefineas{Free variables under lambda substitution}{Free variables under substitution}]
For finite named terms,
$$
\FreeVarsLambda{\SubstLambda{M}{x}{N}}=
\begin{cases}
\SetDifference{\FreeVarsLambda{M}}{\{x\}}\cup\FreeVarsLambda{N},
  & x\in\FreeVarsLambda{M},\\
\FreeVarsLambda{M}, & x\notin\FreeVarsLambda{M}.
\end{cases}
$$
\end{lemma*}

\begin{proof}[Proof]
Induct using the node-count bound from the preceding lemma. For a variable, check whether it is the variable being
replaced; for an application, take the union of the two free-variable sets. Under an abstraction binding the variable
being replaced, substitution stops. Under any other binder whose variable is absent from the replacement's free-variable
set, remove that binder variable after applying the induction hypothesis to the body.

In the remaining branch, let $y$ be the old binder and $z$ the fresh variable. The induction hypothesis applies to the
variable substitution in the body, which removes the free occurrences of $y$ and replaces them by occurrences of $z$.
The renamed body's node count is unchanged, so the hypothesis also applies to the subsequent substitution. Since $z$ is
absent from the free-variable sets of both the original body and the replacement, and differs from $x$, the final
abstraction binds only the renamed occurrences. The replacement's free variables remain free. These cases give the
stated formula, including the case where the replaced variable was absent.
\end{proof}

For example, if $x\ne y$ and $z$ is the first variable outside $\{x,y\}$, then
$$
\SubstLambda{(\lambdaab{y}{x})}{x}{y}=\lambdaab{z}{y}.
$$
The occurrence of $y$ introduced by the substitution remains free; returning $\lambdaab{y}{y}$ would capture it.

### Alpha-Equivalence {#sec:lambda-alpha-equivalence}

\begin{mathmeta}
  \define{AlphaEquivalent}
\end{mathmeta}

Define \termdefine{alpha-equivalence}, written $\AlphaEquivalent{M}{N}$, as the least equivalence relation preserved by
application and abstraction and containing the fresh binder renamings
$$\AlphaEquivalent{\lambdaab{x}{M}}{\lambdaab{z}{(\SubstLambda{M}{x}{z})}},
\qquad z\notin\FreeVarsLambda{M}.$$
Thus a bound variable may be renamed inside any subterm, provided substitution avoids capture. Alpha-equivalence records
a finite sequence of such changes, used in either direction.

\begin{proposition*}[\termdefineas{Invariants of binder renaming}{Invariants of binder renaming}]
Alpha-equivalent terms have the same free variables, the same number of syntax-tree nodes, and the same outer
constructor. One contains a beta-redex if and only if the other does.
\end{proposition*}

\begin{proof}[Proof]
Induct on the derivation of alpha-equivalence. Reflexivity, symmetry and transitivity preserve each assertion. The
application and abstraction cases follow from the corresponding assertions for their immediate subterms. For one
generating renaming, the free-variable formula for substitution and the freshness of $z$ give the same free variables
after abstraction. Substitution of a variable for a variable preserves node count. It also preserves the outer
constructor of every subterm, even when it must rename an inner binder to avoid capture. This follows by induction on
the substitution budget: the renaming branch makes two variable-for-variable calls on smaller budgets. Hence an
application has an abstraction as its operator before the renaming exactly when it does afterwards. This proves
preservation of redex-freeness and completes the induction.
\end{proof}

\begin{mathmeta}
  \define{LambdaNameCorrespondence,LambdaBoundNames}
\end{mathmeta}

To compare named terms, keep a relation $R$ between the variable names on the two sides. Upon entering abstractions with
binders $x,y$, replace it by the relation
$$\begin{aligned}
\LambdaBoundNames{R}{x}{y}(a,b)
&\Longleftrightarrow (a=x\ \land\ b=y)\\
&\qquad\lor\bigl(a\ne x\ \land\ b\ne y\ \land\ R(a,b)\bigr).
\end{aligned}$$
The two bound names now correspond to each other; their previous correspondences are hidden by these binders.

Write $\LambdaNameCorrespondence{R}{M}{N}$ for the comparison defined recursively on the original named terms by
$$\begin{aligned}
\LambdaNameCorrespondence{R}{a}{b}&\Longleftrightarrow R(a,b),\\
\LambdaNameCorrespondence{R}{MP}{NQ}&\Longleftrightarrow
 \LambdaNameCorrespondence{R}{M}{N}\ \land\ \LambdaNameCorrespondence{R}{P}{Q},\\
\LambdaNameCorrespondence{R}{\lambdaab{x}{M}}{\lambdaab{y}{N}}
 &\Longleftrightarrow\LambdaNameCorrespondence{\LambdaBoundNames{R}{x}{y}}{M}{N}.
\end{aligned}$$
Terms with different outer constructors do not correspond. In particular, the equality relation on names compares free
names literally while allowing corresponding bound names to differ.

\begin{lemma*}[\termdefineas{Named-term comparison}{Comparison of named terms}]
Two named terms satisfy $\AlphaEquivalent{M}{N}$ if and only if $\LambdaNameCorrespondence{=}{M}{N}$. More generally, if
the relation $R$ is decidable, then $\LambdaNameCorrespondence{R}{M}{N}$ is decidable for all finite terms.
\end{lemma*}

\begin{proof}[Proof]
First observe by induction that a comparison uses the relation only on the free-variable sets of its two terms. Every
free name on either side has a corresponding free name on the other. The comparison with equality is reflexive and
symmetric. Composition of comparisons follows by induction: beneath abstractions, the intermediate name is either bound
on both sides or free on both sides. These cases give the extended composite relation. In particular, comparison with
equality is transitive.

The key renaming step is the following. Suppose $\LambdaNameCorrespondence{R}{M}{N}$ and, for free names $a$ of $M$ and
$b$ of $N$, the implication
$$\begin{aligned}
R(a,b)\ \land\ a=x&\ \Longrightarrow\ S(z,b),\\
R(a,b)\ \land\ a\ne x&\ \Longrightarrow\ S(a,b)
\end{aligned}$$
holds. Then $\LambdaNameCorrespondence{S}{\SubstLambda{M}{x}{z}}{N}$. Induct on a node-count bound for $M$, allowing
both relations to vary. Variables and applications follow from the substitution clauses. Under an abstraction binding
$x$, substitution stops, and the extended relation masks $x$. Under any other binder different from $z$, apply the
induction hypothesis to the body. If the binder is $z$, substitution first renames it to a fresh variable. Apply the
induction hypothesis to that variable renaming, then again to replacement of $x$ by $z$. Both calls concern bodies with
the original body's node count. Freshness ensures that the newly chosen name has no pre-existing free occurrence, so
only the intended bound-name correspondence changes. This proves the claim, and the symmetric claim applies on the
right.

Apply this renaming step to a pair of corresponding abstraction bodies. A fresh change of one binder preserves the
comparison when its recorded name is changed at the same time. Hence every generating alpha-renaming, and therefore
every alpha-equivalence derivation, preserves comparison with equality. Conversely, induct on a node-count bound for two
terms that compare with equality. Variables agree, and applications reduce to their component comparisons. For
abstractions, choose one name fresh for both bodies and rename both binders to it. The renaming step makes the two
renamed bodies compare with equality. Their node counts are unchanged, so the induction hypothesis gives
alpha-equivalence of the bodies. Lift through their common abstraction and undo the two binder renamings. This proves
the converse.

Finally, the displayed comparison rules give a terminating decision procedure. Compare the outer constructors; at
variables test the current relation, at applications compare both components, and at abstractions extend the relation
and compare the bodies. Extending a decidable relation remains decidable. Every recursive call concerns a proper subterm
of the first term, so its node count decreases.
\end{proof}

\begin{lemma*}[\termdefineas{Substitution under corresponding names}{Substitution of related terms}]
Suppose $\LambdaNameCorrespondence{R}{M}{M'}$ and $\LambdaNameCorrespondence{S}{N}{N'}$. Assume that, whenever $R(a,b)$
holds,
$$a=x\ \Longleftrightarrow\ b=y,\qquad
 a\ne x\ \Longrightarrow\ S(a,b).$$
Then
$$\LambdaNameCorrespondence{S}{\SubstLambda{M}{x}{N}}{\SubstLambda{M'}{y}{N'}}.$$
\end{lemma*}

\begin{proof}[Proof]
Induct on a node-count bound for $M$, allowing the terms and relations to vary. If $x$ is not free in $M$, the
correspondence of free names and the first hypothesis imply that $y$ is not free in $M'$. Substitution for an absent
variable changes a term only by binder renaming: this follows directly from the substitution clauses by induction on
node count, undoing any fresh binder renaming after applying the induction hypothesis to its body. Thus both
substitutions preserve comparison, and the second hypothesis changes the comparison relation from $R$ to $S$. At
variables that are replaced, use the given comparison of $N,N'$; at other variables use the second hypothesis.
Applications follow from the two induction hypotheses.

It remains to consider abstractions when the variables being replaced occur freely. Neither binder is then the variable
being replaced. On each side inspect the existing substitution clause: retain the binder if it is absent from the
replacement's free variables, and otherwise rename it to the fresh variable chosen by that clause. The preceding
renaming step transports the body comparison to the resulting pair of binders. Both resulting binders are distinct from
the variables being replaced and absent from their respective replacement terms. Hence the comparison of the
replacements remains valid under the extended relation. The two hypotheses on the variable relations remain valid as
well: the two bound names correspond to each other and are not replaced, while every free-name pair satisfies the
original hypotheses. Apply the induction hypothesis to the two bodies and restore the abstractions. Variable renaming
preserves body size, so this recursive call has a smaller bound.
\end{proof}

\begin{samepage}

\begin{theorem*}[\termdefineas{Alpha-equivalence and binder renaming}{Alpha-equivalence by renaming}]
Alpha-equivalence is decidable and is preserved by capture-avoiding substitution. More precisely,
$\AlphaEquivalent{M}{M'}$ and $\AlphaEquivalent{N}{N'}$ imply
$$
\AlphaEquivalent{\SubstLambda{M}{x}{N}}{\SubstLambda{M'}{x}{N'}}.
$$
In particular, different choices of a fresh binder give alpha-equivalent results.
\end{theorem*}

\end{samepage}

\begin{proof}[Proof]
By \termuse{Named-term comparison}, alpha-equivalence is comparison under equality of free names, so it is decidable.
Apply \termuse{Substitution under corresponding names} with both variable relations equal to equality and with the same
variable replaced on both sides. The hypotheses hold, and the conclusion gives the asserted alpha-equivalence after
substitution. For two choices of a fresh binder, both resulting abstractions are alpha-equivalent to the original one by
a generating renaming. Symmetry and transitivity give their alpha-equivalence.
\end{proof}

### Beta-Reduction and Substitution Laws {#sec:lambda-beta-substitution}

From now on, terms are identified under alpha-equivalence. A term with no free variables is
\termdefineas{closed lambda term}{closed}. A one-step
\termdefine{beta-reduction} is
the least relation $\to_\beta$ on lambda terms satisfying the following rules:
$$
\dfrac{}{\;(\lambdaab{x}{B})A \to_\beta B\subst{x}{A}\;}\;(\beta)
$$
and the context-closure rules
$$
\dfrac{R\to_\beta R'}{RS\to_\beta R'S}\;(\mathrm{App}_L)
\qquad
\dfrac{S\to_\beta S'}{RS\to_\beta RS'}\;(\mathrm{App}_R)
\qquad
\dfrac{B\to_\beta B'}{\lambdaab{x}{B}\to_\beta \lambdaab{x}{B'}}\;(\lambda).
$$
The rule $(\beta)$ contracts an actual redex and uses the capture-avoiding substitution just defined. The context rules
say that the outermost term need not itself have the form $(\lambdaab{x}{B})A$: a beta step may occur in the left side
of an application, in the right side of an application, or in the body of an abstraction. The reflexive transitive
closure of $\to_\beta$ is written $\to_\beta^*$.

\begin{lemma*}[\termdefineas{Beta-reduction on alpha-classes}{Beta-reduction on alpha-classes}]
Application, abstraction with a specified binder, substitution, and free-variable sets are well-defined on
alpha-equivalence classes. If $\AlphaEquivalent{\lambdaab{x}{M}}{\lambdaab{y}{M'}}$ and $\AlphaEquivalent{N}{N'}$, then
$$
\AlphaEquivalent{\SubstLambda{M}{x}{N}}{\SubstLambda{M'}{y}{N'}}.
$$
The displayed beta rules define a relation on these classes. A one-step reduction between classes exists exactly when
some named representatives admit a one-step reduction by the same rules.
\end{lemma*}

\begin{proof}[Proof]
Compatibility with alpha-equivalence allows the operations and free-variable sets to descend to classes. If two named
abstractions are alpha-equivalent, their bodies compare under the relation that pairs their bound names and equates all
other free names. Apply \termuse{Substitution under corresponding names} to these bodies and the two alpha-equivalent
arguments, with equality as the output relation. The paired bound names are exactly the names being replaced, and every
other corresponding pair is equal. The conclusion states that the two contracta compare with equality, hence are
alpha-equivalent. Thus contraction is independent of both the binder name and the chosen representatives.

Generate reduction on classes by the contraction and context rules using these quotient operations. Every named
reduction projects to such a reduction by induction on its derivation. Conversely, a contraction of classes is witnessed
by representatives of its body and argument. For each application context, take the representatives supplied by the
induction hypothesis for the reduced side and any representative of the other side. For an abstraction context, put the
specified binder around the two representatives supplied by the hypothesis. This proves the converse by induction on the
derivation of a class reduction. Hence the rules introduce precisely named reductions modulo alpha-equivalence.
\end{proof}

\begin{samepage}

\begin{lemma*}[\termdefineas{Substitution laws on alpha-classes}{Substitution laws on alpha-classes}]
The following equalities hold after identifying alpha-equivalent terms. If $x\notin\FreeVarsLambda{M}$, then
$\SubstLambda{M}{x}{N}=M$. If $x\ne y$ and $x\notin\FreeVarsLambda{P}$, then
$$
\SubstLambda{\SubstLambda{M}{x}{N}}{y}{P} =
\SubstLambda{\SubstLambda{M}{y}{P}}{x}{\SubstLambda{N}{y}{P}}.
$$
If $y\ne x$ and $y\notin\FreeVarsLambda{N}$, then
$$
\SubstLambda{(\lambdaab{y}{M})}{x}{N}
=\lambdaab{y}{(\SubstLambda{M}{x}{N})}.
$$
\end{lemma*}

\end{samepage}

\begin{proof}[Proof]
For the first identity, induct on the number of nodes of a named representative. Variables and applications follow from
the substitution clauses. For an abstraction whose binder is the variable being replaced, substitution stops. For any
other abstraction, the variable is absent from its body. If the binder must be renamed to avoid capture, the renamed
body still lacks that variable and has the same number of nodes as the original body. Apply the induction hypothesis to
that body and then undo the binder renaming up to alpha-equivalence. This gives the identity in every case. The
abstraction formula follows directly from the substitution clause when the stated freshness conditions hold.

For the composition identity, induct on a node-count bound for a named representative of $M$. At the variable $x$, both
sides give $\SubstLambda{N}{y}{P}$. At the variable $y$, both sides give $P$, since $x$ does not occur freely in $P$. At
any other variable, both sides leave it unchanged. The application case follows from the two induction hypotheses. For
an abstraction, first rename its binder to a variable different from $x,y$ and absent from the free-variable sets of
$N$, $P$ and $\SubstLambda{N}{y}{P}$. The renamed body has the original body's node count. Move each substitution under
this common binder by the abstraction formula, apply the induction hypothesis to the body, and restore the abstraction.
Thus the argument uses only named terms and capture-avoiding renaming.
\end{proof}

\begin{samepage}

\begin{theorem*}[\termdefineas{Substitution and finite beta-reduction}{Substitution and finite beta-reduction}]
On alpha-classes, $M\to_\beta M'$ implies
$$
\SubstLambda{M}{x}{N}\to_\beta\SubstLambda{M'}{x}{N}.
$$
More generally, if $M\to_\beta^*M'$ and $N\to_\beta^*N'$, then
$$
\SubstLambda{M}{x}{N}\to_\beta^*\SubstLambda{M'}{x}{N'}.
$$
\end{theorem*}

\end{samepage}

\begin{proof}[Proof]
For the first assertion, strengthen the claim to any finite list of substitutions, applied from left to right, and
induct on the derivation of the beta step. Consider a contraction at the root. For one substitution, rename the redex's
binder to a variable absent from the body's and replacement's free-variable sets and different from the variable being
replaced. The abstraction formula moves substitution under this binder. The composition formula then identifies the new
contractum with the substituted old contractum. Thus one substitution takes a root redex to a root redex with the
required contractum. Iterating this observation proves the root case for a finite list.

Application contexts follow because the list distributes over both sides of an application. In an abstraction context,
choose a common binder absent from both bodies' free-variable sets, from every replacement's free-variable set, and from
every variable replaced by the list. Only finitely many names are excluded. Rename both bodies to this binder and move
the whole list under it. The induction hypothesis applies to the list obtained by first performing this renaming and
then performing the original list. Its conclusion lifts through the common abstraction. This is the reason for
strengthening the induction hypothesis to lists: an arbitrary fresh renaming must be allowed before the intended
substitution. The singleton list proves the first assertion, and induction on the length of a reduction proves its
finite-step version with a fixed replacement.

It remains to reduce the replacement itself. Fix $N\to_\beta^*N'$ and induct on a node-count bound for a named
representative of $M$. At the variable $x$, use the given reduction; at any other variable, use zero steps. For an
application, reduce the inserted copies in one branch and then in the other, using the two context rules. For an
abstraction, choose one binder fresh for its body, both replacements, and $x$. Rename to this binder and move
substitution under it on both sides. The renamed body has the original body's node count, so the induction hypothesis
applies and its reduction lifts through the abstraction. This proves
$$
\SubstLambda{M}{x}{N}\to_\beta^*\SubstLambda{M}{x}{N'}.
$$
There may be several copies of the replacement, or none, so a finite reduction is required here.

\begin{samepage}

Finally, first reduce $M$ to $M'$ while keeping $N$ fixed, then reduce the copies of $N$ to $N'$ in the resulting
substitution. Transitivity gives the asserted joint reduction.

\end{samepage}
\end{proof}

### Confluence and Uniqueness of Outputs {#sec:lambda-confluence}

\begin{mathmeta}
  \define{ParallelBeta,BetaConvertible}
\end{mathmeta}

\begin{samepage}

To prove that a computed value is unique, we introduce \termdefine{parallel beta-reduction}. This is the least relation
$\ParallelBeta{M}{N}$ satisfying
$$\begin{gathered}
\dfrac{}{\ParallelBeta{x}{x}},\qquad
\dfrac{\ParallelBeta{M}{M'}\quad\ParallelBeta{N}{N'}}{\ParallelBeta{MN}{M'N'}},\\[6pt]
\dfrac{\ParallelBeta{M}{M'}}{\ParallelBeta{\lambdaab{x}{M}}{\lambdaab{x}{M'}}},\qquad
\dfrac{\ParallelBeta{M}{M'}\quad\ParallelBeta{N}{N'}}{\ParallelBeta{(\lambdaab{x}{M})N}{\SubstLambda{M'}{x}{N'}}}.
\end{gathered}$$
All these rules act on alpha-classes. The application rule may retain a redex at the root, whereas the last rule
contracts it after reducing the body and argument in parallel. Induction on a named representative gives
$\ParallelBeta{M}{M}$ for every term.

\end{samepage}

\begin{lemma*}[\termdefineas{Parallel reduction and substitution}{Parallel reduction and substitution}]
If $\ParallelBeta{M}{M'}$ and $\ParallelBeta{N}{N'}$, then
$$
\ParallelBeta{\SubstLambda{M}{x}{N}}{\SubstLambda{M'}{x}{N'}}.
$$
Parallel reduction introduces no new free variables. Moreover,
$$
M\to_\beta N\quad\Longrightarrow\quad\ParallelBeta{M}{N}
\quad\Longrightarrow\quad M\to_\beta^*N.
$$
Consequently, finite parallel reductions and finite beta-reductions have the same endpoints.
\end{lemma*}

\begin{proof}[Proof]
First, induction on a parallel derivation proves inclusion of free-variable sets. In the contraction rule, use the
free-variable formula for substitution and the inclusions for the body and argument. The other rules use unions and
deletion of the binder variable.

For substitution, strengthen the assertion to two finite lists of substitutions. Apply each list from left to right, and
assume that the final image of every variable under the first list reduces in parallel to its final image under the
second. Induct on the parallel derivation. The variable case is the assumption, and application distributes over both
lists.

At an abstraction, choose one binder fresh for both bodies, every replacement in both lists, and every variable replaced
by either list. Rename both bodies to this binder, and prepend that same variable renaming to both lists. The assumption
on final variable images still holds: the old binder variable is sent to the final image of the new variable, and every
other variable keeps its old image. The induction hypothesis therefore compares the renamed and substituted bodies. Move
both lists under the fresh binder and apply the abstraction rule.

At a contraction, use the same fresh renaming for the original and reduced bodies. The induction hypotheses compare the
substituted bodies and the substituted arguments. Repeated use of the substitution composition law moves the fresh
binder's substitution past the second list; freshness holds for each entry of that list. Thus the contraction rule
produces exactly the second list applied to the original contractum. Singleton lists give the asserted substitution
property.

Every beta step is parallel: use reflexivity on the unchanged parts of a root contraction and then lift through
contexts. Conversely, induct on a parallel derivation. Application and abstraction lift the finite beta-reductions
supplied by the induction hypotheses. For a parallel contraction, first reduce the body under its binder and reduce the
argument, then perform one root contraction. Concatenating these finite reductions proves the last assertion.
\end{proof}

\begin{samepage}

\begin{lemma*}[\termdefineas{Parallel abstraction inversion}{Parallel abstraction inversion}]
If $\ParallelBeta{\lambdaab{x}{M}}{Q}$, then there is a term $M'$ with
$$
Q=\lambdaab{x}{M'},\qquad \ParallelBeta{M}{M'}.
$$
The binder $x$ may be prescribed in advance, even when the derivation uses a different representative of the
abstraction.
\end{lemma*}

\end{samepage}

\begin{proof}[Proof]
Binder renaming preserves the outer constructor, so a variable, an application and an abstraction belong to distinct
alpha-classes. Hence the last rule must be an abstraction rule. Write its source and target as $\lambdaab{y}{N}$ and
$\lambdaab{y}{N'}$, where $\ParallelBeta{N}{N'}$. If $y=x$, equality of the source abstractions implies equality of
their bodies: substitute the variable $x$ into both bodies, using independence of contraction from the binder name and
the identity substitution. The assertion follows.

Suppose $y\ne x$. Since $\lambdaab{y}{N}=\lambdaab{x}{M}$, their free-variable sets agree. The right-hand side has no
free $x$, so $x\notin\FreeVarsLambda{N}$; otherwise $x$ would remain free on the left. Parallel reduction introduces no
new free variables, hence also $x\notin\FreeVarsLambda{N'}$. Rename both binders from $y$ to $x$. Equality of
abstractions with this fixed binder gives $\SubstLambda{N}{y}{x}=M$. The parallel substitution lemma gives
$$
\ParallelBeta{\SubstLambda{N}{y}{x}}{\SubstLambda{N'}{y}{x}}.
$$
Choose $M'=\SubstLambda{N'}{y}{x}$. The target renaming proves the required equality for $Q$.
\end{proof}

\begin{theorem*}[\termdefineas{Diamond property of parallel reduction}{Diamond property of parallel reduction}]
If $\ParallelBeta{M}{N}$ and $\ParallelBeta{M}{P}$, then some term $Q$ satisfies
$$
\ParallelBeta{N}{Q}\quad\text{and}\quad\ParallelBeta{P}{Q}.
$$
\end{theorem*}

\begin{proof}[Proof]
Induct on the first parallel derivation. A variable only reduces to itself. For an abstraction, use parallel abstraction
inversion to put the second derivation under the first derivation's binder. Apply the induction hypothesis to the bodies
and lift the resulting two steps through that binder.

Suppose the first derivation uses the application rule. The second derivation either also retains the root or contracts
it. If both retain it, join the two operator reductions and the two argument reductions by their induction hypotheses,
and combine the results by the application rule.

If the second derivation contracts the root, the common operator is an abstraction. Write it with binder $x$, and use
abstraction inversion to write the first operator result with the same binder. Apply the operator induction hypothesis
to the first operator step and to the abstraction step formed from the second derivation's body step. Their common
successor is again an abstraction. Inversion on both joining steps, followed by equality of bodies with a fixed binder,
gives parallel steps from both resulting bodies to one body $R$. Independently join the argument steps at $S$. The
application result contracts in parallel to $\SubstLambda{R}{x}{S}$, while the other result reaches that same term by
the parallel substitution lemma.

Finally, suppose the first derivation contracts the root. If the second retains it, invert its operator step using the
first binder. The body and argument induction hypotheses give common successors $R$ and $S$. Parallel substitution joins
the first contractum to $\SubstLambda{R}{x}{S}$, and parallel contraction joins the second result to it. If both
derivations contract, their binders may differ. Lift the second body step to an abstraction step and invert it using the
first binder. Independence of contraction from the binder name expresses the second contractum with this binder as well.
Now apply the body and argument induction hypotheses and the parallel substitution lemma on both sides. These cases
exhaust the four rules.
\end{proof}

\begin{samepage}

\begin{theorem*}[\termdefineas{Church--Rosser theorem}{Church--Rosser theorem}]
Beta-reduction is confluent: if $M\to_\beta^*N$ and $M\to_\beta^*P$, then some $Q$ satisfies $N\to_\beta^*Q$ and
$P\to_\beta^*Q$. Define \termdefine{beta-convertibility}, written $\BetaConvertible{M}{N}$, to be the equivalence
relation generated by beta-reduction. Then
$$
\BetaConvertible{M}{N}
\quad\Longleftrightarrow\quad
\exists P\;\bigl(M\to_\beta^*P\ \text{and}\ N\to_\beta^*P\bigr).
$$
\end{theorem*}

\end{samepage}

\begin{proof}[Proof]
First move one parallel step across a finite sequence of parallel steps with the same source. For the empty sequence,
its endpoint already takes the given step. To add one more step to the sequence, use the diamond property on that step
and the joining step constructed so far, and append the new joining step on the opposite side. Induction gives a finite
parallel reduction from the endpoint of the original single step and one parallel step from the endpoint of the original
sequence, with a common target.

Now induct on the length of one of two finite parallel reductions with the same source. The empty case is immediate. For
the next step, use the construction just proved to move it across the joining sequence supplied by the induction
hypothesis. This joins the new endpoint to the other reduction's endpoint. Finite parallel reduction and finite
beta-reduction have the same endpoints, so beta-reduction is confluent as well.

If two terms have a common reduct, they are beta-convertible by going forward to that reduct and backward to the other
term. Conversely, induct on a derivation in the equivalence relation generated by beta-reduction. A single step and a
reflexive step have an immediate common reduct, and symmetry exchanges the two reductions. For transitivity, suppose the
first pair has common reduct $R$ and the second pair has common reduct $S$. The shared middle term reduces to both $R$
and $S$. Confluence supplies a common reduct of these two terms; concatenate the corresponding reductions from the two
outer terms. This proves the equivalence.
\end{proof}

\begin{samepage}

\begin{corollary*}[\termdefineas{Uniqueness of lambda normal forms}{Uniqueness of normal forms}]
A \termdefine{lambda normal form} is a term admitting no beta-reduction step. If a term reduces to two normal forms,
those normal forms are equal as alpha-classes.
\end{corollary*}

\begin{proof}[Proof]
By confluence the two normal forms have a common reduct. A finite reduction starting at a normal form has length zero,
since otherwise its first step would contradict normality. Hence each normal form equals the common reduct, and they
equal each other.
\end{proof}

\end{samepage}

A computation is a finite or infinite sequence of beta-reductions. A term \termdefine{halts with value} $V$ when it
reduces in finitely many steps to a numeral or data value $V$ in the chosen encoding.
For natural-number outputs we use distinct normal-form numerals. By
\termuseas{Uniqueness of lambda normal forms}{uniqueness of normal forms}, a term cannot reduce to two distinct such
numerals.

\begin{corollary*}[\termdefineas{Free variables under beta-reduction}{Free variables under beta-reduction}]
If $M\to_\beta^*N$, then $\FreeVarsLambda{N}\IncludedIn\FreeVarsLambda{M}$. In particular, every finite beta-reduction
of a closed term ends in a closed term.
\end{corollary*}

\begin{proof}[Proof]
For a contracted redex, the substitution formula places every free variable of the result in the body's free variables
other than its binder, or in the argument's free variables. These are precisely the two contributions to the original
redex's free-variable set. The application contexts preserve inclusion by taking unions, and an abstraction context
preserves it by removing the same binder variable on both sides. Thus one beta step introduces no new free variables.
Induction on the length of a finite reduction gives the result, including the zero-step case. A subset of the empty
free-variable set is empty, proving the assertion about closed terms.

Free-variable sets are constant on alpha-classes. For a class reduction, use \termuse{Beta-reduction on alpha-classes}
to choose named representatives and apply the one-step inclusion to them. The same finite-reduction induction therefore
proves the assertion after identifying bound-variable names as well.
\end{proof}

## Finite Data and Numerical Programs {#sec:lambda-basic-data}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限データ用lambda項を構成する順序とType-Two利用節への案内。各閉項と有限β還元は後続の定理に別に対応。)
--> This section defines the finite data used by the numerical and Type-Two programs: numerals, selectors, numerical
codes, and finite lists. It constructs their closed lambda terms and proves their behavior by finite beta-reductions.
The order is arithmetic and branching, recursion with parameters, numerical coding, and list processing. Program syntax
is coded only after these constructions. §{sec:tte-finite-data} summarizes their use in computable analysis.<!--
formalization: skip-end
-->

### Numerals, Branching, and Arithmetic {#sec:lambda-numerical-data}

#### Church numerals {#sec:lambda-church-numerals}

\begin{mathmeta}
  \define{ChurchNumeral}
\end{mathmeta}

Use the following \termdefineas{Church numeral}{Church numerals} for natural-number data. Choose distinct variables
$f,x$ and define
$$
\ChurchNumeral{n}:=\lambdaab{f}{\lambdaab{x}{\LambdaIterationExpansion{f}{x}{n}}}.
$$
The brace indicates $n$ nested applications of $f$ to $x$. For $n=0$, the body is just $x$. Write $B_n$ for this body.
For example,
$$\begin{aligned}
\ChurchNumeral{0}&=\lambdaab{f}{\lambdaab{x}{x}},\\
\ChurchNumeral{1}&=\lambdaab{f}{\lambdaab{x}{f\,x}},\\
\ChurchNumeral{2}&=\lambdaab{f}{\lambdaab{x}{f(f\,x)}}.
\end{aligned}$$

\begin{lemma*}[\termdefineas{Church numerals as numerical outputs}{Church numerals as numerical outputs}]
Each $\ChurchNumeral{n}$ is closed and is a normal form. The map $n\mapsto\ChurchNumeral{n}$ is injective on
alpha-classes. Hence a lambda term cannot beta-reduce to numerals for two different natural numbers.
\end{lemma*}

\begin{proof}[Proof]
Induction shows that the free variables of $B_n$ lie in $\{f,x\}$, so the two abstractions bind all of them. In the
displayed named numeral, every application has a variable as its operator, so there is no beta-redex. Binder renaming
preserves the absence of redexes by \termuse{Invariants of binder renaming}. Thus no representative of this alpha-class
admits a beta step, and the numeral is a normal form.

Count variable occurrences, applications and abstractions in the named term. The body has $2n+1$ nodes and the numeral
has $2n+3$. Binder renaming preserves this count by \termuse{Invariants of binder renaming}, so the count is
well-defined on alpha-classes. Equal numerals have equal counts and therefore equal indices. Finally apply uniqueness of
normal forms to two reductions of one term to numerals, and then apply this injectivity.
\end{proof}

#### Arithmetic, branching, and finite state {#sec:lambda-numeral-operations}

\begin{mathmeta}
  \define{LambdaIter,LambdaSucc,LambdaAdd,LambdaMul}
  \define{LambdaTrue,LambdaFalse,LambdaZeroTest}
  \define{LambdaPair,LambdaPairValue,LambdaPairNext,LambdaPred,LambdaSub}
  \vars{m,n}{Nat}
\end{mathmeta}

For lambda terms $F,X$, define the finite expression $\LambdaIter{F}{X}{n}$ by
$$\LambdaIter{F}{X}{0}=X,\qquad
\LambdaIter{F}{X}{n+1}=F(\LambdaIter{F}{X}{n}).$$
This notation describes repeated application in the existing syntax; it adds no reduction rule. Choose the numeral's
second binder $x$ outside $\FreeVarsLambda{F}$. Two beta steps then give
$$\ChurchNumeral{n}\,F\,X\to_\beta^*\LambdaIter{F}{X}{n}.$$
Indeed, the first substitution replaces each occurrence of the iterator variable by $F$ without capture by $x$, and the
second replaces the initial-value variable by $X$. Induction on $n$ verifies both substitution formulas. The same
induction gives
$$\LambdaIter{F}{\LambdaIter{F}{X}{n}}{m}=\LambdaIter{F}{X}{m+n}.$$

Define the following closed terms, choosing the displayed bound variables distinct:
$$\begin{aligned}
\LambdaSucc&:=\lambdaab{n}{\lambdaab{f}{\lambdaab{x}{f(nfx)}}},\\
\LambdaAdd&:=\lambdaab{m}{\lambdaab{n}{\lambdaab{f}{\lambdaab{x}{mf(nfx)}}}},\\
\LambdaMul&:=\lambdaab{m}{\lambdaab{n}{\lambdaab{f}{\lambdaab{x}{m(nf)x}}}}.
\end{aligned}$$

\begin{proposition*}[\termdefineas{Church numeral arithmetic}{Arithmetic on Church numerals}]
For all $m,n\in\NN$,
$$\begin{aligned}
\LambdaSucc\,\ChurchNumeral{n}&\to_\beta^*\ChurchNumeral{n+1},\\
\LambdaAdd\,\ChurchNumeral{m}\,\ChurchNumeral{n}&\to_\beta^*\ChurchNumeral{m+n},\\
\LambdaMul\,\ChurchNumeral{m}\,\ChurchNumeral{n}&\to_\beta^*\ChurchNumeral{mn}.
\end{aligned}$$
\end{proposition*}

\begin{proof}[Proof]
First substitute the closed input numerals for the outer variables. In the successor term, reduce $\ChurchNumeral{n}fx$
to $\LambdaIter{f}{x}{n}$; the additional outer application of $f$ gives the numeral for $n+1$. In the addition term,
first reduce the inner iteration of length $n$, then the outer iteration of length $m$. The iteration identity gives the
numeral for $m+n$. All these reductions lift under the two remaining binders.

For multiplication, apply the iteration formula to $\ChurchNumeral{m}(\ChurchNumeral{n}f)x$. Induction on $m$ shows that
the result reduces to $\LambdaIter{f}{x}{mn}$. At the next step, first reduce the preceding iterate, then apply
$\ChurchNumeral{n}f$ to it. This adds $n$ further applications of $f$, giving $(m+1)n=mn+n$. Lifting under the binders
gives the claimed numeral. Counting free variables in the displayed terms proves their closedness.
\end{proof}

For branching, use the closed \termdefineas{Church boolean}{Church booleans}
$$\LambdaTrue:=\lambdaab{a}{\lambdaab{b}{a}},\qquad
\LambdaFalse:=\lambdaab{a}{\lambdaab{b}{b}},$$
and put
$$\LambdaZeroTest:=\lambdaab{n}{n(\lambdaab{u}{\LambdaFalse})\LambdaTrue}.$$
For closed $A$ and arbitrary $B$, two beta steps give $\LambdaTrue\,A\,B\to_\beta^*A$; for arbitrary $A,B$, two give
$\LambdaFalse\,A\,B\to_\beta^*B$. The first calculation also works for open $A$ when the second binder $b$ is chosen
outside $\FreeVarsLambda{A}$. Neither calculation reduces the discarded argument.

\begin{proposition*}[\termdefineas{Church numeral zero test}{Zero test and branching}]
The term $\LambdaZeroTest$ is closed and satisfies
$$\LambdaZeroTest\,\ChurchNumeral{0}\to_\beta^*\LambdaTrue,\qquad
\LambdaZeroTest\,\ChurchNumeral{n+1}\to_\beta^*\LambdaFalse.$$
Consequently, applying the result to closed branch terms $A,B$ selects $A$ at zero and $B$ at every positive input.
\end{proposition*}

\begin{proof}[Proof]
The iteration formula reduces the zero test to iteration of the constant function $\lambdaab{u}{\LambdaFalse}$ starting
from $\LambdaTrue$. Zero iterations leave $\LambdaTrue$. At every positive iteration count, the outermost application of
the constant function reduces to $\LambdaFalse$, discarding the preceding iterate. Lift these reductions through
application to the two branch terms and use the selection calculations above. Closedness follows directly from the
displayed definitions.
\end{proof}

To store two closed terms $A,B$ as one state, define
$$\LambdaPairValue{A}{B}:=\lambdaab{s}{sAB},\qquad
\LambdaPair:=\lambdaab{a}{\lambdaab{b}{\lambdaab{s}{sab}}}.$$
The state $\LambdaPairValue{A}{B}$ is a functional pair. It is not itself a Church numeral and is distinct from a
bijective numerical pairing function on $\NN^2$.

\begin{proposition*}[\termdefineas{lambda pair selection}{Functional pairs and selection}]
For closed $A,B$, the pair constructor and pair value are closed, and
$$\LambdaPair\,A\,B\to_\beta^*\LambdaPairValue{A}{B},\qquad
\LambdaPairValue{A}{B}\LambdaTrue\to_\beta^*A,\qquad
\LambdaPairValue{A}{B}\LambdaFalse\to_\beta^*B.$$
\end{proposition*}

\begin{proof}[Proof]
Two beta steps substitute $A,B$ into the constructor. Applying the resulting pair to any selector $S$ gives $SAB$ in one
beta step, since substitution leaves the closed components unchanged. Use the true and false selection calculations. The
same closedness of the components shows that the pair has no free variable.
\end{proof}

Use a pair to retain the previous and current counter values. Define
$$\begin{aligned}
\LambdaPairNext&:=\lambdaab{s}{\LambdaPair\,(s\LambdaFalse)\,(\LambdaSucc(s\LambdaFalse))},\\
\LambdaPred&:=\lambdaab{n}{\bigl(n\LambdaPairNext\,\LambdaPairValue{\ChurchNumeral{0}}{\ChurchNumeral{0}}
\bigr)\LambdaTrue},\\
\LambdaSub&:=\lambdaab{m}{\lambdaab{n}{n\LambdaPred\,m}}.
\end{aligned}$$

\begin{proposition*}[\termdefineas{Church numeral predecessor}{Predecessor and subtraction}]
The three displayed terms are closed. For $m,n\in\NN$,
$$\LambdaPred\,\ChurchNumeral{n}\to_\beta^*
\begin{cases}
\ChurchNumeral{0},&n=0,\\
\ChurchNumeral{n-1},&n\ge1,
\end{cases}$$
and
$$\LambdaSub\,\ChurchNumeral{m}\,\ChurchNumeral{n}\to_\beta^*
\begin{cases}
\ChurchNumeral{m-n},&m>n,\\
\ChurchNumeral{0},&m\le n.
\end{cases}$$
\end{proposition*}

\begin{proof}[Proof]
The pair selection and successor calculations give
$$\LambdaPairNext\,\LambdaPairValue{\ChurchNumeral{a}}{\ChurchNumeral{b}}
\to_\beta^*\LambdaPairValue{\ChurchNumeral{b}}{\ChurchNumeral{b+1}}.$$
Reduce each occurrence of the second component, apply successor to one copy, and then construct the new pair. Start the
iteration of $\LambdaPairNext$ at $\LambdaPairValue{\ChurchNumeral{0}}{\ChurchNumeral{0}}$. With no iterations, the
state is this initial pair. For $n\ge1$, induction shows that the state after $n$ iterations is
$\LambdaPairValue{\ChurchNumeral{n-1}}{\ChurchNumeral{n}}$: the first step gives the pair of zero and one, and each
subsequent step replaces the first component by the current counter and increments the second. The iteration formula for
numerals followed by true selection proves the two cases of the predecessor assertion.

For subtraction, the two outer beta steps leave iteration of $\LambdaPred$ starting at $\ChurchNumeral{m}$. Each
application decreases a positive numeral by one and leaves the zero numeral unchanged. Thus, for $n<m$, induction gives
$\ChurchNumeral{m-n}$ after $n$ iterations. After $m$ iterations the result is $\ChurchNumeral{0}$, and every further
iteration leaves it unchanged. This proves the case $m\le n$ as well, including $m=0$. The definitions contain only
closed constants and bound variables, which proves their closedness. Together with uniqueness of numeral outputs, these
reductions verify the asserted numerical functions directly in lambda calculus.
\end{proof}

#### Numerical comparisons {#sec:lambda-numerical-comparisons}

\begin{mathmeta}
  \define{LambdaLeCase,LambdaEqual}
\end{mathmeta}

For lambda terms $A,B,X,Y$, abbreviate
$$\LambdaLeCase{A}{B}{X}{Y}:=\LambdaZeroTest\,(\LambdaSub\,A\,B)\,X\,Y.$$
On numeral arguments, this term selects $X$ when the number represented by $A$ is at most that represented by $B$, and
selects $Y$ otherwise. Indeed, the two cases of the subtraction formula show that the test argument reduces to the zero
numeral in the first case and to a positive numeral otherwise. The zero-test reductions therefore select the required
branch. This is an abbreviation for the displayed lambda term.

We use one and zero as the numerical answers to a predicate. Define equality testing by
$$\begin{aligned}
E(u,v)&:=\LambdaLeCase{v}{u}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
\LambdaEqual&:=\lambdaab{u}{\lambdaab{v}{\LambdaLeCase{u}{v}{E(u,v)}{\ChurchNumeral{0}}}}.
\end{aligned}$$
Expand $E$ inside the abstractions. The two comparisons give
$$\LambdaEqual\,\ChurchNumeral{i}\,\ChurchNumeral{j}\to_\beta^*
\begin{cases}\ChurchNumeral{1},&i=j,\\\ChurchNumeral{0},&i\ne j.\end{cases}$$

### Primitive recursion with parameters {#sec:lambda-primitive-recursion}

\begin{mathmeta}
  \define{LambdaRecUpdate,LambdaRecursor,LambdaParamRec}
  \vars{k}{Nat}
\end{mathmeta}

The pair state can carry an arbitrary closed value, not just the previous counter. Given a closed step term $G$, define
$$\LambdaRecUpdate{G}:=\lambdaab{s}{\LambdaPair\,(\LambdaSucc(s\LambdaTrue))\,(G(s\LambdaTrue)(s\LambdaFalse))}.$$
It reads the current index and value, increments the index, and applies $G$ to the old index and value. Define one
closed \termdefine{lambda recursor} by
$$\LambdaRecursor:=\lambdaab{g}{\lambdaab{a}{\lambdaab{n}{\bigl(n\LambdaRecUpdate{g}(\LambdaPair\,\ChurchNumeral{0}
\,a)\bigr)\LambdaFalse}}}.$$
In this expression, expand the definition of $\LambdaRecUpdate{g}$ using a binder $s$ distinct from $g,a,n$. The step
term and initial value are arguments of this single finite lambda term.

\begin{theorem*}[\termdefineas{lambda primitive recursion theorem}{Primitive recursion by a closed lambda term}]
Let $G$ be closed and let $\Sequence{V_k}{k\in\NN}$ be closed lambda terms such that
$$G\,\ChurchNumeral{k}\,V_k\to_\beta^*V_{k+1}$$
for every $k$. Then
$$\LambdaRecursor\,G\,V_0\,\ChurchNumeral{n}\to_\beta^*V_n.$$
In particular, if $G\,\ChurchNumeral{k}\,\ChurchNumeral{r}\to_\beta^*\ChurchNumeral{g(k,r)}$ for all $k,r$, the
recurrence
$$f(0)=a,\qquad f(k+1)=g(k,f(k))$$
is computed by the closed term $\LambdaRecursor\,G\,\ChurchNumeral{a}$.
\end{theorem*}

\begin{proof}[Proof]
For closed $A,B$ with $G\ChurchNumeral{k}A\to_\beta^*B$, one update satisfies
$$\LambdaRecUpdate{G}\,\LambdaPairValue{\ChurchNumeral{k}}{A}
\to_\beta^*\LambdaPairValue{\ChurchNumeral{k+1}}{B}.$$
After the root beta step, reduce the true selectors to the index and the false selector to the value. Apply successor to
the first copy of the index and use the given reduction of $G$ on the second copy and the value. Finally reduce the pair
constructor. Closedness prevents capture in these substitutions.

Induction on $n$ now gives the state invariant
$$\LambdaIter{\LambdaRecUpdate{G}}{\LambdaPairValue{\ChurchNumeral{0}}{V_0}}{n}
\to_\beta^*\LambdaPairValue{\ChurchNumeral{n}}{V_n}.$$
The zero case is the initial state. For the successor case, first reduce the preceding iterate using the induction
hypothesis, then use the single-update calculation. No numerical encoding of the value component is needed.

Three outer beta steps expose the body of the recursor. Construct the initial pair and apply the Church-numeral
iteration formula to the closed term $\LambdaRecUpdate{G}$. The state invariant yields the final pair, and false
selection returns $V_n$. The displayed bindings and the closed constants show that $\LambdaRecursor$ and
$\LambdaRecUpdate{G}$ are closed. Taking $V_k=\ChurchNumeral{f(k)}$ gives numerical primitive recursion; uniqueness of
numeral outputs rules out any different answer.
\end{proof}

Parameters can be supplied uniformly. For closed terms $B,H$, put
$$\LambdaParamRec{B}{H}:=\lambdaab{x}{\lambdaab{n}{\LambdaRecursor\,(Hx)\,(Bx)\,n}}.$$
This term is closed and contains neither the supplied parameter nor the iteration count.

\begin{corollary*}[\termdefineas{parameterized lambda recursion}{Parameterized lambda recursion}]
Let $X$ be any closed parameter value. If
$$BX\to_\beta^*\ChurchNumeral{a},\qquad
HX\,\ChurchNumeral{k}\,\ChurchNumeral{r}\to_\beta^*\ChurchNumeral{g(k,r)}$$
for all $k,r$, then $\LambdaParamRec{B}{H}\,X\,\ChurchNumeral{n}$ reduces to $\ChurchNumeral{f(n)}$ for the recurrence
above.
\end{corollary*}

\begin{proof}[Proof]
Two beta steps give $\LambdaRecursor\,(HX)\,(BX)\,\ChurchNumeral{n}$. Reduce the initial-value argument to
$\ChurchNumeral{a}$. The step term $HX$ is closed and has the required numerical behavior, so apply the theorem. The
same constructed term works for every valid $X$. In particular, several closed parameters may be supplied together as
nested functional pairs.
\end{proof}

### Numerical Codes for Pairs and Rationals {#sec:lambda-finite-codes}

#### Numerical pairing {#sec:lambda-numerical-pairing}

\begin{mathmeta}
  \define{NatPair,LambdaNumericPair}
  \vars{a,b,s,d,z}{Nat}
\end{mathmeta}

For numerical data use the \termdefine{square-shell pairing}
$$\NatPair{a}{b}:=
\begin{cases}
b^2+a,&a<b,\\
a^2+a+b,&b\le a.
\end{cases}$$
Pairs with $\max(a,b)=s$ occupy the consecutive integers from $s^2$ through $(s+1)^2-1$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
既出の数値pairingを6×6格子に表示する図の座標と読み方。新しいpairingの定理ではなく、図の視覚的再審査はここでは行わない。)
--> The diagram places the value $\NatPair{a}{b}$ beside each lattice point $\Pair{a}{b}$ for $0\le a,b\le5$; the
horizontal
coordinate is $a$ and the vertical coordinate is $b$.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
既出のNat.pairの2分岐式を格子の各点に記すTikZ描画指示。数値pairingの数学は先行定理で対応し、この図を新たな局所的証明と数えない。
視覚的承認は別途とする。)
--> \begin{center}
\begin{tikzpicture}[x=0.95cm,y=0.95cm]
  \draw[step=1,gray!25,thin] (0,0) grid (5,5);
  \draw[->] (-0.35,0) -- (5.75,0) node[right] {$a$};
  \draw[->] (0,-0.35) -- (0,5.85) node[above] {$b$};
  \foreach \i in {0,...,5} {
    \draw (\i,0.06) -- (\i,-0.06) node[below=3pt,font=\scriptsize] {$\i$};
    \draw (0.06,\i) -- (-0.06,\i) node[left=3pt,font=\scriptsize] {$\i$};
  }
  \foreach \a in {0,...,5} {
    \foreach \b in {0,...,5} {
      \pgfmathtruncatemacro{\paircode}{ifthenelse(\a<\b,\b*\b+\a,\a*\a+\a+\b)}
      \fill (\a,\b) circle (1.1pt);
      \node[above right,inner sep=2.5pt,font=\small,fill=white]
        at (\a,\b) {$\paircode$};
    }
  }
\end{tikzpicture}
\end{center}<!--
formalization: skip-end
-->

\begin{proposition*}[\termdefineas{square-shell pairing inverse}{Inverse of square-shell pairing}]
The pairing is a bijection from $\NN^2$ to $\NN$. Given $z$, let $s=\Floor{\sqrt z}$ and $d=z-s^2$. Its inverse is
$$z\longmapsto
\begin{cases}
\Pair{d}{s},&d<s,\\
\Pair{s}{d-s},&s\le d.
\end{cases}$$
\end{proposition*}

\begin{proof}[Proof]
The square-root bounds give $s^2\le z<(s+1)^2$, hence $0\le d\le 2s$. If $d<s$, pairing $\Pair{d}{s}$ gives $s^2+d=z$.
If
$s\le d$, then $d-s\le s$, and pairing $\Pair{s}{d-s}$ gives $s^2+s+(d-s)=z$. Conversely, if $a<b$, the number $b^2+a$
has
integer square root $b$ and remainder $a<b$, so decoding returns $\Pair{a}{b}$. If $b\le a$, the number $a^2+a+b$ has
integer
square root $a$ and remainder $a+b$; the second inverse clause again returns $\Pair{a}{b}$. Both round trips hold,
including
zero.
\end{proof}

The forward numerical pairing has a direct lambda implementation using the arithmetic terms already constructed. In
variables $m,n$, abbreviate the following open terms by $T,L,U$:
$$\begin{aligned}
T&:=\LambdaZeroTest\,(\LambdaSub\,(\LambdaSucc\,m)\,n),\\
L&:=\LambdaAdd\,(\LambdaMul\,n\,n)\,m,\\
U&:=\LambdaAdd\,(\LambdaAdd\,(\LambdaMul\,m\,m)\,m)\,n.
\end{aligned}$$
Expand these abbreviations before abstraction and put
$$\LambdaNumericPair:=\lambdaab{m}{\lambdaab{n}{TLU}}.$$

\begin{proposition*}[\termdefineas{lambda numerical pairing}{Numerical pairing by a lambda term}]
The term $\LambdaNumericPair$ is closed, and for all $a,b\in\NN$,
$$\LambdaNumericPair\,\ChurchNumeral{a}\,\ChurchNumeral{b}\to_\beta^*\ChurchNumeral{\NatPair{a}{b}}.$$
\end{proposition*}

\begin{proof}[Proof]
Two beta steps substitute the closed numerals into the body. The arithmetic reductions turn the branch arguments into
the numerals for $b^2+a$ and $a^2+a+b$. If $a<b$, then $a+1\le b$, so the subtraction term in the test reduces to
$\ChurchNumeral{0}$ and the zero test selects the first branch. If $b\le a$, that subtraction term reduces to
$\ChurchNumeral{a+1-b}$, whose value is positive, so the second branch is selected. These are precisely the two clauses
of the pairing definition. All constants are closed and both input variables are bound, proving closedness.
\end{proof}

#### Integer square root and numerical projections {#sec:lambda-numerical-projections}

\begin{mathmeta}
  \define{LambdaSqrt,LambdaNumericProjection}
  \vars{z,s,d,k,r,r_*}{Nat}
  \vars{a,b}{Nat}
\end{mathmeta}

Define closed terms
$$\begin{aligned}
B&:=\lambdaab{z}{\ChurchNumeral{0}},\\
H&:=\lambdaab{z}{\lambdaab{k}{\lambdaab{r}{
\LambdaLeCase{\LambdaMul\,(\LambdaSucc\,k)\,(\LambdaSucc\,k)}{z}{\LambdaSucc\,k}{r}}}},\\
\LambdaSqrt&:=\lambdaab{z}{\LambdaParamRec{B}{H}\,z\,z}.
\end{aligned}$$
Thus the input is supplied both as the fixed parameter and as the number of iterations. All abbreviations are expanded
before binding variables.

\begin{proposition*}[\termdefineas{lambda integer square root}{Integer square root by a lambda term}]
For every $z\in\NN$,
$$\LambdaSqrt\,\ChurchNumeral{z}\to_\beta^*\ChurchNumeral{\Floor{\sqrt z}}.$$
\end{proposition*}

\begin{proof}[Proof]
Fix $z$ and put $s=\Floor{\sqrt z}$. The step term computes the recurrence
$$r_0=0,\qquad r_{k+1}=\begin{cases}k+1,&(k+1)^2\le z,\\r_k,&(k+1)^2>z.\end{cases}$$
We claim that $r_k=\min(k,s)$. The claim holds at zero. If $k+1\le s$, then $(k+1)^2\le z$ and the next value is $k+1$.
Otherwise $s\le k$, the test fails, and the induction hypothesis gives the retained value $s$. This proves the claim by
induction. The parameterized recursor therefore returns the numeral for $\min(z,s)$ after $z$ iterations. Since $s\le
z$, this is the numeral for $s$, including when $z=0$. Each arithmetic operation and branch has a finite beta-reduction,
so the recursor theorem supplies a finite reduction of the whole term.
\end{proof}

For an input variable $z$, form the open terms
$$S:=\LambdaSqrt\,z,\qquad D:=\LambdaSub\,z\,(\LambdaMul\,S\,S).$$
Define the two closed numerical projections by
$$\begin{aligned}
\LambdaNumericProjection{1}&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,D}{S}{D}{S}},\\
\LambdaNumericProjection{2}&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,D}{S}{S}{\LambdaSub\,D\,S}}.
\end{aligned}$$
Here $S$ and $D$ are expanded inside each abstraction.

\begin{proposition*}[\termdefineas{lambda numerical projections}{Numerical projections by lambda terms}]
Let $\Pair{a}{b}$ be the inverse image of $z$ under square-shell pairing. Then
$$\LambdaNumericProjection{1}\,\ChurchNumeral{z}\to_\beta^*\ChurchNumeral{a},\qquad
\LambdaNumericProjection{2}\,\ChurchNumeral{z}\to_\beta^*\ChurchNumeral{b}.$$
In particular, the projections applied to the numeral for $\NatPair{a}{b}$ return the numerals for $a$ and $b$,
respectively.
\end{proposition*}

\begin{proof}[Proof]
After substituting the input numeral, reduce each copy of $S$ to the numeral for $s=\Floor{\sqrt z}$ and each copy
of $D$ to the numeral for $d=z-s^2$. The comparison tests $d+1\le s$, equivalently $d<s$. In that case the two branches
return $d$ and $s$; otherwise they return $s$ and $d-s$. These are the two clauses of the inverse already proved in
§{sec:lambda-numerical-pairing}. The encode/decode identity gives the last assertion. The only free variable of each
projection body is $z$, which is bound in the displayed terms.
\end{proof}

#### Rational arithmetic on numerical codes {#sec:lambda-rational-arithmetic}

\begin{mathmeta}
  \vars{a,b,c}{Nat}
  \vars{r,s}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次の有理数code定義に入る短い案内。符号付き分子と正分母の実定義とその被覆性は直後に別に対応。)
--> For rational data, use the following code with signed numerator and positive denominator.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{RationalCode}
\end{mathmeta}
$$\RationalCode{a}{b}{c}:=\NatPair{\NatPair{a}{b}}{c},\qquad
\RationalCode{a}{b}{c}\longmapsto\frac{a-b}{c+1},\qquad a,b,c\in\NN.$$
The numerator difference is taken in the integers. Every natural number decodes to exactly one triple, and every
rational has at least one code. No reduction to lowest terms is required.

Numerical unpairing recovers the three entries from every natural number. Conversely, a rational with integer
numerator $z$ and positive denominator $d$ has such a code: write $z=a-b$ with $a,b\in\NN$ and take $c=d-1$.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
分数への符号化とunpairingはRationalCode.value_surjectiveとnatCode/ofNatへ接続済み。
未リンク部分はmetric算法用の算術手続きを次に構成するという案内のみ。)
--> We now construct the arithmetic procedures used by the metric algorithms.<!--
formalization: skip-end
-->

First define closed component programs
$$\begin{aligned}
P&:=\lambdaab{u}{\LambdaNumericProjection{1}(\LambdaNumericProjection{1}u)},\\
N&:=\lambdaab{u}{\LambdaNumericProjection{2}(\LambdaNumericProjection{1}u)},\\
D&:=\lambdaab{u}{\LambdaSucc(\LambdaNumericProjection{2}u)}.
\end{aligned}$$
On the numeral for $\RationalCode{a}{b}{c}$ these return the numerals for $a,b,c+1$, respectively. For a numerical input
term $z$, abbreviate $u:=\LambdaNumericProjection{1}z$ and $v:=\LambdaNumericProjection{2}z$, and use the following
expressions, whose only possible free variable is $z$:
$$\begin{aligned}
A&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Pv)\,(Du)),\\
B&:=\LambdaAdd\,(\LambdaMul\,(Nu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
C&:=\LambdaMul\,(Du)\,(Dv),\\
E&:=\LambdaAdd\,(\LambdaMul\,(Pu)\,(Dv))\,(\LambdaMul\,(Nv)\,(Du)),\\
F&:=\LambdaAdd\,(\LambdaMul\,(Pv)\,(Du))\,(\LambdaMul\,(Nu)\,(Dv)).
\end{aligned}$$

\begin{mathmeta}
  \define{LambdaRationalAdd,LambdaRationalLess,LambdaDyadic}
\end{mathmeta}
Define
$$\begin{aligned}
\LambdaRationalAdd&:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericPair\,A\,B)\,(\LambdaPred\,C)},\\
\LambdaRationalLess&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,E}{F}{\ChurchNumeral{1}}{\ChurchNumeral{0}}},\\
\LambdaDyadic&:=\lambdaab{n}{\LambdaNumericPair\,\ChurchNumeral{\NatPair{1}{0}}\,
 (\LambdaPred\,(n\,(\LambdaMul\,\ChurchNumeral{2})\,\ChurchNumeral{1}))}.
\end{aligned}$$
Expand the abbreviations before abstraction, using fresh bound variables inside the component terms. Each displayed
program is a single closed lambda term.

\begin{proposition*}[\termdefineas{rational-code lambda reductions}{Lambda reductions for rational codes}]
Let $r=\RationalCode{a}{b}{c}$, $s=\RationalCode{u}{v}{w}$, $d=c+1$, and $e=w+1$. Then
$$\begin{aligned}
\LambdaRationalAdd\,\ChurchNumeral{\NatPair{r}{s}}
 &\to_\beta^*\ChurchNumeral{\RationalCode{ae+ud}{be+vd}{de-1}},\\
\LambdaRationalLess\,\ChurchNumeral{\NatPair{r}{s}}
 &\to_\beta^*\begin{cases}\ChurchNumeral{1},&ae+vd<ud+be,\\
 \ChurchNumeral{0},&ud+be\le ae+vd,\end{cases}\\
\LambdaDyadic\,\ChurchNumeral{k}
 &\to_\beta^*\ChurchNumeral{\RationalCode{1}{0}{2^k-1}}.
\end{aligned}$$
The sum code represents the sum of the input rationals, the comparison tests their strict order, and the last code
represents $2^{-k}$. The natural differences here are defined because $de\ge1$ and $2^k\ge1$.
\end{proposition*}

\begin{proof}[Proof]
For composition, if closed terms $G,H$ compute numerical functions $g,h$, then $\lambdaab{x}{G(Hx)}$ computes $g\circ
h$: contract the outer abstraction, reduce the inner application, and then reduce the outer application. The same
argument works for a closed binary operation applied to two computed arguments. This constructs every component above.

After the outer abstraction of the addition program is contracted, numerical projections recover the six input entries.
Reduction in application contexts gives $A\to_\beta^*\ChurchNumeral{ae+ud}$, $B\to_\beta^*\ChurchNumeral{be+vd}$, and
$C\to_\beta^*\ChurchNumeral{de}$. Predecessor and two numerical pairings give the asserted output. Its value is
$$\frac{ae+ud-be-vd}{de}=\frac{a-b}{d}+\frac{u-v}{e}.$$
For comparison the same argument gives the cross sums $ae+vd$ and $ud+be$. Successor followed by the less-than-or-equal
test returns one exactly for strict inequality. Multiplication by the positive number $de$ shows that this is equivalent
to $(a-b)/d<(u-v)/e$.

For the dyadic program, induction on $k$ shows that applying $\ChurchNumeral{k}$ to multiplication by two and then to
$\ChurchNumeral{1}$ reduces to $\ChurchNumeral{2^k}$. The successor step uses one further multiplication, so this is
ordinary Church iteration. Predecessor and pairing finish the reduction. Its denominator is exactly $2^k$, so its value
is $2^{-k}$. Every natural input decodes, every component reduction is finite, and all remaining variables are bound.
This proves totality and closedness, including the zero inputs. Confluence gives uniqueness of each numeral output.
\end{proof}

\begin{corollary*}[\termdefineas{lambda rational arithmetic}{Rational arithmetic by lambda terms}]
There are closed lambda programs for addition, strict comparison, and dyadic error bounds on these codes. Given codes
$\RationalCode{a}{b}{c}$ and $\RationalCode{u}{v}{w}$, put $d=c+1$ and $e=w+1$. Addition returns
$$\RationalCode{ae+ud}{be+vd}{de-1}.$$
Strict comparison returns the numeral one exactly when $ae+vd<ud+be$, and zero otherwise. On input $k$, the dyadic
program returns $\RationalCode{1}{0}{2^k-1}$, which represents $2^{-k}$. Both differences in the denominator codes are
ordinary differences of positive integers and one.
\end{corollary*}

\begin{proof}[Proof]
The preceding beta-reductions provide the three closed programs and their outputs on every numerical input.
Their rational values and the comparison criterion were verified in the same proof.
\end{proof}

### Finite lists and their programs {#sec:lambda-finite-lists}

\begin{mathmeta}
  \define{LambdaListCode,LambdaListDecode,LambdaListCons,LambdaListField,LambdaListFold,LambdaListRecursor}
  \define{LambdaListAppend,LambdaListMap,LambdaListAny,LambdaListMember,ListConcat,ListMap}
  \vars{a,d,x}{Nat}
  \vars{e}{Nat}
\end{mathmeta}

Finite lists store an ordered sequence of numerical data. We encode them by natural numbers so that the same arithmetic
and comparison programs apply to their entries and codes. The corner notation $\LambdaListCode{\ell}$
denotes the natural-number code of the list $\ell$, while $\ChurchNumeral{\LambdaListCode{\ell}}$
is the closed lambda term representing that number. For a finite list $\ell$ of natural numbers, set
$$\LambdaListCode{[]}:=0,\qquad
\LambdaListCode{a::\ell}:=\NatPair{a}{\LambdaListCode{\ell}}+1.$$
Define $\LambdaListDecode{0}:=[]$. For $e>0$, unpair $e-1$, use the first component as the head, and recursively decode
the second component as the tail. The tail code is at most $e-1$, hence smaller than $e$, so this recursion terminates.

\begin{proposition*}[\termdefineas{lambda finite-list coding}{Coding finite lists}]
Coding and decoding are mutually inverse:
$$\LambdaListDecode{\LambdaListCode{\ell}}=\ell,\qquad
\LambdaListCode{\LambdaListDecode{e}}=e.$$
Thus every natural number codes exactly one finite list.
\end{proposition*}

\begin{proof}[Proof]
Induction on the list proves the first identity using the inverse equations for pairing. For the second, use strong
induction on the code. Zero is immediate. At a positive code, the tail has smaller code, so the induction hypothesis
recovers it; pairing the unchanged head with that tail and adding one recovers the original code.
\end{proof}

The constructor and field programs are
$$\begin{aligned}
\LambdaListCons&:=\lambdaab{a}{\lambdaab{d}{\LambdaSucc(\LambdaNumericPair\,a\,d)}},\\
\LambdaListField{i}&:=\lambdaab{e}{\LambdaNumericProjection{i}(\LambdaPred\,e)}
 \qquad(i=1,2).
\end{aligned}$$
The first field is the head, and the second is the tail code. The field equations below are asserted for nonempty lists;
no head of the empty list is needed.

\begin{lemma*}[\termdefineas{lambda list constructors and fields}{List constructors and fields}]
The constructor and both field programs are closed, and for all $a,d\in\NN$,
$$\begin{aligned}
\LambdaListCons\,\ChurchNumeral{a}\,\ChurchNumeral{d}
 &\to_\beta^*\ChurchNumeral{\NatPair{a}{d}+1},\\
\LambdaListField{1}\,\ChurchNumeral{\NatPair{a}{d}+1}&\to_\beta^*\ChurchNumeral{a},\\
\LambdaListField{2}\,\ChurchNumeral{\NatPair{a}{d}+1}&\to_\beta^*\ChurchNumeral{d}.
\end{aligned}$$
\end{lemma*}

\begin{proof}[Proof]
For the constructor, two beta steps expose numerical pairing followed by successor. For each field, one beta step
exposes predecessor followed by numerical projection. The input to predecessor is positive, so it returns the pair code.
The projection equations then give the indicated component. All constants are closed and every displayed variable is
bound.
\end{proof}

For closed terms $Z,H$, construct a list recursor by self-application. With fresh distinct binders $s,e$, put
$$\begin{aligned}
B(Z,H,R,e)&:=\LambdaZeroTest\,e\,Z\\
 &\qquad\bigl(H(\LambdaListField{1}\,e)(R(\LambdaListField{2}\,e))\bigr),\\
K_{Z,H}&:=\lambdaab{s}{\lambdaab{e}{B(Z,H,ss,e)}},\\
\LambdaListFold{Z}{H}&:=K_{Z,H}K_{Z,H},\\
\LambdaListRecursor&:=\lambdaab{h}{\lambdaab{z}{\LambdaListFold{z}{h}}}.
\end{aligned}$$
Expand the abbreviations before abstraction. In the last line keep the binders of each kernel distinct from $h,z$. The
zero branch returns the base value; the other branch passes the head and recursively computed tail value to $H$. The
wrapper $\LambdaListRecursor$ supplies the handler and base value as inputs to one closed program.

\begin{theorem*}[\termdefineas{lambda finite-list recursion}{Recursion on finite lists by a lambda term}]
Let $Z,H$ be closed, and assign a term $W_\ell$ to each finite list. Suppose
$$Z\to_\beta^*W_{[]},\qquad
H\ChurchNumeral{a}W_\ell\to_\beta^*W_{a::\ell}$$
for every $a$ and $\ell$. Then $\LambdaListFold{Z}{H}$ is closed and
$$\LambdaListFold{Z}{H}\,\ChurchNumeral{\LambdaListCode{\ell}}\to_\beta^*W_\ell.$$
The closed term $\LambdaListRecursor$ satisfies the same reduction after receiving $H,Z$ and the list code as its three
inputs.
\end{theorem*}

\begin{proof}[Proof]
Two beta steps unfold the self-application. At code zero, zero testing returns $Z$ and discards the recursive branch. At
a nonempty list, the positive branch is selected and the field equations expose its head and tail code. Induct on the
list: the empty case uses the assumed reduction of $Z$, and the nonempty case first applies the induction hypothesis to
the tail, then uses the hypothesis for $H$. Thus each input list has a finite reduction to its assigned value.
Closedness follows from the fresh binders and closed constants. Finally, two beta steps in the wrapper supply $H,Z$ to
the same fold. Coding and decoding extend these computations to every numerical input.
\end{proof}

Write $\ListConcat{\ell}{m}$ for concatenation and $\ListMap{f}{\ell}$ for applying $f$ to every element, in order.
Define
$$\begin{aligned}
\LambdaListAppend&:=\lambdaab{e}{\lambdaab{d}{\LambdaListRecursor\,\LambdaListCons\,d\,e}},\\
M&:=\lambdaab{f}{\lambdaab{a}{\lambdaab{r}{\LambdaListCons\,(fa)\,r}}},\\
\LambdaListMap&:=\lambdaab{f}{\lambdaab{e}{\LambdaListRecursor\,(Mf)\,\ChurchNumeral{0}\,e}},\\
T&:=\lambdaab{f}{\lambdaab{a}{\lambdaab{r}{\LambdaZeroTest\,(fa)\,r\,\ChurchNumeral{1}}}},\\
\LambdaListAny&:=\lambdaab{f}{\lambdaab{e}{\LambdaListRecursor\,(Tf)\,\ChurchNumeral{0}\,e}},\\
\LambdaListMember&:=\lambdaab{x}{\lambdaab{e}{\LambdaListAny\,(\LambdaEqual\,x)\,e}}.
\end{aligned}$$
These are closed terms. The map handler constructs the new head from the transformed element. The existence handler
keeps the tail's answer when the head fails its test, and returns one when the head succeeds.

\begin{proposition*}[\termdefineas{lambda finite-list operations}{Finite-list operations by lambda terms}]
For finite lists $\ell,m$ and $x\in\NN$,
$$\begin{aligned}
\LambdaListAppend\,\ChurchNumeral{\LambdaListCode{\ell}}\,\ChurchNumeral{\LambdaListCode{m}}
 &\to_\beta^*\ChurchNumeral{\LambdaListCode{\ListConcat{\ell}{m}}},\\
\LambdaListMember\,\ChurchNumeral{x}\,\ChurchNumeral{\LambdaListCode{\ell}}
 &\to_\beta^*\begin{cases}\ChurchNumeral{1},&x\in\ell,\\\ChurchNumeral{0},&x\notin\ell.\end{cases}
\end{aligned}$$
If a closed term $F$ satisfies $F\ChurchNumeral{a}\to_\beta^*\ChurchNumeral{f(a)}$ for every natural number $a$, then
$$\LambdaListMap\,F\,\ChurchNumeral{\LambdaListCode{\ell}}
 \to_\beta^*\ChurchNumeral{\LambdaListCode{\ListMap{f}{\ell}}}.$$
If a closed term $P$ returns one or zero according as a predicate $p(a)$ is true or false, for every $a$, then
$$\LambdaListAny\,P\,\ChurchNumeral{\LambdaListCode{\ell}}
 \to_\beta^*\begin{cases}\ChurchNumeral{1},&\exists a\in\ell\;p(a),\\
 \ChurchNumeral{0},&\text{otherwise}.\end{cases}$$
All four conclusions apply to arbitrary numerical list codes through decoding.
\end{proposition*}

\begin{proof}[Proof]
For concatenation, use the code of the second list as the base value and the list constructor as the handler. Induction
on the first list then prepends exactly its elements. For mapping, use the empty-list code as the base. At each head,
the reduction assumed for $F$ computes the new element and the constructor prepends it to the already mapped tail.

For existence, use zero as the base value. At a head where the predicate is false, zero testing retains the tail's
answer; where it is true, it returns one. Induction on the list gives exactly the stated existential condition.
Membership is the special case obtained by taking equality with the given number as the predicate. In each case, the
list-recursion theorem supplies the finite reduction, and the outer beta steps supply the parameters. The code-decoding
identities give the arbitrary-code statements.
\end{proof}

#### List Length and Access {#sec:lambda-list-access}

\begin{mathmeta}
  \define{LambdaListLength,LambdaListDrop,LambdaListGet}
  \vars{n}{Nat}
\end{mathmeta}
To inspect a finite prefix, we need its length and its entries. Extend both list fields to the empty-list code by
returning zero. Define
$$\begin{aligned}
H_0&:=\lambdaab{a}{\LambdaSucc},\\
\LambdaListLength&:=\LambdaListRecursor\,H_0\,\ChurchNumeral{0},\\
\LambdaListDrop&:=\lambdaab{e}{\lambdaab{n}{n\,\LambdaListField{2}\,e}},\\
\LambdaListGet&:=\lambdaab{z}{\LambdaListField{1}\bigl(
 \LambdaListDrop\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)\bigr)}.
\end{aligned}$$
These formulas use the list coding and recursor of §{sec:lambda-finite-lists}. The zero extension specifies the behavior
at the boundary explicitly; no rule for natural-number subtraction is needed here.

\begin{proposition*}[\termdefineas{lambda finite-list access}{Length and entries of finite lists}]
These terms are closed and total on numerical inputs. On the code of a list $s$, $\LambdaListLength$ returns
$\Length{s}$.
Given that code and $n$, $\LambdaListDrop$ returns the code of the list with its first $n$ entries removed; it returns
the empty-list code when $n\ge\Length{s}$. On input $\NatPair{\LambdaListCode{s}}{n}$, $\LambdaListGet$ returns $s(n)$
when
$n<\Length{s}$, and zero otherwise. Every numerical code decodes to a finite list, so no validity check is needed.
\end{proposition*}

\begin{proof}[Proof]
List recursion starts the length at zero and ignores each head, applying successor to the recursively computed length of
the tail. Induction on the list proves the length formula. The Church numeral in the drop program iterates the tail
operation exactly $n$ times. Induction on $n$ proves that the result is the code of the remaining suffix, including the
empty suffix since its tail stays empty. The first list field then returns the requested entry, or zero if that suffix
is empty. Numerical projections supply the paired arguments. The constants are closed and the abstractions bind every
remaining variable.
\end{proof}

#### Finite Tabulation {#sec:lambda-finite-tabulation}

\begin{mathmeta}
  \define{LambdaListTabulate}
  \vars{k,n,x}{Nat}
\end{mathmeta}
Let a closed numerical term $F$ compute $f(x,k)$ on the paired input $\NatPair{x}{k}$.
To generate its first $n$ values while retaining $x$, expand
$$\begin{aligned}
B&:=\lambdaab{x}{\ChurchNumeral{0}},\\
H_F&:=\lambdaab{x}{\lambdaab{k}{\lambdaab{r}{
 \LambdaListAppend\,r\,(\LambdaListCons\,(F(\LambdaNumericPair\,x\,k))\,\ChurchNumeral{0})}}},\\
\LambdaListTabulate{F}&:=\lambdaab{z}{\LambdaParamRec{B}{H_F}\,
 (\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}.
\end{aligned}$$
All bound variables are distinct and fresh for the component terms. The initial value is the empty-list
code; the update appends one newly computed value.

\begin{lemma*}[\termdefineas{lambda finite tabulation}{Finite tabulation by a lambda term}]
If $f$ is total, $\LambdaListTabulate{F}$ is closed and total. On input $\NatPair{x}{n}$ it returns
$$\LambdaListCode{[f(x,k)]_{k<n}}.$$
The entries are listed in increasing order of $k$; for $n=0$ the list is empty.
\end{lemma*}

\begin{proof}[Proof]
Induct on the number of updates. Zero updates return the empty-list code. At stage $k$, pairing computes
the input for $F$, whose output becomes a singleton list. Concatenation appends it to the accumulated
first $k$ values, giving exactly the first $k+1$ values in their original order. The parameterized numerical
recursor realizes this recurrence by beta reduction. Every component terminates, and abstraction binds
all added variables, proving totality and closedness.
\end{proof}

### Computable functions and predicates {#sec:lambda-computable-functions}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
これまで構成した自然数・pair・有限list用の閉lambda項を計算概念の定義に使う旨の案内。
一般の部分関数の定義は直後のComputesPartial/LambdaComputableで対応。)
-->
The preceding constructions represent natural numbers, pairs and finite lists by closed lambda terms. Statements about
algorithms on these data refer to lambda terms operating on those representations. We now fix the corresponding notion
of a computable partial function.<!--
formalization: skip-end
-->

A partial function
$$
\PartialFunctionMap{\varphi}{\seqPower{\omega}{k}}{\omega}
$$
is \termdefine{lambda-computable} if there is a closed lambda term $P$ such that, on numerals for $\vec n$, the term
$P\vec n$ reduces to the numeral for $m$ exactly when $\varphi(\vec n)=m$, and otherwise has no normal-form numeral
output. A total function is computable if it is lambda-computable and defined on every input. A set $A\IncludedIn\omega$
is \termdefine{decidable} if its characteristic function is computable, and \termdefine{recursively enumerable} if some
computable partial function halts exactly on the members of $A$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Turing計算・partial recursive functionとの古典的比較の明示的な文献案内。この比較を局所形式化の証明対象に追加せず、
本書のlambda項による計算の定義とは分離する。)
--> The classical comparison with Turing computability and partial recursive functions can be found in [@Barendregt1984;
@Sipser2013]. It explains agreement with other conventions; the definition of computation and the constructions in this
book use lambda terms directly.<!--
formalization: skip-end
-->

## Programs for Lambda Syntax {#sec:lambda-syntax-programs}

### Finite syntax codes {#sec:lambda-syntax-codes}

\begin{mathmeta}
  \define{LambdaSyntaxCode,LambdaSyntaxDecode,LambdaVarCode,LambdaTaggedCode}
  \vars{a,b,e,i,t,q,r}{Nat}
\end{mathmeta}

Number the variables as $x_0,x_1,\ldots$ in their fixed order. A code records a named term before passage to its
alpha-class. Define its \termdefine{lambda syntax code} by
$$\begin{aligned}
\LambdaSyntaxCode{x_i}&:=3i,\\
\LambdaSyntaxCode{MN}&:=3\NatPair{\LambdaSyntaxCode{M}}{\LambdaSyntaxCode{N}}+1,\\
\LambdaSyntaxCode{\lambdaab{x_i}{M}}&:=3\NatPair{i}{\LambdaSyntaxCode{M}}+2.
\end{aligned}$$
The residue modulo three records the constructor. Different names for a bound variable may give different codes;
equality of alpha-classes is checked by comparing the decoded named terms under equality of free names.

\begin{proposition*}[\termdefineas{lambda syntax coding bijection}{Coding and decoding lambda syntax}]
There is a total decoding function $\LambdaSyntaxDecode{e}$ on $\NN$ satisfying
$$\LambdaSyntaxDecode{\LambdaSyntaxCode{M}}=M,\qquad
\LambdaSyntaxCode{\LambdaSyntaxDecode{e}}=e.$$
Thus the coding is a bijection between named terms and natural numbers. The code of each proper immediate subterm is
smaller than the code of the whole term.
\end{proposition*}

\begin{proof}[Proof]
Given $e$, put $q:=\Floor{e/3}$ and $r:=e\bmod3$. If $r=0$, return $x_q$. Otherwise unpair $q$ as
$\NatPair{a}{b}$: for $r=1$, return the application of $\LambdaSyntaxDecode{a}$ to $\LambdaSyntaxDecode{b}$; for $r=2$,
return the abstraction with binder $x_a$ and body $\LambdaSyntaxDecode{b}$. Each unpaired component is at most $q$, and
$q<e$ in these two cases. Recursion on the code therefore terminates. Induction on a term proves the first identity,
using the inverse equations for numerical pairing. Strong induction on $e$ proves the second: the recursive calls
recover the component codes, pairing recovers $q$, and $e=3q+r$. The same inequalities prove the assertion about subterm
codes.
\end{proof}

The numerical constructor functions themselves have closed lambda implementations:
$$\begin{aligned}
\LambdaVarCode&:=\lambdaab{a}{\LambdaMul\,\ChurchNumeral{3}\,a},\\
\LambdaTaggedCode{t}&:=\lambdaab{a}{\lambdaab{b}{
\LambdaAdd\,(\LambdaMul\,\ChurchNumeral{3}\,(\LambdaNumericPair\,a\,b))\,\ChurchNumeral{t}}}.
\end{aligned}$$
Use $t=1$ for application and $t=2$ for abstraction.

\begin{proposition*}[\termdefineas{lambda syntax constructor programs}{Lambda terms constructing syntax codes}]
For every $i,a,b,t\in\NN$,
$$\LambdaVarCode\,\ChurchNumeral{i}\to_\beta^*\ChurchNumeral{3i},\qquad
\LambdaTaggedCode{t}\,\ChurchNumeral{a}\,\ChurchNumeral{b}
\to_\beta^*\ChurchNumeral{3\NatPair{a}{b}+t}.$$
All these constructor terms are closed.
\end{proposition*}

\begin{proof}[Proof]
For a variable code, one beta step substitutes the input numeral and multiplication gives the result. For a tagged pair,
two beta steps substitute both numerals. Reduce numerical pairing, multiply its output by three, and add the tag. Each
reduction is lifted through its application context. All constants are closed, and the displayed abstractions bind the
remaining variables.
\end{proof}

Define $P_e$ to be the alpha-class of $\LambdaSyntaxDecode{e}$ when this term is closed, and to be $\ChurchNumeral{0}$
otherwise. Then every $P_e$ is closed and every closed alpha-class occurs in the sequence. Indeed, free variables are
determined by a finite traversal, and for a closed representative $M$, its code gives $P_{\LambdaSyntaxCode{M}}=[M]$.
Repetitions in this enumeration are harmless.

### Inspecting syntax codes by lambda terms {#sec:lambda-syntax-inspection}

\begin{mathmeta}
  \vars{e,q,r,r_*,k,z,i,j}{Nat}
  \vars{a,b}{Nat}
\end{mathmeta}

The decoder uses division by three and numerical projections. We now implement these operations by closed lambda terms,
so subsequent programs can inspect codes within the same calculus. The payload of a code $e$ is $\Floor{e/3}$,
and its constructor tag is $e\bmod3$.

\begin{mathmeta}
  \define{LambdaSyntaxPayload,LambdaSyntaxTag,LambdaSyntaxField}
\end{mathmeta}

Define the closed step term and payload program by
$$\begin{aligned}
G&:=\lambdaab{k}{\lambdaab{r}{
\LambdaLeCase{\LambdaMul\,\ChurchNumeral{3}\,(\LambdaSucc\,r)}{\LambdaSucc\,k}{\LambdaSucc\,r}{r}}},\\
\LambdaSyntaxPayload&:=\LambdaRecursor\,G\,\ChurchNumeral{0}.
\end{aligned}$$
The step compares the next multiple of three with the next iteration count. Define the tag and field programs by
$$\begin{aligned}
\LambdaSyntaxTag&:=\lambdaab{z}{\LambdaSub\,z\,(\LambdaMul\,\ChurchNumeral{3}\,(\LambdaSyntaxPayload\,z))},\\
\LambdaSyntaxField{j}&:=\lambdaab{z}{\LambdaNumericProjection{j}(\LambdaSyntaxPayload\,z)}\qquad(j=1,2).
\end{aligned}$$

\begin{proposition*}[\termdefineas{lambda syntax inspection programs}{Lambda terms inspecting syntax codes}]
All four programs are closed. For every $e\in\NN$, put $q:=\Floor{e/3}$ and write $q=\NatPair{a}{b}$. Then
$$\begin{aligned}
\LambdaSyntaxPayload\,\ChurchNumeral{e}&\to_\beta^*\ChurchNumeral{q},&
\LambdaSyntaxTag\,\ChurchNumeral{e}&\to_\beta^*\ChurchNumeral{e\bmod3},\\
\LambdaSyntaxField{1}\,\ChurchNumeral{e}&\to_\beta^*\ChurchNumeral{a},&
\LambdaSyntaxField{2}\,\ChurchNumeral{e}&\to_\beta^*\ChurchNumeral{b}.
\end{aligned}$$
\end{proposition*}

\begin{proof}[Proof]
Successor, multiplication and comparison show that $G$ computes the recurrence
$$r_0=0,\qquad r_{k+1}=\begin{cases}r_k+1,&3(r_k+1)\le k+1,\\r_k,&3(r_k+1)>k+1.\end{cases}$$
We prove $r_k=\Floor{k/3}$ by induction. It holds at zero. At stage $k$, the induction hypothesis gives $3r_k\le
k<3r_k+3$. If the next comparison succeeds, $k+1=3(r_k+1)$ and the quotient increases by one. Otherwise $3r_k\le
k+1<3(r_k+1)$ and the quotient is unchanged. The recursor theorem therefore gives the claimed payload reduction after
$e$ iterations.

For the tag, substitute the input numeral, compute the payload, multiply by three, and subtract. Since $3q\le e$, the
difference $e-3q$ is an ordinary nonnegative difference and equals $e\bmod3$. For each field, compute the payload and
apply the corresponding numerical projection. These are finite beta-reductions in application contexts. The constants
are closed and the displayed abstractions bind every remaining variable.
\end{proof}

\begin{corollary*}[\termdefineas{lambda syntax destructor equations}{Reading the three syntax constructors}]
On the code of $x_i$, the tag program returns zero and the payload program returns $i$. On the code of $MN$, the tag is
one and the two field programs return $\LambdaSyntaxCode{M}$ and $\LambdaSyntaxCode{N}$. On the code of
$\lambdaab{x_i}{M}$, the tag is two and the field programs return $i$ and $\LambdaSyntaxCode{M}$. Each returned natural
number is represented by its Church numeral.
\end{corollary*}

\begin{proof}[Proof]
Insert the three constructor-code formulas into the proposition. Division and remainder recover the payload and tag, and
the inverse identities for numerical pairing recover the two fields. For a variable code only the payload is needed; the
field programs are used after checking that the tag is one or two.
\end{proof}

### Structural recursion on syntax codes {#sec:lambda-syntax-recursion}

\begin{mathmeta}
  \define{LambdaSyntaxCase,LambdaSyntaxFold,LambdaNodeCount,LambdaSyntaxNodes}
  \vars{e}{Nat}
\end{mathmeta}

Code inspection lets a lambda program follow the structure of a decoded term. For a code term $e$ and three branch terms
$X,Y,Z$, abbreviate
$$\begin{aligned}
\LambdaSyntaxCase{e}{X}{Y}{Z}&:=\LambdaZeroTest\,(\LambdaSyntaxTag\,e)\,X\\
&\qquad\bigl(\LambdaZeroTest\,(\LambdaPred(\LambdaSyntaxTag\,e))\,Y\,Z\bigr).
\end{aligned}$$
On the code of a variable, application or abstraction, this selects the first, second or third branch, respectively. The
unselected branches need not be reduced.

Fix closed handler terms $V,A,L$ for variables, applications and abstractions. With fresh distinct variables $s,z$,
define the following abbreviations, expanding them inside the abstractions:
$$\begin{aligned}
X(z)&:=V(\LambdaSyntaxPayload\,z),\\
Y(R,z)&:=A\bigl(R(\LambdaSyntaxField{1}\,z)\bigr)\bigl(R(\LambdaSyntaxField{2}\,z)\bigr),\\
Z(R,z)&:=L(\LambdaSyntaxField{1}\,z)\bigl(R(\LambdaSyntaxField{2}\,z)\bigr),\\
B(R,z)&:=\LambdaSyntaxCase{z}{X(z)}{Y(R,z)}{Z(R,z)},\\
K&:=\lambdaab{s}{\lambdaab{z}{B(ss,z)}},\\
\LambdaSyntaxFold{V}{A}{L}&:=KK.
\end{aligned}$$
Thus the recursive call is the same self-application, with a subterm code as its input. The three handlers are fixed
parts of this finite term; they do not vary with the input code.

\begin{theorem*}[\termdefineas{lambda structural recursion on syntax}{Structural recursion by a lambda term}]
Let $V,A,L$ be closed, and let $W_M$ be a lambda term for each named term $M$. Suppose
$$\begin{aligned}
V\ChurchNumeral{i}&\to_\beta^*W_{x_i},\\
A\,W_M\,W_N&\to_\beta^*W_{MN},\\
L\ChurchNumeral{i}\,W_M&\to_\beta^*W_{\lambdaab{x_i}{M}}.
\end{aligned}$$
Then $\LambdaSyntaxFold{V}{A}{L}$ is closed and, for every named term $M$,
$$\LambdaSyntaxFold{V}{A}{L}\,\ChurchNumeral{\LambdaSyntaxCode{M}}
\to_\beta^*W_M.$$
\end{theorem*}

\begin{proof}[Proof]
Put $F:=\LambdaSyntaxFold{V}{A}{L}$. Two beta steps give $F\ChurchNumeral{e}\to_\beta^*B(F,\ChurchNumeral{e})$. All
inserted constants and handlers are closed, so the fresh binders prevent capture. Reduce the constructor tag and select
the appropriate branch. The payload and field equations then give
$$\begin{aligned}
F\ChurchNumeral{\LambdaSyntaxCode{x_i}}&\to_\beta^*V\ChurchNumeral{i},\\
F\ChurchNumeral{\LambdaSyntaxCode{MN}}&\to_\beta^*A\bigl(F\ChurchNumeral{\LambdaSyntaxCode{M}}
\bigr)\bigl(F\ChurchNumeral{\LambdaSyntaxCode{N}}\bigr),\\
F\ChurchNumeral{\LambdaSyntaxCode{\lambdaab{x_i}{M}}}&\to_\beta^*L\ChurchNumeral{i}
\bigl(F\ChurchNumeral{\LambdaSyntaxCode{M}}\bigr).
\end{aligned}$$
These reductions expose the required recursive calls without reducing discarded branches.

Induct on the structure of $M$. At a variable, apply the variable-handler assumption. At an application, the induction
hypotheses give finite reductions for both subterms; lift them through the application contexts, then apply the
application-handler assumption. At an abstraction, use the induction hypothesis for its body and then the
abstraction-handler assumption. Every case concatenates finitely many finite reductions. Finally, the kernel binds its
two remaining free variables, so both the kernel and its self-application are closed.
\end{proof}

\begin{example*}[Reconstructing a code]
Choose $V=\LambdaVarCode$, $A=\LambdaTaggedCode{1}$ and $L=\LambdaTaggedCode{2}$. The resulting fold returns the input
code on every Church numeral.
\end{example*}

\begin{proof}[Proof]
Take $W_M=\ChurchNumeral{\LambdaSyntaxCode{M}}$. The constructor-program equations verify the three hypotheses. Every
natural number is the code of its decoded term, so the conclusion covers every numeral input.
\end{proof}

Let $\LambdaNodeCount{M}$ count the variable, application and abstraction nodes of $M$. Thus
$$\begin{aligned}
\LambdaNodeCount{x_i}&=1,\\
\LambdaNodeCount{MN}&=\LambdaNodeCount{M}+\LambdaNodeCount{N}+1,\\
\LambdaNodeCount{\lambdaab{x_i}{M}}&=\LambdaNodeCount{M}+1.
\end{aligned}$$
Define
$$\begin{aligned}
V_\#&:=\lambdaab{i}{\ChurchNumeral{1}},\\
A_\#&:=\lambdaab{m}{\lambdaab{n}{\LambdaSucc(\LambdaAdd\,m\,n)}},\\
L_\#&:=\lambdaab{i}{\LambdaSucc},\\
\LambdaSyntaxNodes&:=\LambdaSyntaxFold{V_\#}{A_\#}{L_\#}.
\end{aligned}$$

\begin{corollary*}[\termdefineas{lambda syntax node count}{Counting syntax nodes by a lambda term}]
The term $\LambdaSyntaxNodes$ is closed and, for every $e\in\NN$,
$$\LambdaSyntaxNodes\,\ChurchNumeral{e}
\to_\beta^*\ChurchNumeral{\LambdaNodeCount{\LambdaSyntaxDecode{e}}}.$$
In particular, on a term code it returns the node-count bound used to define capture-avoiding substitution in
§{sec:lambda-calculus}.
\end{corollary*}

\begin{proof}[Proof]
The variable handler discards its input and returns one. Two beta steps, addition and successor make the application
handler return the sum of its two inputs plus one. The abstraction handler discards the binder index and returns the
successor of the body count. Apply structural recursion with $W_M=\ChurchNumeral{\LambdaNodeCount{M}}$, and then use the
coding identity for $\LambdaSyntaxDecode{e}$.
\end{proof}

### Free variables and fresh names {#sec:lambda-free-variable-programs}

\begin{mathmeta}
  \define{LambdaFreeVarTest,LambdaFreshVar}
\end{mathmeta}

Capture-avoiding substitution must test free-variable membership and choose a fresh variable. The structural recursor
and the equality test from §{sec:lambda-numerical-comparisons} supply the first operation.

Each recursive value will be a function of the variable index to be tested. Define closed handlers and the membership
program by
$$\begin{aligned}
A_f&:=\lambdaab{f}{\lambdaab{g}{\lambdaab{k}{\LambdaZeroTest\,(fk)\,(gk)\,\ChurchNumeral{1}}}},\\
L_f&:=\lambdaab{i}{\lambdaab{f}{\lambdaab{k}{\LambdaZeroTest\,(\LambdaEqual\,i\,k)\,(fk)\,\ChurchNumeral{0}}}},\\
\LambdaFreeVarTest&:=\LambdaSyntaxFold{\LambdaEqual}{A_f}{L_f}.
\end{aligned}$$
The application handler takes the union of the two membership predicates. The abstraction handler removes the binder
index.

\begin{proposition*}[\termdefineas{lambda free-variable decision}{Free-variable membership by a lambda term}]
The term $\LambdaFreeVarTest$ is closed. For every named term $M$ and index $i$,
$$\LambdaFreeVarTest\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{i}
\to_\beta^*\begin{cases}\ChurchNumeral{1},&x_i\in\FreeVarsLambda{M},\\
\ChurchNumeral{0},&x_i\notin\FreeVarsLambda{M}.\end{cases}$$
Equivalently, on any numerical code $e$ it decides membership in $\FreeVarsLambda{\LambdaSyntaxDecode{e}}$.
\end{proposition*}

\begin{proof}[Proof]
Define closed predicate values recursively by
$$W_{x_i}:=\LambdaEqual\,\ChurchNumeral{i},\qquad
W_{MN}:=A_fW_MW_N,\qquad
W_{\lambdaab{x_i}{M}}:=L_f\ChurchNumeral{i}W_M.$$
The structural-recursion theorem reduces the first application of the membership program to $W_M$. It remains to prove
that $W_M\ChurchNumeral{k}$ returns the required answer. Induct on $M$. At a variable, equality testing gives membership
in the singleton. At an application, if the first predicate returns zero, zero testing returns the second predicate's
answer; otherwise it returns one. This is precisely membership in the union. At an abstraction, equality with the binder
returns zero, and inequality retains the body's answer. This is precisely removal of the binder from the free-variable
set. All tests have finite reductions by the induction hypotheses. Closedness follows from the displayed binders and the
closed structural recursor. The decoding identity extends the result to every numerical input.
\end{proof}

### Numerical search and least fresh variables {#sec:lambda-numerical-search}

\begin{mathmeta}
  \define{LambdaSearchKernel,LambdaSearch}
  \vars{j}{Nat}
\end{mathmeta}

Self-application allows a finite term to continue testing candidates without a prescribed iteration bound. For a test
term $G$, choose $s,k$ fresh for $G$ and put
$$\LambdaSearchKernel{G}:=\lambdaab{s}{\lambdaab{k}{
\LambdaZeroTest\,(Gk)\,k\,\bigl((ss)(\LambdaSucc\,k)\bigr)}}.$$
The zero branch returns the current candidate; the positive branch applies the duplicated self argument to the next
candidate. Define one closed \termdefine{lambda search term} by
$$\LambdaSearch:=\lambdaab{g}{
\bigl(\LambdaSearchKernel{g}\,\LambdaSearchKernel{g}\bigr)\ChurchNumeral{0}}.$$
Expand both occurrences of the kernel before abstraction, keeping their binders distinct from $g$. These are finite
lambda terms; no numerical bound is an argument of the search.

\begin{lemma*}[\termdefineas{lambda numerical search}{Numerical search by beta-reduction}]
Let $G$ be closed and $j\in\NN$. Suppose $G\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{0}$ and that, for each $k<j$, the
term $G\ChurchNumeral{k}$ reduces to a positive numeral. Then
$$\LambdaSearch\,G\to_\beta^*\ChurchNumeral{j}.$$
No condition is imposed on tests after $j$.
\end{lemma*}

\begin{proof}[Proof]
Put $S_k:=(\LambdaSearchKernel{G}\,\LambdaSearchKernel{G})\ChurchNumeral{k}$. Two beta steps expose the zero test of
$G\ChurchNumeral{k}$. If $k<j$, a positive result selects the continuation and successor gives $S_{k+1}$. At $j$, the
zero result selects $\ChurchNumeral{j}$ and discards the continuation. Starting from this final reduction, backward
induction through the finitely many preceding candidates gives $S_0\to_\beta^*\ChurchNumeral{j}$. One beta step reduces
$\LambdaSearch\,G$ to $S_0$. This proof uses only ordinary beta-reduction.
\end{proof}

For term codes $e,d$ and a variable index $i$, define a candidate test and a single closed search program by
$$\begin{aligned}
T(e,d,i)&:=\lambdaab{k}{\LambdaAdd\,
\bigl(\LambdaAdd\,(\LambdaFreeVarTest\,e\,k)\,(\LambdaFreeVarTest\,d\,k)\bigr)
\,(\LambdaEqual\,i\,k)},\\
\LambdaFreshVar&:=\lambdaab{e}{\lambdaab{d}{\lambdaab{i}{\LambdaSearch\,T(e,d,i)}}}.
\end{aligned}$$
Expand $T$ inside the outer abstractions, using a fresh binder for its candidate. The test adds three zero-or-one
answers; it returns zero exactly when the candidate belongs to neither free-variable set and differs from the excluded
index.

\begin{proposition*}[\termdefineas{lambda least fresh-variable program}{Least fresh-variable choice by a lambda term}]
The term $\LambdaFreshVar$ is closed. For named terms $M,N$ and an index $i$, let $j$ be the least index such that
$$x_j\notin\FreeVarsLambda{M}\cup\FreeVarsLambda{N}\cup\{x_i\}.$$
Then
$$\LambdaFreshVar\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{\LambdaSyntaxCode{N}}\,\ChurchNumeral{i}
\to_\beta^*\ChurchNumeral{j}.$$
This is exactly the least fresh-variable choice in the capture-avoiding substitution definition.
\end{proposition*}

\begin{proof}[Proof]
The excluded set is finite, so an index outside it exists and has a least value $j$. Every candidate test terminates by
free-variable decision and equality testing. At $j$ all three answers are zero. At each smaller index, membership in the
excluded set makes at least one answer one, so their sum is positive. Apply numerical search to this closed test. Three
outer beta steps supply the two codes and excluded index. The result is the required numeral, and the displayed binders
show closedness. Since every natural number decodes, the same program works on arbitrary numerical codes as well.
\end{proof}

### Capture-avoiding substitution on codes {#sec:lambda-code-substitution}

\begin{mathmeta}
  \define{LambdaSubstBase,LambdaSubstStep,LambdaSubstFuel,LambdaSubstCode,LambdaBoundedSubst}
  \vars{u,v}{Nat}
\end{mathmeta}

The termination proof in §{sec:lambda-calculus} used a depth-bounded substitution procedure. Write
$\LambdaBoundedSubst{k}{M}{x_i}{N}$ for its result at budget $k$. Budget zero returns $M$. At budget $k+1$, each
recursive call in the substitution clauses receives budget $k$, including both calls in the renaming branch. We now
implement that very procedure on numerical codes. The recursor's state will be a function of three inputs: the source
code, the variable index, and the replacement code.

For a prospective smaller-budget function $r$ and code arguments $e,i,d$, use the following abbreviations for the
variable and application branches:
$$\begin{aligned}
V(e,i,d)&:=\LambdaZeroTest\,(\LambdaEqual\,(\LambdaSyntaxPayload\,e)\,i)\,e\,d,\\
A(r,e,i,d)&:=\LambdaTaggedCode{1}\,
 \bigl(r(\LambdaSyntaxField{1}\,e)\,i\,d\bigr)\\
 &\qquad\bigl(r(\LambdaSyntaxField{2}\,e)\,i\,d\bigr).
\end{aligned}$$
In the abstraction branch, write $b$ for the body code and $y$ for the binder index. Define
$$\begin{aligned}
Q(r,b,y,i,d,z)&:=\LambdaTaggedCode{2}\,z\,
 \bigl(r\bigl(r\,b\,y\,(\LambdaVarCode\,z)\bigr)\,i\,d\bigr),\\
U(r,b,y,i,d)&:=\LambdaZeroTest\,(\LambdaFreeVarTest\,d\,y)\\
 &\qquad\bigl(\LambdaTaggedCode{2}\,y\,(r\,b\,i\,d)\bigr)\\
 &\qquad Q(r,b,y,i,d,\LambdaFreshVar\,b\,d\,i),\\
L(r,e,i,d)&:=\LambdaZeroTest\,(\LambdaEqual\,(\LambdaSyntaxField{1}\,e)\,i)\\
 &\qquad U(r,\LambdaSyntaxField{2}\,e,\LambdaSyntaxField{1}\,e,i,d)\,e,\\
B(r,e,i,d)&:=\LambdaSyntaxCase{e}{V(e,i,d)}{A(r,e,i,d)}{L(r,e,i,d)}.
\end{aligned}$$
Thus $L$ returns the original abstraction when its binder is the variable being replaced. Otherwise $U$ tests whether
the binder occurs freely in the replacement. If it does, $Q$ first renames the body's free occurrences of that binder,
then substitutes the intended replacement into the renamed body. Both calls use the same function $r$.

Expand all these abbreviations inside the abstractions below, choosing the displayed binders distinct from one another.
Define closed terms
$$\begin{aligned}
\LambdaSubstBase&:=\lambdaab{e}{\lambdaab{i}{\lambdaab{d}{e}}},\\
\LambdaSubstStep&:=\lambdaab{k}{\lambdaab{r}{\lambdaab{e}{\lambdaab{i}{\lambdaab{d}{B(r,e,i,d)}}}}},\\
\LambdaSubstFuel&:=\LambdaRecursor\,\LambdaSubstStep\,\LambdaSubstBase,\\
\LambdaSubstCode&:=\lambdaab{e}{\lambdaab{i}{\lambdaab{d}{
 \LambdaSubstFuel\,(\LambdaSyntaxNodes\,e)\,e\,i\,d}}}.
\end{aligned}$$
The step term ignores its numerical argument $k$; its function argument $r$ already carries the smaller budget. The
final program computes a sufficient budget from the source code, so the caller supplies no bound.

\begin{theorem*}[\termdefineas{lambda capture-avoiding substitution program}{Capture-avoiding substitution by a
lambda term}]
For every budget $k$, named terms $M,N$, and variable index $i$,
$$\begin{aligned}
&\LambdaSubstFuel\,\ChurchNumeral{k}\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,
 \ChurchNumeral{i}\,\ChurchNumeral{\LambdaSyntaxCode{N}}\\
&\qquad\to_\beta^*\ChurchNumeral{\LambdaSyntaxCode{\LambdaBoundedSubst{k}{M}{x_i}{N}}}.
\end{aligned}$$
Consequently the single closed term $\LambdaSubstCode$ satisfies
$$\begin{aligned}
&\LambdaSubstCode\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{i}\,
 \ChurchNumeral{\LambdaSyntaxCode{N}}\\
&\qquad\to_\beta^*\ChurchNumeral{\LambdaSyntaxCode{\SubstLambda{M}{x_i}{N}}}.
\end{aligned}$$
On arbitrary numerical codes $e,d$, its output is the code of the substitution into $\LambdaSyntaxDecode{e}$ with
replacement $\LambdaSyntaxDecode{d}$. Thus it returns the exact named term chosen by the substitution definition, not
merely an alpha-equivalent representative.
\end{theorem*}

\begin{proof}[Proof]
Define closed function values by $R_0:=\LambdaSubstBase$ and $R_{k+1}:=\LambdaSubstStep\,\ChurchNumeral{k}\,R_k$. The
primitive-recursion theorem gives $\LambdaSubstFuel\,\ChurchNumeral{k}\to_\beta^*R_k$. We prove by induction on $k$,
simultaneously for all source terms, indices and replacement terms, that $R_k$ computes the bounded procedure. At zero,
three beta steps return the source code. At a successor, five beta steps expose $B(R_k,e,i,d)$, and code inspection
selects the constructor branch. At a variable, equality testing chooses the replacement code or the unchanged variable
code. At an application, the induction hypothesis computes the two substituted subterms, and the application constructor
combines their codes.

For an abstraction whose binder is the variable being replaced, the original code is returned. If the binder is absent
from the replacement's free variables, the induction hypothesis computes the substituted body and the abstraction
constructor retains the binder. In the remaining case, fresh-name search returns precisely the least index required by
the substitution definition. The variable constructor produces its variable code. Apply the induction hypothesis first
to the body with that variable as replacement, then to the resulting named term with the intended replacement. The
hypothesis covers all named terms, so this second application is valid even though the renamed body is not a literal
subterm. The abstraction constructor supplies the fresh binder. These are exactly the bounded substitution clauses, and
every selected computation is finite; discarded branches need not be evaluated.

For the final program, three beta steps pass the input codes and index. Node counting computes $\LambdaNodeCount{M}$.
The preceding result then gives the bounded substitution at that budget, which equals $\SubstLambda{M}{x_i}{N}$ by the
termination lemma. All constants used above are closed, and all displayed variables are bound, so both programs are
closed. Finally, decoding and recoding any natural number gives that number back, extending the result to arbitrary
numerical codes.
\end{proof}

\begin{lemma*}[\termdefineas{uniform fixed-template indices}{Uniform indices from a fixed template}]
Fix a named term $M$ and a variable $x_i$. A closed lambda term computes the total numerical map
$$t(u):=\LambdaSyntaxCode{\SubstLambda{M}{x_i}{\LambdaSyntaxDecode{u}}}.$$
If $\FreeVarsLambda{M}\IncludedIn\{x_i\}$ and $u$ decodes to a closed term, then $t(u)$ also decodes to a
closed term, and $P_{t(u)}$ is obtained by substituting $P_u$ for $x_i$ in the alpha-class of $M$.
\end{lemma*}

\begin{proof}[Proof]
Use the closed term
$$V:=\LambdaSubstCode\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{i}.$$
The substitution theorem gives $V\ChurchNumeral{u}\to_\beta^*\ChurchNumeral{t(u)}$ for every natural number $u$.
It constructs the substituted syntax without executing the term decoded from the input. Substitution respects
alpha-equivalence, so decoding the output gives the asserted alpha-class. If the only possible free variable of
$M$ is $x_i$ and the inserted term is closed, the free-variable formula for substitution makes the result closed.
The representative of the fixed template is chosen once; the input syntax is supplied by its numerical code.
\end{proof}

The same construction accepts two input codes. Fix a named term $M$ and variable indices $i,j$, and put
$$M_u:=\SubstLambda{M}{x_i}{\LambdaSyntaxDecode{u}},\qquad
 t(u,v):=\LambdaSyntaxCode{\SubstLambda{M_u}{x_j}{\LambdaSyntaxDecode{v}}}.$$
The first substitution computes the code of $M_u$ from $u$. Use that computed code as the source argument of
$\LambdaSubstCode$, with variable index $j$ and replacement code $v$. Numerical projections and composition
therefore give a single closed term computing $t(u,v)$ on input $\NatPair{u}{v}$. Both substitutions terminate
for every pair of input codes and execute neither decoded term. Decoding the result gives the two successive
capture-avoiding substitutions on alpha-classes.

### Deciding alpha-equivalence on codes {#sec:lambda-alpha-decision}

\begin{mathmeta}
  \define{LambdaBindingTree}
  \vars{a,b}{Nat}
\end{mathmeta}

For a numerical implementation of the comparison, associate a finite
\termdefineas{lambda binding tree}{locally nameless syntax tree} $\LambdaBindingTree{M}$ to each named term. Keep
application nodes and abstraction nodes, but erase the variable name attached to each abstraction. A free occurrence
retains its variable name as a free leaf. A bound occurrence becomes a bound leaf labeled by the number of intervening
abstractions between that occurrence and its binder: the innermost binder has index zero. Free leaves and bound leaves
are distinct kinds of leaf. Thus shadowing is recorded by the actual binding structure, rather than by the spelling of a
variable.

The construction is recursive. A variable gives a free leaf, and application combines two trees. For $\lambdaab{x}{M}$,
first construct $\LambdaBindingTree{M}$, then replace each free $x$ leaf by a bound leaf whose index is the number of
abstractions passed while descending to that leaf, and finally add the outer abstraction node. Call this replacement
operation closing the free variable $x$. Existing bound leaves do not change. Induction shows that every bound index in
a tree constructed from a named term points to an enclosing abstraction. The theorem below proves that two terms are
alpha-equivalent exactly when these representations agree.

\begin{lemma*}[\termdefineas{Substitution and binding trees}{Substitution and indexed trees}]
The tree $\LambdaBindingTree{\SubstLambda{M}{x}{N}}$ is obtained from $\LambdaBindingTree{M}$ by replacing every free
$x$ leaf by a copy of $\LambdaBindingTree{N}$, leaving all other leaves and the surrounding nodes unchanged.
\end{lemma*}

\begin{proof}[Proof]
First observe two identities by induction on a tree. Closing a variable commutes with replacement of a different free
variable if the inserted tree has no free occurrence of the variable being closed. Also, replacing free $y$ leaves by a
fresh free $z$ leaf and then closing $z$ gives the same tree as directly closing $y$. For the second identity, freshness
excludes any pre-existing free $z$ leaf. Both identities continue beneath an abstraction with the closing depth
increased by one.

Now induct on the node-count bound for named substitution. Variables and applications follow directly from the
definitions. In an abstraction binding $x$, substitution stops, and its tree has no free $x$ leaf to replace. In an
abstraction binding a different variable absent from the replacement's free-variable set, apply the induction hypothesis
to the body and use the first identity.

In the renaming branch, first apply the induction hypothesis to the variable replacement in the body. Its node count is
unchanged, so the hypothesis also applies to the following substitution. The chosen fresh variable occurs freely in
neither the original body nor the replacement. The first identity moves closing past the final substitution, and the
second removes the intermediate renaming. The result is exactly free-leaf replacement in the original abstraction's
tree. The inserted tree has no dangling bound index, so its internal binding structure remains intact under any
surrounding abstractions.
\end{proof}

\begin{lemma*}[\termdefineas{Indexed syntax and alpha-equivalence}{Indexed syntax and alpha-equivalence}]
For all named terms,
$$\AlphaEquivalent{M}{N}\quad\Longleftrightarrow\quad\LambdaBindingTree{M}=\LambdaBindingTree{N}.$$
\end{lemma*}

\begin{proof}[Proof]
Equality of the auxiliary trees is preserved by application and abstraction. The closing identity in the preceding lemma
shows that each generating binder renaming preserves the tree. Induction on the derivation of alpha-equivalence
therefore proves that alpha-equivalent terms have equal trees.

For the converse, induct on a node-count bound for the first of two terms with equal trees. Equal trees have the same
outer constructor. Variable leaves have the same name, and applications reduce to their two pairs of subterms. For two
abstractions, choose one variable fresh for both bodies. Open each outer binder by replacing its bound occurrences by
that free variable. To locate those occurrences beneath further abstractions, increase the target index by one at each
descent. Opening a closed free variable in a tree made from a named term is precisely replacement of its free leaves: no
pre-existing bound index can point to the newly added outer binder. Consequently, equality of the abstraction trees
gives equality of the trees of the two renamed bodies. Their node counts equal those of the original bodies. Apply the
induction hypothesis, lift through the common abstraction, and compose with the fresh renaming on either side. This
produces the required finite sequence of renamings and context steps.
\end{proof}

\begin{mathmeta}
  \define{LambdaBindingCode,LambdaCloseTree,LambdaCloseCode,LambdaBindingProgram,LambdaAlphaTest}
\end{mathmeta}

We now implement equality of these indexed syntax trees. Assign each finite indexed syntax tree $A$ a numerical code
$\LambdaBindingCode{A}$ by the following rules. A free leaf with index $i$ has code $6i$, and a bound leaf with index
$i$ has code $6i+3$. An application whose children have codes $a,b$ has code $3\NatPair{a}{b}+1$. An abstraction whose
child has code $a$ has code $3\NatPair{0}{a}+2$. This reuses the syntax-code constructors: leaf indices are $2i$ for
free leaves and $2i+1$ for bound leaves, and every abstraction uses the dummy binder index zero. These are codes of
data; no beta-reduction of the encoded data term is intended.

\begin{lemma*}[\termdefineas{lambda binding-tree code injectivity}{Injectivity of indexed syntax codes}]
Two finite indexed syntax trees have equal codes if and only if they are equal.
\end{lemma*}

\begin{proof}[Proof]
The syntax tag distinguishes leaves, applications and abstractions. At a leaf, parity of its variable index
distinguishes free from bound, and the index determines its label. At an application, injectivity of numerical pairing
recovers both child codes. At an abstraction, it recovers the child code. Induction on the trees proves injectivity. The
converse is immediate.
\end{proof}

Write $\LambdaCloseTree{A}{i}{k}$ for closing the free variable $x_i$ in $A$ starting at depth $k$. At a free $x_i$
leaf, put a bound leaf labeled by the current depth; leave other free leaves and all existing bound leaves unchanged.
Descend through application with the same depth and through abstraction with depth increased by one. This is the closing
operation used to construct $\LambdaBindingTree{M}$.

To compute closing, let each syntax-fold value be a function of the index to be closed and the starting depth. Use the
abbreviations
$$\begin{aligned}
D(v,i,k)&:=\LambdaZeroTest\,(\LambdaEqual\,v\,(\LambdaMul\,\ChurchNumeral{2}\,i))\\
 &\qquad(\LambdaVarCode\,v)\\
 &\qquad\bigl(\LambdaVarCode\,(\LambdaSucc(\LambdaMul\,\ChurchNumeral{2}\,k))\bigr),\\
V_c&:=\lambdaab{v}{\lambdaab{i}{\lambdaab{k}{D(v,i,k)}}},\\
A_c&:=\lambdaab{f}{\lambdaab{g}{\lambdaab{i}{\lambdaab{k}{
 \LambdaTaggedCode{1}\,(f\,i\,k)\,(g\,i\,k)}}}},\\
L_c&:=\lambdaab{y}{\lambdaab{f}{\lambdaab{i}{\lambdaab{k}{
 \LambdaTaggedCode{2}\,y\,(f\,i\,(\LambdaSucc\,k))}}}},\\
\LambdaCloseCode&:=\LambdaSyntaxFold{V_c}{A_c}{L_c}.
\end{aligned}$$
Expand $D$ inside the abstraction. All three handlers are closed. The abstraction handler preserves the dummy binder
field and passes the increased depth to its body function.

\begin{lemma*}[\termdefineas{lambda binding-tree closing program}{Closing a free variable by a lambda term}]
For every finite indexed syntax tree $A$ and indices $i,k$, the closed term $\LambdaCloseCode$ satisfies
$$\begin{aligned}
&\LambdaCloseCode\,\ChurchNumeral{\LambdaBindingCode{A}}\,\ChurchNumeral{i}\,\ChurchNumeral{k}\\
&\qquad\to_\beta^*\ChurchNumeral{\LambdaBindingCode{\LambdaCloseTree{A}{i}{k}}}.
\end{aligned}$$
\end{lemma*}

\begin{proof}[Proof]
The structural recursor produces the function built from the three handlers. Prove its required action by induction on
the tree, for every starting depth. At a free leaf with label $j$, the variable index is $2j$. The equality test
succeeds precisely when $j=i$, producing a bound leaf with index $k$; otherwise it preserves the leaf. At a bound leaf
the variable index is odd, so equality with $2i$ fails and the leaf is preserved. Application combines the two results
at the same depth. Abstraction uses the induction hypothesis at depth $k+1$ and restores the abstraction node. All
numerical tests and constructors have finite reductions. The handlers and structural recursor are closed, so the
assembled program is closed as well.
\end{proof}

Now fold over the original named term to compute its indexed syntax code. Set
$$\begin{aligned}
V_b&:=\lambdaab{i}{\LambdaVarCode\,(\LambdaMul\,\ChurchNumeral{2}\,i)},\\
L_b&:=\lambdaab{i}{\lambdaab{b}{\LambdaTaggedCode{2}\,\ChurchNumeral{0}\,
 (\LambdaCloseCode\,b\,i\,\ChurchNumeral{0})}},\\
\LambdaBindingProgram&:=\LambdaSyntaxFold{V_b}{\LambdaTaggedCode{1}}{L_b},\\
\LambdaAlphaTest&:=\lambdaab{e}{\lambdaab{d}{
 \LambdaEqual\,(\LambdaBindingProgram\,e)\,(\LambdaBindingProgram\,d)}}.
\end{aligned}$$
The abstraction handler closes its binder in the already computed body tree, then adds an abstraction node. The final
program compares the two resulting numerical codes.

\begin{theorem*}[\termdefineas{lambda alpha-equivalence decision}{Alpha-equivalence by a lambda term}]
The terms $\LambdaBindingProgram$ and $\LambdaAlphaTest$ are closed. For all named terms $M,N$,
$$\LambdaBindingProgram\,\ChurchNumeral{\LambdaSyntaxCode{M}}
 \to_\beta^*\ChurchNumeral{\LambdaBindingCode{\LambdaBindingTree{M}}},$$
and
$$\LambdaAlphaTest\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{\LambdaSyntaxCode{N}}
 \to_\beta^*\begin{cases}\ChurchNumeral{1},&\AlphaEquivalent{M}{N},\\
 \ChurchNumeral{0},&\neg\AlphaEquivalent{M}{N}.\end{cases}$$
On arbitrary numerical inputs $e,d$, the latter program decides alpha-equivalence of $\LambdaSyntaxDecode{e}$ and
$\LambdaSyntaxDecode{d}$.
\end{theorem*}

\begin{proof}[Proof]
For the first reduction, apply structural recursion with the value at $M$ equal to the numeral of its indexed syntax
code. The variable handler produces a free leaf. The application handler combines the two child codes. The abstraction
handler first uses the closing lemma at depth zero and then adds an abstraction node. These are precisely the recursive
clauses defining $\LambdaBindingTree{M}$. This proves the first reduction by induction on $M$.

Two beta steps in the comparison program expose numerical equality of the computed codes. Code injectivity identifies
equality of these codes with equality of the indexed syntax trees, which characterizes alpha-equivalence by the earlier
theorem. Equality testing gives the stated one-or-zero answer. Closedness follows from the closed handlers and recursor.
The decoding identity extends both computations to arbitrary numerical syntax codes.
\end{proof}

## Reduction Certificates, Universality, and Halting {#sec:lambda-indices}

### Programs for one-step reduction {#sec:lambda-one-step-programs}

\begin{mathmeta}
  \define{LambdaBetaSuccessors,LambdaReductListCode,LambdaRootReduct,LambdaReductState,LambdaReductProgram}
  \define{LambdaBetaStepTest}
\end{mathmeta}

For the finite syntactic checks here and in §{sec:lambda-reduction-certificates}, apply the beta rules to named terms
using the prescribed capture-avoiding substitution. Keep variable names in these checks. Changes of representative under
alpha-equivalence will be handled separately when joining the steps of a certificate.

For a named term $M$, form the finite list $\LambdaBetaSuccessors{M}$ of its one-step reducts as follows. A variable has
no reducts. At an application $AB$, include the root contraction when $A$ is an abstraction, then include the reducts
obtained by reducing the left side and those obtained by reducing the right side. Under an abstraction, put the binder
around each reduct of the body. Root contraction uses the capture-avoiding substitution already constructed. Induction
on a term shows that every listed term is a one-step reduct; induction on a beta-step derivation shows that every reduct
is listed.

Let $\LambdaReductListCode{M}$ be the numerical code of the list of codes of the named reducts:
$$\LambdaReductListCode{M}:=
\LambdaListCode{\ListMap{\LambdaSyntaxCode{\cdot}}{\LambdaBetaSuccessors{M}}}.$$
The list keeps the indicated order, including repeated entries if distinct redex positions yield the same term. A
structural fold will carry the pair consisting of the original term code and this list code. Keeping the original code
makes the body and binder of a potential root redex available to the application handler.

First define the list contributed by a contraction at the root of an application. Use the abbreviations
$$\begin{aligned}
C(a,b)&:=\LambdaListCons\,
 \bigl(\LambdaSubstCode\,(\LambdaSyntaxField{2}\,a)\,(\LambdaSyntaxField{1}\,a)\,b\bigr)
 \,\ChurchNumeral{0},\\
\LambdaRootReduct&:=\lambdaab{a}{\lambdaab{b}{
 \LambdaSyntaxCase{a}{\ChurchNumeral{0}}{\ChurchNumeral{0}}{C(a,b)}}}.
\end{aligned}$$
Expand $C$ inside the abstractions. If the left term is an abstraction, its body and binder are extracted, substitution
computes the contracted term, and cons puts its code into a singleton list. A variable or application on the left gives
the empty list. In particular, the substitution branch is not evaluated when there is no root redex.

For the internal reductions, define a left-context program and an abbreviation for the combined list:
$$\begin{aligned}
E&:=\lambdaab{b}{\lambdaab{c}{\LambdaTaggedCode{1}\,c\,b}},\\
J(a,b,l,r)&:=\LambdaListAppend\\
 &\quad\bigl(\LambdaListAppend\,(\LambdaRootReduct\,a\,b)
       (\LambdaListMap\,(Eb)\,l)\bigr)\\
 &\quad\bigl(\LambdaListMap\,(\LambdaTaggedCode{1}\,a)\,r\bigr).
\end{aligned}$$
The first map restores the unchanged right term around each left reduct; the second restores the unchanged left term
around each right reduct. Form the state-building programs
$$\begin{aligned}
V&:=\lambdaab{i}{\LambdaNumericPair\,(\LambdaVarCode\,i)\,\ChurchNumeral{0}},\\
A_0&:=\lambdaab{a}{\lambdaab{b}{\lambdaab{l}{\lambdaab{r}{
 \LambdaNumericPair\,(\LambdaTaggedCode{1}\,a\,b)\,J(a,b,l,r)}}}},\\
L_0&:=\lambdaab{i}{\lambdaab{a}{\lambdaab{l}{
 \LambdaNumericPair\,(\LambdaTaggedCode{2}\,i\,a)
 (\LambdaListMap\,(\LambdaTaggedCode{2}\,i)\,l)}}}.
\end{aligned}$$
Expand $J$ in $A_0$. The variable state records its original code and an empty list. The abstraction state restores its
binder around every body reduct.

Extract the two fields of each recursive state and assemble the fold:
$$\begin{aligned}
A&:=\lambdaab{s}{\lambdaab{t}{
 A_0(\LambdaNumericProjection{1}\,s)(\LambdaNumericProjection{1}\,t)
 (\LambdaNumericProjection{2}\,s)(\LambdaNumericProjection{2}\,t)}},\\
L&:=\lambdaab{i}{\lambdaab{s}{
 L_0\,i\,(\LambdaNumericProjection{1}\,s)(\LambdaNumericProjection{2}\,s)}},\\
\LambdaReductState&:=\LambdaSyntaxFold{V}{A}{L},\\
\LambdaReductProgram&:=\lambdaab{e}{\LambdaNumericProjection{2}(\LambdaReductState\,e)},\\
\LambdaBetaStepTest&:=\lambdaab{e}{\lambdaab{d}{
 \LambdaListMember\,d\,(\LambdaReductProgram\,e)}}.
\end{aligned}$$
The last program checks membership of the target code in the computed list. All displayed programs are closed.

\begin{theorem*}[\termdefineas{lambda one-step reduction programs}{One-step reduction programs}]
For every named term $M$,
$$\LambdaReductProgram\,\ChurchNumeral{\LambdaSyntaxCode{M}}
 \to_\beta^*\ChurchNumeral{\LambdaReductListCode{M}}.$$
For named terms $M,N$,
$$\LambdaBetaStepTest\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{\LambdaSyntaxCode{N}}
 \to_\beta^*\begin{cases}\ChurchNumeral{1},&N\in\LambdaBetaSuccessors{M},\\
 \ChurchNumeral{0},&N\notin\LambdaBetaSuccessors{M}.\end{cases}$$
The membership condition is exactly one beta step on named terms with the fixed substitution convention. Both programs
work on every numerical code by decoding it first in this specification; the programs themselves use only code
operations.
\end{theorem*}

\begin{proof}[Proof]
Use structural recursion with the state at $M$ equal to
$$\ChurchNumeral{\NatPair{\LambdaSyntaxCode{M}}{\LambdaReductListCode{M}}}.$$
At a variable, the variable constructor recovers its code and the empty list gives all reducts. At an application,
numerical projections recover both original child codes and both child reduct lists. Constructor inspection computes the
root list: it is empty unless the left child is an abstraction, in which case the substitution program produces exactly
the prescribed contraction. Mapping restores the unchanged context around the left and right reducts. Two concatenations
place the root result first, then the left results, then the right results. The syntax constructor also recovers the
original application code. This is exactly the defining application clause for the reduct list.

At an abstraction, mapping restores the same binder around every body reduct, and the abstraction constructor
reconstructs the original term code. The induction hypotheses and the proved numerical, list and substitution operations
therefore establish the state invariant with finite reductions. Projecting the second state component proves the first
displayed conclusion.

For the final test, apply numerical list membership to the target code and the computed list. Injectivity of syntax
coding identifies membership of the target code with membership of the named target term. Soundness and completeness of
the reduct list then identify this with a named one-step reduction. All inserted constants and handlers are closed.
Finally, the syntax code-decoding identities extend both results to arbitrary natural-number inputs.
\end{proof}

### Finite reduction certificates {#sec:lambda-reduction-certificates}

\begin{mathmeta}
  \define{LambdaCertificateCode,LambdaBetaTest}
  \vars{s}{Nat}
\end{mathmeta}

A \termdefine{lambda reduction certificate} from $M$ to $N$ is a finite list of pairs of named terms. The empty list is
accepted exactly when $M$ and $N$ are alpha-equivalent. A nonempty list beginning with $\Pair{A}{B}$ is accepted exactly
when
$M$ is alpha-equivalent to $A$, the term $B$ belongs to $\LambdaBetaSuccessors{A}$, and the remaining list is accepted
from $B$ to $N$. Each test terminates: lists are finite, the reduct list is finite, and alpha-equivalence is decidable
by comparison of the named terms. The checks at the joins account for changes of representative when passing between
named reductions and reductions of alpha-classes.

\begin{proposition*}[\termdefineas{lambda reduction certificate criterion}{Finite certificates for beta-reduction}]
The alpha-class of $M$ reduces in finitely many beta steps to the alpha-class of $N$ if and only if some reduction
certificate from $M$ to $N$ is accepted.
\end{proposition*}

\begin{proof}[Proof]
Induct on an accepted list. The empty list gives equality of alpha-classes. For a nonempty list, its first pair gives a
raw beta step, which projects to a class step; prepend it to the reduction supplied by the remaining list. Conversely,
induct on a finite class reduction. For its first step, choose raw representatives witnessing that step, as established
in the beta-reduction lemma of §{sec:lambda-calculus}. Prepend this pair to a certificate for the remaining reduction,
using alpha-equivalence at the join. For the empty reduction, use the empty list. The same argument covers arbitrary
choices of the two endpoint representatives.
\end{proof}

Encode certificate lists by
$$\begin{aligned}
\LambdaCertificateCode{[]}&:=0,\\
\LambdaCertificateCode{\Pair{A}{B}::c}&:=
\NatPair{\NatPair{\LambdaSyntaxCode{A}}{\LambdaSyntaxCode{B}}}{\LambdaCertificateCode{c}}+1.
\end{aligned}$$
Decode zero as the empty list. For a positive code $e$, unpair $e-1$, decode the first component as a pair of term
codes, and recursively decode the second as the tail. The tail code is at most $e-1$, hence smaller than $e$, so this
recursion terminates. Induction on lists shows that decoding their codes returns the original lists. For $s\in\NN$, let
$\LambdaBetaTest{s}{M}{N}$ be true when at least one certificate with code less than $s$ is accepted from $M$ to $N$,
and false otherwise.

\begin{corollary*}[\termdefineas{bounded beta certificate test}{Finite-stage detection of beta-reduction}]
Each stage test terminates. Acceptance is preserved when the stage increases, and
$$[M]\to_\beta^*[N]\quad\Longleftrightarrow\quad
\exists s\in\NN\;\LambdaBetaTest{s}{M}{N}=\mathrm{true}.$$
\end{corollary*}

\begin{proof}[Proof]
At a fixed stage only finitely many finite certificates are checked. Increasing the stage retains every code already
checked. If a stage accepts, its successful certificate yields the reduction by the proposition. Conversely, take an
accepted certificate for the reduction and choose a stage greater than its code. At that stage the certificate is
decoded and accepted. Thus every finite successful reduction is eventually detected, even if some other reduction paths
are infinite.
\end{proof}

### Programs for certificate checking {#sec:lambda-certificate-programs}

\begin{mathmeta}
  \define{LambdaCertificateCheck,LambdaBoundedBetaProgram}
  \vars{s}{Nat}
\end{mathmeta}

We now implement the preceding tests by closed lambda terms. A certificate code is the list code of its paired term
codes, so the list recursor applies directly. Its value for a tail will be a function of two further inputs: the current
source code and the fixed target code. Keeping these inputs open allows the source to change after each checked step.

Define
$$\begin{aligned}
T(a,b,r,e,d)&:=\LambdaZeroTest\,(\LambdaAlphaTest\,e\,a)\,\ChurchNumeral{0}\\
 &\quad\bigl(\LambdaZeroTest\,(\LambdaBetaStepTest\,a\,b)\,\ChurchNumeral{0}\,(rbd)\bigr),\\
H&:=\lambdaab{c}{\lambdaab{r}{\lambdaab{e}{\lambdaab{d}{
 T(\LambdaNumericProjection{1}\,c,\LambdaNumericProjection{2}\,c,r,e,d)}}}},\\
\LambdaCertificateCheck&:=\LambdaListFold{\LambdaAlphaTest}{H}.
\end{aligned}$$
Expand $T$ in $H$. The fold's base value compares the two endpoints. Its handler extracts the pair at the head, checks
the alpha-equivalence at the join and the named beta step, and then passes the new source to the tail function. Either
failed check returns zero. All displayed variables in $H$ are bound, so $H$ and $\LambdaCertificateCheck$ are closed.

\begin{theorem*}[\termdefineas{lambda certificate-checking program}{Certificate checking by a lambda term}]
For every certificate $c$ and named terms $M,N$, the term
$$\LambdaCertificateCheck\,\ChurchNumeral{\LambdaCertificateCode{c}}\,
 \ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{\LambdaSyntaxCode{N}}$$
reduces in finitely many beta steps to $\ChurchNumeral{1}$ if $c$ is accepted from $M$ to $N$, and to
$\ChurchNumeral{0}$ otherwise. The same conclusion holds for arbitrary numerical inputs after decoding the certificate
and endpoint codes.
\end{theorem*}

\begin{proof}[Proof]
For each certificate $c$, define a closed term $W_c$ recursively by
$$W_{[]}:=\LambdaAlphaTest,\qquad
W_{\Pair{A}{B}::c}:=H\ChurchNumeral{\NatPair{\LambdaSyntaxCode{A}}{\LambdaSyntaxCode{B}}}W_c.$$
The list-recursion theorem gives the reduction of the checker on the certificate code to $W_c$. Induct on $c$, keeping
both endpoints arbitrary, to compute the value of $W_c$ at their codes. For the empty list, the alpha-equivalence
program gives exactly the acceptance condition. For a nonempty list, the two numerical projections extract the codes of
$A,B$. If the source is not alpha-equivalent to $A$, the first test returns zero. Otherwise the second test checks
membership of $B$ in the named reduct list of $A$. Failure again returns zero; success leaves $W_c$ applied to the codes
of $B,N$, to which the induction hypothesis applies. These are exactly the three acceptance requirements for a nonempty
certificate. The coding and decoding identities extend the calculation to all numerical inputs.
\end{proof}

The finite-stage test is obtained by numerical primitive recursion. Set
$$\begin{aligned}
G&:=\lambdaab{e}{\lambdaab{d}{\lambdaab{k}{\lambdaab{r}{
 \LambdaZeroTest\,r\,(\LambdaCertificateCheck\,k\,e\,d)\,\ChurchNumeral{1}}}}},\\
\LambdaBoundedBetaProgram&:=\lambdaab{e}{\lambdaab{d}{\lambdaab{s}{
 \LambdaRecursor\,(Ged)\,\ChurchNumeral{0}\,s}}}.
\end{aligned}$$
The initial value is zero because no certificate has yet been checked. At step $k$, a previous success is retained;
otherwise the certificate with code $k$ is checked. Both programs are closed.

\begin{theorem*}[\termdefineas{lambda finite-stage reduction program}{Finite-stage reduction testing by a lambda term}]
For named terms $M,N$ and $s\in\NN$, put
$$D_{M,N,s}:=\LambdaBoundedBetaProgram\,
 \ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{\LambdaSyntaxCode{N}}\,\ChurchNumeral{s}.$$
Then
$$D_{M,N,s}\to_\beta^*\begin{cases}
 \ChurchNumeral{1},&\LambdaBetaTest{s}{M}{N}=\mathrm{true},\\
 \ChurchNumeral{0},&\LambdaBetaTest{s}{M}{N}=\mathrm{false}.
\end{cases}$$
This calculation also holds for arbitrary numerical endpoint codes through decoding. Moreover,
$$[M]\to_\beta^*[N]\quad\Longleftrightarrow\quad
 \exists s\in\NN\;D_{M,N,s}\to_\beta^*\ChurchNumeral{1}.$$
\end{theorem*}

\begin{proof}[Proof]
The stage-zero test is false. The test at stage $k+1$ is the disjunction of the test at stage $k$ and acceptance of the
certificate with code $k$. The step program computes precisely this disjunction by the certificate-checking theorem and
zero testing. Apply numerical primitive recursion with the numeral of this Boolean value as the state. It gives the
asserted finite reduction for every stage, including stage zero. Decode arbitrary endpoint codes to obtain the general
input statement.

For the last equivalence, a finite reduction has a certificate, which is detected once the stage exceeds its code.
Conversely, if $D_{M,N,s}$ reduces to $\ChurchNumeral{1}$, uniqueness of numeral outputs forces the stage test to be
true: a false test would also give a reduction to $\ChurchNumeral{0}$. The finite-certificate criterion then gives the
desired reduction of alpha-classes.
\end{proof}

### Coding program inputs and testing outputs {#sec:lambda-program-input-codes}

\begin{mathmeta}
  \define{LambdaNumeralCodeProgram,LambdaClosedTest,LambdaProgramCode,LambdaProgramInputCode,LambdaOutputTest}
  \define{LambdaOutputCandidate}
  \vars{e,m,n,s,i,k,r}{Nat}
\end{mathmeta}

To apply the finite tests to numerical computations, we must construct the syntax codes of their inputs and outputs. Fix
the named representative of $\ChurchNumeral{n}$ whose iterator binder is $x_1$ and whose initial-value binder is $x_2$.
Whenever a syntax code of a numeral is used below, it refers to this representative. Its body starts at $x_2$ and
acquires one application of $x_1$ at each step.

Since the variable codes of $x_1,x_2$ are $3,6$, define
$$\LambdaNumeralCodeProgram:=\lambdaab{n}{
 \LambdaTaggedCode{2}\,\ChurchNumeral{1}\,
 \bigl(\LambdaTaggedCode{2}\,\ChurchNumeral{2}\,
   (n(\LambdaTaggedCode{1}\,\ChurchNumeral{3})\ChurchNumeral{6})\bigr)}.$$
The inner iteration builds the body code. The two abstraction constructors then bind $x_2$ and $x_1$, in that order.

\begin{proposition*}[\termdefineas{lambda numeral-code program}{Constructing numeral codes}]
The term $\LambdaNumeralCodeProgram$ is closed and, for every $n\in\NN$,
$$\LambdaNumeralCodeProgram\,\ChurchNumeral{n}
 \to_\beta^*\ChurchNumeral{\LambdaSyntaxCode{\ChurchNumeral{n}}}.$$
\end{proposition*}

\begin{proof}[Proof]
Apply the Church-numeral iteration formula to the closed function $\LambdaTaggedCode{1}\,\ChurchNumeral{3}$ and initial
value $\ChurchNumeral{6}$. Induction on the number of iterations shows that the result reduces to the numeral for the
code of the corresponding body: the base is the code of $x_2$, and the application-code program adds $x_1$ at the next
step. Apply the abstraction-code equations with binder indices two and one. The result is the Church numeral
for the syntax code of the fixed named representative.
The constants are closed and the remaining variable is bound.
\end{proof}

The enumeration $P_e$ in §{sec:lambda-syntax-codes} replaces an open decoded term with the zero numeral. To implement
this convention, observe that every free variable $x_i$ of a named term $M$ satisfies $i\le\LambdaSyntaxCode{M}$. At a
variable this follows from $i\le3i$. At an application, a free variable belongs to one of the two children, whose code
is smaller than the parent code. At an abstraction, removing the binder introduces no new free variable and the body
code is again smaller. Structural induction proves the bound. Thus checking the variable indices from zero through the
code suffices to decide whether the term is closed.

Define the closed programs
$$\begin{aligned}
J&:=\lambdaab{e}{\lambdaab{i}{\lambdaab{r}{
 \LambdaZeroTest\,r\,(\LambdaFreeVarTest\,e\,i)\,\ChurchNumeral{1}}}},\\
\LambdaClosedTest&:=\lambdaab{e}{\LambdaZeroTest\,
 \bigl(\LambdaRecursor\,(Je)\,\ChurchNumeral{0}\,(\LambdaSucc\,e)\bigr)
 \,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
\LambdaProgramCode&:=\lambdaab{e}{\LambdaZeroTest\,(\LambdaClosedTest\,e)
 \,\ChurchNumeral{\LambdaSyntaxCode{\ChurchNumeral{0}}}\,e},\\
\LambdaProgramInputCode&:=\lambdaab{e}{\lambdaab{n}{
 \LambdaTaggedCode{1}\,(\LambdaProgramCode\,e)\,(\LambdaNumeralCodeProgram\,n)}}.
\end{aligned}$$
The recurrence records whether a free variable has already been found. The outer zero test reverses this answer to
obtain the closedness test. The program-code selector then implements the fallback convention, and the final constructor
attaches the numerical input.

\begin{proposition*}[\termdefineas{lambda closed-program code construction}{Codes of closed programs and their inputs}]
For $e\in\NN$, let $Q_e$ be $\LambdaSyntaxDecode{e}$ if that term is closed, and the fixed representative of
$\ChurchNumeral{0}$ otherwise. Thus $[Q_e]=P_e$. For every $e,n\in\NN$,
$$\begin{aligned}
\LambdaClosedTest\,\ChurchNumeral{e}&\to_\beta^*
 \begin{cases}\ChurchNumeral{1},&\FreeVarsLambda{\LambdaSyntaxDecode{e}}=\varnothing,\\
 \ChurchNumeral{0},&\FreeVarsLambda{\LambdaSyntaxDecode{e}}\ne\varnothing,\end{cases}\\
\LambdaProgramCode\,\ChurchNumeral{e}&\to_\beta^*\ChurchNumeral{\LambdaSyntaxCode{Q_e}},\\
\LambdaProgramInputCode\,\ChurchNumeral{e}\,\ChurchNumeral{n}
 &\to_\beta^*\ChurchNumeral{\LambdaSyntaxCode{Q_e\ChurchNumeral{n}}}.
\end{aligned}$$
\end{proposition*}

\begin{proof}[Proof]
Fix the decoded term $M$. After $i$ iterations, the state is one exactly when some variable with index less than $i$ is
free in $M$, and zero otherwise. The assertion holds initially. At the next step, $J$ preserves a previous success or
tests the next variable by the free-variable program. The numerical recursor therefore produces this state after
$\LambdaSyntaxCode{M}+1$ steps. The free-variable bound shows that the state is zero exactly when $M$ is closed. Zero
testing gives the first conclusion. The selector then returns either the original code or the code of the fixed zero
numeral. Finally use the numeral-code and application-code equations. The code-decoding identity makes the argument
valid for every natural-number index.
\end{proof}

We can now test a proposed numerical output without selecting a single reduction path. Define
$$\begin{aligned}
\LambdaOutputTest&:=\lambdaab{e}{\lambdaab{n}{\lambdaab{m}{\lambdaab{s}{
 \LambdaBoundedBetaProgram\,(\LambdaProgramInputCode\,e\,n)
 (\LambdaNumeralCodeProgram\,m)\,s}}}},\\
\LambdaOutputCandidate&:=\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
 \LambdaOutputTest\,e\,n\,(\LambdaNumericProjection{1}\,k)
 (\LambdaNumericProjection{2}\,k)}}}.
\end{aligned}$$
A candidate $k=\NatPair{m}{s}$ combines the proposed output $m$ and the finite search stage $s$. Both displayed programs
are closed. Searching such pairs treats every possible output and every finite certificate bound.

\begin{theorem*}[\termdefineas{lambda numerical-output candidate tests}{Finite tests for numerical outputs}]
For every $e,n,m,s\in\NN$,
$$\LambdaOutputTest\,\ChurchNumeral{e}\,\ChurchNumeral{n}\,\ChurchNumeral{m}\,\ChurchNumeral{s}
 \to_\beta^*\begin{cases}
 \ChurchNumeral{1},&\LambdaBetaTest{s}{Q_e\ChurchNumeral{n}}{\ChurchNumeral{m}}=\mathrm{true},\\
 \ChurchNumeral{0},&\LambdaBetaTest{s}{Q_e\ChurchNumeral{n}}{\ChurchNumeral{m}}=\mathrm{false}.
 \end{cases}$$
The candidate program gives the same answer on the input $\ChurchNumeral{\NatPair{m}{s}}$. In particular,
$$\begin{aligned}
P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}
\quad\Longleftrightarrow\quad
\exists s\in\NN\;\LambdaOutputCandidate\,\ChurchNumeral{e}\,\ChurchNumeral{n}
 \,\ChurchNumeral{\NatPair{m}{s}}\to_\beta^*\ChurchNumeral{1}.
\end{aligned}$$
Any two successful candidates for fixed $e,n$ have the same output component, even if their stage components differ.
\end{theorem*}

\begin{proof}[Proof]
First compute the code of the program applied to its input and the code of the proposed output numeral. The finite-stage
reduction tester gives the first formula. The two projections of a candidate pair supply exactly its output and stage,
so the candidate program gives the same result. Uniqueness of numeral outputs shows that a candidate program reduces to
one exactly when its Boolean test is true; a false test already yields zero.

A reduction of $P_e\ChurchNumeral{n}$ to $\ChurchNumeral{m}$ has a finite accepted certificate between the chosen
representatives. Some stage exceeds its code, so the corresponding candidate succeeds. Conversely, a successful
candidate gives a true finite-stage test and hence the asserted reduction. If two candidates succeed, both proposed
numerals are outputs of the same term $P_e\ChurchNumeral{n}$. Uniqueness of numeral outputs makes their numerical values
equal.
\end{proof}

### Exposing an abstraction by head reduction {#sec:lambda-head-exposure}

\begin{mathmeta}
  \define{LambdaHeadSteps,LambdaHeadStep,LambdaStandardSteps}
\end{mathmeta}

A \termdefine{head beta step} contracts a redex at the root or takes such a step in the operator of an application. It
does not enter an argument or an abstraction body. Write $\LambdaHeadSteps{M}{N}$ for finitely many head steps,
including none. Head steps are beta steps. They are preserved by substitution: a root redex remains a root redex after
capture-avoiding substitution, and substitution preserves application contexts on the operator side.

We use Kashima's inductive organization of standard reduction [@Kashima2000]. Define $\LambdaStandardSteps{M}{N}$ by the
following three rules:
$$\frac{\LambdaHeadSteps{L}{x}}{\LambdaStandardSteps{L}{x}},\qquad
\frac{\LambdaHeadSteps{L}{AB}\quad\LambdaStandardSteps{A}{C}\quad\LambdaStandardSteps{B}{D}}
 {\LambdaStandardSteps{L}{CD}},$$
$$\frac{\LambdaHeadSteps{L}{\lambdaab{x}{A}}\quad\LambdaStandardSteps{A}{B}}
 {\LambdaStandardSteps{L}{\lambdaab{x}{B}}}.$$
Each rule first exposes the required outer constructor by head steps and then treats its immediate subterms.

\begin{lemma*}[\termdefineas{inductive lambda standard reduction}{Inductive standard reduction}]
For all terms modulo alpha-equivalence,
$$M\to_\beta^*N\quad\Longleftrightarrow\quad\LambdaStandardSteps{M}{N}.$$
\end{lemma*}

\begin{proof}[Proof]
The rules give reflexivity by structural induction and imply finite beta-reduction. Prefixing a derivation by head steps
also preserves the relation. Its substitution property follows by induction on the derivation, strengthened to two
finite substitution lists whose final images of each variable are related. At an abstraction, choose a binder fresh for
both bodies and both lists, rename both bodies, and prepend this renaming to each list. This gives
$$\LambdaStandardSteps{M}{N},\quad\LambdaStandardSteps{A}{B}
\quad\Longrightarrow\quad
\LambdaStandardSteps{\SubstLambda{M}{x}{A}}{\SubstLambda{N}{x}{B}}.$$

Now append one beta step. For a root contraction, invert the application rule and then the abstraction rule. Their head
prefixes expose a root redex in the source; contract it and apply the substitution property to its body and argument.
Independence of contraction from the binder name identifies the resulting target. Application contexts use the
corresponding subderivation.

For an abstraction context, strengthen this argument to an arbitrary finite substitution list. Choose a common binder
fresh also for the earlier source of the standard derivation. Head steps introduce no free variables, so the exposed
abstraction can be written with this binder; the substitution property renames its body derivation. Prepending the
binder renaming to the substitution list makes the induction hypothesis applicable. Lift the resulting body derivation
under the common binder. Thus the relation is closed under appending one beta step, and induction on a finite beta
reduction proves the forward implication.
\end{proof}

\begin{corollary*}[\termdefineas{lambda head exposure}{Head exposure of an abstraction}]
If $M\to_\beta^*\lambdaab{x}{A}$, then $\LambdaHeadSteps{M}{\lambdaab{y}{B}}$ for some $y,B$. In particular, a term with
a numerical output reaches an abstraction by head steps alone.
\end{corollary*}

\begin{proof}[Proof]
Apply the lemma. The last rule of a derivation with an abstraction as its target must be the abstraction rule, since the
three outer constructors remain distinct on alpha-classes. Its head prefix gives the required reduction. Every Church
numeral is an abstraction.
\end{proof}

\begin{lemma*}[\termdefineas{lambda leading head step}{Moving a head step to the front}]
Write $\LambdaHeadStep{M}{N}$ for one head step. If $L\to_\beta^*M$ and $\LambdaHeadStep{M}{N}$, then some $P$ satisfies
$$\LambdaHeadStep{L}{P}\quad\text{and}\quad P\to_\beta^*N.$$
\end{lemma*}

\begin{proof}[Proof]
Replace the first reduction by a standard derivation and induct on the final head step. For a root contraction, invert
the application rule and then the abstraction rule. Their head prefixes, followed by the exposed root contraction, form
a nonempty head reduction from $L$. Remove its first step. The remaining head steps followed by the substitution of the
related argument into the related body reach $N$ by beta-reduction. For a head step in the operator, apply the induction
hypothesis to the operator subderivation, lift the resulting head step through application, and prepend the
application's head prefix. This is again a nonempty head reduction. After its first step, finish the operator and
argument reductions. These two cases prove the assertion.
\end{proof}

\begin{proposition*}[\termdefineas{lambda infinite head stages}{Infinite head stages exclude numerical output}]
Suppose terms $S_0,S_1,\ldots$ satisfy, for every $k$, a reduction
$$\LambdaHeadStep{S_k}{A_k}\to_\beta^*S_{k+1}$$
for some $A_k$. Then $S_0$ has no numerical output.
\end{proposition*}

\begin{proof}[Proof]
A numerical output would give a finite head reduction to an abstraction by head exposure. Prove the stronger assertion
that, whenever $M$ has such a head reduction and $M\to_\beta^*S_0$, no infinite sequence as displayed can start at
$S_0$. Induct on the length of the chosen head reduction from $M$. If the length is zero, $M$ is already an abstraction.
Moving the first stage's head step to the front would give a head step from this abstraction, which is impossible.
Otherwise write the first head step as $\LambdaHeadStep{M}{N}$. Moving the first stage's head step to the front gives
another head step from $M$, followed by a beta-reduction to $S_1$. Head steps are deterministic: an abstraction cannot
step, and an application either has a root redex or inherits the unique head step of its operator. Thus the new head
step also ends at $N$. Apply the induction hypothesis to the shorter head reduction from $N$ and the shifted sequence
$S_1,S_2,\ldots$.
\end{proof}

### Searching output candidates {#sec:lambda-output-search}

\begin{mathmeta}
  \define{LambdaResultSearchKernel,LambdaResultSearch,LambdaOutputSearch}
  \vars{e,k,m,n}{Nat}
\end{mathmeta}

We need search to produce a result only in its successful branch. For closed terms $G,F$, choose distinct binders $s,k$
fresh for them and put
$$\LambdaResultSearchKernel{G}{F}:=\lambdaab{s}{\lambdaab{k}{
\LambdaZeroTest\,(Gk)\,(Fk)\,\bigl((ss)(\LambdaSucc\,k)\bigr)}}.$$
Define one closed search term by
$$\LambdaResultSearch:=\lambdaab{g}{\lambdaab{f}{
(\LambdaResultSearchKernel{g}{f}\,\LambdaResultSearchKernel{g}{f})\ChurchNumeral{0}}}.$$
Expand the kernels inside the abstractions, with their binders distinct from $g,f$. The test is $G$; the successful
branch applies $F$ to the successful candidate. The continuation retains both terms and advances to the next candidate.

\begin{lemma*}[\termdefineas{lambda search with a result function}{Search with a result function}]
Let $G,F$ be closed. If $G\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{0}$ and every $G\ChurchNumeral{k}$ with $k<j$
reduces to a positive numeral, then
$$\LambdaResultSearch\,G\,F\to_\beta^*F\ChurchNumeral{j}.$$
If $G\ChurchNumeral{k}$ reduces to a positive numeral for every $k\in\NN$, then $\LambdaResultSearch\,G\,F$ has no
numerical output.
\end{lemma*}

\begin{proof}[Proof]
Put $S_k:=(\LambdaResultSearchKernel{G}{F}\,\LambdaResultSearchKernel{G}{F})\ChurchNumeral{k}$. Two beta steps expose
the test, the first being a head step. A positive test followed by successor reduces this term to $S_{k+1}$; a zero test
reduces it to $F\ChurchNumeral{k}$. Backward induction from the successful candidate proves the first assertion, after
the two outer contractions supplying $G,F$.

If every test is positive, these reductions give infinitely many stages, each beginning with a head step. The
infinite-stage proposition in §{sec:lambda-head-exposure} excludes a numerical output from $S_0$. If the outer search
term had a numerical output, confluence would give the same output from $S_0$, since numerals are normal forms. This
contradiction proves the second assertion.
\end{proof}

The candidate tester returns one on success, whereas search stops when its test returns zero. Reverse the answers and
define
$$\begin{aligned}
T&:=\lambdaab{e}{\lambdaab{n}{\lambdaab{k}{
 \LambdaZeroTest\,(\LambdaOutputCandidate\,e\,n\,k)\,\ChurchNumeral{1}\,\ChurchNumeral{0}}}},\\
\LambdaOutputSearch&:=\lambdaab{e}{\lambdaab{n}{
 \LambdaResultSearch\,(Ten)\,\LambdaNumericProjection{1}}}.
\end{aligned}$$
All constants are closed and all displayed variables are bound. Thus $\LambdaOutputSearch$ is one closed term receiving
the program index and its numerical input. It searches the candidate codes in order and extracts the output component in
the successful branch.

\begin{proposition*}[\termdefineas{lambda successful output search}{Exact numerical output search}]
For every $e,n,m\in\NN$,
$$\LambdaOutputSearch\,\ChurchNumeral{e}\,\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}
\quad\Longleftrightarrow\quad
P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}.$$
In particular, one term has a numerical output if and only if the other does.
\end{proposition*}

\begin{proof}[Proof]
Suppose the indexed program outputs $m$. The candidate-test theorem supplies a successful pair whose output component is
$m$. Let $j$ be the least successful candidate code. Every preceding candidate fails, so
$T\ChurchNumeral{e}\ChurchNumeral{n}$ returns one before $j$ and zero at $j$. Search with the result function
$\LambdaNumericProjection{1}$ reaches the first projection of $\ChurchNumeral{j}$. All successful candidates have the
same output component, so this projection reduces to $\ChurchNumeral{m}$.

If the indexed program has no numerical output, every candidate test fails. The reversed tests all return one, so the
no-output part of the search lemma applies. The two outer contractions supplying the index and input preserve any
putative numeral output by confluence and normality of numerals; hence the full term has no numerical output either.

Finally, if the indexed program has an output, completeness produces that same numeral from the search term. Uniqueness
of numeral outputs excludes any different value. Together with the no-output case this proves both directions without a
termination assumption.
\end{proof}

### Universal evaluation and program indices {#sec:lambda-universal-evaluation}

\begin{mathmeta}
  \vars{e,n}{Nat}
\end{mathmeta}

For each $e$, define the partial numerical function $\varphi_e$ by
$$\varphi_e(n)=m\quad\Longleftrightarrow\quad
P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}.$$
Uniqueness of numeral outputs makes this a partial function. Write $\simeq$ for equality of partial values: either both
sides are undefined or both are defined and equal. The closed term $\LambdaOutputSearch$ just constructed computes a
\termdefineas{universal program}{universal evaluator}, a partial function
$\PartialFunctionMap{U}{\omega\times\omega}{\omega}$ satisfying
$$
U(e,n)\simeq\varphi_e(n).
$$
Indeed, the exact-output proposition proves equality of every numerical value and of the domains. The evaluator searches
finite reduction certificates and extracts an output only after its certificate is accepted. Thus program indices and
the search over computations are both handled by lambda terms on natural-number codes.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次の3つの結果を利用する旨の導入ラベル。結果そのものは後続の対応対象。)
--> Three standard consequences are used throughout the effective chapters.<!--
formalization: skip-end
-->

*   **Parameterization.** If a computable procedure computes a partial function $\psi(\vec a,n)$ from parameters $\vec
    a$ and input $n$, then there is a computable function producing an index $e_{\vec a}$ such that
    $$
    \varphi_{e_{\vec a}}(n) \simeq \psi(\vec a,n).
    $$
    This is the lambda-calculus form of the $s$--$m$--$n$ theorem.
*   **Recursion theorem.** Every total computable operator on program indices has an extensional fixed point:
    if $F$ is total computable, there is $e_0$ with $\varphi_{e_0}\simeq\varphi_{F(e_0)}$.
    §{sec:lambda-index-recursion} constructs the index explicitly from syntax specialization and proves
    equality of partial values, including undefined values. It also proves a version that preserves an arbitrary
    input function with the same index for all input functions.
    Lambda terms also admit a fixed-point combinator
    $$\mathsf Y := \lambdaab{f}{(\lambdaab{x}{f(xx)})(\lambdaab{x}{f(xx)})}.$$
    It satisfies $\BetaConvertible{\mathsf Y F}{F(\mathsf Y F)}$. This is not a one-step reduction identity: with
    $A=\lambdaab{x}{F(xx)}$, both sides reduce to $F(AA)$.
    <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    パラメータ固定の正確な部分値はuniform_partial_parameter_indices、recursion
    theoremと一様oracle版は既存の2定理、Yの共通還元はyCombinator_convertible、
    Kのr.e./非決定性はdiagonalHalts_enumerable/diagonalHalts_not_decidableへ対応。
    未リンク部分はそれらを利用するrealizability節への参照案内のみ。)
    --> The index theorem and this term construction provide the self-reference used in
    §{sec:effective-topos-internal-logic} and §{sec:realizability-pca}.<!--
    formalization: skip-end
    -->
*   **Undecidability of halting.** The \termdefine{halting problem} concerns the set
    $$
    K=\{e:\varphi_e(e)\downarrow\}
    $$
    which is recursively enumerable but not decidable.

\begin{proof}[Proof of undecidability] If $K$ were decidable, define a partial computable function
$$
d(e)=
\begin{cases}
\uparrow, & \varphi_e(e)\downarrow,\\
0, & \varphi_e(e)\uparrow.
\end{cases}
$$
Let $d=\varphi_m$ for some index $m$. Then
$$
\varphi_m(m)\downarrow
\quad\Longleftrightarrow\quad
d(m)\downarrow
\quad\Longleftrightarrow\quad
\varphi_m(m)\uparrow,
$$
a contradiction. Hence $K$ is not decidable.
\end{proof}

The same argument gives the usual halting language. Using a computable binary-string code
$\BinaryPair{e}{n}\in\finseq{2}$ for pairs of natural numbers, set
$$
H:=\{\BinaryPair{e}{n}\in\finseq{2}:\varphi_e(n)\downarrow\}.
$$
Then $H$ is recursively enumerable, because the universal evaluator semidecides it, but $H$ is not decidable.
