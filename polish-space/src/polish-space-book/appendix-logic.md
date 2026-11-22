# Appendix: Logic {#sec:appendix-logic}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
付録の目的と、古典的意味論と内部論理の取り扱いの違いを案内する導入文。新規の論理体系や翻訳を構成する段落ではない。)
-->
This appendix collects the first-order logical background used throughout the text. The point is to separate syntactic
proof from classical semantic truth in a model, because §{sec:forcing} and §{sec:appendix-set-theory} use that relation
constantly. Internal intuitionistic and realizability truth are different ambient readings of formulas; they are treated
with the categorical machinery in Appendix §{sec:appendix-category-realizability}.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
構文・証明体系・完全性・モデル理論・不完全性・定義拡張への節案内。各局所証明は参照先で別途対象となる。)
--> The development starts with syntax and capture-avoiding substitution in §{sec:fol-language}, then separates the
proof calculus of §{sec:fol-deduction} from the structures and soundness theorem of §{sec:fol-semantics}.
§{sec:fol-completeness} constructs Henkin models and proves completeness; §{sec:fol-model-theory} derives compactness
and the elementary-substructure results. The final sections prove the first incompleteness theorem and justify
extension by definition. §{sec:appendix-set-theory} specializes this logic to $L_\in$ and ZFC.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \vars{x,y,z,t,t_0,t_1,t_i,f}{fo-term}
  \vars{\varphi,\psi,\chi}{fo-formula}
  \vars{\Gamma,\Delta}{fo-context}
\end{mathmeta}

## First-order Syntax and Substitution {#sec:fol-language}

ZFC is a theory in \termdefine{first-order logic} over the \termdefineas{language of set theory}{language $L_\in$}, and
this is the \termdefine{logic} used throughout the set-theoretic development. The language has one non-logical symbol,
the binary relation $\in$; equality $=$ is a logical primitive. It is useful to define first-order syntax for a general
language first, because later sections use definitional extensions of $L_\in$ and category/realizability sections use
other first-order languages.

### Languages, Terms, and Formulas {#sec:fol-syntax}

**Languages.** A first-order language is a tuple
$$L=\Tuple{\mathrm{Rel}_L,\mathrm{Fun}_L,\mathrm{ar}_L},$$
where $\mathrm{Rel}_L$ is a set of relation symbols, $\mathrm{Fun}_L$ is a set of function symbols, disjoint
from the relation symbols and from the logical symbols and variables, and
$$\mathrm{ar}_L : \mathrm{Rel}_L \cup \mathrm{Fun}_L \to \omega$$
assigns each symbol its \termdefine{arity}. Syntactically, an $n$-ary symbol is one that expects $n$ input terms. A
constant symbol is just a $0$-ary function symbol. Equality $=$ is logical, not part of $L$. The language of set theory
is the special case $L_\in=\Tuple{\{\in\},\emptyset,\mathrm{ar}}$, where $\mathrm{ar}(\in)=2$. The definitional
extensions
used to add symbols such as $\emptyset$, $\cup$, and $\mathrm{dom}$ are formalized in §{sec:definitional-extensions}.

**Syntax.** Fix a countably infinite set of \termdefineas{variable}{variables} $\mathrm{Var}=\{x_0,x_1,x_2,\ldots\}$,
indexed by $\omega$ and well-ordered by the index — so phrases like "the first variable not in a given finite set $S
\IncludedIn \mathrm{Var}$" pick out a unique $x_n$, namely the one with smallest index. We usually write elements as
$x,y,z,\ldots$. The \termdefineas{term}{terms} of a language $L$ are defined recursively:

*   Every variable $x$ is a term.
*   If $f$ is an $n$-ary function symbol and $t_1,\ldots,t_n$ are terms, then $f(t_1,\ldots,t_n)$ is a term.
*   Nothing else is a term.

For $n=0$ the second clause gives a constant term, usually written $c$ rather than $c()$. For pure $L_\in$, the only
terms are variables.

Equivalently, in EBNF summary form,
$$
\textit{Term} ::= \textit{Var} \mid f(\textit{Term},\ldots,\textit{Term}),
$$
where $f$ ranges over function symbols and the number of displayed arguments is the arity of $f$. The case of arity $0$
gives a constant symbol.

The \termdefineas{atomic formula}{atomic formulas} are:

*   $\bot$, called \termdefine{falsum}, satisfied in no interpretation.
*   $t_0=t_1$, where $t_0,t_1$ are terms.
*   $R(t_1,\ldots,t_n)$, where $R$ is an $n$-ary relation symbol and $t_1,\ldots,t_n$ are terms.

In $L_\in$, the relation-symbol atomic formulas are exactly $t_0 \in t_1$; $\bot$ and equalities $t_0=t_1$ are still
atomic formulas.

The \termdefineas{formula}{formulas} are defined recursively:

*   Every atomic formula is a formula.
*   If $\varphi$ and $\psi$ are formulas, then $(\varphi \land \psi)$, $(\varphi \lor \psi)$, and $(\varphi \to \psi)$
    are formulas.
*   If $\varphi$ is a formula and $x$ is a variable, then $(\forallbind{x}{\varphi})$ and $(\existsbind{x}{\varphi})$
    are formulas.
*   Nothing else is a formula.

Equivalently, in EBNF summary form,
$$
\begin{aligned}
\textit{Atom} &::= \bot\\
&\mid \textit{Term}=\textit{Term}\\
&\mid R(\textit{Term},\ldots,\textit{Term}),\\
\textit{Formula} &::= \textit{Atom}\\
&\mid (\textit{Formula}\land\textit{Formula})\\
&\mid (\textit{Formula}\lor\textit{Formula})\\
&\mid (\textit{Formula}\to\textit{Formula})\\
&\mid (\forallbind{\textit{Var}}{\textit{Formula}})\\
&\mid (\existsbind{\textit{Var}}{\textit{Formula}}).
\end{aligned}
$$
Here $R$ ranges over relation symbols, again with the arity determining the number of arguments.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
完全な括弧付き構文と、通常の文章での括弧省略に関する表記規約。新規の構文解析器の正当性や一意性を証明する箇所ではない。)
-->
Thus a formal formula built with binary connectives or quantifiers is fully parenthesized: for example $((\varphi \land
\psi) \land \chi)$ and $((\forallbind{x}{\varphi}) \land \psi)$, not the raw strings $\varphi \land \psi \land \chi$ or
$\forallbind{x}{\varphi} \land \psi$. In ordinary prose we omit parentheses when associativity or precedence makes the
intended parse clear.<!--
formalization: skip-end
-->

Negation and the biconditional are abbreviations:
$$\neg\varphi \;:=\; \varphi \to \bot, \qquad
\varphi \leftrightarrow \psi \;:=\; (\varphi \to \psi) \land (\psi \to \varphi).$$
When parentheses are omitted, we use the precedence convention
$$\forall x,\ \exists x \;>\; \neg \;>\; \land \;>\; \lor \;>\; \to \;>\; \leftrightarrow,$$
with $\land$ and $\lor$ parsed left-associatively and $\to$ parsed right-associatively.

\begin{mathmeta}
  \type{fo-term}
  \type{fo-formula}
  \type{fo-context}
  \type{lambda-term}
  \notationtype{\FreeVars}{fo-term}{\FreeVarsTerm}
  \notationtype{\FreeVars}{fo-formula}{\FreeVarsFormula}
  % Context free variables reuse the formula free-variable notation-index entry.
  \notationtype{\FreeVars}{fo-context}{\FreeVarsFormula}
  \notationtype{\FreeVars}{lambda-term}{\FreeVarsLambda}
  \notationtype{\subst}{fo-term}{SubstTerm}
  \notationtype{\subst}{fo-formula}{SubstFormula}
  \notationtype{\subst}{lambda-term}{SubstLambda}
  \inferbinder{\forallbind}{fo-formula}
  \inferbinder{\existsbind}{fo-formula}
  \inferatom{\bot}{fo-formula}
  % Infix levels increase as binding strength decreases.
  \inferinfix{=}{fo-formula}{70}{non}
  \inferinfix{\land}{fo-formula}{80}{left}
  \inferinfix{\lor}{fo-formula}{85}{left}
  \inferinfix{\to}{fo-formula}{90}{right}
  \inferhead{upper}{fo-formula}
  \inferhead{lower}{fo-term}
  \inferpostfix{\subst}
  \vars{x,y,z,t,t_0,t_1,t_i,f}{fo-term}
  \vars{\varphi,\psi,\chi}{fo-formula}
  \vars{\Gamma,\Delta}{fo-context}
  \define{FreeVarsTerm}
\end{mathmeta}

An occurrence of a variable $x$ inside the scope of a binding $\forall x$ or $\exists x$ is
\termdefineas{bound variable occurrence}{bound}; an occurrence not so bound is
\termdefineas{free variable occurrence}{free}. A variable is
\termdefineas{free variable}{free in} a term or formula when it has at least one free occurrence there. The set
$\FreeVars{t}$ of free variables of a term $t$ is defined by induction on $t$:
$$\begin{aligned}
\FreeVars{x} &= \{x\}, \\
\FreeVars{f(t_1,\ldots,t_n)} &= \bigcup_i \FreeVars{t_i},
\end{aligned}$$
where $x$ is a variable and $f$ is an $n$-ary function symbol; the $n=0$ case covers constants, for which the empty
union gives $\emptyset$.

\begin{mathmeta}
  \define{FreeVarsFormula}
\end{mathmeta}

The set $\FreeVars{\varphi}$ of free variables of a formula $\varphi$ is then defined by induction on $\varphi$:
$$\begin{aligned}
\FreeVars{\bot} &= \emptyset, \\
\FreeVars{R(t_1,\ldots,t_n)} &= \bigcup_i \FreeVars{t_i}, \\
\FreeVars{t_0=t_1} &= \FreeVars{t_0} \cup \FreeVars{t_1}, \\
\FreeVars{\varphi \land \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
\FreeVars{\varphi \lor \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
\FreeVars{\varphi \to \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
\FreeVars{\forallbind{x}{\varphi}} &= \SetDifference{\FreeVars{\varphi}}{\{x\}}, \\
\FreeVars{\existsbind{x}{\varphi}} &= \SetDifference{\FreeVars{\varphi}}{\{x\}}.
\end{aligned}$$
A \termdefine{sentence}, also called a \termdefineas{logical proposition}{proposition}, is a formula with
$\FreeVars{\varphi} = \emptyset$ — its truth value depends only on the interpretation of the non-logical symbols of $L$,
not on a variable assignment. For $L_\in$, the only such symbol is $\in$.

### Capture-Avoiding Substitution and Bound Names {#sec:fol-substitution}

\begin{mathmeta}
  \define{SubstTerm,SubstFormula}
\end{mathmeta}

**Substitution.** Fix a variable $x$ and a term $t$. The \termdefine{substitution} $t_0\subst{x}{t}$ of $t$ for $x$ in a
term $t_0$ is defined by induction on $t_0$:
$$\begin{aligned}
y\subst{x}{t} &:= \begin{cases}
t & \text{if } y = x, \\
y & \text{if } y \ne x,
\end{cases}\\
f(t_1,\ldots,t_n)\subst{x}{t} &:= f(t_1\subst{x}{t},\ldots,t_n\subst{x}{t}),
\end{aligned}$$
where $y$ is a variable and $f$ is an $n$-ary function symbol; the $n=0$ case covers constants.

The \termuse{substitution} $\varphi\subst{x}{t}$ of $t$ for $x$ in a formula $\varphi$ replaces every free occurrence of
$x$ by $t$, defined by induction on $\varphi$:
$$\begin{aligned}
\bot\subst{x}{t} &:= \bot, \\
R(t_1,\ldots,t_n)\subst{x}{t} &:= R(t_1\subst{x}{t},\ldots,t_n\subst{x}{t}), \\
(t_0=t_1)\subst{x}{t} &:= t_0\subst{x}{t}=t_1\subst{x}{t}, \\
(\varphi \land \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \land \psi\subst{x}{t}, \\
(\varphi \lor \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \lor \psi\subst{x}{t}, \\
(\varphi \to \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \to \psi\subst{x}{t}, \\
(\forallbind{y}{\varphi})\subst{x}{t} &:= \begin{cases}
\forallbind{y}{\varphi} & \text{if } y = x, \\
\forallbind{y}{(\varphi\subst{x}{t})} & \text{if } y \ne x \text{ and } y \notin \FreeVars{t}, \\
\forallbind{z}{(\varphi\subst{y}{z}\subst{x}{t})} & \text{if } y \ne x \text{ and } y \in \FreeVars{t},
\end{cases}\\
(\existsbind{y}{\varphi})\subst{x}{t} &:= \begin{cases}
\existsbind{y}{\varphi} & \text{if } y = x, \\
\existsbind{y}{(\varphi\subst{x}{t})} & \text{if } y \ne x \text{ and } y \notin \FreeVars{t}, \\
\existsbind{z}{(\varphi\subst{y}{z}\subst{x}{t})} & \text{if } y \ne x \text{ and } y \in \FreeVars{t},
\end{cases}
\end{aligned}$$
where in the renaming clauses $z$ is the first variable (in the well-order on $\mathrm{Var}$) not in $\FreeVars{\varphi}
\cup \FreeVars{t} \cup \{x\}$. By construction, substitution is \termdefine{capture-avoiding}: a bound variable $y$ that
would otherwise capture a free occurrence in $t$ is first renamed to a fresh $z$, so $\varphi\subst{x}{t}$ is defined
for every $\varphi$, $x$, $t$.

To justify the recursion in the renaming clauses, count formula constructors, counting each atomic formula as one
regardless of the sizes of its terms. Substitution preserves this count. More precisely, first evaluate the displayed
clauses with a finite recursion budget: at budget zero return the original formula, and at each recursive call
use one less unit. Induction on the budget proves that the formula-constructor count is unchanged, including through
both calls in a renaming clause. A second induction shows that any two budgets at least the original formula's count
give the same result. In the renaming case, the intermediate body has the same count as the original body, so both
recursive calls have sufficient smaller budgets. Taking the original count as budget therefore defines a total
operation satisfying the displayed clauses.

\begin{lemma*}[\termdefineas{free variables of first-order substitution}{Free variables of substitution}]
For a formula $\varphi$, variable $x$, and term $t$,
$$\FreeVars{\varphi\subst{x}{t}}=
\begin{cases}
(\SetDifference{\FreeVars{\varphi}}{\{x\}})\cup\FreeVars{t} & \text{if } x\in\FreeVars{\varphi},\\
\FreeVars{\varphi} & \text{if } x\notin\FreeVars{\varphi}.
\end{cases}$$
The same formula holds for substitution into a term.
\end{lemma*}

\begin{proof}
For terms, use structural induction: substituting for a variable gives the stated alternatives, and a function
application takes the union of the free-variable sets of its arguments. For formulas, use strong induction on the
number of formula constructors. The atomic and Boolean cases take unions of the corresponding free-variable sets.
At a quantifier binding $x$, substitution stops and $x$ is absent from the quantified formula's free variables.
At a different binder $y\notin\FreeVars{t}$, apply the induction hypothesis to the body and remove $y$.
In the remaining case, first rename $y$ to the prescribed fresh $z$. The induction hypothesis replaces free occurrences
of $y$ in the body by occurrences of $z$. Apply it again to substitution of $t$ for $x$ in that renamed body.
Since $z\notin\FreeVars{\varphi}\cup\FreeVars{t}\cup\{x\}$ for the original body $\varphi$, removing $z$ at the new
quantifier removes precisely the renamed occurrences. This gives the displayed formula in both quantifier cases.
\end{proof}

**$\alpha$-equivalence.** The choice of bound-variable name is a syntactic accident: $\forall x\, (x = x)$ and $\forall
y\, (y = y)$ express the same proposition. We define \termdefineas{alpha-equivalence}{$\alpha$-equivalence}
$\equiv_\alpha$ on formulas as the smallest equivalence relation such that
$$\forall y\, \varphi \;\equiv_\alpha\; \forall z\, (\varphi\subst{y}{z}), \qquad \exists y\, \varphi \;\equiv_\alpha\;
\exists z\, (\varphi\subst{y}{z})$$
whenever $z \notin \FreeVars{\varphi}$, and which is a congruence with respect to all formula constructors. Atomic
formulas are $\alpha$-equivalent only to themselves, and $\varphi \star \psi \equiv_\alpha \varphi' \star \psi'$
whenever $\varphi \equiv_\alpha \varphi'$ and $\psi \equiv_\alpha \psi'$.
Quantifiers obey the corresponding congruence rule.

\begin{lemma*}[\termdefineas{first-order alpha invariance lemma}{Free variables and binder renaming}]
If $\varphi\equiv_\alpha\psi$, then $\FreeVars{\varphi}=\FreeVars{\psi}$.
If $x\notin\FreeVars{\varphi}$, then $\varphi\subst{x}{t}\equiv_\alpha\varphi$.
\end{lemma*}

\begin{proof}
For the first assertion, induct on a derivation of $\alpha$-equivalence. The equivalence and congruence rules preserve
the equality of free-variable sets. For a generating renaming, the preceding lemma and $z\notin\FreeVars{\varphi}$ give
$$\FreeVars{\forallbind{z}{(\varphi\subst{y}{z})}}
=\SetDifference{\FreeVars{\varphi}}{\{y\}}
=\FreeVars{\forallbind{y}{\varphi}},$$
and the existential case is identical.

For the second assertion, use strong induction on the number of formula constructors. Terms with no occurrence of $x$
are unchanged, which settles the atomic cases; the Boolean cases follow by congruence. Under a quantifier binding $x$,
substitution stops. Under a different binder $y$, the body still has no free occurrence of $x$.
If no renaming is needed, apply the induction hypothesis to the body.
Otherwise the rule renames $y$ to a fresh $z\ne x$. The preceding lemma
shows that $x$ remains absent from the renamed body, so the induction hypothesis removes the subsequent substitution
up to $\alpha$-equivalence. The remaining formula is a generating renaming of the original quantified formula.
\end{proof}

The second assertion need not be literal equality of named formulas: the substitution rule may rename a binder
even when $x$ is absent.

\begin{mathmeta}
  \define{FirstOrderNameCorrespondence,FirstOrderBoundNames}
\end{mathmeta}

To prove that substitution respects $\alpha$-equivalence, compare expressions under a relation $R$ between variable
names. Write $\FirstOrderNameCorrespondence{R}{t}{t'}$ when corresponding variables satisfy $R$ and function
symbols and argument positions agree. For formulas, write $\FirstOrderNameCorrespondence{R}{\varphi}{\psi}$ when
the outer constructors agree and their components compare. At an atomic formula, require the same relation symbol
or equality sign and compare corresponding terms. At a binary connective, compare its two pairs of subformulas.
The formula $\bot$ compares with itself.
At quantifiers of the same kind with binders $x,y$, compare their bodies under the relation defined by
$$\begin{aligned}
\FirstOrderBoundNames{R}{x}{y}(a,b)\quad\Longleftrightarrow\quad
&(a=x\land b=y)\\
&{}\lor(a\ne x\land b\ne y\land R(a,b)).
\end{aligned}$$
Thus the new binders replace any earlier correspondence involving either bound name.

\begin{lemma*}[\termdefineas{comparison of named first-order formulas}{Comparison of named formulas}]
For named formulas, $\varphi\equiv_\alpha\psi$ if and only if
$\FirstOrderNameCorrespondence{=}{\varphi}{\psi}$.
\end{lemma*}

\begin{proof}
Structural induction shows that a comparison depends only on the relation on the two free-variable sets,
and that each free name on either side has a corresponding free name on the other.
Comparison with equality is reflexive and symmetric. Comparisons compose by induction on constructors:
under two quantifiers, the intermediate name is either bound in both comparisons or free in both.
In particular, comparison with equality is transitive.

The key renaming fact is that $\FirstOrderNameCorrespondence{R}{\varphi}{\psi}$ implies
$\FirstOrderNameCorrespondence{S}{\varphi\subst{x}{z}}{\psi}$ whenever, for corresponding free names $a,b$,
$$\begin{aligned}
R(a,b)\land a=x&\ \Longrightarrow\ S(z,b),\\
R(a,b)\land a\ne x&\ \Longrightarrow\ S(a,b).
\end{aligned}$$
Prove this by strong induction on the number of formula constructors, allowing both relations to vary.
Terms follow by structural induction; atomic formulas and binary connectives follow componentwise.
At a binder for $x$, substitution stops and the binder correspondence masks that name.
At any other binder different from $z$, apply the induction hypothesis to the body.
If the binder is $z$, the substitution rule first renames it to a fresh name.
Apply the induction hypothesis to this renaming and then to the remaining substitution.
Both calls concern bodies of the original body's size. Freshness ensures that only the intended correspondence changes.
The same assertion holds on the right by symmetry.

It follows that renaming a binder and updating its recorded name preserve comparison.
Every generating $\alpha$-renaming therefore preserves comparison with equality, and the equivalence and
congruence rules preserve it as well. Conversely, induct on the number of formula constructors.
Atomic formulas that compare with equality are identical, and binary connectives reduce to their components.
For quantifiers, rename both binders to one name fresh for both bodies.
The renaming fact makes the two renamed bodies compare with equality, so induction gives their $\alpha$-equivalence.
Restore the common quantifier and undo the two renamings to obtain the original formulas' $\alpha$-equivalence.
\end{proof}

\begin{lemma*}[\termdefineas{alpha compatibility of first-order substitution}{Substitution and bound-variable names}]
If $\varphi\equiv_\alpha\psi$, then
$$\varphi\subst{x}{t}\equiv_\alpha\psi\subst{x}{t}.$$
If $\forallbind{x}{\varphi}\equiv_\alpha\forallbind{y}{\psi}$, then
$$\varphi\subst{x}{t}\equiv_\alpha\psi\subst{y}{t}.$$
The second assertion also holds with both universal quantifiers replaced by existential quantifiers.
\end{lemma*}

\begin{proof}
Prove the following stronger assertion about comparison. Suppose
$\FirstOrderNameCorrespondence{R}{\varphi}{\psi}$ and $\FirstOrderNameCorrespondence{S}{t}{t'}$, and assume that
$$\begin{aligned}
R(a,b)&\ \Longrightarrow\ (a=x\Longleftrightarrow b=y),\\
R(a,b)\land a\ne x&\ \Longrightarrow\ S(a,b).
\end{aligned}$$
Then $\FirstOrderNameCorrespondence{S}{\varphi\subst{x}{t}}{\psi\subst{y}{t'}}$.
Induct on the number of formula constructors. If $x$ is not free on the left, the correspondence of free names
shows that $y$ is not free on the right. Substitution for these absent variables changes each formula only up to
$\alpha$-equivalence, as proved above. Comparison with equality on each side and the second hypothesis
then give the required comparison under $S$.

Otherwise both variables occur freely. The term cases follow by structural induction, using the comparison of
the replacements at the variables being replaced and the second hypothesis at all other variables.
Atomic formulas and binary connectives follow componentwise.
Under quantifiers, neither binder is the variable being replaced. On each side use the binder prescribed by
the substitution rule: keep it if it is absent from the replacement's free variables, and otherwise rename it.
The preceding renaming fact transports the body comparison to this pair of binders.
The replacement terms still compare under the extended relation because the new binders are absent from them.
The two hypotheses on the relations also hold under this extension: the bound names correspond and are not replaced,
and every remaining pair satisfies the original hypotheses. Apply induction to the prepared bodies and restore
the quantifiers. The bodies have unchanged size, so the induction applies.

For the first assertion, take both relations to be equality, use the same variable on both sides, and set $t'=t$.
For the second, the bodies compare under $\FirstOrderBoundNames{=}{x}{y}$.
Take this as the input relation and equality as the output relation, again with $t'=t$.
The two hypotheses hold by the definition of the binder correspondence.
The comparison lemma converts both conclusions to $\alpha$-equivalence.
\end{proof}

Consequently, substitution and the free-variable operation are well defined on $\alpha$-equivalence classes.
From here on, we identify $\alpha$-equivalent formulas: "the formula $\varphi$" means its $\alpha$-class, and a
bound variable can always be renamed to any fresh choice without changing $\varphi$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
φ(x)とφ(t)の用法を定める略記規約。代入そのものの定義・正当性は別途接続済みの対象で、この一文に新規の主張はない。)
-->
We write $\varphi(x)$ for a formula with the free variable $x$ singled out, and $\varphi(t) := \varphi\subst{x}{t}$.<!--
formalization: skip-end
-->

## Deduction and Derived Rules {#sec:fol-deduction}

### Proof Trees and Primitive Rules {#sec:fol-proof-calculus}

**Deduction.** The formal derivability relation is the syntactic side of the later comparison with classical semantic
truth. A \termdefine{sequent} in a language $L$ is a pair $\Gamma \vdash \varphi$ in which the
\termdefineas{hypothesis}{hypotheses} $\Gamma$ form a finite set of $L$-formulas and the \termdefine{conclusion}
$\varphi$ is an $L$-formula. We write $\Gamma,\varphi$ for $\Gamma \cup \{\varphi\}$. Thus an assumption may be used
repeatedly inside a proof; this is contraction, built into the finite-set convention. Each \termdefine{inference rule}
below — one or two rules per connective, plus an axiom (Ax) for assumption, equality rules ($=$I, $=$E), and classically
the law of excluded middle (LEM) — is a syntactic relation between a finite list of premise sequents and a conclusion
sequent: given a candidate $\Tuple{S_1, \ldots, S_n; S}$, one checks whether the tuple matches the rule schema and
satisfies
its side condition. \termdefineas{introduction rule}{Introduction} rules (I) build a connective into the conclusion;
\termdefineas{elimination rule}{elimination} rules (E) decompose a connective in a hypothesis or premise. A
\termdefine{proof} is a finite rooted tree whose nodes are labeled by sequents such that, at each non-leaf node $S$, the
labels of its children are the premises of some rule instance with conclusion $S$, and each leaf is the conclusion of a
nullary rule. For effectively presented languages such as $L_\in$, the set of proofs is decidable. Since hypotheses are
finite sets, exchange and contraction are built in. A sequent $\Gamma \vdash\varphi$ is
\termdefine{derivable} iff some proof has it as root. The renaming and weakening lemma below justifies enlarging
the hypothesis set, including the necessary changes of eigenvariables.

For a finite set of formulas $\Gamma$, write
$$\FreeVars{\Gamma} := \bigcup_{\varphi \in \Gamma}\FreeVars{\varphi}.$$

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続の自然演繹規則表の見出しのみ。各規則を定める数式は個別にDerivesへ接続する。)
--> The **primitive rules**:<!--
formalization: skip-end
-->

\begingroup\small

$$\dfrac{}{\Gamma, \varphi \vdash \varphi}\,(\text{Ax})$$

$$\dfrac{\Gamma \vdash \varphi \quad \Gamma \vdash \psi}{\Gamma \vdash \varphi \land \psi}\,(\land\text{I}) \qquad
\dfrac{\Gamma \vdash \varphi \land \psi}{\Gamma \vdash \varphi}\,(\land\text{E}_1) \qquad
\dfrac{\Gamma \vdash \varphi \land \psi}{\Gamma \vdash \psi}\,(\land\text{E}_2)$$

$$\dfrac{\Gamma \vdash \varphi}{\Gamma \vdash \varphi \lor \psi}\,(\lor\text{I}_1) \qquad
\dfrac{\Gamma \vdash \psi}{\Gamma \vdash \varphi \lor \psi}\,(\lor\text{I}_2) \qquad
\dfrac{\Gamma \vdash \varphi \lor \psi \quad \Gamma, \varphi \vdash \chi \quad \Gamma, \psi \vdash \chi}{\Gamma \vdash
\chi}\,(\lor\text{E})$$

$$\dfrac{\Gamma, \varphi \vdash \psi}{\Gamma \vdash \varphi \to \psi}\,(\to\text{I}) \qquad
\dfrac{\Gamma \vdash \varphi \to \psi \quad \Gamma \vdash \varphi}{\Gamma \vdash \psi}\,(\to\text{E})$$

$$\dfrac{\Gamma \vdash \bot}{\Gamma \vdash \chi}\,(\bot\text{E})$$

$$\dfrac{\Gamma \vdash \varphi(x)}{\Gamma \vdash \forall x\, \varphi(x)}\,(\forall\text{I},\ \text{where } x \notin
\FreeVars{\Gamma}) \qquad
\dfrac{\Gamma \vdash \forall x\, \varphi(x)}{\Gamma \vdash \varphi(t)}\,(\forall\text{E})$$

$$\dfrac{\Gamma \vdash \varphi(t)}{\Gamma \vdash \exists x\, \varphi(x)}\,(\exists\text{I})$$

$$\dfrac{\Gamma \vdash \exists x\, \varphi(x) \quad \Gamma, \varphi(y) \vdash \chi}{\Gamma \vdash
\chi}\,(\exists\text{E})$$
The side condition on existential elimination is
$$y \notin \FreeVars{\Gamma} \cup \FreeVars{\chi} \cup \FreeVars{\existsbind{x}{\varphi}}.$$

$$\dfrac{}{\Gamma \vdash t = t}\,(=\text{I}) \qquad
\dfrac{\Gamma \vdash \varphi(t_0) \quad \Gamma \vdash t_0 = t_1}{\Gamma \vdash \varphi(t_1)}\,(=\text{E})$$

$$\dfrac{}{\Gamma \vdash \varphi \lor \neg \varphi}\,(\text{LEM})$$

\endgroup

The rule $(\to\text{E})$ is \termdefine{modus ponens}, $(\bot\text{E})$ is \termdefine{ex falso quodlibet}, and (LEM) is
the \termdefine{law of excluded middle}.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
古典的体系からLEMを除く直観主義的変種の背景説明で、ここではその体系の健全性・完全性を証明しないと明示する。
内部意味論の実際の展開先をcat-internal-logicとrealizability-triposに指定する読書案内。
古典的Derivesを直観主義の実装と扱わない。)
--> For \termdefine{intuitionistic} first-order logic, LEM is dropped from the primitive rules; the others above remain.
This sentence records only the proof-theoretic variant. The Heyting-valued and topos-internal semantics used for
realizability are developed in §{sec:cat-internal-logic} and §{sec:realizability-tripos}.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefineas{finite equality-template lemma}{Finite equality-template search}]
In $L_\in$, fix formulas $A,B$ and variables $t,r$. Choose a representative of $A$ and a variable $z$
that does not occur in it, even as a binder. Form a finite list of candidate formulas by replacing
an arbitrary subset of the free occurrences of $t$ in this representative by $z$.
There are a formula $\theta$ and a variable $x$ such that
$$A=\theta\subst{x}{t},\qquad B=\theta\subst{x}{r}$$
if and only if some candidate $\psi$ satisfies $B=\psi\subst{z}{r}$.
All equalities are equalities of $\alpha$-classes.
\end{lemma*}

\begin{proof}
For every candidate, substituting $t$ back for $z$ recovers $A$, since $z$ was absent from the
chosen representative and no bound occurrence was replaced. Thus a successful candidate gives
the required template by taking $\theta=\psi$ and $x=z$.

Conversely, suppose a template $\theta$ and a variable $x$ give the two displayed instances.
Compare formulas by the positions of their binders, so changes of bound names are ignored.
Each free occurrence of $x$ in the template becomes a free occurrence of $t$ in $A$.
Select exactly those occurrences in the candidate construction. Every other free name of the
template survives in $A$, so the fresh name $z$ cannot be one of these other names.
The selected candidate therefore represents the template with its distinguished free name replaced by $z$.
Substituting $r$ for $z$ gives $B$, by compatibility of capture-avoiding substitution with
$\alpha$-equivalence. The empty subset is included, so the argument also covers vacuous templates
and the case $t=r$.
\end{proof}

\begin{proposition*}[\termdefineas{effective proof-tree checking}{Effective proof-tree checking}]
Suppose the function and relation symbols of $L$ have injective numerical codes, with given closed lambda programs
that return $n+1$ for a valid symbol of arity $n$ and zero for an invalid code.
There is a closed lambda program that halts on every numerical
input with $0$ or $1$ and returns $1$ exactly for codes of finite sequent-labelled trees satisfying the primitive rules
above. The input contains no rule names, substitution terms, or equality templates. A sequent is derivable exactly
when it is the root of some accepted code.
\end{proposition*}

\begin{proof}
Use the named lambda syntax codes of §{sec:lambda-syntax-codes} as finite data. Encode a source variable by the
corresponding lambda variable and a quantifier by a tagged lambda abstraction with the same binder. Function and
relation applications carry a constructor tag, a closed tag for the symbol code, and a finite argument list.
Logical constructors have fixed closed tags. All binders inside canonical tags have index zero. Compare tags
structurally up to $\alpha$-equivalence. The given symbol programs check arities, including zero, so a structural
syntax fold recognizes exactly the term and formula data. Comparison of names through corresponding binders shows
that this encoding preserves and reflects $\alpha$-equivalence, preserves free variables, and commutes with
capture-avoiding substitution up to $\alpha$-equivalence. Thus the lambda programs for these operations in
§{sec:appendix-lambda-computability} apply to the encoded first-order syntax.

Here are explicit finite bounds for the witnesses that the input does not supply. For a raw syntax code $a$, the
decoded term has at most $2a+1$ nodes, and every free variable index is at most $a$. Define
\begin{mathmeta}
  \define{LambdaSyntaxSizeBound}
\end{mathmeta}
$$
\LambdaSyntaxSizeBound{k}{0}=3k+3,\qquad
\LambdaSyntaxSizeBound{k}{m+1}=3\bigl(\LambdaSyntaxSizeBound{k}{m}+1\bigr)^2+3.
$$
Induction on the syntax shows that a term with at most $m$ nodes and with every variable and binder index at most
$k$ has code at most $\LambdaSyntaxSizeBound{k}{m}$. The variable case follows from its code being three times its
index. The application and abstraction cases use the fact that pairing two numbers at most $d$ gives a number
less than $(d+1)^2$. The displayed recurrence is implemented by the numerical lambda recursor.

For $(\forall\mathrm E)$ and $(\exists\mathrm I)$, suppose the displayed instance has raw code $b$ and the
designated variable occurs freely in the quantified body. Such a substitution inserts the whole replacement
syntax, so its node count is at most that of the instance; every free name of the replacement also survives.
The canonical encoding of that replacement
has at most $2b+1$ nodes and all its names at most $b$, since its tag binders have index zero.
It therefore suffices to search codes through $\LambdaSyntaxSizeBound{b}{2b+1}$, retaining only term codes and
testing the actual substitution up to $\alpha$-equivalence. If the designated variable is absent, the variable of
index zero supplies an instance whenever any term does. For the eigenvariable rules, an effective witness is
either bounded by a free occurrence in the displayed data or can be replaced by a name fresh for all those data.
Finite searches therefore also decide the free-variable side conditions of $(\forall\mathrm I)$ and
$(\exists\mathrm E)$, including vacuous quantifiers.

For $(=\mathrm E)$ with compound terms, let $a$ be the code of the first displayed instance and put $z=a+1$.
If an unknown formula and distinguished variable give the two required instances, rename that distinguished free
name to $z$ in its encoding. Every other free name survives in the first instance, so this renaming is fresh for
the other free names. The resulting template has at most $2a+1$ nodes and free names at most $a+1$.
Normalize its bound names without changing its $\alpha$-class, starting with an index above all free names and
increasing it on descent. At an abstraction, retain the binder if it already has the chosen index; otherwise rename
it to that index, which is then fresh for the body. This keeps the node count fixed and bounds all
names by $3a+3$. Hence a suitable raw formula template has code at most
$\LambdaSyntaxSizeBound{3a+3}{2a+1}$. Search this finite range, check the formula grammar, and compare both actual
substitutions with the two displayed instances. A successful candidate supplies the required rule instance;
the bound proves that every possible rule instance is found. This includes vacuous templates and equal replacement
terms. The existence of a bounded representative justifies the exhaustive search and does not require selecting
an unknown template in advance.

Encode a context as a finite list of formula codes. Test equality of contexts by mutual membership up to
$\alpha$-equivalence, so neither ordering nor repetition changes the test. Check all seventeen primitive rule
alternatives, their exact numbers of premises, and their context conditions using the preceding finite searches.
Finally apply a structural lambda fold to the proposed tree, carrying the root labels of its children and their
acceptance bits. Reject malformed labels, malformed tree structure, or any failed local test. Each numerical
subroutine is total, and the fold descends through proper syntax subtrees, so it halts on every numerical input.
Induction on an accepted tree turns its verified local rules into a derivation. Conversely, induction on a
derivation produces a finite sequent-labelled tree; choose representatives of its finitely many formula classes
and contexts and encode them. The local equivalences show that every node is accepted. This proves the stated
equivalence with existence of an accepted code, while deciding only each supplied finite tree.
\end{proof}

### Derived Rules, Renaming, and Weakening {#sec:fol-derived-rules}

**Derived rules.** A rule is \termdefine{derived} if every instance can be obtained by a fixed combination of primitive
rules. Since $\neg\varphi$ abbreviates $\varphi\to\bot$, the usual negation rules are derived:
$$\dfrac{\Gamma, \varphi \vdash \bot}{\Gamma \vdash \neg \varphi}\,(\neg\text{I}) \qquad
\dfrac{\Gamma \vdash \varphi \quad \Gamma \vdash \neg \varphi}{\Gamma \vdash \chi}\,(\neg\text{E}).$$
$(\neg\text{I})$ is $(\to\text{I})$ with $\psi := \bot$. For $(\neg\text{E})$, expand $\neg\varphi$ to $\varphi\to\bot$,
apply $(\to\text{E})$ to obtain $\Gamma \vdash \bot$, then $(\bot\text{E})$ delivers $\Gamma \vdash \chi$.

For a permutation $e$ of the variable set, extend $e$ to terms and formulas by changing every variable name,
including bound names, and leaving function symbols, relation symbols, and logical operations unchanged.
For a finite context, put $e(\Gamma):=\{e(\psi):\psi\in\Gamma\}$.
This operation respects $\alpha$-equivalence. Moreover,
$$\begin{aligned}
\FreeVars{e(\varphi)}&=e[\FreeVars{\varphi}],\\
e(\varphi\subst{x}{t})&=e(\varphi)\subst{e(x)}{e(t)}.
\end{aligned}$$
These are identities of $\alpha$-classes. To verify them, compare each free name $a$ with $e(a)$ using
\termuse{comparison of named first-order formulas}. At a binder, injectivity preserves the distinction between
its bound name and the other names. The free-variable identity follows in both directions from this comparison;
the substitution identity follows from the substitution compatibility lemma. In particular, if $e$ fixes all
free variables of a formula, it fixes its $\alpha$-class. No equivariance of the least-fresh-name choice is required.

\begin{lemma*}[\termdefineas{renaming and weakening lemma}{Renaming and weakening}]
If $\Gamma\vdash\varphi$, $e$ is a permutation of the variables, and $\Delta$ is a finite context with
$e(\Gamma)\IncludedIn\Delta$, then $\Delta\vdash e(\varphi)$.
Consequently, variable permutations preserve derivability, and
$\Gamma\IncludedIn\Delta$ implies that $\Gamma\vdash\varphi$ entails $\Delta\vdash\varphi$.
\end{lemma*}

\begin{proof}
Prove the first assertion by induction on the derivation, allowing both the permutation and the enlarged context
to vary. For the assumption rule, the renamed assumption belongs to the new context. The propositional rules
follow by applying induction to their premises; for a discharged assumption, add its renamed formula to the new
context. Equality and quantifier instantiation use the substitution identity above. The two eigenvariable rules
require a fresh choice.

For $(\forall\text{I})$, the premise is $\Gamma\vdash\varphi$ and $x\notin\FreeVars{\Gamma}$.
Choose $z$ outside $\FreeVars{\Delta}\cup\FreeVars{e(\varphi)}$, let $\tau$ interchange $e(x)$ and $z$, and
put $f:=\tau\circ e$. The transposition fixes every formula of $e(\Gamma)$ and fixes
$e(\forallbind{x}{\varphi})$: the first name is absent from their free-variable sets, and the second was chosen
fresh. Apply induction to the premise with permutation $f$ and context $\Delta$.
It gives $\Delta\vdash f(\varphi)$. Since $f(x)=z\notin\FreeVars{\Delta}$, universal introduction gives
$\Delta\vdash\forallbind{z}{f(\varphi)}$, whose conclusion is $e(\forallbind{x}{\varphi})$.

For $(\exists\text{E})$, the premises are $\Gamma\vdash\existsbind{x}{\varphi}$ and
$\Gamma,\varphi\subst{x}{y}\vdash\chi$, with the displayed side condition on $y$.
Choose $z$ outside the free-variable sets of $\Delta$, $e(\chi)$, and $e(\existsbind{x}{\varphi})$.
Let $\tau$ interchange $e(y)$ and $z$, and put $f:=\tau\circ e$.
The side condition and freshness imply that $\tau$ fixes $e(\Gamma)$, $e(\chi)$, and
$e(\existsbind{x}{\varphi})$. Apply induction to both premises with permutation $f$, adding
$f(\varphi)\subst{f(x)}{z}$ to $\Delta$ in the second premise.
The substitution identity identifies this added assumption with the renamed original assumption.
Existential elimination with eigenvariable $z$ now gives $\Delta\vdash f(\chi)$, which is the required conclusion.
This argument also allows $y=x$.

Taking $\Delta=e(\Gamma)$ proves invariance under variable permutations. Taking $e$ to be the identity proves
weakening.
\end{proof}

A \termdefine{theory} in a language $L$ is a set $T$ of $L$-sentences, called its \termdefineas{axiom}{axioms}; the
notation $T\vdash\varphi$ means that $\Gamma\vdash\varphi$ for some finite $\Gamma\IncludedIn T$. The
consequences of $T$ are the sentences in its \termdefine{deductive closure} $\{\varphi : T \vdash \varphi\}$. When an
axiom schema is written using an open formula, each instance is its universal closure: all free variables not explicitly
bound in the displayed formula are universally quantified outside the displayed expression. In schemas with parameters,
such as Replacement and Separation, the parameters are precisely those additional free variables before this universal
closure is applied. \termdefine{ZFC} is the $L_\in$-theory whose axioms are listed in §{sec:zfc-axioms}.

## Semantics and Soundness {#sec:fol-semantics}

### Structures, Assignments, and Satisfaction {#sec:fol-satisfaction}

\begin{mathmeta}
  \vars{L,T,M}{Set}
\end{mathmeta}

**Semantics.** A \termdefineas{structure for a language}{structure} for a language $L$ is the data needed to interpret
the symbols of $L$. It consists of a nonempty set $M$, called the \termdefineas{domain of structure}{domain} or
\termdefineas{underlying set of structure}{underlying set}, together with interpretations of the non-logical symbols:
each $n$-ary relation symbol $R$ is interpreted as a subset $R^{\mathcal M} \IncludedIn \seqPower{M}{n}$, and each
$n$-ary
function symbol $f$ as a function $f^{\mathcal M} : \seqPower{M}{n} \to M$. For a $0$-ary function symbol $c$, this is
equivalently an element $c^{\mathcal M} \in M$. For $L_\in$, a structure is just a pair $\mathcal M=\Pair{M}{E}$ with
$E\IncludedIn M\times M$ interpreting $\in$.

A structure $\mathcal M$ is a \termdefineas{model of a theory}{model} of a theory $T$, written $\mathcal M\models T$,
when every axiom of $T$ is true in $\mathcal M$ under the satisfaction relation defined below. Thus every model is a
structure, but not every structure is a model of the theory under discussion. This is why model-theoretic theorems such
as downward Löwenheim--Skolem are stated for arbitrary structures, even though the forcing application in
§{sec:internal-model-closure} applies them to structures that are already models of a fragment of ZFC.

*Set-sized convention.* "Model" always means \termdefine{set-sized}: the domain $M$ is a set, so quantifying over models
stays within ZFC's class of sets — and the Henkin construction below shows this is no real restriction, since every
consistent theory $T$ in a language $L$ has a model of size $\le \max(\Card{L}, \Card{T}, \alephNull)$. Readers working
inside
a fixed Grothendieck universe $U$ as in §{sec:inaccessible-universes} may read "set-sized" as "$U$-small" when
the language and theory are $U$-small and the universe contains
the set of natural numbers.
Proper-class "models" such as the universe $V$ of §{sec:zfc-classes} are spoken of only informally, with satisfaction
interpreted by relativizing formulas in the metatheory of §{sec:zfc-absoluteness}.\termref{absoluteness}

A \termdefine{variable assignment} is a function $s : \mathrm{Var} \to M$; write $s[x \mapsto a]$ for the assignment
defined by
$$s[x \mapsto a](y) = \begin{cases} a & \text{if } y = x, \\ s(y) & \text{if } y \ne x. \end{cases}$$ Terms are
interpreted recursively:
$$\begin{aligned}
x^{\mathcal M,s} &= s(x),\\
f(t_1,\ldots,t_n)^{\mathcal M,s} &= f^{\mathcal M}(t_1^{\mathcal M,s},\ldots,t_n^{\mathcal M,s}),
\end{aligned}$$
where $x$ is a variable and $f$ is an $n$-ary function symbol; the $n=0$ case covers constants, giving $c^{\mathcal
M,s}=c^{\mathcal M}$.
In pure $L_\in$, every term is a variable, so $t^{\mathcal M,s}=s(t)$. Satisfaction $\mathcal M,s \models \varphi$ is
defined by induction on formulas:
$$\begin{aligned}
\mathcal M,s &\nvDash \bot,\\
\mathcal M,s \models t = u &\iff t^{\mathcal M,s} = u^{\mathcal M,s},\\
\mathcal M,s \models R(t_1,\ldots,t_n) &\iff \Tuple{t_1^{\mathcal M,s},\ldots,t_n^{\mathcal M,s}} \in R^{\mathcal M},\\
\mathcal M,s \models \varphi \land \psi &\iff \mathcal M,s \models \varphi \text{ and } \mathcal M,s \models \psi,\\
\mathcal M,s \models \varphi \lor \psi &\iff \mathcal M,s \models \varphi \text{ or } \mathcal M,s \models \psi,\\
\mathcal M,s \models \varphi \to \psi &\iff \mathcal M,s \nvDash \varphi \text{ or } \mathcal M,s \models \psi,\\
\mathcal M,s \models \forall x\,\varphi &\iff \mathcal M,s[x \mapsto a] \models \varphi \text{ for every } a \in M,\\
\mathcal M,s \models \exists x\,\varphi &\iff \mathcal M,s[x \mapsto a] \models \varphi \text{ for some } a \in M.
\end{aligned}$$
For $L_\in$, the relation clause says $\mathcal M,s \models t \in u$ iff $\Pair{t^{\mathcal M,s}}{u^{\mathcal M,s}}\in
E$.

### Substitution and the Soundness Theorem {#sec:fol-soundness}

\begin{lemma*}[\termdefineas{assignment locality lemma}{Assignments and free variables}]
If assignments $s,s'$ agree on $\FreeVars{t}$, then $t^{\mathcal M,s}=t^{\mathcal M,s'}$.
If they agree on $\FreeVars{\varphi}$, then
$$\mathcal M,s\models\varphi\quad\Longleftrightarrow\quad\mathcal M,s'\models\varphi.$$
In particular, the truth of a sentence is independent of the assignment.
\end{lemma*}

\begin{proof}
Induct first on terms and then on formulas. For a variable, the claim is the agreement hypothesis. For a function
application, it follows by applying the function interpretation to the equal values of its arguments. The atomic and
Boolean formula cases then follow from their semantic clauses. At a quantified formula with binder $x$, the two
assignments agree on the free variables of the body other than $x$. For each $a\in M$, the updated assignments
$s[x\mapsto a]$ and $s'[x\mapsto a]$ agree on all free variables of the body. The induction hypothesis applies for every
$a$, giving both the universal and existential cases. A sentence has no free variables, so the agreement hypothesis
is vacuous.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後の代入補題を紹介する一文のみ。補題の主張・証明は別の対象として保持している。)
--> The semantic counterpart of syntactic substitution is the following lemma.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{substitution lemma}] For every structure $\mathcal M$, assignment $s$, formula $\varphi$,
variable $x$, and term $t$,
$$\mathcal M,s \models \varphi\subst{x}{t}
\quad\Longleftrightarrow\quad
\mathcal M,s[x \mapsto t^{\mathcal M,s}] \models \varphi.$$

\end{lemma*}

\begin{proof}[Proof]
The term statement follows by induction on terms: interpreting $t_0\subst{x}{t}$ under $s$ gives the same element as
interpreting $t_0$ under $s[x\mapsto t^{\mathcal M,s}]$. Use strong induction on the number of formula constructors
for the formula statement. This applies to each renamed body as well as to each literal subformula, since renaming
does not change that number. The atomic and Boolean cases follow from the term statement and the semantic clauses.

Write $a=t^{\mathcal M,s}$. For $\forall y\,\psi$, if $y=x$, substitution leaves the formula unchanged, and
$s[x\mapsto a][x\mapsto b]=s[x\mapsto b]$ for every $b\in M$. If $y\ne x$ and $y\notin\FreeVars{t}$,
\termuseas{assignment locality lemma}{assignment locality} gives $t^{\mathcal M,s[y\mapsto b]}=a$.
The induction hypothesis identifies the substituted body's interpretation with that of $\psi$ under
$s[y\mapsto b][x\mapsto a]$. The updates commute, giving the required universal clause.

Finally suppose $y\ne x$ and $y\in\FreeVars{t}$. Let $z$ be the fresh variable specified by the substitution rule.
Then
$$(\forall y\,\psi)\subst{x}{t}=\forall z\,(\psi\subst{y}{z}\subst{x}{t}).$$
Fix $b\in M$ and evaluate the body on the right under $s[z\mapsto b]$.
Since $z\notin\FreeVars{t}$, the value of $t$ is still $a$. Apply the induction hypothesis first to substitution of
$t$ into the renamed body, and then to substitution of $z$ into $\psi$. Since $z\ne x$, the resulting condition is
$$\mathcal M,s[z\mapsto b][x\mapsto a][y\mapsto b]\models\psi.$$
Because $z\notin\FreeVars{\psi}$, assignment locality allows us to remove the initial update at $z$. We obtain
$$\mathcal M,s[x\mapsto a][y\mapsto b]\models\psi.$$
Quantifying over $b$ proves the universal case. The existential case uses the same argument with "some" in place of
"every". Thus the renaming step is justified directly by assignment locality, without presupposing that
$\alpha$-equivalence preserves truth.
\end{proof}

\begin{corollary*}[$\alpha$-equivalence preserves truth]
If $\varphi\equiv_\alpha\psi$, then, for every structure $\mathcal M$ and assignment $s$,
$$\mathcal M,s\models\varphi\quad\Longleftrightarrow\quad\mathcal M,s\models\psi.$$
\end{corollary*}

\begin{proof}
Induct on a derivation of $\alpha$-equivalence. Equivalence rules preserve logical equivalence, and congruence follows
from the semantic clauses. For a generating renaming with $z\notin\FreeVars{\varphi}$, the substitution lemma gives,
for each $a\in M$,
$$\mathcal M,s[z\mapsto a]\models\varphi\subst{y}{z}
\quad\Longleftrightarrow\quad
\mathcal M,s[z\mapsto a][y\mapsto a]\models\varphi.$$
The assignment locality lemma removes the update at $z$, leaving $\mathcal M,s[y\mapsto a]\models\varphi$.
Quantifying over $a$ proves the universal and existential renaming cases.
\end{proof}

If $\varphi$ is a sentence, its truth does not depend on $s$, and we write $\mathcal M \models \varphi$. A model
$\mathcal M$ satisfies a theory $T$, written $\mathcal M \models T$, if $\mathcal M \models \sigma$ for every sentence
$\sigma \in T$.

\begin{theorem*}[\termdefineas{first-order soundness theorem}{Soundness}]
If $\Gamma\vdash\varphi$, then, in every structure $\mathcal M$, any assignment $s$ satisfying every formula
in $\Gamma$ also satisfies $\varphi$.
\end{theorem*}

\begin{proof}
Induct on the derivation. The assumption rule uses a formula already satisfied by the assignment.
The conjunction and disjunction introduction rules and conjunction elimination follow directly from the semantic
clauses. For disjunction elimination, one disjunct is true, so the induction hypothesis for its branch applies to
the context enlarged by that disjunct. For implication introduction, assume the antecedent is true and apply
induction to the enlarged context; implication elimination then uses the resulting implication.
Falsity elimination has an impossible true premise, and excluded middle is valid in classical semantics.

For $(\forall\text{I})$, the side condition $x\notin\FreeVars{\Gamma}$ and assignment locality show that
$s[x\mapsto a]$ satisfies $\Gamma$ for every $a\in M$. The induction hypothesis therefore gives
$\mathcal M,s[x\mapsto a]\models\varphi$ for every such $a$, which is the universal clause.
For $(\forall\text{E})$, evaluate the universal premise at $t^{\mathcal M,s}$ and use the substitution lemma.
For $(\exists\text{I})$, the same lemma shows that $t^{\mathcal M,s}$ is a witness.

For $(\exists\text{E})$, choose $a\in M$ with $\mathcal M,s[x\mapsto a]\models\varphi$.
The side condition gives
$$y\notin\FreeVars{\Gamma}\cup\FreeVars{\chi}\cup\FreeVars{\existsbind{x}{\varphi}}.$$
Put $s'=s[y\mapsto a]$. This assignment still satisfies $\Gamma$. Moreover, the substitution lemma gives
$$\mathcal M,s'\models\varphi\subst{x}{y}
\quad\Longleftrightarrow\quad
\mathcal M,s[y\mapsto a][x\mapsto a]\models\varphi.$$
The assignments on the right and $s[x\mapsto a]$ agree on $\FreeVars{\varphi}$:
both assign $a$ to $x$, and a free variable of the body different from $x$ cannot be $y$ by the side condition.
This also covers $y=x$. Assignment locality therefore makes the extra premise true under $s'$.
Apply induction to the second derivation to obtain $\mathcal M,s'\models\chi$.
Since $y\notin\FreeVars{\chi}$, assignment locality gives $\mathcal M,s\models\chi$.

Equality introduction is reflexivity in the domain. For equality elimination, the equality premise gives
$t_0^{\mathcal M,s}=t_1^{\mathcal M,s}$. By the substitution lemma, the instances
$\varphi\subst{x}{t_0}$ and $\varphi\subst{x}{t_1}$ are evaluated under the same updated assignment,
so the truth of the first implies the truth of the second.
\end{proof}

\begin{mathmeta}
  \define{ConsistentTheory}
\end{mathmeta}

For a theory $T$, write $\ConsistentTheory{T}$ for the metatheoretic assertion that $T$ is syntactically consistent,
meaning that $T\nvdash\bot$. The completeness theorem below will show that this is equivalent to having a model.

\begin{corollary*}[Models imply consistency]
If a theory $T$ has a model, then $\ConsistentTheory{T}$.
\end{corollary*}

\begin{proof}
Choose an assignment in the model's nonempty domain. If $T\vdash\bot$, some finite set of axioms of $T$
derives $\bot$. The assignment satisfies those axioms, so the \termuse{first-order soundness theorem} would make
$\bot$ true, a contradiction.
\end{proof}

## Henkin Models and Completeness {#sec:fol-completeness}

### Consistent Theories and Language Extensions {#sec:fol-consistent-extensions}

\begin{lemma*}[\termdefineas{first-order deduction and consistency lemma}{Deduction and consistency}]
For a theory $T$ and sentences $\sigma,\tau$,
$$T\cup\{\sigma\}\vdash\tau\quad\Longleftrightarrow\quad T\vdash\sigma\to\tau.$$
A finite derivation may also use previously derived consequences of $T$ as assumptions.
Consequently:

- If $\ConsistentTheory{T}$ and $T\vdash\sigma$, then $\ConsistentTheory{T\cup\{\sigma\}}$.
- If $T\nvdash\sigma$, then $\ConsistentTheory{T\cup\{\neg\sigma\}}$.
- If $T\cup\{\sigma\to\tau\}\vdash\bot$, then $T\vdash\sigma$ and $T\vdash\neg\tau$.

\end{lemma*}

\begin{proof}
For the forward implication, choose the finite context used in the derivation, remove $\sigma$ from that context,
and discharge it by implication introduction. The remaining context lies in $T$. For the reverse implication,
use weakening to combine a finite derivation of the implication with the additional assumption, then apply
modus ponens. To replace derived assumptions in a finite derivation, induct on their number: discharge one
assumption by implication introduction, apply induction to the remaining assumptions, and apply modus ponens
to a derivation of the discharged assumption. The empty case is weakening.

For the first consequence, a contradiction after adjoining the sentence would yield its negation by deduction;
modus ponens with its existing derivation contradicts consistency. For the second, a contradiction after adjoining
the negation would yield the double negation of the sentence. Double-negation elimination follows by splitting
into the sentence and its negation using LEM: the latter case contradicts the double negation, and falsity
elimination finishes. This would contradict non-derivability.

For the third consequence, deduction gives $T\vdash\neg(\sigma\to\tau)$.
Under the additional assumption $\neg\sigma$, one derives $\sigma\to\tau$ by assuming $\sigma$, obtaining
falsity, and using falsity elimination. This contradicts the negated implication, so double-negation elimination
gives $T\vdash\sigma$. Under the additional assumption $\tau$, implication introduction again gives
$\sigma\to\tau$, hence a contradiction; discharging this assumption gives $T\vdash\neg\tau$.
\end{proof}

\begin{lemma*}[\termdefineas{Lindenbaum extension lemma}{Lindenbaum extension}]
Every consistent theory $S$ in a fixed language has a maximal consistent extension $T^*$ in that language.
This extension is deductively closed among sentences, and for every sentence $\sigma$ exactly one of
$\sigma$ and $\neg\sigma$ belongs to $T^*$.
\end{lemma*}

\begin{proof}
Let $\mathcal P$ be the set of all consistent theories in the fixed language that extend $S$, ordered by
inclusion. It is a set because the collection of sentences is a set. For a nonempty chain
$\mathcal C\IncludedIn\mathcal P$, its union contains $S$. A derivation of falsity from this union would use a
finite set of axioms, all belonging to one member of the chain, contradicting that member's consistency.
Thus the union is an upper bound in $\mathcal P$. For the empty chain, take $S$ itself as an upper bound.
Zorn's lemma gives a maximal element $T^*$.

If $T^*\vdash\sigma$ for a sentence $\sigma$, the \termuse{first-order deduction and consistency lemma} shows
that adjoining this sentence preserves consistency; maximality therefore puts $\sigma$ in $T^*$.
If instead $\sigma\notin T^*$, adjoining it is inconsistent by maximality. Deduction then gives
$T^*\vdash\neg\sigma$, so deductive closure puts $\neg\sigma$ in $T^*$.
Finally, the theory cannot contain both a sentence and its negation, since modus ponens would derive falsity.
\end{proof}

\begin{lemma*}[\termdefineas{language inclusion lemma}{Language inclusion}]
Let $L$ be a sublanguage of $K$, and let $i$ regard an $L$-term or formula as a $K$-term or formula.
The map is well-defined on $\alpha$-classes and satisfies
$$\FreeVars{i(\varphi)}=\FreeVars{\varphi},\qquad
 i(\varphi\subst{x}{t})=i(\varphi)\subst{x}{i(t)}.$$
If $\Gamma\vdash\varphi$ in $L$, then $i(\Gamma)\vdash i(\varphi)$ in $K$, where
$i(\Gamma):=\{i(\psi):\psi\in\Gamma\}$. The same holds for derivations from a theory.
\end{lemma*}

\begin{proof}
The inclusion changes only the ambient language of function and relation symbols, leaving their arities and
all variable names unchanged. Induction on terms proves preservation of free variables and commutation with
term substitution. Induction on formulas preserves their free-variable sets and constructor counts.
To check formula substitution, induct on the recursion budget in its definition. At a quantifier, the test for
capture is unchanged, and a renaming clause chooses the same least fresh variable in both languages.
Apply induction to both recursive calls in that clause. Since the constructor count is unchanged, this proves
the substitution identity for the total operation. The generators of $\alpha$-equivalence are therefore preserved.

Now induct on the derivation. Each rule maps to the same rule in the larger language. Implication introduction,
disjunction elimination, and existential elimination map an added hypothesis to its image. Quantifier
instantiation and equality elimination use the substitution identity. The free-variable identity, also for
finite contexts, preserves every eigenvariable condition. Finally, a theory derivation uses a finite context,
whose image is still a finite subset of the image theory.
\end{proof}

\begin{lemma*}[\termdefineas{fresh bound names lemma}{Fresh bound names}]
For every formula $\varphi$ and finite set $S$ of variable names, there is an $\alpha$-equivalent formula
whose bound names all lie outside $S$.
\end{lemma*}

\begin{proof}
Use strong induction on the number of formula constructors. Atomic formulas have no binders, and binary
connectives follow by applying induction to both subformulas. At a quantifier with bound name $x$ and body
$\psi$, choose $z\notin\FreeVars{\psi}\cup S$ and rename the binder to $z$. Apply induction to
$\psi\subst{x}{z}$, whose constructor count equals that of $\psi$. The resulting body has no bound names in
$S$, and the outer name $z$ also lies outside $S$. The same construction works for both quantifiers.
\end{proof}

\begin{lemma*}[\termdefineas{constant extension lemma}{Adjoining constants is conservative}]
Let $K$ be obtained from $L$ by adjoining any set of new constant symbols. If an $L$-sentence $\varphi$ is
derivable in $K$ from an $L$-theory $T$, it is already derivable from $T$ in $L$.
In particular, interpreting an $L$-theory in $K$ preserves its consistency.
\end{lemma*}

\begin{proof}
Fix a variable $y$. To replace every added constant in a formula by $y$, first use the
\termuse{fresh bound names lemma} to choose a representative with no binder named $y$, then perform the
literal replacement. This operation is well-defined on $\alpha$-classes. Indeed, compare two such representatives
using \termuse{comparison of named first-order formulas}. At a new constant, both replacements are the same
variable; at each quantifier, that variable is different from either bound name, so it remains paired with itself.
The operation adds no free variable other than $y$, and on old-language formulas it is the identity.

Replacement commutes with substitution for a variable $x\ne y$. To see this for substitution of a term $t$,
choose a representative whose bound names avoid $\FreeVars{t}\cup\{y\}$.
The replacement term has no free variables outside this set, so neither substitution needs to rename a binder
to avoid capture. Induction on terms and formulas now proves commutation, including the case where substitution
stops at a binder for the substituted variable. Independence of the representative gives the identity on
$\alpha$-classes.

Given a finite derivation in the expanded language, choose the replacement name outside the finitely many
names used as quantifier binders, eigenvariables, or substitution variables in its rule instances.
Induction on the derivation replaces it by a derivation in the old language. Assumptions and propositional rules
are immediate. Quantifier instantiation and equality elimination use commutation with substitution.
For the two eigenvariable rules, a newly introduced free variable cannot equal the eigenvariable by the choice
of the replacement name, so the side conditions remain valid. When the assumptions and conclusion belong to
the old language, replacement leaves them unchanged. Applying this to a putative derivation of falsity proves
preservation of consistency. The reverse transport of old derivations is the \termuse{language inclusion lemma}.
\end{proof}

### Adjoining Henkin Witnesses {#sec:fol-henkin-witnesses}

\begin{lemma*}[\termdefineas{single Henkin witness lemma}{One fresh Henkin witness}]
Let $T$ be a consistent $L$-theory and let $\psi$ be an $L$-formula with
$\FreeVars{\psi}\IncludedIn\{x\}$. Adjoin a new constant $c$, allowing other new constants as well, and the axiom
$$(\existsbind{x}{\psi})\to\psi\subst{x}{c}.$$
The resulting theory is consistent.
\end{lemma*}

\begin{proof}
If the new axiom caused a contradiction, the \termuse{first-order deduction and consistency lemma} would give
$T\vdash\existsbind{x}{\psi}$ and $T\vdash\neg(\psi\subst{x}{c})$ in the expanded language.
The \termuse{constant extension lemma} brings the first derivation back to the original language.
In the second derivation, replace the added constants by a sufficiently fresh variable $y\ne x$ as in that
lemma's proof. Commutation with substitution gives $T\vdash\neg(\psi\subst{x}{y})$ in the original language.

Combine the finite sets of axioms used in these two derivations and apply weakening to use the same context.
Under the additional assumption $\psi\subst{x}{y}$, modus ponens gives falsity.
Existential elimination now gives $T\vdash\bot$. Its side condition holds because the theory consists of
sentences, the existential premise is closed, and falsity has no free variables. This contradicts consistency.
\end{proof}

\begin{lemma*}[\termdefineas{Henkin witness family lemma}{A family of Henkin witnesses}]
Let $T$ be a consistent $L$-theory. For each $a\in I$, choose a variable $x_a$ and an $L$-formula $\psi_a$
with $\FreeVars{\psi_a}\IncludedIn\{x_a\}$. Adjoin pairwise distinct new constants $c_a$ to obtain a language $K$.
Then the following $K$-theory is consistent:
$$T\cup\{H_a:a\in I\},\qquad
H_a:=(\existsbind{x_a}{\psi_a})\to\psi_a\subst{x_a}{c_a}.$$
\end{lemma*}

\begin{proof}
Work in the fixed language $K$, which contains all the new constants from the start.
For a finite set $F\IncludedIn I$, put $T_F:=T\cup\{H_b:b\in F\}$.
We prove its consistency by induction on the size of $F$. For the empty set, use the
\termuse{constant extension lemma}.

Suppose $T_F$ is consistent and $a\in\SetDifference{I}{F}$. Adjoin a further new constant $d$ to $K$.
The \termuse{single Henkin witness lemma} makes the following theory consistent:
$$T_F\cup\{(\existsbind{x_a}{\psi_a})\to\psi_a\subst{x_a}{d}\}.$$
Map symbols from $K$ into this further language by sending $c_a$ to $d$ and keeping every other symbol fixed.
The rule-by-rule proof of the \termuse{language inclusion lemma} applies to this map as well:
arities and variable names are unchanged, and the map commutes with substitution.
It fixes every axiom of $T_F$, since each witness formula belongs to the old language and each witness
axiom uses only its own new constant. It sends $H_a$ to the newly adjoined axiom.
Thus a derivation of falsity from $T_{F\cup\{a\}}$ would give one from the displayed consistent theory,
a contradiction. This completes the induction.

A derivation from the whole family uses only finitely many axioms, hence only finitely many witness labels.
It is therefore already a derivation from some $T_F$ in the same language $K$.
The consistency just proved rules out a derivation of falsity.
\end{proof}

\begin{lemma*}[\termdefineas{Henkin extension lemma}{Henkin extension}]
Every consistent $L$-theory $T$ has a consistent extension $S$ in a language $L_H$ obtained by adjoining constants.
For every variable $x$ and $L_H$-formula $\psi$ with $\FreeVars{\psi}\IncludedIn\{x\}$, there is a constant $c$
such that $S$ contains the \termdefine{Henkin axiom}
$$(\existsbind{x}{\psi})\to\psi\subst{x}{c}.$$
\end{lemma*}

\begin{proof}
Let $L_0=L$ and $T_0=T$. Given $L_n$ and $T_n$, add a distinct new constant $c_{n,\psi,x}$ for every pair
consisting of a variable $x$ and an $L_n$-formula $\psi$ with $\FreeVars{\psi}\IncludedIn\{x\}$.
Let $L_{n+1}$ be the resulting language and obtain $T_{n+1}$ from $T_n$ by adjoining all corresponding Henkin axioms.
A formula may receive another constant at a later stage; the stage number keeps these symbols distinct.
Set $L_H=\bigcup_n L_n$ and $S=\bigcup_n T_n$, identifying symbols and formulas with their images under inclusion.

At each stage, the \termuse{language inclusion lemma} lets us use the old terms, formulas, and derivations in
the expanded language. Each new constant is a closed term, so the free-variable substitution formula gives
$$\begin{aligned}
&\FreeVars{(\existsbind{x}{\psi})\to\psi\subst{x}{c_{n,\psi,x}}}\\
&\qquad=\SetDifference{\FreeVars{\psi}}{\{x\}}=\varnothing.
\end{aligned}$$
Thus every added Henkin axiom is a sentence.

The \termuse{Henkin witness family lemma} proves by induction that $T_n$ is consistent in $L_n$ for every $n$.
It remains consistent when regarded as a theory in $L_H$. For $n=0$, this follows from the
\termuse{constant extension lemma}. For $n\ge 1$, one can also see it directly: $L_1$ already has a constant,
since $\bot$ is eligible at stage zero. Fix a constant of $L_n$, fix every symbol of $L_n$, and send every
later constant to the chosen one. This defines a symbol map from $L_H$ to $L_n$ whose restriction to $L_n$
is the identity. Transporting a putative derivation of falsity from $T_n$ along this map gives a contradiction
in $L_n$. Finally, any derivation from $S$ uses finitely many axioms, all contained in one $T_n$.
Thus $S$ is consistent.

Every $L_H$-formula belongs to some finite stage. Each symbol was introduced at a finite stage, and each term
and formula uses only finitely many symbols. More explicitly, mapping to a sufficiently late stage by the
preceding symbol map and then including back fixes every symbol occurring in the formula. Induction on terms
and formulas shows that this round trip fixes the formula itself; the same holds for its $\alpha$-class.
Thus an $L_H$-formula with free variables among $x$ is an $L_n$-formula for some $n$, and its Henkin axiom
belongs to $T_{n+1}\IncludedIn S$. The construction also shows $T\IncludedIn S$.
\end{proof}

This covers closed parameters as well. If $\theta(x,\vec y)$ is an $L_H$-formula and $\vec r$ is a tuple of closed
$L_H$-terms, then $\theta(x,\vec r)$ has free variables only among $x$ and belongs to a finite stage.
Its Henkin axiom supplies a constant witnessing $\exists x\,\theta(x,\vec r)$.

### The Term Model and Completeness {#sec:fol-term-model}

\begin{mathmeta}
  \define{TermModelClass}
\end{mathmeta}

\begin{lemma*}[\termdefineas{term-model construction lemma}{Term-model construction}]
Let $T^*$ be a maximal consistent $L_H$-theory with Henkin witnesses.
For closed terms, define $t\sim u$ to mean $T^*\vdash t=u$ and write $\TermModelClass{t}$ for the equivalence class.
The \termdefine{term model} $\mathcal M_{T^*}$ has these classes as its domain, with functions and relations given by
$$f^{\mathcal M_{T^*}}(\TermModelClass{t_1},\ldots,\TermModelClass{t_n})
:=\TermModelClass{f(t_1,\ldots,t_n)},$$
$$R^{\mathcal M_{T^*}}(\TermModelClass{t_1},\ldots,\TermModelClass{t_n})
\quad\Longleftrightarrow\quad R(t_1,\ldots,t_n)\in T^*.$$
In particular, a constant $c$ is interpreted by $\TermModelClass{c}$.
This is a well-defined nonempty structure. An atomic formula is true under an assignment of term classes
exactly when the closed instance obtained by substituting representatives belongs to $T^*$.
\end{lemma*}

\begin{proof}
Equality introduction gives reflexivity. To derive symmetry from $t=u$, apply equality elimination to the
formula $z=t$, starting from $t=t$ and replacing $z$ by $u$. To derive transitivity from $t=u$ and $u=v$,
use the formula $t=z$ and replace $z$ by $v$ in the instance with $z$ replaced by $u$.
The fixed terms are closed, so the variable $z$ is fresh for them. Thus provable equality is an equivalence relation.
For a closed equality, deductive closure gives
$$\TermModelClass{t}=\TermModelClass{u}
\quad\Longleftrightarrow\quad T^*\vdash t=u
\quad\Longleftrightarrow\quad (t=u)\in T^*.$$

To replace one argument of a function, start with the reflexive equality
$f(t_1,\ldots,t_n)=f(t_1,\ldots,t_n)$ and put a variable in the chosen argument on the right.
Equality elimination replaces that argument by any provably equal closed term.
Replace the finitely many arguments one at a time and use transitivity to compose the resulting equalities.
Consequently the class of the function value does not depend on the representatives.

For a relation, place a variable in one argument of the atomic formula and apply equality elimination.
This transfers provability to the replaced tuple; symmetry gives the converse.
Again replace the finitely many arguments in succession. Since these atomic formulas are sentences,
deductive closure identifies their provability with membership in the theory.
This proves that the relation interpretation also does not depend on the representatives.

The domain is nonempty: the Henkin axiom for $\existsbind{x}{\bot}$ includes a constant, whose class is an element.
Its existence does not require the existential sentence to hold.

Induction on terms shows that a term evaluated at classes of closed terms is the class of the closed term
obtained by substitution. The variable case is the assignment itself, and the function case is the defining
clause above applied after the induction hypotheses for the arguments.
For an equality, the displayed equivalences now give the atomic truth clause.
For a relation, use its defining membership clause after the same evaluation of its arguments.
\end{proof}

\begin{lemma*}[\termdefineas{Henkin truth lemma}{Truth lemma for the term model}]
Let $T^*$ be a maximal consistent $L_H$-theory with Henkin witnesses and let $\mathcal M_{T^*}$ be its term model.
Let the distinct variables $x_1,\ldots,x_n$ include all free variables of an $L_H$-formula
$\psi(x_1,\ldots,x_n)$. Choose closed terms $t_1,\ldots,t_n$ and an assignment with
$s(x_i)=\TermModelClass{t_i}$. Then
$$\mathcal M_{T^*},s \models \psi(x_1,\ldots,x_n)
\quad\Longleftrightarrow\quad
\psi(t_1,\ldots,t_n) \in T^*.$$
Here the formula on the right is obtained by successively substituting the displayed closed terms for the free
variables. These substitutions are defined on $\alpha$-classes, and later substitutions do not change the inserted
closed terms. In particular, for a sentence $\sigma$,
$$\mathcal M_{T^*}\models\sigma\quad\Longleftrightarrow\quad\sigma\in T^*.$$
\end{lemma*}

\begin{proof}
First record the membership rules in the maximal consistent theory. For sentences $A,B$,
$$\begin{aligned}
(A\land B)\in T^*&\iff A\in T^*\text{ and }B\in T^*,\\
(A\lor B)\in T^*&\iff A\in T^*\text{ or }B\in T^*,\\
(A\to B)\in T^*&\iff (A\in T^*\Rightarrow B\in T^*),\\
\neg A\in T^*&\iff A\notin T^*.
\end{aligned}$$
Also $\bot\notin T^*$. Conjunction uses its introduction and elimination rules. For disjunction, decide $A$;
if $\neg A\in T^*$, disjunction elimination gives $B$. The reverse implication uses disjunction introduction.
For implication, the forward direction is modus ponens. Conversely, decide $A$: when $A\in T^*$ the hypothesis
gives $B$, and otherwise $\neg A\in T^*$ makes the assumption $A$ contradictory. In either case implication
introduction gives $A\to B$. The negation and falsity clauses follow from maximal consistency.

Suppose $\FreeVars{\varphi}\IncludedIn\{x\}$. The quantifier rules are
$$\begin{aligned}
(\existsbind{x}{\varphi})\in T^*&\iff
  \exists t\;\SubstFormula{\varphi}{x}{t}\in T^*,\\
(\forallbind{x}{\varphi})\in T^*&\iff
  \forall t\;\SubstFormula{\varphi}{x}{t}\in T^*,
\end{aligned}$$
where $t$ ranges over closed $L_H$-terms. In the existential clause, the Henkin axiom and modus ponens give a
constant witnessing membership; the converse is existential introduction. Universal elimination gives the forward
direction of the universal clause.

For the converse, first derive the equivalence of $\forallbind{x}{\varphi}$ and
$\neg\existsbind{x}{\neg\varphi}$ in the deduction system. Universal elimination and existential elimination
make the first formula incompatible with $\existsbind{x}{\neg\varphi}$. In the other direction, under the
assumption $\neg\existsbind{x}{\neg\varphi}$, an additional assumption $\neg\varphi$ gives
$\existsbind{x}{\neg\varphi}$ by existential introduction. Double-negation elimination gives $\varphi$;
universal introduction then gives $\forallbind{x}{\varphi}$. The undischarged assumptions are sentences,
so the eigenvariable conditions hold. Suppose every closed instance of $\varphi$ belongs to $T^*$.
If $\existsbind{x}{\neg\varphi}\in T^*$, its Henkin witness gives the negation of one of these instances,
contradicting consistency.
Thus $\existsbind{x}{\neg\varphi}\notin T^*$, and the negation clause and this syntactic equivalence give
$(\forallbind{x}{\varphi})\in T^*$.

Now prove the truth lemma for sentences by strong induction on the number of formula constructors, without counting
constructors inside terms. The atomic cases are the \termuse{term-model construction lemma}; the Boolean cases
follow from the membership rules above. For a quantified sentence, substitute a closed term for the quantified
variable in its body. The result is a sentence, and substitution leaves its number of formula constructors unchanged,
so it is smaller than the original quantified formula. Apply the induction hypothesis to every such instance.
The substitution lemma and evaluation of closed terms identify the truth of the instance with truth of the body
under the assignment of that term's class to the quantified variable. Every element of the model is represented
by a closed term, so the displayed membership rules give exactly the semantic quantifier clauses.

Finally, substitute the chosen closed terms successively for all free variables of $\psi$.
The free-variable formula for substitution shows that the result is a sentence. Repeated semantic substitution
identifies its truth with the truth of $\psi$ under the assignment of those term classes. Assignment locality
allows any assignment agreeing on the free variables, including $s$. The sentence case just proved therefore
gives the stated assignment version.
\end{proof}

\begin{theorem*}[\termdefine{Gödel completeness theorem}] For any theory $T$ and sentence $\varphi$,
$$T \vdash \varphi \quad\Longleftrightarrow\quad \text{every model of } T \text{ satisfies } \varphi.$$
\end{theorem*}

\begin{proof}[Proof]
The forward implication is the \termuse{first-order soundness theorem}, since a derivation from $T$ uses only
finitely many axioms.

For \emph{completeness}, prove the contrapositive. Suppose $T \nvdash \varphi$, where $T$ is a theory in a language $L$.
The \termuse{first-order deduction and consistency lemma} shows that $T\cup\{\neg\varphi\}$ is consistent.
Apply the \termuse{Henkin extension lemma} to obtain a consistent theory $S$ extending
$T\cup\{\neg\varphi\}$ in a language $L_H$, with all Henkin witnesses.
The \termuse{Lindenbaum extension lemma} gives a maximal consistent extension $T^*\supseteq S$ in $L_H$.
It is deductively closed and decides every sentence. Since it contains $S$, it retains all Henkin witnesses.

Apply the \termuse{term-model construction lemma} to form $\mathcal M_{T^*}$.
Since $T\IncludedIn T^*$ and $\neg\varphi\in T^*$, the \termuse{Henkin truth lemma} shows that this model
satisfies $T$ and falsifies $\varphi$.

Finally forget the additional constants and retain only the interpretations of the symbols of $L$.
Induction on terms and formulas shows that this reduct preserves the interpretation of every $L$-formula:
term evaluation is unchanged, and the logical clauses use the same domain and assignments.
It is therefore an $L$-model of $T$ falsifying $\varphi$, which proves the contrapositive.
\end{proof}

Thus syntactic and semantic consequence coincide for models; the proper-class case is handled informally as noted in the
Semantics paragraph.

## Compactness and Elementary Substructures {#sec:fol-model-theory}

\begin{theorem*}[\termdefine{compactness theorem}] Let $T$ be a theory in a first-order language. If every finite subset
of $T$ has a model, then $T$ has a model.
\end{theorem*}

\begin{proof}[Proof] If $T$ had no model, then $T \vDash \bot$ vacuously, so by Gödel completeness the sentence $\bot$
would be derivable from $T$. A formal proof is finite, so it uses only finitely many axioms $\sigma_1,\ldots,\sigma_n$
from $T$. Hence the finite theory $\{\sigma_1,\ldots,\sigma_n\}$ would prove $\bot$, and soundness would imply that it
has no model. This contradicts the finite satisfiability hypothesis.
\end{proof}

Equivalently, a theory is consistent iff every finite fragment is consistent. This is the form used behind the forcing
convention of working with "a sufficiently large finite fragment of ZFC": compactness lets finite-fragment consistency
be checked one fragment at a time, while downward Löwenheim--Skolem and Mostowski collapse then turn suitable transitive
models into countable transitive ones.

### Elementary Substructures and the Tarski–Vaught Test {#sec:fol-elementary-substructures}

**Elementary substructure.** A structure $\mathcal B$ is an \termdefine{elementary substructure} of $\mathcal A$,
written
$\mathcal B \prec \mathcal A$, if $B \IncludedIn A$, the interpretations of relation and function symbols on $B$ are the
restrictions of those on $A$, and for every formula $\varphi(\vec x)$ and every $\vec b \in B$,
$$\mathcal B \models \varphi(\vec b) \iff \mathcal A \models \varphi(\vec b).$$

\begin{theorem*}[\termdefineas{Tarski--Vaught test}{Tarski–Vaught test}] A subset $B \IncludedIn A$ closed under the
function-symbol interpretations of $\mathcal A$ is
the domain of an elementary substructure $\mathcal B \prec \mathcal A$ iff for every formula $\varphi(y, \vec x)$ and
every $\vec b \in B$, whenever $\mathcal A \models \exists y\,\varphi(y, \vec b)$, some witness $a \in B$ satisfies
$\mathcal A \models \varphi(a, \vec b)$.
\end{theorem*}

\begin{proof}
If $\mathcal B\prec\mathcal A$, an existential formula true in $\mathcal A$ with parameters in $B$ is true in
$\mathcal B$. Its witness in $B$ satisfies the body in both structures, giving the test.

Conversely, suppose the witness condition holds. Applied to the parameter-free formula $\existsbind{y}{y=y}$,
it first shows that $B$ is nonempty. Restrict the interpretations to $B$. Induction on terms shows that evaluation
commutes with the inclusion into $A$: variables retain their assigned values, and the function step uses the
restriction of the same function. Hence atomic formulas have the same truth value in the two structures.
The Boolean steps follow from the induction hypotheses and their truth tables.

For an existential formula true in $\mathcal A$, the witness condition supplies a witness in $B$, and the induction
hypothesis for the body makes it a witness in $\mathcal B$. Conversely, a witness in $\mathcal B$ is a witness in
$\mathcal A$ by that same induction hypothesis. A universal formula true in $\mathcal A$ is true in $\mathcal B$
by restriction and induction. For the converse, if it failed in $\mathcal A$, apply the witness condition to the
negation of its body. This gives a counterexample in $B$, and induction contradicts its truth in $\mathcal B$.
Thus every formula has the same truth value under parameter assignments from $B$, as required.
\end{proof}

\begin{theorem*}[\termdefineas{downward Löwenheim--Skolem theorem}{downward Löwenheim–Skolem}] Let $\mathcal A$ be a
structure in a countable language, and let $X \IncludedIn A$ be countable. Then there is a countable elementary
substructure $\mathcal B \prec \mathcal A$ with $X \IncludedIn B$.

\end{theorem*}

\begin{proof}
Fix $a_0\in A$. For each formula $\exists y\,\varphi(y,\vec x)$, choose a
\termdefine{Skolem function} $F_\varphi$ that returns a witness when one exists and $a_0$ otherwise.
Let $\mathcal F$ consist of these functions and the interpretations of the original function symbols.
The language is countable and formulas are finite strings, so $\mathcal F$ is countable.
Each $F\in\mathcal F$ has a finite arity $r(F)$, which may be zero. Define
$$\begin{aligned}
B_0&:=X\cup\{a_0\},\\
B_{n+1}&:=B_n\cup\bigcup_{F\in\mathcal F}F[B_n^{r(F)}],\\
B&:=\bigcup_{n<\omega}B_n.
\end{aligned}$$
Each finite power of a countable set is countable, including its zeroth power, which consists of the empty tuple.
Thus each successor step adds a countable union of countable images. Induction shows that every $B_n$ is countable,
and their union $B$ is countable. It contains $X$ and is nonempty.

Every finite tuple from $B$ lies in one $B_n$: choose a stage for each entry and take the maximum, or use stage zero
for the empty tuple. Applying any $F\in\mathcal F$ to this tuple gives an element of $B_{n+1}$.
Consequently $B$ is closed under the original function interpretations and under the chosen Skolem functions.
If $\mathcal A\models\exists y\,\varphi(y,\vec b)$ with $\vec b\in B$, the value $F_\varphi(\vec b)$ belongs to
$B$ and satisfies the body in $\mathcal A$. The \termuse{Tarski--Vaught test} therefore makes the restricted
structure on $B$ an elementary substructure of $\mathcal A$.
\end{proof}

### Cardinal Bounds for Substructures and Models {#sec:fol-model-cardinality}

\begin{mathmeta}
  \vars{B,L,T,X}{Set}
\end{mathmeta}

\begin{lemma*}[\termdefineas{elementary substructure cardinal bound}{Cardinal bound for elementary substructures}]
Let $\kappa$ be an infinite cardinal and let $L$ be a language with $\Card{L}\le\kappa$.
For any nonempty $L$-structure $\mathcal A$ and any $X\IncludedIn A$ with $\Card{X}\le\kappa$, the preceding
construction gives an elementary substructure $\mathcal B\prec\mathcal A$ with $X\IncludedIn B$ and $\Card{B}\le\kappa$.
\end{lemma*}

\begin{proof}
The symbols of $L$, the variable names, and the logical constructors form an alphabet of size at most $\kappa$.
Finite expressions over this alphabet also number at most $\kappa$. In particular, there are at most $\kappa$
formulas and hence at most $\kappa$ chosen Skolem functions. Adding the original function interpretations still
leaves $\Card{\mathcal F}\le\kappa$.

Use the same stages as above, starting with $B_0=X\cup\{a_0\}$, whose size is at most $\kappa$.
For every finite arity $r$, one has $\kappa^r\le\kappa$, including $r=0$. If $\Card{B_n}\le\kappa$, then
$$\begin{aligned}
\Card{B_{n+1}}&\le \Card{B_n}+\sum_{F\in\mathcal F}\Card{B_n}^{r(F)}\\
&\le\kappa+\kappa\cdot\kappa=\kappa.
\end{aligned}$$
Induction bounds every stage, and the countable union satisfies
$$\Card{B}\le\alephNull\cdot\kappa=\kappa.$$
The closure argument and the \termuse{Tarski--Vaught test} apply as before: each finite parameter tuple lies
in a single stage, and its chosen witness lies in the next stage.
\end{proof}

\begin{lemma*}[\termdefineas{Henkin model cardinal bound}{Cardinal bound for the Henkin model}]
Let $\kappa$ be an infinite cardinal and let $L$ be a language with $\Card{L}\le\kappa$.
For every consistent $L$-theory $T$, the Henkin construction above gives an $L$-model of $T$ of size at most $\kappa$.
\end{lemma*}

\begin{proof}
At a stage with $\Card{L_n}\le\kappa$, there are at most $\kappa$ formulas with named variables, by the same
finite-syntax
count. Passing to $\alpha$-classes cannot increase this number. A Henkin request consists of a variable and such a
formula, subject to the free-variable condition, so there are at most $\alephNull\cdot\kappa=\kappa$ requests.
Adding their constants gives $\Card{L_{n+1}}\le\kappa+\kappa=\kappa$.
Starting with $L_0=L$, induction therefore bounds all stage languages by $\kappa$.

The final added constants are tagged by their birth stage, so there are at most
$\alephNull\cdot\kappa=\kappa$ of them. Together with the original symbols they form a language $L_H$ of size at
most $\kappa$. Extending the Henkin theory to a maximal consistent theory adds no symbols.
The closed $L_H$-terms are finite expressions, so there are at most $\kappa$ of them. Taking their classes modulo
provable equality does not increase cardinality. Thus the term model has size at most $\kappa$.
The truth lemma makes it a model of the extended theory; its reduct to $L$ has the same domain and satisfies $T$.
\end{proof}

Taking $\kappa=\max(\Card{L},\Card{X},\alephNull)$ gives the general downward bound. For a consistent $L$-theory,
$\kappa=\max(\Card{L},\alephNull)$ already suffices. A separate factor for $\Card{T}$ is unnecessary: a theory is a set
of
sentences, and the total number of $L$-sentences is at most this same bound.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前のLöwenheim–Skolemの結果からinternal-model-closure節へ案内する説明文。
ここで新しいcountable-transitive-modelの存在を主張・証明する箇所ではない。)
--> This is the model-theoretic engine behind the countable-transitive-model convention used in forcing arguments; see
§{sec:internal-model-closure}.<!--
formalization: skip-end
-->

## The First Incompleteness Theorem {#sec:first-incompleteness}

\begin{mathmeta}
  \vars{b,d,e,k,p}{Nat}
\end{mathmeta}

Completeness of a proof system and completeness of a theory are different assertions. A theory $T$ is
\termdefineas{complete theory}{complete} if, for every sentence $\varphi$ in its language, either
$T\vdash\varphi$ or $T\vdash\neg\varphi$. Gödel completeness identifies derivability with truth in every model of
$T$; it does not say that all models of $T$ agree on every sentence. We now prove that sufficiently strong consistent
arithmetic theories with effective axioms cannot decide every sentence. All programs below use the lambda calculus of
§{sec:appendix-lambda-computability}.

\begin{mathmeta}
  \define{ArithmeticNumeral,RobinsonArithmetic}
  \forward{LambdaZeroTest,LambdaSyntaxCode}
\end{mathmeta}

The arithmetic language has symbols $0,S,+,\cdot$. Write $\ArithmeticNumeral{n}:=S^n0$ for its numeral;
this is an arithmetic term, whereas $\ChurchNumeral{n}$ denotes a Church numeral in a lambda program.
\termdefineas{Robinson arithmetic}{Robinson arithmetic} $\RobinsonArithmetic$ consists of the universal closures of
$$\begin{aligned}
Sx&\ne0,& Sx=Sy&\to x=y,& x\ne0&\to\exists y\,x=Sy,\\
x+0&=x,& x+Sy&=S(x+y),\\
x\cdot0&=0,& x\cdot Sy&=x\cdot y+x.
\end{aligned}$$
Use $x\le y$ as an abbreviation for $\exists z\,(z+x=y)$. No induction scheme is part of
$\RobinsonArithmetic$. A theory is \termdefineas{effectively axiomatized theory}{effectively axiomatized} here if its
axioms form a computably enumerable set of finite formula codes.

<!-- formalization: skip-begin (standard external arithmetization and finite-numeral facts for Robinson arithmetic) -->

We use the standard arithmetization of finite syntax and the numeralwise representability of computable relations in
$\RobinsonArithmetic$ [@Zach2025, §§3.6, 4.7, 4.9, 6.13]. The precise arithmetic input is as follows. There is an
arithmetic formula $B(x,y,z)$ such that, for standard $e,b,s$, $\RobinsonArithmetic$ proves
$B(\ArithmeticNumeral{e},\ArithmeticNumeral{b},\ArithmeticNumeral{s})$ if $s$ is an accepted finite certificate for
$\varphi_e(e)=b$, and proves its negation otherwise. Use the finite lambda-reduction certificates from
§{sec:lambda-output-search}; their acceptance test is total. Also, in any model of $\RobinsonArithmetic$, the elements
below a fixed numeral are exactly the finitely many preceding numerals, and every element is comparable with that
fixed numeral. These finite-numeral facts follow by finitely many predecessor decompositions; they do not assert
induction or a global linear-order theorem in $\RobinsonArithmetic$.

For an effectively axiomatized theory, a proof certificate records the finite derivation together with finite
computations confirming every axiom used. Thus a proposed certificate can be checked by a total lambda program even
when membership in the axiom set itself is undecidable. Every proof has such a certificate. Substituting a numeral in a
fixed formula and forming its negation are effective operations on finite syntax. These are the proof-coding facts used
below; the diagonal search itself is constructed explicitly.

<!-- formalization: skip-end -->

Define the following computable family of arithmetic sentences:
$$\sigma_e:=\exists u\,\bigl(B(\ArithmeticNumeral{e},\ArithmeticNumeral{0},u)
  \land\forall v\,(v\le u\to\neg B(\ArithmeticNumeral{e},\ArithmeticNumeral{1},v))\bigr).$$
The comparison of certificate sizes is a Rosser comparison: a certificate for output $0$ is accepted only if no
certificate for output $1$ has appeared at or below its size. We need only the following two implications.

\begin{lemma*}[\termdefineas{Rosser separation of computation outputs}{Rosser separation of computation outputs}]
For every standard index $e$,
$$\varphi_e(e)=0\ \Longrightarrow\ \RobinsonArithmetic\vdash\sigma_e,\qquad
  \varphi_e(e)=1\ \Longrightarrow\ \RobinsonArithmetic\vdash\neg\sigma_e.$$
\end{lemma*}

\begin{proof}[Proof]
Work in an arbitrary model of $\RobinsonArithmetic$. If $\varphi_e(e)=0$, choose a standard certificate $s$ for this
output. Numerical output uniqueness excludes every standard certificate for output $1$.
Every model element below $\ArithmeticNumeral{s}$ is a standard numeral, so the numeralwise facts about $B$ prove
that $\ArithmeticNumeral{s}$ witnesses $\sigma_e$ in this model.

If $\varphi_e(e)=1$, choose a standard certificate $t$ for that output. Suppose an element $u$ witnessed
$\sigma_e$. If $u\le\ArithmeticNumeral{t}$, then $u$ is a standard numeral, so
$B(\ArithmeticNumeral{e},\ArithmeticNumeral{0},u)$ would give a standard computation with output $0$, contradicting
output uniqueness. If $\ArithmeticNumeral{t}\le u$, the universal clause of $\sigma_e$ contradicts the accepted
certificate $t$. Comparison with the fixed numeral covers both cases, so this model satisfies $\neg\sigma_e$.
The conclusions hold in every model of $\RobinsonArithmetic$; Gödel completeness gives the two derivability claims.
This argument works equally in nonstandard models.
\end{proof}

Let $T$ now be a consistent effectively axiomatized extension of $\RobinsonArithmetic$.
For a candidate $k=\NatPair{b}{p}$, let $c_T(e,k)$ be $1$ if either $b=0$ and $p$ certifies $T\vdash\sigma_e$,
or $b=1$ and $p$ certifies $T\vdash\neg\sigma_e$; let it be $0$ otherwise.
Let $\LambdaTermName{certificateTest}_T$ be a closed lambda program computing this total test on the paired
input $\NatPair{e}{k}$.
Malformed certificates and other tags are rejected. Consistency ensures that, for a fixed $e$, all accepted candidates
have the same tag.

Use the parameterized result search from §{sec:lambda-rational-ball-programs}, replacing the identity result
function by the first numerical projection. This gives a closed program $\LambdaTermName{proofSearch}_T$ that
searches the candidates in numerical
order and returns the tag of the first accepted one. Every individual test terminates. If a proof of either sentence
exists, its certificate is eventually reached; consistency makes the returned tag independent of which certificate
appears first. Consequently
$$T\vdash\sigma_e\ \Longrightarrow\ \LambdaTermName{proofSearch}_T\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{0},\qquad
  T\vdash\neg\sigma_e\ \Longrightarrow\ \LambdaTermName{proofSearch}_T\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{1}.$$
If neither sentence is provable, $\LambdaTermName{proofSearch}_T \ChurchNumeral{e}$ has no numeral output. We
have not assumed that this search
is total.

\begin{theorem*}[\termdefineas{Gödel--Rosser first incompleteness theorem}{First incompleteness theorem (Gödel–Rosser)}]
Every consistent effectively axiomatized theory $T$ extending $\RobinsonArithmetic$ is incomplete: there is a sentence
$G$ such that
$$T\nvdash G\qquad\text{and}\qquad T\nvdash\neg G.$$
\end{theorem*}

\begin{proof}[Proof]
Form the closed program
$$\LambdaTermName{opposite}_T:= \lambdaab{z}{ \LambdaZeroTest\,( \LambdaTermName{proofSearch}_Tz)\,
\ChurchNumeral{1}\, \ChurchNumeral{0}}.$$
When the proof search returns $0$, it returns $1$; when the search returns $1$, it returns $0$.
Choose a named representative of $\LambdaTermName{opposite}_T$ and let
$d:=\LambdaSyntaxCode{\LambdaTermName{opposite}_T}$ be its index. Define $G:=\sigma_d$.
If $T\vdash G$, then the proof search and the final zero test give
$$\LambdaTermName{opposite}_T\ChurchNumeral{d}\to_\beta^*\ChurchNumeral{1},\qquad\varphi_d(d)=1.$$
The Rosser separation lemma gives $\RobinsonArithmetic\vdash\neg\sigma_d$, hence $T\vdash\neg G$, contradicting
consistency. If $T\vdash\neg G$, the same program instead gives
$$\LambdaTermName{opposite}_T\ChurchNumeral{d}\to_\beta^*\ChurchNumeral{0},\qquad\varphi_d(d)=0.$$
Now the lemma gives $\RobinsonArithmetic\vdash\sigma_d$, hence $T\vdash G$, again contradicting consistency.
Thus neither sentence is provable. Every step uses a finite computation under the corresponding hypothetical proof;
no decision of the entire theorem set, and no totality of $\LambdaTermName{proofSearch}_T$, was assumed.
\end{proof}

Only consistency is required, not soundness in the standard natural numbers or $\omega$-consistency.
If $T$ is consistent, the two extensions $T\cup\{G\}$ and $T\cup\{\neg G\}$ are both consistent and hence have models
by Gödel completeness. The models disagree on $G$, which explains why completeness of first-order logic and
incompleteness of $T$ coexist. The second incompleteness theorem concerns the additional claim that $T$ cannot prove
its own formalized consistency statement; that requires a separate analysis of the proof predicate inside $T$.

## Definitional Extensions {#sec:definitional-extensions}

Mathematical writing almost never stays in the bare language in which a theory is first stated. Set theory is the main
example in this book. Officially ZFC is written in $L_\in$, whose only non-logical symbol is $\in$, but ordinary
set-theoretic prose uses $\emptyset$, $\{a,b\}$, $\bigcup x$, ordered pairs, functions, domains, restrictions, products,
and many other notations. The mechanism that justifies this practice is
\termdefineas{definitional extension}{extension by definition}. It adds names for objects, operations, or relations
that the old theory already
defines uniquely, and it does not create new theorems in the old language.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
定義拡張の議論で理論Tと言語Lを固定する設定文のみ。新しい主張・構成・仮定の充足証明は含まない。)
--> Let $T$ be a theory in a language $L$.<!--
formalization: skip-end
-->

### Schematic Notation and Simultaneous Substitution {#sec:definition-schematic-substitution}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限の変数・項・量化子列をvecで表すメタ言語の略記規約。新しい項形成操作ではないことを明示する。実際の同時代入は次の補題として別途対象。)
--> **Schematic notation.**
We use vector notation for finite lists of variables and terms. Thus $\vec{x}$ abbreviates $x_1,\ldots,x_n$, and
$\forall \vec{x}\,\varphi$ means $\forall x_1\cdots\forall x_n\,\varphi$. If $\vec{t}=t_1,\ldots,t_n$, then $R(\vec{t})$
means $R(t_1,\ldots,t_n)$ and $f(\vec{t})$ means $f(t_1,\ldots,t_n)$. This is metalinguistic notation for schemata, not
a new term-forming operation inside the object language.<!--
formalization: skip-end
-->

When several variables are replaced, the substitution is simultaneous: a later replacement must not alter a term
inserted by an earlier one. Number the pairwise distinct formal input variables as $x_1,\ldots,x_n$.

\begin{lemma*}[\termdefineas{simultaneous substitution}{Simultaneous substitution}]
For a formula $\varphi$ and terms $\vec{t}$, there is a capture-avoiding formula $\varphi\subst{\vec{x}}{\vec{t}}$
such that
$$\mathcal M,s\models\varphi\subst{\vec{x}}{\vec{t}}
\quad\Longleftrightarrow\quad
\mathcal M,s'\models\varphi,$$
where $s'(x_i)=t_i^{\mathcal M,s}$ and $s'$ agrees with $s$ outside the input variables.
Every free variable of the result is either a free variable of $\varphi$ outside $\vec{x}$ or a free variable
of one of the replacement terms.
\end{lemma*}

\begin{proof}
Choose pairwise distinct temporary variables $z_1,\ldots,z_n$ outside the input variables and the free variables
of the original formula and all replacement terms. Such names exist by taking their indices above all indices
in these finite sets. Carry out two passes of the already defined capture-avoiding single-variable substitution:
$$\begin{aligned}
\varphi_0&:=\varphi,&
\varphi_i&:=\varphi_{i-1}\subst{x_i}{z_i},\\
\psi_0&:=\varphi_n,&
\psi_i&:=\psi_{i-1}\subst{z_i}{t_i}
\qquad(1\le i\le n).
\end{aligned}$$
Set $\varphi\subst{\vec{x}}{\vec{t}}:=\psi_n$.

Apply the single-variable substitution lemma successively, starting from the last substitution.
In the second pass, later substitutions change only temporary variables, which occur in none of the replacement
terms. Hence every replacement term is evaluated in the original assignment $s$.
In the first pass, later substitutions change only input variables, so they leave the temporary names unchanged.
Thus each original input variable receives its corresponding term value. Other original free variables keep
their values, because they are not temporary names. Assignment locality gives the asserted equivalence.
For free variables, each single substitution removes its target variable and introduces only variables of its
replacement term. After the first pass, the only possible extra free variables are the temporary names; the
second pass removes all of them and introduces only free variables of the replacement terms.
\end{proof}

When the language contains a binary relation symbol $\in$, we also use **bounded quantifiers** as abbreviations:
$$
(\exists u \in v)\,\varphi
\quad:\equiv\quad
\exists u\,(u\in v \land \varphi),
\qquad
(\forall u \in v)\,\varphi
\quad:\equiv\quad
\forall u\,(u\in v \to \varphi).
$$
The variable $u$ is bound in $\varphi$, and $v$ is the bounding term, in which $u$ must not occur freely. Thus
bounded quantification is not an additional
logical primitive; it is notation available in set-theoretic languages such as $L_\in$.

### Relation Definitions and Proof Translation {#sec:definition-relations}

**Relation symbols.**
Suppose $\varphi(\vec{x})$ is an $L$-formula whose free variables are among the distinct variables in $\vec{x}$.
Add a fresh $n$-ary relation symbol $R$ and the defining axiom
$$
\forall \vec{x}\,\bigl(R(\vec{x}) \leftrightarrow \varphi(\vec{x})\bigr).
$$

\begin{lemma*}[\termdefineas{unique expansion by relation definitions}{Unique expansion by relation definitions}]
Every nonempty $L$-structure $\mathcal M$ has a unique expansion satisfying the defining axiom for $R$.
The same holds for any family of fresh relation symbols defined by old-language formulas.
\end{lemma*}

\begin{proof}
Keep the domain and the interpretations of all old symbols. For each tuple $\vec{a}$, choose an assignment $s$
with $s(\vec{x})=\vec{a}$, and put
$$\vec{a}\in R^{\mathcal M'}\quad\Longleftrightarrow\quad\mathcal M,s\models\varphi.$$
Such an assignment exists because the domain is nonempty. Assignment locality shows that the right-hand side
is independent of values outside $\vec{x}$. Old-language formulas have the same truth value in the expansion
and its reduct, by induction on terms and formulas. Thus the displayed equivalence is exactly the defining axiom
at an arbitrary tuple, so its universal closure holds. Conversely, that axiom forces the interpretation of $R$
at every tuple. All old interpretations are fixed, hence the expansion is unique. For a family of definitions,
apply this construction to each new symbol independently. The argument includes $0$-ary relations.
\end{proof}

\begin{theorem*}[\termdefineas{elimination of defined relations}{Elimination of defined relations}]
Every formula in the language expanded by these relation definitions can be translated to an $L$-formula.
In every model of the defining axioms, the translated formula has the same truth value at every assignment
and has no free variables beyond those of the original formula.
\end{theorem*}

\begin{proof}
There are no new function symbols, so leave terms, equalities, and old relation atoms unchanged.
Replace each atom $R(\vec{t})$ for a new relation by $\varphi\subst{\vec{x}}{\vec{t}}$, using its defining formula.
Recursively translate the subformulas of each connective and quantified formula, preserving the connective,
the quantifier, and its bound variable.

Prove truth preservation by structural induction. Old atoms have unchanged interpretations.
For a new relation atom, the defining axiom identifies the relation at the argument values with the defining
formula at those values. The simultaneous-substitution lemma gives exactly that assignment, even when an
argument term contains another input variable. Connectives follow from their truth clauses.
At a quantifier, apply the induction hypothesis under every assignment obtained by changing its bound variable;
the universal and existential clauses then give the result. The free-variable assertion follows by the same
induction: an inserted definition has only the argument terms' free variables, connectives take unions, and
quantification removes the bound variable. Temporary names introduced inside an atom therefore cannot be
captured by an outer quantifier or escape from the translated formula.
\end{proof}

\begin{lemma*}[\termdefineas{alpha invariance of relation elimination}{Bound names in relation elimination}]
The preceding translation sends $\alpha$-equivalent formulas to $\alpha$-equivalent formulas.
It therefore defines a translation on $\alpha$-classes, with the same truth-preservation and free-variable bounds.
\end{lemma*}

\begin{proof}
First compare two instances of one defining formula $\varphi$, whose free variables lie among $\vec{x}$.
Choose a representative of $\varphi$ whose bound names avoid the input variables, all variables in both argument
lists, and the temporary names in both two-pass substitutions. Such a representative exists by fresh renaming.
On this representative, every substitution step is literal term replacement: no binder is a target or captures
an inserted variable. Composing the steps sends each $x_i$ to its argument term and fixes every other name
occurring in the representative. Thus both constructions are represented by literal simultaneous replacement,
even if their temporary names differ.

Let $R$ be any relation on names, and suppose $\FirstOrderNameCorrespondence{R}{t_i}{u_i}$ for every input position.
Structural induction on the common representative gives
$$\FirstOrderNameCorrespondence{R}
{\varphi\subst{\vec{x}}{\vec{t}}}{\varphi\subst{\vec{x}}{\vec{u}}}.$$
At a quantifier with bound name $y$, both replacements fix $y$, and no replacement of another name contains $y$.
Consequently the compared terms remain related under $\FirstOrderBoundNames{R}{y}{y}$, as required for the body.
Atoms and connectives follow componentwise. Comparison is unchanged by replacing either representative by an
$\alpha$-equivalent one: compose with comparison under equality using the comparison lemma above.

Now induct on a comparison of two formulas in the expanded language, allowing its relation on names to vary.
Old atoms preserve the comparison. At a new relation atom, apply the preceding instance comparison to its defining
formula. Connectives preserve the induction hypotheses; under a quantifier, apply the hypothesis with the updated
bound-name relation. Taking equality as the initial relation proves the assertion by the comparison lemma.
Hence the recursive translation descends to $\alpha$-classes. Its truth and free-variable assertions follow from
those already proved for representatives.
\end{proof}

\begin{lemma*}[\termdefineas{proof translation for relation definitions}{Proof translation for relation definitions}]
Eliminating defined relations commutes with capture-avoiding substitution, up to $\alpha$-equivalence.
Moreover, every natural-deduction derivation translates to a derivation of its translated conclusion from
its translated context.
\end{lemma*}

\begin{proof}
First consider an instance of a defining formula $\varphi$ with input variables $\vec{x}$.
For a further substitution of $t$ for $y$, put $u_i:=r_i\subst{y}{t}$. Then
$$\bigl(\varphi\subst{\vec{x}}{\vec{r}}\bigr)\subst{y}{t}
\equiv_\alpha\varphi\subst{\vec{x}}{\vec{u}}.$$
To prove this, choose one representative of $\varphi$ whose binders avoid the inputs, both argument lists,
both lists of temporary names, $y$, and all variables of $t$. The preceding literal-replacement argument applies
to both instances and to the further substitution. Composition replaces each input by $u_i$ and fixes every
other name occurring in the representative. This proves the displayed identity even if $y$ is an input variable.

For a general formula, first choose its bound names to avoid the substitution variable and the variables of the
inserted term. Induct on the formula. Old atoms use ordinary term substitution, and new relation atoms use the
identity just proved. Connectives commute with both operations. At a quantifier, the bound name is neither the
substitution target nor a variable of the inserted term, so substitution passes into the body on both sides.
The induction hypothesis completes this case. Independence of representatives gives the assertion on
$\alpha$-classes.

Now induct on the derivation. Translate each finite context by taking its image under elimination.
Adding a hypothesis commutes with this operation, so discharged hypotheses remain the required hypotheses.
The quantifier-instantiation and equality-elimination rules use the substitution identity. The free-variable
bound for elimination implies the same bound for the union of the context's free-variable sets. Thus a fresh
eigenvariable remains fresh for the translated context and conclusions, including all three sets in the
existential-elimination condition. Every remaining rule preserves its displayed constructors directly.
\end{proof}

\begin{corollary*}[\termdefineas{syntactic conservativity of relation definitions}{Syntactic conservativity}]
A proof from $T$ and the relation defining axioms translates to an old-language proof of the translated conclusion
from $T$. In particular, an old-language conclusion already has a proof from $T$.
\end{corollary*}

\begin{proof}
Elimination fixes old-language formulas by structural induction. It also fixes a defining formula instantiated
at its own input variables: on a representative with fresh binders, the literal replacement is the identity.
Consequently, the defining axiom for a relation translates to the universal closure of
$$(\varphi\to\varphi)\land(\varphi\to\varphi).$$
Each implication follows by discharging its own hypothesis, and conjunction introduction combines them.
Universal introduction closes the variables because the context is empty. Hence the translated defining axiom
has a proof without assumptions.

Apply proof translation to the given derivation. Its finitely many translated assumptions are either old axioms
of $T$ or translated defining axioms. Replace the latter by the proofs just constructed, using the hypothesis
substitution proved earlier. The resulting derivation uses only assumptions from $T$. An old-language conclusion
is unchanged by elimination, which proves conservativity directly.
\end{proof}

### Function Definitions and Graph Translation {#sec:definition-functions}

#### Model Expansions and Graph Witnesses {#sec:definition-function-expansions}

**Function symbols.**
Function notation requires uniqueness. Suppose $\theta(\vec{x},y)$ is an $L$-formula whose free variables are
among the pairwise distinct variables in $\vec{x}$ and $y$, and suppose
$$
T \vdash \forall \vec{x}\,\exists! y\,\theta(\vec{x},y).
$$
Here unique existence abbreviates
$$\exists!y\,\theta(\vec{x},y)
\quad:\equiv\quad
\exists y\,\bigl(\theta(\vec{x},y)\land
\forall z\,(\theta(\vec{x},z)\to z=y)\bigr),$$
where $z$ is fresh, and $\theta(\vec{x},z)$ is obtained by capture-avoiding substitution for $y$.
The substitution lemma and assignment locality show that this formula says exactly that there is one and only one
possible value of $y$. The comparison variable introduces no additional free parameter.

Add a fresh $n$-ary function symbol $f$ and the defining axiom
$$
\forall \vec{x}\,\theta(\vec{x},f(\vec{x})).
$$

\begin{lemma*}[\termdefineas{unique expansion by function definitions}{Unique expansion by function definitions}]
Under the displayed unique-existence hypothesis, each nonempty model of $T$ has a unique expansion satisfying
the defining axiom for $f$. This also holds for a family of fresh function symbols defined by old-language graphs,
including constants as the $0$-ary case.
\end{lemma*}

\begin{proof}
Fix $\mathcal M\models T$. Soundness gives, for every input tuple $\vec{a}$, exactly one $b$ satisfying
$\theta(\vec{a},b)$. Assignment locality makes this assertion independent of values assigned outside the input
and output variables. Define $f^{\mathcal M'}(\vec{a})=b$, keeping the domain and all old interpretations.
The substitution lemma shows that $\theta(\vec{x},f(\vec{x}))$ holds at every assignment, so its universal closure
holds in the expansion. Conversely, any expansion satisfying this axiom must assign to each input the unique
value in its defining graph. Thus all function values are forced. Apply the construction separately to each
new symbol in a family. An empty input tuple gives the required unique interpretation of a constant.
\end{proof}

\begin{lemma*}[\termdefineas{graph-witness elimination}{Graph-witness elimination}]
In every model of the function definition and its unique-existence hypothesis, for any formula $\psi$ in the
expanded language,
$$\psi\subst{y}{f(\vec{x})}
\quad\longleftrightarrow\quad
\exists y\,\bigl(\theta(\vec{x},y)\land\psi\bigr).$$
Here $y$ is the output variable and does not occur among the input variables.
\end{lemma*}

\begin{proof}
Fix an assignment $s$, and let $b$ be the value of $f(\vec{x})$ at that assignment.
The defining axiom and uniqueness say that $\theta(\vec{x},y)$ holds under $s[y\mapsto a]$ exactly when $a=b$.
By the substitution lemma, the left side holds exactly when $\psi$ holds under $s[y\mapsto b]$.
The right side requires some graph witness for which the same formula holds; that witness must be $b$.
This proves both implications, with all other parameters fixed.
\end{proof}

\begin{lemma*}[\termdefineas{syntactic graph-witness replacement}{Graph replacement in proofs}]
Let $T$ be a theory of sentences, let $\rho,\psi$ be formulas, and let $t$ be a term not containing $y$.
In the abbreviation $\exists!y\,\rho$, choose the comparison variable $z$ distinct from $y$, not free in
$\rho$ or $\psi$, and absent from $t$. If
$$T\vdash\exists!y\,\rho
\qquad\text{and}\qquad T\vdash\rho\subst{y}{t},$$
then
$$T\vdash\bigl(\psi\subst{y}{t}\ \leftrightarrow\ \exists y\,(\rho\land\psi)\bigr).$$
\end{lemma*}

\begin{proof}
First derive
$$T\vdash\forall z\,(\rho\subst{y}{z}\to z=t).$$
Open the unique-existence premise with temporary variable $y$. Its comparison clause is
$\forall z\,(\rho\subst{y}{z}\to z=y)$. Instantiate it at $t$ and use the other premise to obtain $t=y$,
hence $y=t$ by equality elimination. Here substitution through the fresh variable $z$ gives
$(\rho\subst{y}{z})\subst{z}{t}=\rho\subst{y}{t}$ as $\alpha$-classes.
Under the additional assumption $\rho\subst{y}{z}$, the comparison clause gives $z=y$, hence $z=t$.
Discharge that assumption and universally quantify $z$. This is allowed because $z$ is not free in the
temporary unique-existence assumption or in $T$. Eliminate the original existential assumption:
$y$ is not free in the resulting universal formula, since it is absent from $t$ and distinct from $z$.

For the forward implication, assume $\psi\subst{y}{t}$. Combine it with $\rho\subst{y}{t}$ and introduce
the existential quantifier using $t$ as witness. Then discharge the added assumption.

For the reverse implication, assume $\exists y\,(\rho\land\psi)$ and rename its bound variable to $z$.
Open it with temporary assumption $\rho\subst{y}{z}\land\psi\subst{y}{z}$. The universal formula just
derived gives $z=t$. Equality elimination in $\psi\subst{y}{z}$, followed by substitution through the
fresh variable, gives $\psi\subst{y}{t}$. The variable $z$ is free in neither this conclusion nor $T$
nor the added existential assumption, so existential elimination applies. Discharge that existential assumption.
Conjunction introduction combines the two implications, which is the stated biconditional.
\end{proof}

To eliminate a chosen occurrence of $f(\vec{t})$, replace it by a variable fresh for the original formula,
rename bound variables to avoid capture, and apply this equivalence with the graph at $\vec{t}$. For example,
one truth-preserving elimination of
$$
P(f(x),z)
$$
is
$$
\exists u\,\bigl(\theta(x,u) \land P(u,z)\bigr),
$$
and
$$
f(x)=g(z)
$$
translates to
$$
\exists u\,\exists v\,\bigl(\theta_f(x,u) \land \theta_g(z,v) \land u=v\bigr).
$$
Unique existence makes this translation independent of the chosen fresh witnesses, so the expanded notation has the same
truth conditions as its old-language expansion.

Constants are the $0$-ary function case. If $T \vdash \exists! y\,\theta(y)$, a new constant $c$ may be added with axiom
$\theta(c)$, and each occurrence of $c$ can be eliminated by replacing it with a fresh witness satisfying $\theta$.

#### Recursive Term Graphs and Formula Elimination {#sec:definition-term-graphs}

The following recursion handles arbitrary nesting of function terms. Enumerate variable names as
$v_0,v_1,\ldots$. Choose $B$ larger than the index of every variable in a term $t$ and of its output variable $y$.

\begin{mathmeta}
  \define{FirstOrderOperationGraph,FirstOrderTermGraph}
\end{mathmeta}

For an old function symbol $f$, let $\FirstOrderOperationGraph{f}{\vec{z}}{y}$ be the equality $y=f(\vec{z})$.
For a new symbol, let it be $\theta_f(\vec{z},y)$, obtained from its defining graph by simultaneous substitution
at every input and the output. Define the old-language formula $\FirstOrderTermGraph{t}{y}{B}$ recursively.
For a variable,
$$\FirstOrderTermGraph{v_i}{y}{B}\quad:\equiv\quad y=v_i.$$
For $t=f(t_0,\ldots,t_{n-1})$, put $z_i:=v_{B+i}$ and set
$$\begin{aligned}
\FirstOrderTermGraph{t}{y}{B}\quad:\equiv\quad
\exists z_{n-1}\cdots\exists z_0\,\Bigl(
&\bigwedge_{i<n}\FirstOrderTermGraph{t_i}{z_i}{B+n}\\
&{}\land\FirstOrderOperationGraph{f}{\vec{z}}{y}\Bigr).
\end{aligned}$$
The conjunction over an empty family is true, and an empty block of quantifiers does nothing.
Thus the rule includes constants. Each child graph starts its internal names at $B+n$; those names can be reused
in different child graphs because their quantifiers have separate scopes.

\begin{lemma*}[\termdefineas{recursive graphs of function terms}{Recursive graphs of terms}]
Let $\mathcal M'$ satisfy the function defining axioms and the unique-existence hypotheses, and let $\mathcal M$
be its old-language reduct. With $B$ and $y$ as above,
$$\mathcal M,s\models\FirstOrderTermGraph{t}{y}{B}
\quad\Longleftrightarrow\quad s(y)=t^{\mathcal M',s}.$$
Moreover,
$$\FreeVarsFormula{\FirstOrderTermGraph{t}{y}{B}}\IncludedIn\FreeVarsTerm{t}\cup\{y\}.$$
\end{lemma*}

\begin{proof}
Induct on the term. The variable case is equality. For an application, the induction hypothesis applies to each
child because its output index is below $B+n$, as are all original variables. A witness assignment changes only
$z_0,\ldots,z_{n-1}$. Hence it leaves the values of the original terms and of $y$ unchanged. The child graphs
force each $z_i$ to equal the value of $t_i$ under the original assignment. For an old operation, the remaining
constraint is its ordinary value equation. For a new operation, its defining axiom and uniqueness identify its
graph with exactly that value equation. This proves the forward implication. Conversely, assign each $z_i$ the
value of $t_i$. The child graphs then hold, and the assumed output equation gives the remaining constraint.

For the free-variable assertion, each child contributes only its original variables and its output $z_i$.
The operation constraint contributes only the argument variables and $y$; the defining graph has no other free
parameters. Existential quantification removes every $z_i$. Induction therefore gives the displayed inclusion.
\end{proof}

\begin{lemma*}[\termdefineas{derivable existence of term values}{Derivable existence of term values}]
Let $T$ be a theory of sentences proving the unique-existence hypothesis for each defined function.
If $y$ does not occur in $t$, and $B$ exceeds the indices of $y$ and every variable of $t$, then
$$T\vdash\exists y\,\FirstOrderTermGraph{t}{y}{B}.$$
For a finite tuple of terms $t_0,\ldots,t_{n-1}$, choose $B$ above all their variable indices and put
$z_i=v_{B+i}$. Then
$$T\vdash\exists z_{n-1}\cdots\exists z_0\,
\bigwedge_{i<n}\FirstOrderTermGraph{t_i}{z_i}{B+n}.$$
These are derivations in the old language, including when the terms contain newly defined function symbols.
\end{lemma*}

\begin{proof}
First derive $T\vdash\exists y\,\FirstOrderOperationGraph{f}{\vec{z}}{y}$ at the input names $z_i=v_{B+i}$
and an output name whose index is below $B$. For an old function, use the term $f(\vec{z})$ as witness and
equality reflexivity. For a defined function, instantiate the universal closure of its unique-existence
hypothesis at its original input variables and discard the uniqueness conjunct under existential elimination.
The resulting existential formula can be renamed to the desired inputs and output: their names are distinct,
so the finite bijection extends to a permutation by pairing the remaining names in the union of its domain and
range. Apply the renaming rule to the derivation. The assumptions from $T$ are sentences and hence are fixed
as $\alpha$-classes. Comparison of simultaneous instances identifies the renamed defining graph with the required
operation graph.

We use a finite witness argument. Suppose $\Gamma\vdash\exists z_i\,\rho_i$ for each $i<n$, the names
$z_i$ are distinct and absent from the free variables of $\Gamma$ and $\chi$, and $z_i$ is not free in
$\rho_j$ when $i\ne j$. If $\Gamma,\bigwedge_{i<n}\rho_i\vdash\chi$, then $\Gamma\vdash\chi$.
To see this, open the existential assumptions one at a time and combine their bodies by conjunction introduction.
Each later witness name remains fresh for every earlier body by the cross-freshness condition.
Use the given derivation of the conclusion, then discharge the temporary assumptions by existential elimination.
For an empty family, the conjunction is true and has a proof without assumptions.
In particular, the bodies together imply their existentially quantified conjunction by using their own variable
names as witnesses, so the individual existence proofs give a proof of that quantified conjunction.

Now induct on the term. For a variable, its own name supplies the value. At a function application, induction
gives existence of each child value. The child graphs have no free variables other than their own output names
and original term variables, so the finite witness argument applies. Under these child assumptions, obtain an
operation value using the first paragraph. Its output name is absent from the child graphs because it does not
occur in the original term and differs from every child output. Conjoin the child graphs with the operation
graph, introduce the block of child quantifiers using their own names as witnesses, and introduce the output
quantifier. Existential elimination discharges the operation witness and then the child witnesses. The final
conclusion has no free child output, and the original assumptions are sentences, so all eigenvariable conditions
hold. This proves the first assertion.

Apply the finite witness argument to the resulting child-value proofs to obtain the second assertion.
The empty tuple gives the provable empty conjunction.
\end{proof}

\begin{theorem*}[\termdefineas{elimination of defined functions}{Elimination of defined functions}]
Every formula in the language expanded by these function definitions has an old-language translation with the
same truth value in every model of the defining axioms and unique-existence hypotheses. Its free variables are
a subset of those of the original formula.
\end{theorem*}

\begin{proof}
For an atom $R(t_0,\ldots,t_{n-1})$, choose $B$ above all variable indices in its terms and put $z_i=v_{B+i}$.
Translate it to
$$\exists z_{n-1}\cdots\exists z_0\,\Bigl(
\bigwedge_{i<n}\FirstOrderTermGraph{t_i}{z_i}{B+n}\land R(\vec{z})\Bigr).$$
For an equality, use two witnesses in the same construction and put their equality in the last conjunct.
Leave falsity unchanged, and translate recursively through connectives and quantifiers while retaining their
constructors and bound variables.

The recursive-graph lemma forces the witnesses of an atom to be exactly its argument values. Conversely, these
values supply witnesses, so the original and translated atoms have the same truth value. The free-variable
inclusion follows because all witness variables are bound. Structural induction now proves both assertions
for every formula: connectives combine their subformulas, and quantifiers apply the induction hypothesis under
each assignment to the bound variable. No new free variable can be captured by an outer quantifier.
\end{proof}

\begin{lemma*}[\termdefineas{alpha invariance of function elimination}{Bound names in function elimination}]
Changing the admissible starting index $B$ in $\FirstOrderTermGraph{t}{y}{B}$ changes the formula only up to
$\alpha$-equivalence. Elimination of defined functions sends $\alpha$-equivalent formulas to
$\alpha$-equivalent formulas. It therefore defines a translation on $\alpha$-classes, retaining the truth and
free-variable assertions above.
\end{lemma*}

\begin{proof}
Compare two terms under an arbitrary relation $R$ on names, with output names also related by $R$.
Choose fresh starting indices $B,C$ on the two sides. At an application with $n$ arguments, pair the witnesses
$v_{B+i}$ and $v_{C+i}$ for each $i<n$. Under their existential quantifiers, repeatedly update the name relation
by the bound-name rule used in the comparison lemma. Each pair of witnesses then corresponds.
A name outside the left block and a name outside the right block retain their original relation.
The original term variables and output names are outside their respective blocks by freshness.

Induct on the compared terms. Variables give corresponding equalities. At an application, compare each pair of
child graphs under the updated relation. Their outputs are the paired witnesses, their internal names start at
$B+n$ and $C+n$, and the original variables remain below those indices. Thus induction applies. For an old
operation, its value equation compares componentwise. For a new operation, use the comparison of simultaneous
instances of its defining graph proved above, including the output among the arguments. Combine the child
graphs by conjunction and close each paired existential quantifier. This yields comparison under the original
relation. Applying this result to identical terms and outputs with equality as the relation proves independence
of the fresh starting index up to $\alpha$-equivalence.

The same argument compares translations of atoms: pair their argument witnesses, compare the recursive term
graphs, and compare the final relation or equality at those witnesses. Now induct on formula comparison.
Connectives preserve comparison, and at a quantifier the induction hypothesis uses the updated relation on
bound names. Taking equality as the initial relation and applying the comparison lemma proves that elimination
respects $\alpha$-equivalence. The translation consequently descends to $\alpha$-classes, and its truth and
free-variable properties follow from those already proved for representatives.
\end{proof}

#### Substitution and Proof Translation {#sec:definition-function-proofs}

\begin{lemma*}[\termdefineas{equality in simultaneous instances}{Equality in simultaneous instances}]
Let the free variables of $\varphi$ be among the input variables $\vec{u}$.
If $\Gamma\vdash s_i=t_i$ for every input position and
$\Gamma\vdash\varphi\subst{\vec{u}}{\vec{s}}$, then
$\Gamma\vdash\varphi\subst{\vec{u}}{\vec{t}}$.
This applies to operation graphs, including the output as the last input position.
\end{lemma*}

\begin{proof}
Change one position at a time. For the current position, replace its argument by a variable absent from all
current arguments. Substituting the old or new argument into this hole yields precisely the corresponding
simultaneous instance: the substitution composition lemma shows that every other argument stays unchanged.
Equality elimination therefore transports the current instance to the one with this argument changed.
Induction on the finite set of positions yet to be changed gives the conclusion. No assumption on the free
variables of the context is needed. For an old operation, use the formula equating the output slot to its
function term; for a defined operation, use its defining graph. Both have free variables only in their input
and output slots, so the same argument applies.
\end{proof}

\begin{lemma*}[\termdefineas{derivable uniqueness of term values}{Derivable uniqueness of term values}]
Let $T$ be a theory of sentences proving the unique-existence hypotheses of the function definitions.
Choose distinct variables $y,z$ absent from $t$, and let $B$ exceed their indices and all variable indices in $t$.
Then
$$T\vdash\bigl(\FirstOrderTermGraph{t}{y}{B}\land\FirstOrderTermGraph{t}{z}{B}\to y=z\bigr),$$
and
$$T\vdash\exists!y\,\FirstOrderTermGraph{t}{y}{B},$$
where the comparison variable in the unique-existence abbreviation is $z$.
\end{lemma*}

\begin{proof}
Each operation graph has a provably unique output at distinct named inputs. For an old function, its value term
supplies existence; two values equal to that term are equal by symmetry and transitivity. For a defined function,
instantiate the universal unique-existence axiom at its original inputs. Extend the finite correspondence of
input, output, and comparison names to a permutation, and rename the derivation. The graph is the desired
simultaneous instance, and sentence assumptions are unchanged. Symmetry and transitivity for open terms follow
from the same equality-elimination proofs given earlier, choosing the hole fresh for the fixed terms.

Consequently, two values satisfying the same operation graph are provably equal. To keep their actual names
unrestricted, choose auxiliary output and comparison names fresh for the inputs and both values. From unique
existence and the graph at the first value, the graph-replacement proof gives a universal characterization of
all graph values. Instantiate it at the second value and use its graph assumption. This gives equality of the
second value with the first; symmetry gives the desired orientation. The auxiliary names are not free in the
added graph assumptions, so all eigenvariable conditions remain valid.

The output variable of a recursive graph can also be replaced directly:
$$\bigl(\FirstOrderTermGraph{t}{y}{B}\bigr)\subst{y}{z}
\equiv_\alpha\FirstOrderTermGraph{t}{z}{B}.$$
For a variable term this is substitution into equality. At an application, the child graphs contain no free
occurrence of the output: their free variables are original parameters or their own child outputs. Substitution
therefore leaves them unchanged. It passes through the child quantifiers because their names have indices at
least $B$, and it changes only the output of the final operation graph.

Prove pairwise equality by induction on the term. The variable case follows by symmetry and transitivity.
For an application with $n$ arguments, set $C=B+n$. In the second graph change the starting index from $B$ to
$C$, using the independence of fresh starting indices proved above. Open the two child blocks with names
$u_i=v_{B+i}$ and $w_i=v_{C+i}$. The blocks are disjoint. Each original parameter and both final outputs have
indices below $B$.

For each child, move the first graph's internal starting index from $B+n$ to $C+n$ by the same independence
lemma. The induction hypothesis now gives $u_i=w_i$. Equality in simultaneous instances transports the first
operation graph from the inputs $\vec{u}$ to $\vec{w}$, preserving its output. The second operation graph
already has the latter inputs. Operation uniqueness therefore identifies the two final outputs. Discharge the
second child block and then the first by existential elimination. The second block's names are not free in
the first unquantified matrix, whose free names have indices below $C$. The first block's names are not free in
the entire second graph. Neither block has a free occurrence in the final equality or the sentence assumptions.
Thus these eliminations satisfy their eigenvariable conditions.

Finally combine pairwise equality with the previously proved existence of a term value. Under the graph
assumption for the output, assume the graph at the comparison variable and derive their equality. Reverse its
orientation, discharge the comparison assumption, and universally quantify the comparison variable, which is
fresh for the output graph. Conjoin this uniqueness clause with the output graph and introduce the existential
output quantifier. Existential elimination using the existence proof discharges the temporary output
assumption. The substitution identity above identifies the comparison instance with the graph at the second
output, so the result is exactly the displayed unique-existence abbreviation.
\end{proof}

\begin{lemma*}[\termdefineas{variable substitution in function elimination}{Variable substitution and elimination}]
Let $\psi$ be the translation of $\varphi$ obtained by eliminating the defined functions.
The translation of $\varphi\subst{x}{y}$ is $\psi\subst{x}{y}$ up to $\alpha$-equivalence,
even if $y$ already occurs freely in $\varphi$.
The same holds for simultaneous replacement of all free variables by variables, with repeated names allowed.
For recursive term graphs, if $w\ne x$, then
$$\bigl(\FirstOrderTermGraph{t}{w}{B}\bigr)\subst{x}{y}
\equiv_\alpha\FirstOrderTermGraph{t\subst{x}{y}}{w}{C},$$
where each starting index exceeds the indices of its term variables and its output variable.
If the output variable is also replaced, use its replacement on the right.
\end{lemma*}

\begin{proof}
Let $r$ send $x$ to $y$ and fix every other name, and put $R(a,b)$ if and only if $a=r(b)$.
The substitution comparison lemma compares the substituted formula with the original under $R$.
Function elimination preserves this comparison, by the proof of bound-name invariance above.
Independently, substitution in the translated formula compares with that same original translation under $R$.
Compose the first comparison with the reverse of the second. A right-hand name determines its left-hand name
uniquely, so the resulting comparison is equality of names and gives $\alpha$-equivalence.
This does not require the replacement map to be injective.

For simultaneous variable replacement, use the finite replacement map and the comparison lemma for simultaneous
instances. The free-variable inclusion for elimination ensures that the translated formula has no extra input
positions. The same comparison argument applies to term graphs, including the output in the name relation
and choosing admissible internal starting indices independently on the two sides.
\end{proof}

\begin{lemma*}[\termdefineas{substitution in term graphs}{Substitution in term graphs}]
Let $T$ be a theory of sentences proving the unique-existence hypotheses of the function definitions,
and let $t,r$ be terms of the expanded language. Choose distinct variables $y,w$ absent from both terms,
and let $B$ exceed their indices and every variable index in the terms. Then
$$\begin{aligned}
T\vdash\FirstOrderTermGraph{t\subst{x}{r}}{w}{B}
\;\leftrightarrow\;\exists y\,\Bigl(
&\FirstOrderTermGraph{r}{y}{B}\\
&{}\land\FirstOrderTermGraph{t\subst{x}{y}}{w}{B}\Bigr).
\end{aligned}$$
Thus substitution of a term is represented by binding its value and using that value in the outer graph.
\end{lemma*}

\begin{proof}
First assume the graph of the replacement value and the outer graph with that value substituted.
Induct on the outer term to derive the graph with the term itself substituted. At the variable being replaced,
the outer graph equates its output with the replacement value; equality elimination transports the replacement
graph to that output. At any other variable, the value equation is unchanged. At an application with $n$
arguments, open the child values $v_{B+i}$ for $i<n$. Move the replacement graph's internal starting index to
$B+n$, using bound-name invariance, and apply induction to each child. The operation graph is unchanged.
Conjoin the resulting child graphs with it and introduce their existential block. Discharge the original child
block by existential elimination: its names are not free in the original assumptions or final graph, whose
free-variable indices are below $B$. This also covers the empty child block of a constant.

For the converse under the replacement-value assumption, take a value $u=v_B$ of the outer term
$t\subst{x}{y}$, using existence with internal starting index $C=B+1$. The preceding direction gives the graph
of $t\subst{x}{r}$ at $u$. Change the given graph at $w$ to the same internal starting index.
Uniqueness identifies these two values. Equality elimination in the outer graph then replaces its output
$u$ by $w$, and bound-name invariance restores its starting index to $B$.
The auxiliary name is absent from the parameters and conclusion, so existential elimination discharges its
temporary graph assumption. This proves the converse without a second induction on terms.

Finally, existence supplies a value of the replacement term. Under that value's graph, the converse just proved
turns the left side of the displayed equivalence into the outer graph, and existential introduction gives
the right side. Conversely, open the value on the right and use the first direction. The bound value's name
is not free in the left side or in the sentence assumptions, so both existential eliminations are valid.
\end{proof}

\begin{lemma*}[\termdefineas{relational substitution in atoms}{Relational substitution in atoms}]
Let $T$ be a theory of sentences proving the unique-existence hypotheses of the function definitions.
Let $\varphi$ be a relation atom, an equality, or falsity, and let $r$ be a term of the expanded language.
Choose a variable $y$ absent from $\varphi,r$, and let $B$ exceed its index and all variable indices in them.
Write $\psi$ for the translation of $\varphi$ and $\chi$ for the translation of $\varphi\subst{x}{r}$.
Then
$$T\vdash\chi\;\leftrightarrow\;\exists y\,\Bigl(
\FirstOrderTermGraph{r}{y}{B}\land\psi\subst{x}{y}\Bigr).$$
\end{lemma*}

\begin{proof}
For a relation or equality, use the common starting index $B$ for the argument witnesses in both translations.
This is admissible after either substitution. Pairing the corresponding witness positions, as in the proof of
bound-name invariance, identifies these formulas up to $\alpha$-equivalence with the translations using their
originally chosen indices. Translation also commutes with variable substitution by the earlier lemma.

Assume the graph of the replacement value. For each of the $n$ arguments, the two conditional implications
in the term-graph substitution proof transform its graph in either direction. The child output is $v_{B+i}$,
its internal starting index is $B+n$, and this output is absent from the original arguments and replacement
term. Move the replacement graph to this internal starting index by bound-name invariance.
Open the block of argument values, apply the appropriate implication to each child, retain the final relation
or equality, and reintroduce the same block. The original assumptions and the final translated atom contain no
free witness name, so existential elimination discharges the opened block. This is one argument for any finite
number of argument positions, including zero; equality uses two positions.

Both conditional implications now hold under the same replacement-value graph. Existence supplies such a
value. From the left side of the displayed equivalence, the conditional implication gives the translated atom
at that value, and existential introduction gives the right side. In the other direction, open the value and
apply the other implication. The free-variable bound for translation shows that the value's name is not free
in the left side. It is also not free in the sentence assumptions, so both existential eliminations are valid.
These are the same value-binding steps used in \termuse{substitution in term graphs}.

For falsity, each conditional implication simply extracts falsity from its conjunction with the value graph.
The same value-binding argument applies, giving the remaining base case.
\end{proof}

\begin{theorem*}[\termdefineas{relational substitution for function elimination}{Relational substitution}]
Let $T$ be a theory of sentences proving the unique-existence hypotheses of the function definitions.
Let $\varphi$ be any formula and $r$ any term of the expanded language. Choose $y$ not free in $\varphi$
and absent from $r$, and let $B$ exceed its index and all variable indices in $r$.
If $\psi$ is the translation of $\varphi$ and $\chi$ is the translation of $\varphi\subst{x}{r}$, then
$$T\vdash\chi\;\leftrightarrow\;\exists y\,\Bigl(
\FirstOrderTermGraph{r}{y}{B}\land\psi\subst{x}{y}\Bigr).$$
\end{theorem*}

\begin{proof}
Choose a representative of the formula whose bound names avoid $x,y$ and every variable of $r$,
using \termuseas{fresh bound names lemma}{lemma on fresh bound names}.
Keep $\rho:=\FirstOrderTermGraph{r}{y}{B}$ as an assumption and prove
$$T\vdash\rho\to\bigl(\chi\leftrightarrow\psi\subst{x}{y}\bigr)$$
by structural induction, before binding the replacement value. The conditional implications in the proof of
\termuse{relational substitution in atoms} give the atomic cases. At an atom, enlarge its witness starting index
if needed to exceed its argument variables. Bound-name invariance identifies the replacement graph at this
larger index with the original one, so the same assumption is retained throughout the induction.

For conjunction, transform the two components and reintroduce the conjunction. For disjunction, transform each
branch and use disjunction elimination. For implication, transform the antecedent in the reverse direction,
apply the given implication, and transform the consequent in the forward direction. Reverse both component
equivalences to obtain the other implication. These are derivations under the same value assumption, so no
existential quantifier has to be moved through a connective.

At a quantifier with bound variable $z$, the choice of names ensures that $z$ is different from $x,y$ and
absent from $r$. Both substitutions therefore pass into the body. The free-variable bound for the term graph
also gives $z\notin\FreeVarsFormula{\rho}$. For a universal quantifier, instantiate the quantified premise at
its own bound variable, apply the appropriate direction of the body's equivalence, and universally quantify
again. The bound name is not free in the sentence assumptions, the value graph, or the quantified premise,
so universal introduction is valid.

For an existential quantifier, open the premise at its own bound variable, apply the body's implication, and
introduce the target existential quantifier. The bound name is absent from the free variables of the original
context and the quantified conclusion, so existential elimination discharges the temporary body assumption.
The same argument in reverse gives the other implication. Translation commutes with variable substitution,
and its independence of representatives transfers the resulting conditional equivalence to the original formula.

Finally, the existence lemma supplies the replacement value. The variable $y$ is not free in $\chi$, by the
free-variable formulas for substitution and translation. Apply the shared value-binding argument from
\termuse{relational substitution in atoms} to obtain the displayed equivalence.
\end{proof}

\begin{corollary*}[\termdefineas{translated equality reflexivity}{Translated equality reflexivity}]
Let $T$ be a theory of sentences proving the unique-existence hypotheses of the function definitions.
For every term $t$ in the expanded language, the translation of $t=t$ is provable from $T$.
\end{corollary*}

\begin{proof}
Choose the starting index $B$ used in translating the equality, so its two argument witnesses are
$v_B,v_{B+1}$. Put $w=v_{B+2}$ and $C=B+3$.
The existence lemma gives $T\vdash\exists w\,\FirstOrderTermGraph{t}{w}{C}$.
Temporarily assume the graph at this value. Substitute this same value for both argument witnesses in the
translated equality. The preceding lemma identifies each instantiated argument graph with the assumed graph,
up to $\alpha$-equivalence. Reflexivity proves equality of the two values, and the empty conjunction is true.
Conjunction introduction and the two existential introductions therefore prove the translated equality under
the temporary graph assumption. The variable $w$ is absent from the original term, hence is not free in the
translation by its free-variable bound. It is also not free in the sentence assumptions. Existential elimination
using the
existence proof therefore discharges the temporary graph assumption and yields the required proof in $T$.
\end{proof}

\begin{theorem*}[\termdefineas{proof translation for function definitions}{Proof translation for functions}]
Let $T$ be a theory of sentences proving the unique-existence hypotheses of the function definitions.
Let $\Gamma$ be a finite set of expanded-language formulas, let $\Delta$ be their translations,
and let $\psi$ be the translation of $\varphi$. Then
$$\Gamma\vdash\varphi\quad\Longrightarrow\quad T\cup\Delta\vdash\psi.$$
The same conclusion holds for arbitrary sets of assumptions, since proofs have finite support.
\end{theorem*}

\begin{proof}
Induct on the given natural-deduction derivation. Translate each finite context pointwise and add the old
sentence theory. If translated subderivations use different finite subsets of that theory, take their union.
Adding an assumption commutes with translation of contexts, so assumption discharge is preserved by the
deduction lemma. A free variable of the translated context already occurred in the original context.
The added sentence assumptions have no free variables.

The connective rules, falsity elimination, and excluded middle retain their constructors. Universal introduction
therefore retains its eigenvariable condition. For existential elimination, the original eigenvariable remains
absent from the translated context, conclusion, and existential premise. The temporary body assumption is the
required variable instance because translation commutes with variable substitution. For equality introduction,
use \termuse{translated equality reflexivity}.

For the rules with a term instance, write $\theta$ for the body and $\eta$ for its translation.
For universal elimination at $t$, choose a value name $y$ fresh for the body and the term and an admissible
starting index $B$. Existence gives the graph $\FirstOrderTermGraph{t}{y}{B}$ at some value.
Under that graph, instantiate $\forall x\,\eta$ at the variable $y$ to obtain $\eta\subst{x}{y}$.
Introduce the existential value quantifier and apply \termuse{relational substitution for function elimination}
to obtain the translation of $\theta\subst{x}{t}$. The temporary value name is not free in the universally
quantified premise or the sentence assumptions, so its graph assumption can be discharged.

For existential introduction, relational substitution turns the translated instance into existence of a value
whose graph and body instance both hold. Open this value, use it as the witness for the original existential
quantifier, and discharge the graph-and-body assumption. The temporary value name is not free in the translated
instance, the existential conclusion, or the sentence assumptions. These two quantifier implications are proved
from the old theory and then applied to the translated premises of the derivation.

For equality elimination, choose $B$ above all free-variable indices in $\theta$ and all variable indices in
$t,r$. By bound-name invariance, the translated equality can use the value names $u=v_B$ and $v=v_{B+1}$,
with internal graph indices $B+2$. Open its two value graphs and their final equality $u=v$.
The conditional substitution lemma for the first graph turns the translated $\theta\subst{x}{t}$ into
$\eta\subst{x}{u}$. Ordinary equality elimination gives $\eta\subst{x}{v}$, and the conditional lemma for the
second graph gives the translation of $\theta\subst{x}{r}$. Discharge the two value assumptions
by existential elimination.
Their names are not free in either original translated premise or in the final conclusion: all such free-variable
indices are below $B$. This proves the equality-elimination implication in the old theory, ready to be applied
to the translated premises.

All rules have now been translated. For an arbitrary theory of expanded-language assumptions, choose the finite
support of its proof, apply the result just established, and include the translated support in the translated
theory. No additional assumption on the free variables of the original hypotheses is needed.
\end{proof}

### Conservativity and Model Expansion {#sec:definition-conservativity}

**Conservativity.**
An extension of $T$ is \termdefineas{conservative extension}{conservative} if every old-language sentence provable
in the extension is already provable from $T$. The following criterion separates this property from uniqueness
of model expansions.

\begin{lemma*}[\termdefineas{model-expansion criterion for conservativity}{Model-expansion criterion}]
Let $L'$ extend $L$, let $T$ be a theory of $L$-sentences, and let $T'$ be a theory of $L'$-sentences containing $T$.
If every nonempty model of $T$ admits an expansion to a model of $T'$, then $T'$ is conservative over $T$.
\end{lemma*}

\begin{proof}
Suppose an $L$-sentence $\sigma$ is provable from $T'$ but not from $T$.
Completeness gives a nonempty model $\mathcal M\models T$ with $\mathcal M\not\models\sigma$.
By hypothesis it has an expansion $\mathcal M'\models T'$ with the same domain and old interpretations.
Induction on terms and formulas shows that the expansion and its reduct agree on $L$-formulas,
so $\mathcal M'\not\models\sigma$. This contradicts soundness applied to the proof from $T'$.
Uniqueness of the expansion is not needed for this argument.
\end{proof}

\begin{corollary*}[\termdefineas{conservativity of definitional extensions}{Conservativity of definitional extensions}]
Adding the relation, function, and constant definitions described above gives a conservative extension of $T$.
\end{corollary*}

\begin{proof}
For relation symbols, use \termuse{unique expansion by relation definitions}.
For function symbols and constants, use \termuse{unique expansion by function definitions}.
In each case every old model admits an expansion satisfying the new axioms, so the
\termuse{model-expansion criterion for conservativity} applies. To combine relation definitions with function
definitions, first add the relations and then the functions, including constants as the nullary case.
The defining graphs may use the relations already added, provided the intermediate theory proves their
unique-existence assertions. A sentence of the original language provable in the final theory is first
provable in the intermediate theory, by conservativity of the function definitions, and then in $T$,
by conservativity of the relation definitions.

More generally, let $T_0,\ldots,T_n$ be successive theories obtained by such definitions, and let $\sigma$
be a sentence of the language of $T_0$. For $n=0$ there is nothing to prove. If $n\ge 1$ and $T_n\vdash\sigma$,
conservativity of the last extension gives
$T_{n-1}\vdash\sigma$. Repeating this step gives $T_0\vdash\sigma$. Induction on $n$ therefore handles
any finite succession of definitions, each allowed to use the symbols introduced earlier.
\end{proof}

For relation definitions, \termuse{syntactic conservativity of relation definitions} gives a direct transformation
of proofs. The model argument above also covers the function and constant definitions.

Uniqueness is essential for treating function and constant definitions as mere abbreviations.
If $T$ proves only $\forall \vec{x}\,\exists y\,\theta(\vec{x},y)$, adding a function $f$ with
$\theta(\vec{x},f(\vec{x}))$ chooses a witness at each input. Using the set-theoretic axiom of choice,
every model admits such a \termuse{Skolem function}, so the model-expansion criterion still gives a
\termuse{conservative extension}. However, the expansion need not be unique and the new function is not determined
by the old structure. In
§{sec:appendix-set-theory}, total term notations such as $\emptyset$, $\{a,b\}$, and $\bigcup x$ are
introduced only where
ZFC proves unique existence. Partial notations such as $f(a)$ are treated contextually rather than as total function
symbols.

### Complexity After Unfolding Definitions {#sec:definition-complexity}

\begin{mathmeta}
  \vars{u}{Set}
\end{mathmeta}

**Complexity bookkeeping.**
Elimination is a proof-theoretic translation, not by itself a promise about the Lévy hierarchy. The complexity level
must be measured after the expanded notation has been translated back into the old language. Thus $P(f(x),z)$ is atomic
only in the expanded language $L\cup\{f\}$. In the old language $L$, the term $f(x)$ has to be replaced by a witness to
its defining graph:
$$
P(f(x),z)
\quad\leadsto\quad
\exists u\,\bigl(\theta(x,u) \land P(u,z)\bigr).
$$
If $\theta(x,u)$ is $\Sigma_1$, say $\theta(x,u)$ has the form $\exists w\,\delta(x,u,w)$ with $\delta$ $\Delta_0$, then
this becomes
$$
\exists u\,\exists w\,\bigl(\delta(x,u,w) \land P(u,z)\bigr),
$$
which is $\Sigma_1$. The apparent atomicity of $P(f(x),z)$ was therefore an artifact of the abbreviation. Definitional
extension preserves truth and provability in the old language, but it does not automatically preserve the boundedness of
quantifiers that the Lévy hierarchy tracks.

There is, however, a systematic bounded version. A definition is \termdefine{$\DeltaZero$-safe} when eliminating it
introduces only bounded quantifiers and formulas already known to be $\Delta_0$-safe. For relation symbols, this means
that the defining formula is $\Delta_0$ after recursively unfolding earlier safe definitions. For function symbols, the
graph must have a bounded definition in the following stronger sense: there is an already available term or
contextual parameter $B(\vec{x})$
such that
$$
T \vdash \forall \vec{x}\,\exists! y \in B(\vec{x})\,\theta(\vec{x},y),
$$
with $\theta$ itself $\Delta_0$ after recursively unfolding earlier safe definitions. In this bounded version,
the defining axiom is
$$f(\vec{x})=y\quad\longleftrightarrow\quad
 y\in B(\vec{x})\land\theta(\vec{x},y).$$
If the function was already defined by its graph without a bound, verify that its unique value lies in the
proposed bound. An atomic formula containing $f(\vec{t})$ can then be translated by a bounded witness:
$$
P(f(x),z)
\quad\leadsto\quad
\exists u \in B(x)\,\bigl(\theta(x,u) \land P(u,z)\bigr).
$$
This keeps the translation $\Delta_0$ whenever the surrounding atomic formula and the defining graph are $\Delta_0$.
The bound itself must already admit bounded elimination, or be supplied as a parameter; introducing an
unboundedly defined bound would defeat the argument. Multiple function terms are handled by adding one bounded
witness for each occurrence.

\begin{proposition*}[\termdefineas{bounded unfolding lemma}{Bounded unfolding}]
Suppose each relation abbreviation has a $\Delta_0$ expansion and each function abbreviation has a bounded
unique-value definition as above. Every formula built from these expansions by Boolean connectives, bounded
quantifiers, and bounded substitution of function values has an equivalent $\Delta_0$ formula in the membership
language. Each bound must be a parameter or a value already introduced by an earlier bounded clause.
The equivalence holds in every model satisfying the defining axioms and the bounded unique-existence hypotheses.
\end{proposition*}

\begin{proof}
Keep, at each step, both a formula in the membership language and the facts that it is bounded and expresses
the intended predicate. A relation abbreviation supplies the initial formula. Boolean connectives preserve both
facts. For a quantifier bounded by an available variable, apply the equivalence for its body separately to each
value in that bound. Adding this bounded quantifier preserves $\Delta_0$ complexity.

For a function value, let $\chi(u)$ denote the already expanded surrounding formula, with its other parameters
fixed. The defining axiom and bounded unique existence give
$$\chi(f(\vec{x}))\quad\longleftrightarrow\quad
\exists u\in B(\vec{x})\,\bigl(\theta(\vec{x},u)\land\chi(u)\bigr).$$
In the forward direction, use the value of the function as the witness; it lies in the bound and satisfies the
graph. In the reverse direction, uniqueness identifies every witness with that value, so the surrounding
formula holds at the function value. The displayed right-hand side is $\Delta_0$ because its graph and body
are $\Delta_0$ and its existential quantifier is bounded. All other parameters are retained.

Iterate this step from the innermost function occurrences outward. Introduce a fresh variable for each value,
and retain each bounded witness inside the scope of every parameter on which it depends. A later bound may
use values already introduced, but may not rely on its own witness or on an unexpanded function term.
Induction on the finite construction now proves the assertion, including nested function occurrences and
function values used as bounds. No unbounded quantifier is introduced.
\end{proof}

As a sample relation abbreviation, $y \IncludedIn x$ unfolds to
$$\forall z \in y\; z \in x,$$
so $\IncludedIn$ is $\Delta_0$-safe. As a sample function abbreviation, the graph of binary union can be written
$$
\theta_\cup\Tuple{x,y,u} \;:\equiv\;
(\forall z \in u)(z\in x \lor z\in y)
\land (\forall z \in x)\,z\in u
\land (\forall z \in y)\,z\in u.
$$
This graph is $\Delta_0$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
subsetの有界展開・binaryUnionGraphのΔ₀性・unionへの所属の直接展開は既存リンクで対象。残る箇所は、
未展開のpair/union/powersetを値の上界と勝手に扱えないという適用限界と、transitive
model間でpowersetが変わり得るという背景上の警告。具体的な二つのモデルの構成・非絶対性の証明をこの段落では示さず、bounded
unfoldingの局所証明にも使用しない。一般のpower-set非絶対性をこのコードが証明したとは扱わない。)
--> That alone does not license treating binary union as a primitive term in every
bounded formula. The proposed bound
$$u \in \PowerSet{\bigcup\{x,y\}}$$
would itself require eliminating pair, union, and power-set terms; it is not an already available bound in
pure set-theoretic language. In particular, the power-set operation cannot generally be eliminated by bounded
formulas: transitive models can disagree about which subsets of a given set exist.<!--
formalization: skip-end
-->
For the common membership context, use the direct bounded expansion
$$z\in x\cup y\quad\Longleftrightarrow\quad z\in x\lor z\in y.$$
<!--
formalization: skip-begin (引用・背景説明・読書案内:
subsetの有界展開・binaryUnionGraphのΔ₀性・unionへの所属の直接展開は既存リンクで対象。残る箇所は、
未展開のpair/union/powersetを値の上界と勝手に扱えないという適用限界と、transitive
model間でpowersetが変わり得るという背景上の警告。具体的な二つのモデルの構成・非絶対性の証明をこの段落では示さず、bounded
unfoldingの局所証明にも使用しない。一般のpower-set非絶対性をこのコードが証明したとは扱わない。)
--> Other contexts must be checked by their own expansions, or by a bound explicitly supplied as a parameter.<!--
formalization: skip-end
-->

Call the recursive replacement of expanded notation by these bounded clauses \termdefine{bounded unfolding}. Thus
definitional extension preserves old-language theorems in general, while Lévy-complexity preservation requires
$\Delta_0$-safe definitions or explicitly contextual notation. When this text claims that a formula is $\Delta_0$,
$\Sigma_n$, or $\Pi_n$ in §{sec:zfc-absoluteness}, the claim is made after bounded unfolding, so no hidden unbounded
quantifier is being counted as harmless.\termref{absoluteness}
