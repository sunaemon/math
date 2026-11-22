# Appendix: Absoluteness of Borel Measure {#sec:appendix-measure-absoluteness}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
付録の目的と構成順序の導入。個々の測度値構成・比較定理は後続で別に対応し、この段落で新たな局所証明を提示していない。)
--> This appendix constructs measure values inside a transitive model and identifies them with external Borel measure.
The Borel interpretations and rank certificates come from §{sec:appendix-borel-absoluteness}.
We first construct internal approximations, then codes for real measure values, and finally verify the measure laws
and the comparison with the external measure. Each construction states the model axioms it needs.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続のrandom forcing付録と本文章への案内。ここに独立した測度代数・名前評価・generic回復の定理を追加したとは扱わない。)
--> §{sec:appendix-random-forcing} uses these comparisons to construct internal measure algebras, evaluate names,
and recover a generic filter from a random point. The applications to Polish spaces are presented in §{sec:forcing}.<!--
formalization: skip-end
-->

## Internal Approximations of Borel Sets {#sec:internal-measure-approximations}

### Finite Tests and Open Approximations {#sec:internal-finite-measure-bounds}

\begin{mathmeta}
  \vars{a,b,k,n,p,u,v}{Nat}
  \vars{s,t}{Seq(Nat)}
  \vars{\sigma,\tau,\alpha,\beta}{Set}
  \vars{A}{Set}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
BijとCountの実際の式はbijectionPredicate/finiteCardinalityFormulaへ対応済み。
残るのはモデル公理の仮定と有限個数を扱う方針を述べる導入だけ。)
--> For the numerical part, assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set,
and Separation. We first justify counting finite sets inside $M$.<!--
formalization: skip-end
-->  For a finite ordinal $k$, let
$$\begin{aligned}
\mathrm{Bij}(k,A,g):\equiv{}&g:k\to A\\
&{}\land\forall y\in A\;\exists i\in k\;\Pair{i}{y}\in g\\
&{}\land\forall i,j\in k\;\forall y\in A\;[\\
&\quad(\Pair{i}{y}\in g\land\Pair{j}{y}\in g)
\longrightarrow i=j].
\end{aligned}$$
This is a bounded predicate. Define $\mathrm{Count}(k,A):\equiv\exists g\;\mathrm{Bij}(k,A,g)$.
The quantifier over $g$ is unrestricted, so absoluteness of $\mathrm{Count}$ requires a further argument.

\begin{lemma*}[\termdefine{Absolute finite cardinalities}]
For every finite set $A\in M$ and every $k\in\omega$,
$$M\models\mathrm{Count}(k,A)\quad\Longleftrightarrow\quad k=\Card{A}.$$
\end{lemma*}

\begin{proof}[Proof]
An internal witness $g$ satisfies the actual bijection conditions by the uniform interpretation principle.
An actual bijection from $k$ to $A$ gives $k=\Card{A}$.
Conversely, such a bijection exists if $k=\Card{A}$. Its graph belongs to $M$ by the finite-function lemma of
§{sec:internal-borel-inputs}, since its domain is finite and all its values lie in $A\in M$.
The same interpretation principle makes this graph an internal witness. The argument includes $k=0$ and
$A=\emptyset$.
\end{proof}

\begin{proposition*}[\termdefine{Internal finite tree levels}]
Let $T\IncludedIn\finseq{2}$, and encode its words as natural-number words with entries $0$ or $1$.
Suppose $W_T\in M$.
For every $n\in\omega$, the exact finite level
$$W_{T,n}:=\{e(s):s\in T_n\}$$
belongs to $M$, and its internally recognized cardinality is the actual number $\Card{T_n}$ used in
§{sec:coded-measure-bounds}.
\end{proposition*}

\begin{proof}[Proof]
Separate from $W_T$ the graphs $\sigma$ satisfying $\sigma:n\to\omega$. The finite-word length lemma identifies
this predicate with having length $n$. Thus the separated set is precisely $W_{T,n}$.
Binary functions on $n$ correspond bijectively to binary words of length $n$, and coding a word by its graph
is injective. Restricting this correspondence to $T$ shows that $\Card{W_{T,n}}=\Card{T_n}$.
Apply the finite-cardinality lemma. This counts the entire level, including nodes with no infinite extension;
neither downward closure nor the existence of a branch is needed here.
\end{proof}

\begin{lemma*}[\termdefine{Internal powers of two}]
The graph $P_2:=\{\Pair{n}{2^n}:n\in\omega\}$ belongs to $M$.
\end{lemma*}

\begin{proof}[Proof]
Use the internal addition graph to separate the graph of $j\mapsto j+j$ from $\omega\times\omega$.
Apply internal numerical iteration from §{sec:internal-natural-arithmetic}, starting at $1$.
Induction identifies the $n$th value with $2^n$, including $2^0=1$.
\end{proof}

Let $G_\times$ be the internal multiplication graph. For natural numbers $n,k,a,b$, define the bounded test
$$\begin{aligned}
\mathrm{DB}(n,k,a,b):\equiv{}&\exists p,u,v\in\omega\;[\Pair{n}{p}\in P_2\\
&{}\land\Pair{\Pair{a}{p}}{u}\in G_\times\\
&{}\land\Pair{\Pair{k}{b}}{v}\in G_\times
\land v\notin u].
\end{aligned}$$
The last condition compares finite ordinals and means $u\le v$.

\begin{proposition*}[\termdefine{Absolute dyadic comparisons}]
Suppose $b>0$ and $M\models\mathrm{Count}(k,W_{T,n})$. Then
$$M\models\mathrm{DB}(n,k,a,b)\quad\Longleftrightarrow\quad\frac ab\le d_n(T).$$
\end{proposition*}

\begin{proof}[Proof]
The count is $k=\Card{T_n}$ by the finite-level proposition. The three graph lookups force
$p=2^n$, $u=a2^n$, and $v=kb$. The common interpretation theorem therefore reduces the internal test to
$a2^n\le\Card{T_n}b$. Since $b>0$ and $2^n>0$, multiplying by the positive denominators gives exactly the stated
rational comparison.
\end{proof}

Every nonnegative rational has a representation $a/b$ with $a\in\omega$ and $b>0$.
For a negative rational $q$, the lower comparison $q\le d_n(T)$ is automatically true, since $d_n(T)\ge0$.
Strict upper comparisons $d_n(T)<q$ are obtained by negating $q\le d_n(T)$.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
非負・負の有理数の下側比較はrational_le_levelWeight_iff、
厳密上側比較はlevelWeight_lt_rational_iffに対応済み。残りは同じ有限データを使う適用範囲と実装方針の説明で、
別の算術宇宙の構成を主張しない。)
--> Thus the argument covers all rational thresholds, using their finite sign, numerator, and denominator data;
it does not require constructing a new arithmetic universe inside $M$.<!--
formalization: skip-end
-->

We can now quantify the finite counts inside a single formula. With $\omega,G_\times,P_2$ retained as
parameters, put
$$\begin{aligned}
L(W,n,A):\equiv{}&A\IncludedIn W\land\forall \sigma\in W\;(\sigma\in A\leftrightarrow \sigma:n\to\omega),\\
H(W,a,b):\equiv{}&\forall n\in\omega\;\exists k\in\omega\;\exists A\;[\\
&L(W,n,A)\land\mathrm{Count}(k,A)\land\mathrm{DB}(n,k,a,b)].
\end{aligned}$$
For $W=W_T$, the bounded predicate $L$ recognizes exactly $A=W_{T,n}$. The unrestricted quantifiers
in $H$ range over the model when $H$ is interpreted there.

\begin{corollary*}[\termdefine{Closed measure bounds from internal finite tests}]
Let $T\IncludedIn\finseq{2}$ be downward closed with $W_T\in M$, and let $a,b\in\omega$ with $b>0$. Then
$$M\models H(W_T,a,b)\quad\Longleftrightarrow\quad\frac ab\le\mu(\TreeBody{T}),$$
where the right-hand side uses the entire external closed set.
\end{corollary*}

\begin{proof}[Proof]
If $M\models H(W_T,a,b)$, the internal level set is $W_{T,n}$ and its recognized count is $\Card{T_n}$.
The preceding proposition therefore gives $a/b\le d_n(T)$ for every actual $n$.
Conversely, if these inequalities hold, use the internal set $W_{T,n}$, the finite ordinal $\Card{T_n}$,
and a finite bijection witnessing its cardinality. The earlier lemmas place these witnesses in $M$ and
verify the corresponding dyadic comparison there. Thus $M\models H(W_T,a,b)$.
The closed lower-bound criterion of §{sec:coded-measure-bounds} identifies the inequalities with
$a/b\le\mu(\TreeBody{T})$. No graph collecting all finite counts is assumed: the formula has the
quantifier order $\forall n\,\exists k\,\exists A$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
任意の語族の開集合・グラフ符号の定義はopenFromWords/wordTreeSetに対応済み。未リンク部分はモデル仮定と、入力族にprefix
closureを課さないという定義域の説明。)
--> Assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, and Separation.<!--
formalization: skip-end
-->
Encode binary words as finite graphs with values in $2=\{0,1\}$, and write
$$W_O:=\{e(s):s\in O\},\qquad U(O):=\bigcup_{s\in O}\cyl{s}$$
for a family $O\IncludedIn\finseq{2}$. An internal open code means that $W_O\in M$.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
任意の語族の開集合・グラフ符号の定義はopenFromWords/wordTreeSetに対応済み。未リンク部分はモデル仮定と、入力族にprefix
closureを課さないという定義域の説明。)
--> The family $O$ need not be prefix closed.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Internal binary words}]
The set $F_2:=\{e(s):s\in\finseq{2}\}$ belongs to $M$.
\end{lemma*}

\begin{proof}[Proof]
From the internal set $F$ of finite natural-number word graphs, separate the graphs satisfying
$$\exists n\in\omega\;(\sigma:n\to2).$$
This bounded predicate recognizes exactly the binary words: each value is $0$ or $1$, and conversely every
binary word has such a graph. Apply the bounded-recognition lemma of §{sec:internal-finite-tests}.
\end{proof}

\begin{proposition*}[\termdefine{Internal avoidance trees}]
For $O\IncludedIn\finseq{2}$, define
$$D(O):=\{s\in\finseq{2}:\forall t\in O\;\neg(t\prefixOf s)\}.$$
Then $D(O)$ is downward closed and $\TreeBody{D(O)}=\SetDifference{\CantorSpace}{U(O)}$.
If $W_O\in M$, then $W_{D(O)}\in M$.
\end{proposition*}

\begin{proof}[Proof]
A prefix of a word avoiding every member of $O$ also avoids every member of $O$.
A branch lies in $\TreeBody{D(O)}$ exactly when none of its prefixes lies in $O$, which is equivalent to
belonging to no cylinder in the union defining $U(O)$. For the internal construction, separate from $F_2$
the graphs $\sigma$ satisfying
$$\forall \tau\in W_O\;\neg(\tau\IncludedIn \sigma).$$
Graph inclusion is the prefix relation, so the same bounded-recognition lemma gives the required node set.
This also covers $O=\emptyset$ and families containing the empty word.
\end{proof}

\begin{theorem*}[\termdefine{Internal clopen approximations}]
Let $T\IncludedIn\finseq{2}$ be downward closed with $W_T\in M$. For $n\in\omega$, put
$$S_n:=D(T\cap\funcspace{n}{2}).$$
Then $S_n$ is downward closed, $W_{S_n}\in M$, and
$$\TreeBody{S_n}=\SetDifference{\CantorSpace}{C_n(T)}
\IncludedIn\SetDifference{\CantorSpace}{\TreeBody{T}}.$$
Each $\TreeBody{S_n}$ is clopen, and
$$\mu\bigl(\SetDifference{(\SetDifference{\CantorSpace}{\TreeBody{T}})}{\TreeBody{S_n}}\bigr)
=d_n(T)-\mu(\TreeBody{T})\longrightarrow0.$$
Consequently, for every internal open code $W_O$ and every real $\varepsilon>0$, there is a downward-closed
binary tree $S$ with $W_S\in M$ such that $\TreeBody{S}$ is clopen and
$$\TreeBody{S}\IncludedIn U(O),\qquad
\mu(\SetDifference{U(O)}{\TreeBody{S}})<\varepsilon.$$
\end{theorem*}

\begin{proof}[Proof]
§{sec:internal-finite-measure-bounds} constructs the entire finite-level node set inside $M$.
Apply the avoidance-tree proposition to that set. A branch survives precisely when its length-$n$ prefix is
absent from $T$, proving the displayed identity. The finite union $C_n(T)$ is clopen.
It contains $\TreeBody{T}$, so the discarded part has measure $d_n(T)-\mu(\TreeBody{T})$.
By §{sec:coded-measure-bounds}, this difference tends to $0$.
For the last assertion, take $T=D(O)$ and choose a finite stage at which this
error is below $\varepsilon$. Every stage already has its code in $M$; no external regularity witness is
assumed to belong to $M$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
収束からの段階選択はexists_internal_openCode_approximationの存在証明であり、
計算可能な収束率を主張しないという注意と後続構成への案内。新たな計算可能性定理を提示していない。)
--> The stage chosen by convergence is an existence assertion; no computable rate of convergence is claimed.
This proves the open-code base case. §{sec:internal-finite-measure-bounds} establishes closure under
complementation and constructs the choice graphs and code operations needed for countable unions.
§{sec:internal-approximation-errors} formulates the admissibility of these codes, and
§{sec:internal-borel-measure-identification} proves agreement with the model's measure.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
可算族では全グラフの内部所属が必要という適用条件とモデル公理の再掲。直後のinternal_definable_choiceの前提を説明する導入で、
内部所属の反例を証明する段落ではない。)
--> For countable unions, individual internal codes are not enough: the graph of the chosen family must belong
to the model. The following construction supplies such a graph from an internally verified existence
statement. Assume throughout this section that $M$ is transitive and satisfies Infinity, Pairing, Union,
Power Set, Separation, Replacement, and Choice.<!--
formalization: skip-end
-->

\begin{theorem*}[\termdefine{Internal definable choice}]
Let $\mathcal D\in M$, and let $\varphi(\alpha,\beta,\vec p)$ be a first-order formula with parameters $\vec p$ in $M$.
If
$$M\models\forall \alpha\in \mathcal D\;\exists \beta\;\varphi(\alpha,\beta,\vec p),$$
then there are $\mathcal W,f\in M$ such that $f:\mathcal D\to \mathcal W$ and
$$M\models\varphi(\alpha,f(\alpha),\vec p)\qquad(\alpha\in \mathcal D).$$
No absoluteness assumption on $\varphi$ is required.
\end{theorem*}

\begin{proof}[Proof]
The internal Collection theorem gives $\mathcal W\in M$ containing a suitable witness for every input.
For each $\alpha\in \mathcal D$, internal Separation gives the nonempty set
$$R_\alpha:=\{\beta\in \mathcal W:M\models\varphi(\alpha,\beta,\vec p)\}\in M.$$
The first-order formula
$$\psi(\alpha,r):\equiv\forall \beta\;
\bigl(\beta\in r\longleftrightarrow \beta\in \mathcal W\land\varphi(\alpha,\beta,\vec p)\bigr)$$
defines this set uniquely inside $M$, by Extensionality. Replacement and the graph-construction lemma give
$$\mathcal R:=\{R_\alpha:\alpha\in \mathcal D\}\in M,\qquad
 g:=\{\Pair{\alpha}{R_\alpha}:\alpha\in \mathcal D\}\in M.$$
Choice inside $M$ gives a graph $c:\mathcal R\to\bigcup\mathcal R$ in $M$ with $c(r)\in r$.
The formula
$$\theta(\alpha,\beta):\equiv\exists r\;
\bigl(\Pair{\alpha}{r}\in g\land\Pair{r}{\beta}\in c\bigr)$$
defines a unique value for each input. Applying the same graph-construction lemma gives the entire graph
$f\in M$. Its value belongs to $R_\alpha$, hence to $\mathcal W$, and satisfies the original formula inside $M$.
If a witness bound $\mathcal W\in M$ is already available, the Collection step is unnecessary.
\end{proof}

Taking $\mathcal D=\omega$ gives a whole internal sequence of witnesses. <!--
formalization: skip-begin (引用・背景説明・読書案内:
omega上の全選択列はinternal_countable_choiceへ接続済み。残る文はChoiceによる内部選択と計算可能な選択を区別し、
内部の式とtotalityを先に必要とするという適用上の注意。)
--> This uses the model's Choice axiom and does
not assert computable selection. In particular, one must first express the admissibility condition by an
internal formula and prove its internal totality; externally choosing one code for each index does not meet
these requirements.<!--
formalization: skip-end
-->

\begin{proposition*}[\termdefine{Operations on internal approximation codes}]
If $W_T\in M$, then the missing-word code $W_{\SetDifference{\finseq{2}}{T}}$ belongs to $M$, and
$$U(\SetDifference{\finseq{2}}{T})=\SetDifference{\CantorSpace}{\TreeBody{T}}.$$
For a sequence of open word codes $O_n$, suppose that
$$G:=\{\Pair{n}{W_{O_n}}:n\in\omega\}\in M.$$
Then
$$\begin{aligned}
W_{\bigcup_n O_n}&=\bigcup\GraphRange{G}\in M,\\
U(\bigcup_n O_n)&=\bigcup_n U(O_n).
\end{aligned}$$
Finally, for a finite index set $I$ and downward-closed trees $T_i$ with $W_{T_i}\in M$ for $i\in I$,
$$W_{\bigcup_{i\in I}T_i}\in M,\qquad
\TreeBody{\bigcup_{i\in I}T_i}=\bigcup_{i\in I}\TreeBody{T_i}.$$
\end{proposition*}

\begin{proof}[Proof]
For the first assertion, separate from $F_2$ the graphs absent from $W_T$. A point is outside
$\TreeBody{T}$ exactly when one of its prefixes is missing from $T$.
For the second assertion, internal range construction and Union give the displayed node set; taking the
union of its cylinders gives the required open union. The hypothesis is on the entire graph $G$.
For the last assertion, finite unions of node sets belong to $M$ by Pairing and Union.
For two downward-closed trees, if a branch through their union leaves the first tree at some length, then
all its longer prefixes must belong to the second tree. Downward closure puts all shorter prefixes there
as well. This proves the body identity for two trees; finite induction proves the stated formula.
\end{proof}

Let $\mathcal R_M$ be the class of sets $A\IncludedIn\CantorSpace$ such that, for every real
$\varepsilon>0$, there are a downward-closed binary tree $T$ and a word family $O$ satisfying
$$\begin{gathered}
W_T,W_O\in M,\qquad \TreeBody{T}\IncludedIn A\IncludedIn U(O),\\
\mu(\SetDifference{U(O)}{\TreeBody{T}})<\varepsilon.
\end{gathered}$$
This is an external approximation property; it is not yet a definition of an internal predicate.

\begin{proposition*}[\termdefine{Internal approximations under complementation}]
Every open set with an internal word code belongs to $\mathcal R_M$.
If $A\in\mathcal R_M$, then $\SetDifference{\CantorSpace}{A}\in\mathcal R_M$.
\end{proposition*}

\begin{proof}[Proof]
The open case follows from §{sec:internal-finite-measure-bounds}, retaining the original open code as the
outer approximant. For complementation, replace the inner tree $T$ and outer word family $O$ by
$$T':=D(O),\qquad O':=\SetDifference{\finseq{2}}{T}.$$
Both codes are internal by the preceding constructions, and
$$\TreeBody{T'}=U(O)^c\IncludedIn A^c\IncludedIn\TreeBody{T}^c=U(O').$$
The error set is unchanged:
$$\SetDifference{U(O')}{\TreeBody{T'}}
=\SetDifference{\TreeBody{T}^c}{U(O)^c}
=\SetDifference{U(O)}{\TreeBody{T}}.$$
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
近似のadmissibility、子族のグラフ、有限tail評価、実数コード、測度との一致を扱う後続節の参照一覧。各構成は参照先の対応対象で、
このロードマップを追加の証明としない。)
--> §{sec:internal-approximation-errors} turns membership in $\mathcal R_M$ into internal witness conditions, constructs
the child-indexed input graphs, and selects a whole internal family with external inclusion bounds and summable
errors. It also extracts the component and open-code graphs and constructs the combined approximation codes
internally.
§{sec:internal-approximation-errors} applies the finite-tail measure estimate and completes the
well-founded induction. §{sec:internal-borel-measure-cut} then identifies the internally tested
rational lower cut and proves that it determines the external measure.
§{sec:internal-borel-measure-cut} constructs the entire real code inside the model.
§{sec:internal-borel-measure-identification} identifies it with the model's usual probability measure.<!--
formalization: skip-end
-->

### Approximation Codes and Borel Induction {#sec:internal-approximation-errors}

\begin{mathmeta}
  \vars{N,a,b,d,h,j,k,n}{Nat}
  \vars{c,\eta_*}{Fun(Seq(Nat),Nat)}
  \vars{\sigma,\tau,\alpha,\beta}{Set}
  \vars{s,t,w}{Seq(Nat)}
  \vars{i}{Fun(Name,Name)}
\end{mathmeta}

Continue to assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, and Separation.
For two downward-closed binary trees $T,S$ with $W_T,W_S\in M$, put
$$\mathcal F=\TreeBody{T},\qquad \mathcal K=\TreeBody{S}.$$
To describe a small error outside $\mathcal F\cup \mathcal K$, retain the internal addition graph $G_+$ as well as
$\omega,G_\times,P_2$ as parameters and define
$$\begin{aligned}
E(W,V,h,d):\equiv{}&\exists a,b\in\omega\;[b>0\land bd<ad+hb\\
&{}\land\exists Z\;(Z=W\cup V\land H(Z,a,b))].
\end{aligned}$$
The arithmetic clause abbreviates a bounded formula: read $bd,ad,hb$ from $G_\times$, read the sum of the
last two values from $G_+$, and compare the resulting finite ordinals by membership. Likewise, $b>0$
means that the finite ordinal $b$ is nonempty. The union equality is the ordinary membership-language
formula. Thus $E$ is a first-order formula with all its arithmetic parameters specified.

\begin{proposition*}[\termdefine{Internal tests for approximation errors}]
For $h,d\in\omega$ with $d>0$ and $h\le d$,
$$M\models E(W_T,W_S,h,d)\quad\Longleftrightarrow\quad
\mu(\SetDifference{\CantorSpace}{\mathcal F\cup \mathcal K})<\frac hd.$$
\end{proposition*}

\begin{proof}[Proof]
The union code $Z=W_T\cup W_S=W_{T\cup S}$ belongs to $M$ by
§{sec:internal-finite-measure-bounds}, and $\TreeBody{T\cup S}=\mathcal F\cup \mathcal K$.
The criterion for $H$ gives
$$M\models H(Z,a,b)\quad\Longleftrightarrow\quad
\mu(\SetDifference{\CantorSpace}{\mathcal F\cup \mathcal K})\le 1-\frac ab.$$
For positive $b,d$, the finite arithmetic clause is equivalent to
$$bd<ad+hb\quad\Longleftrightarrow\quad 1-\frac hd<\frac ab.$$
Together these two inequalities imply the required strict error bound.

Conversely, write $r=\mu(\SetDifference{\CantorSpace}{\mathcal F\cup \mathcal K})$ and suppose $r<h/d$.
Since $h/d\le1$, rational density supplies a nonnegative rational $a/b$ with $b>0$ such that
$$1-\frac hd<\frac ab<1-r.$$
Its numerator and denominator are actual natural numbers and hence belong to $M$. The internal union
code and the criterion for $H$ supply the remaining witnesses. The bounded arithmetic test has the same
meaning in $M$, so these witnesses establish $M\models E(W_T,W_S,h,d)$.
\end{proof}

For an inner tree $T$ and an outer open code $O$, take $S=D(O)$ from
§{sec:internal-finite-measure-bounds}. The exact identity
$$\SetDifference{\CantorSpace}{\TreeBody{T}\cup\TreeBody{D(O)}}
=\SetDifference{U(O)}{\TreeBody{T}}$$
shows that the proposition tests the original approximation error. <!--
formalization: skip-begin (引用・背景説明・読書案内:
開集合との差を2閉集合の補集合に直す恒等式はcomplement_treeBody_union_avoidWordsに対応済み。
残りは許容誤差を1以下に取れるという適用範囲と、数値テストだけでは符号の存在・包含まで得られないという注意。)
--> The bound $h/d\le1$ is sufficient for
arbitrarily accurate approximations. This test uses the full external closed sets; it never measures the
set of points that happen to belong to $M$. It does not by itself assert that the required inner and outer
codes exist, or that they satisfy the Borel inclusion conditions.<!--
formalization: skip-end
-->

Assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation, Replacement,
and Choice. Fix a valid Borel expression $c$ whose label graph belongs to $M$. Let
$$B=\BorelInterpretation{c}{M},\qquad A=i^{-1}(B_c),$$
where $B_c$ uses the standard Baire cylinders and $i:\CantorSpace\to\BaireSpace$ is the inclusion.
The internal interpretation $B$, internal Baire space $X_M$, finite-word set $F$, and binary-word set $F_2$
are all elements of $M$ by the preceding constructions. Retain these sets and the arithmetic graphs
from §{sec:internal-approximation-errors} as parameters.

Define the following bounded predicates on proposed tree codes and point graphs:
$$\begin{aligned}
\mathrm{Tree}(W):\equiv{}&W\IncludedIn F_2\land\forall \sigma\in W\;\forall \tau\in F_2\;[\\
&\tau\IncludedIn \sigma\longrightarrow \tau\in W],\\
\mathrm{Br}(W,g):\equiv{}&\forall \sigma\in F\;(\sigma\IncludedIn g\longrightarrow \sigma\in W),\\
\mathrm{Inc}(B,W,V):\equiv{}&\forall g\in X_M\;[\\
&(\mathrm{Br}(W,g)\longrightarrow g\in B)\\
&{}\land(\mathrm{Br}(V,g)\longrightarrow g\notin B)].
\end{aligned}$$
Graph inclusion between finite words is the prefix relation. Consequently, $\mathrm{Tree}(W)$ holds
exactly when $W=W_T$ for a downward-closed binary tree $T$; every subset of $F_2$ codes the corresponding
family of binary words. For a point graph $g_x$, the condition $\mathrm{Br}(W_T,g_x)$ says exactly that
all finite prefixes of $x$ lie in $T$. We use the Baire point graphs here, identifying a binary tree with
its natural-number copy.

Combine these conditions with the error test:
$$\begin{aligned}
\mathrm{Adm}(B,W,V,a,b):\equiv{}&\mathrm{Tree}(W)\land\mathrm{Tree}(V)\\
&{}\land\mathrm{Inc}(B,W,V)\land E(W,V,a,b).
\end{aligned}$$
Here the second tree describes the complement of the outer open approximant.

\begin{theorem*}[\termdefine{Internal admissibility of approximations}]
Let $T,S$ be binary word families with $W_T,W_S\in M$, and let $a,b\in\omega$ satisfy $b>0$ and $a\le b$.
Then $M\models\mathrm{Adm}(B,W_T,W_S,a,b)$ holds exactly when $T,S$ are downward closed and
$$\begin{gathered}
\TreeBody{T}\IncludedIn A\IncludedIn\TreeBody{S}^c,\\
\mu(\SetDifference{\CantorSpace}{\TreeBody{T}\cup\TreeBody{S}})<\frac ab.
\end{gathered}$$
These inclusions and the measure refer to all external binary points.
\end{theorem*}

\begin{proof}[Proof]
The uniform interpretation principle identifies the two internal tree tests with actual downward closure.
It identifies the internal inclusion test with its assertions about all point graphs in $X_M$.
Agreement of the internal Borel interpretation with $B_c$ on those points turns these assertions into
closed inclusion and closed disjointness on internal points. Both transfer to external points by
§{sec:internal-closed-inclusions}. Restricting to binary points gives the two stated inclusions.
Conversely, the external inclusions imply the assertions on internal points, so the bounded test holds
in $M$. Finally, §{sec:internal-approximation-errors} identifies the internal error test with the displayed
strict measure bound in both directions.
\end{proof}

\begin{lemma*}[\termdefine{Internal totality from coded approximations}]
If $A\in\mathcal R_M$, then for every $a,b\in\omega$ with $0<a\le b$ there exist $W,V\in M$ such that
$$M\models\mathrm{Adm}(B,W,V,a,b).$$
\end{lemma*}

\begin{proof}[Proof]
Apply the definition of $\mathcal R_M$ with error $a/b$. It supplies an inner tree $T$ and an outer open
code $O$, both internal. Put $S=D(O)$. Then $W_S\in M$ and
$$\TreeBody{T}\IncludedIn A\IncludedIn\TreeBody{S}^c,
\qquad\SetDifference{\CantorSpace}{\TreeBody{T}\cup\TreeBody{S}}
=\SetDifference{U(O)}{\TreeBody{T}}.$$
The admissibility theorem therefore supplies the required internal witnesses $W_T,W_S$.
\end{proof}

\begin{corollary*}[\termdefine{Internal admissible approximations for open codes}]
If $A=U(O)$ with $W_O\in M$, then for every $a,b\in\omega$ with $0<a\le b$ there exist $W,V\in M$ such that
$$M\models\mathrm{Adm}(B,W,V,a,b).$$
\end{corollary*}

\begin{proof}[Proof]
The open case of §{sec:internal-finite-measure-bounds} gives $A\in\mathcal R_M$. Apply the lemma.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前の内部totality補題を可算選択へ適用する案内。全入力グラフが内部にあることを改めて要求しており、
外部の点ごとの選択から内部列を得る追加原理を主張しない。)
--> For a family of sets in $\mathcal R_M$, the lemma supplies internal witnesses at each index.
§{sec:internal-approximation-errors} collects those witnesses into a single internal graph
when the whole input family is internally coded.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
全ノードの内部解釈族を扱うための入力公理・パラメータとB_sの局所記号を導入する文。
実際の族構成は直後のinternalInterpretationFamily_memで別に対応済み。)
--> We must code the entire input family before using internal choice. First consider the interpretations
at all nodes of one fixed Borel expression. Let $c$ have a well-founded child relation, and suppose its
label graph and the graph of the cylinder enumeration belong to $M$. Write $B_s$ for its internal Borel
interpretation at the node $s$.<!--
formalization: skip-end
-->

\begin{proposition*}[\termdefine{Internal family of node interpretations}]
Under the transitive-model hypotheses of §{sec:internal-approximation-errors},
$$\mathcal I_c:=\{\Pair{e(s)}{B_s}:s\in\finseq{\omega}\}\in M.$$
Absent nodes are included, with their empty interpretations.
\end{proposition*}

\begin{proof}[Proof]
Use the membership formula $\Phi$ of §{sec:internal-borel-sets}. With its label, basis, and other fixed
parameters suppressed, the set-valued fiber at $s$ is defined by
$$\forall g\;[g\in D\longleftrightarrow g\in X_M\land\Phi(e(s),g)].$$
Inside $M$, this formula holds exactly when $D=B_s$. Indeed, for a graph in $X_M$, the interpretation theorem
identifies $\Phi$ with membership in $B_s$; outside $X_M$, both descriptions exclude the graph.
Each $B_s$ belongs to $M$ by that theorem, and Extensionality gives uniqueness. The graph-collection lemma
of §{sec:internal-model-closure}, applied on the internal finite-word set $F$, now puts $\mathcal I_c$ in $M$.
This uses Replacement for the set-valued definition, not just pointwise membership of its values in $M$.
\end{proof}

For countable selection, fix all common parameters of $\mathrm{Adm}$. Let $B_n$ be the internal Borel sets
in question, and let $a_n,b_n\in\omega$ satisfy $0<a_n\le b_n$. The input consists of the three complete graphs
$$\begin{gathered}
G_B:=\{\Pair{n}{B_n}:n\in\omega\},\\
G_a:=\{\Pair{n}{a_n}:n\in\omega\},\qquad
G_b:=\{\Pair{n}{b_n}:n\in\omega\}.
\end{gathered}$$
We require $G_B,G_a,G_b\in M$.

\begin{theorem*}[\termdefine{Internal families of admissible approximations}]
Suppose that for every $n\in\omega$ there are $W,V\in M$ with
$$M\models\mathrm{Adm}(B_n,W,V,a_n,b_n).$$
Then there are choices $W_n,V_n\in M$ satisfying these same conditions for all $n$, whose entire paired graph
belongs to $M$:
$$\mathcal H:=\{\Pair{n}{\Pair{W_n}{V_n}}:n\in\omega\}\in M.$$
\end{theorem*}

\begin{proof}[Proof]
Keep the common parameters and $G_B,G_a,G_b$ fixed. Define a first-order predicate on an input $n$ and
an output $z$ by
$$\begin{aligned}
\Psi(n,z):\equiv{}&\exists B,a,b,W,V\;[\\
&\Pair{n}{B}\in G_B\land\Pair{n}{a}\in G_a\\
&{}\land\Pair{n}{b}\in G_b\land z=\Pair{W}{V}\\
&{}\land\mathrm{Adm}(B,W,V,a,b)].
\end{aligned}$$
The lookup graphs force the first three values to be $B_n,a_n,b_n$. The assumed witnesses and Pairing
show that $\Psi$ is total internally on $\omega$. Apply internal definable choice from
§{sec:internal-finite-measure-bounds}. It gives an internal function graph on $\omega$ whose value at $n$
is a pair satisfying $\Psi$.

Reindex this function by the actual natural numbers. Its value at each index is unique, so the resulting
sequence has exactly the same graph. Unpack each chosen value as $\Pair{W_n}{V_n}$.
Ordered-pair injectivity and uniqueness of the input lookups give the required admissibility conditions.
The paired graph $\mathcal H$ is still the graph supplied by internal choice; it is not a newly chosen external
sequence of unrelated internal values.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
既に証明した内部totality、全族選択、admissibilityの各定理を適用する順序と、計算可能な選択ではないという注意。
新しい選択原理を追加していない。)
--> When each $B_n$ represents a set in $\mathcal R_M$, the internal-totality lemma of
§{sec:internal-approximation-errors} supplies the hypothesis. The admissibility theorem then turns
all selected witnesses into genuine external two-sided approximations with their specified errors.
No computable selection of the witnesses is asserted.<!--
formalization: skip-end
-->

\begin{proposition*}[\termdefine{Re-rooting inside the model}]
Let $c$ be valid with its label graph in $M$, using the standard cylinder enumeration whose first
cylinder is the whole Baire space. Let $A_s$ be its external binary interpretation at a finite node $s$,
and retain $B_s$ for its internal Baire interpretation. There is a valid code $\eta_s$ with internal label graph
such that
$$\BorelInterpretation{\eta_s}{M}=B_s,\qquad i^{-1}(\BorelValue{\eta_s})=A_s.$$
This includes absent nodes.
\end{proposition*}

\begin{proof}[Proof]
For a present node, take $\eta_s(t)=c(s\concat t)$. Its child relation maps into the child relation of $c$
by prepending $s$, so it is well-founded; the local validity clauses are inherited. Restricting the
set evaluation of $c$ to these addresses satisfies the evaluation equations for $\eta_s$. Uniqueness of
well-founded evaluation gives the asserted equality at the root, and restricting to old points gives
the internal equality.

To construct the whole label graph internally, first prepend just one entry $a$. With $K$ from
§{sec:internal-list-coding}, the bounded condition
$$\exists \tau\in F\;[K(a,\sigma,\tau)\land\Pair{\tau}{j}\in\ell]$$
recognizes $j=c(a::t)$ when $\sigma=e(t)$. The shared interpretation and graph-collection principles put this
label graph in $M$. Repeating the operation along the finitely many entries of $s$ gives the graph of
$\eta_s$. This proves internality of the entire graph, rather than just its individual values.

If $c(s)=0$, its evaluation is empty. Use the fixed valid empty code
$$\eta_\varnothing:=\BorelComplementCode{\BorelLeafCode{0}}.$$
Its labels are $2$ at $[]$, $3$ at $[0]$, and $0$ elsewhere. Equality with these two finite words gives a
bounded definition of every label, so the same graph-collection principle puts its label graph in $M$.
Its root evaluates to the complement of the whole space. Thus $\eta_s=\eta_\varnothing$ has both required
interpretations in this case as well.
\end{proof}

\begin{theorem*}[\termdefine{Admissibility at every node}]
Let $c,s,A_s,B_s$ be as above, and let $W,V\in M$ and $a,b\in\omega$ with $b>0$ and $a\le b$.
Then $M\models\mathrm{Adm}(B_s,W,V,a,b)$ holds exactly when $W=W_T$ and $V=W_S$ for downward-closed
binary trees $T,S$ satisfying
$$\begin{gathered}
\TreeBody{T}\IncludedIn A_s\IncludedIn\TreeBody{S}^c,\\
\mu(\SetDifference{\CantorSpace}{\TreeBody{T}\cup\TreeBody{S}})<\frac ab.
\end{gathered}$$
If $A_s\in\mathcal R_M$ and $0<a\le b$, such internal witnesses $W,V$ exist.
\end{theorem*}

\begin{proof}[Proof]
The bounded tree tests decode each accepted set as the full code of a downward-closed binary tree.
Apply the root admissibility theorem to $\eta_s$ from the proposition. Its internal and external
interpretations are exactly $B_s$ and $A_s$, while all arithmetic, word, and point parameters remain
the same. This proves the equivalence, including for absent nodes. The internal-totality lemma of
§{sec:internal-approximation-errors}, applied to the same code, proves the final assertion.
\end{proof}

\begin{proposition*}[\termdefine{Internal inputs at a union node}]
Keep the hypotheses and notation for $\mathcal I_c$. For a finite node $s$ and $k\in\omega$, put
$$B_n=B_{s\concat\SingletonSeq{n}},\qquad a_n=1,\qquad b_n=2^{k+2+n}.$$
Then all three input graphs $G_B,G_a,G_b$ belong to $M$. The corresponding errors satisfy
$$\delta_n:=\frac{a_n}{b_n}=\frac{1}{2^{k+2+n}}>0,
\qquad\sum_{n=0}^{\infty}\delta_n=\frac{1}{2^{k+1}}.$$
Thus the individual errors use half of the target $2^{-k}$.
\end{proposition*}

\begin{proof}[Proof]
Let $\Gamma$ be the internal graph of one-entry extension from §{sec:internal-finite-tests}. The value
$B_{s\concat\SingletonSeq{n}}$ is recognized by the bounded condition
$$\exists \tau\in F\;[\Pair{\Pair{e(s)}{n}}{\tau}\in \Gamma
\land\Pair{\tau}{D}\in\mathcal I_c].$$
The first lookup forces $\tau=e(s\concat\SingletonSeq{n})$ and the second forces $D=B_n$.
The uniform interpretation principle and graph collection therefore give $G_B\in M$.
This argument uses the entire graph $\mathcal I_c$ as a parameter.

The constant value $a_n=1$ is recognized by equality. Write $G_+$ for the internal addition graph and
$P_2$ for the power graph of §{sec:internal-finite-measure-bounds}. The value $b_n$ is recognized by
$$\exists j\in\omega\;[\Pair{\Pair{k+2}{n}}{j}\in G_+
\land\Pair{j}{d}\in P_2].$$
Its unique value is $d=2^{k+2+n}$. Apply the same graph-collection principle to each of these two
bounded definitions. Reindexing the collected graphs by actual natural numbers preserves the graphs,
so $G_a,G_b\in M$. Finally, the geometric-series identity gives the asserted sum of the errors.
\end{proof}

\begin{theorem*}[\termdefine{Internally selected child approximations}]
Let $c$ be valid with its label graph in $M$, fix a node $s$ and $k\in\omega$, and put
$A_n=A_{s\concat\SingletonSeq{n}}$. Suppose $A_n\in\mathcal R_M$ for every present child.
Then there are downward-closed binary trees $T_n,S_n$, with $W_{T_n},W_{S_n}\in M$, such that
$$\begin{gathered}
\{\Pair{n}{\Pair{W_{T_n}}{W_{S_n}}}:n\in\omega\}\in M,\\
\TreeBody{T_n}\IncludedIn A_n\IncludedIn\TreeBody{S_n}^c,\\
\mu(\SetDifference{\CantorSpace}{\TreeBody{T_n}\cup\TreeBody{S_n}})<\frac{1}{2^{k+2+n}}.
\end{gathered}$$
The inclusions and measure bounds hold on all external binary points.
\end{theorem*}

\begin{proof}[Proof]
Absent children have empty interpretation, which belongs to $\mathcal R_M$ by the internal open-code
construction applied to the empty code. Thus the approximation hypothesis holds for every child.
Nodewise internal totality supplies witnesses for the errors $1/2^{k+2+n}$. The preceding input-graph
proposition verifies the hypotheses of internal family selection, giving an internal graph of pairs
$\Pair{W_n}{V_n}$ satisfying the admissibility formula at all children.

The nodewise admissibility theorem decodes these sets as $W_n=W_{T_n}$ and $V_n=W_{S_n}$ and proves the
external inclusions and error bounds. These equalities preserve the entire paired graph, so decoding
does not replace the internally selected family by an unrelated external choice. No computable
selection of the approximations is asserted.
\end{proof}

\begin{proposition*}[\termdefine{Operations on entire approximation families}]
Retain the transitive-model hypotheses above. Suppose $T_n,S_n\IncludedIn\finseq{2}$ have internal
codes and their entire paired graph
$$\mathcal H=\{\Pair{n}{\Pair{W_{T_n}}{W_{S_n}}}:n\in\omega\}$$
belongs to $M$. Put $O_n=\SetDifference{\finseq{2}}{S_n}$. Then
$$\begin{gathered}
G_T:=\{\Pair{n}{W_{T_n}}:n\in\omega\}\in M,\\
G_S:=\{\Pair{n}{W_{S_n}}:n\in\omega\}\in M,\\
G_O:=\{\Pair{n}{W_{O_n}}:n\in\omega\}\in M.
\end{gathered}$$
Consequently, the combined codes are internal:
$$W_{\bigcup_n O_n}\in M,\qquad W_{\bigcup_{n\le N}T_n}\in M\quad(N\in\omega).$$
\end{proposition*}

\begin{proof}[Proof]
Write $R=\operatorname{ran}(\mathcal H)$ and $Q=\bigcup\bigcup R$. These sets belong to $M$ by the range and
union operations. Both components of each pair in $R$ lie in $Q$. For $n\in\omega$, the bounded condition
$$\exists z\in R\;\exists \alpha\in Q\;\exists \beta\in Q\;
[\Pair{n}{z}\in \mathcal H\land z=\Pair{\alpha}{\beta}\land y=\alpha]$$
holds exactly when $y=W_{T_n}$. Replacing $y=\alpha$ by $y=\beta$ recognizes $W_{S_n}$.
Apply the shared bounded-interpretation and graph-collection principles to obtain $G_T,G_S\in M$.

For the third graph, use the internal set $F_2$ of binary-word graphs and $R_S=\operatorname{ran}(G_S)$.
The output $D$ at $n$ is characterized by
$$\begin{gathered}
\exists \beta\in R_S\;[\Pair{n}{\beta}\in G_S
\land D\IncludedIn F_2\\
{}\land\forall \sigma\in F_2\;(\sigma\in D\longleftrightarrow \sigma\notin \beta)].
\end{gathered}$$
Its unique value is $D=\SetDifference{F_2}{W_{S_n}}=W_{O_n}$, which is internal by Separation.
The same interpretation and graph-collection principles give $G_O\in M$.
Now apply the open-union and finite-tree-union constructions of §{sec:internal-finite-measure-bounds}.
They give the two combined codes in the statement.
\end{proof}

For the selected downward-closed trees, these codes have the external meanings
$$\begin{gathered}
U\!\left(\bigcup_n O_n\right)=\bigcup_n\TreeBody{S_n}^c,\\
\TreeBody{\bigcup_{n\le N}T_n}=\bigcup_{n\le N}\TreeBody{T_n}.
\end{gathered}$$
Both identities were proved in §{sec:internal-finite-measure-bounds}. The combined internal codes
are therefore ready for the finite-tail estimate in §{sec:internal-approximation-errors}.

Retain the transitive-model hypotheses of §{sec:internal-approximation-errors}.
For a valid Borel expression $c$ whose label graph belongs to $M$, write $A_s$ for its external binary
interpretation at $s$. Every $A_s$ is Borel: well-founded evaluation preserves Borel measurability,
and the inclusion of Cantor space into Baire space is continuous.

\begin{theorem*}[\termdefine{Internal approximation at a countable union}]
Fix a node $s$, put $A_n=A_{s\concat\SingletonSeq{n}}$, and suppose $A_n\in\mathcal R_M$ for every present
child. Then $\bigcup_n A_n\in\mathcal R_M$.
\end{theorem*}

\begin{proof}[Proof]
Let $\varepsilon>0$. Choose $k\in\omega$ with $2^{-k}<\varepsilon$. The internal selection theorem of
§{sec:internal-approximation-errors} supplies downward-closed trees $T_n,S_n$ with a single internal
paired graph. Put
$$\begin{gathered}
\mathcal F_n=\TreeBody{T_n},\qquad O_n=\SetDifference{\finseq{2}}{S_n},\qquad \mathcal U_n=U(O_n)=\TreeBody{S_n}^c,\\
\mathcal F_n\IncludedIn A_n\IncludedIn \mathcal U_n,\qquad
\mu(\SetDifference{\mathcal U_n}{\mathcal F_n})<\delta_n:=\frac{1}{2^{k+2+n}}.
\end{gathered}$$
Absent children are included with empty interpretation, as in that theorem. The sum of the errors is
at most $\sum_n\delta_n=2^{-(k+1)}$.

Write $A=\bigcup_n A_n$ and $A_N^*=\bigcup_{n\le N}A_n$. Since $\mu$ is finite and all the sets $A_n$
are measurable, the finite-tail estimate of §{sec:borel-measures-radon} gives $N\in\omega$ with
$$\mu(\SetDifference{A}{A_N^*})<2^{-(k+1)}.$$
Use the combined codes
$$T=\bigcup_{n\le N}T_n,\qquad O=\bigcup_n O_n.$$
The family-operation proposition gives $W_T,W_O\in M$. The tree $T$ is downward closed, and its body is
$\mathcal F:=\bigcup_{n\le N}\mathcal F_n$; the open set coded by $O$ is $\mathcal U:=\bigcup_n \mathcal U_n$.
Consequently $\mathcal F\IncludedIn A\IncludedIn \mathcal U$.

Apply the union-gap estimate proved in §{sec:borel-measures-radon}:
$$\begin{aligned}
\mu(\SetDifference{\mathcal U}{\mathcal F})
&\le\sum_{n=0}^{\infty}\mu(\SetDifference{\mathcal U_n}{\mathcal F_n})
  +\mu(\SetDifference{A}{A_N^*})\\
&<2^{-(k+1)}+2^{-(k+1)}=2^{-k}<\varepsilon.
\end{aligned}$$
This proves the required approximation property. The choice of the finite cutoff $N$ is external;
every actual natural number belongs to $M$, and the finite-union construction gives an internal code
for this particular cutoff. No internal sequence of cutoff choices is needed.
\end{proof}

\begin{theorem*}[\termdefine{Internal approximation of Borel interpretations}]
If $c$ is valid and its label graph belongs to $M$, then $A_s\in\mathcal R_M$ for every finite node $s$.
In particular,
$$i^{-1}(\BorelValue{c})\in\mathcal R_M.$$
Thus every positive real error admits an inner closed tree and an outer open word family with internal
codes and the required external inclusions and error bound.
\end{theorem*}

\begin{proof}[Proof]
Induct along the well-founded child relation of $c$. An absent node has empty interpretation, and the
empty open code gives the approximation property there.
For a leaf whose basic open set is $\cyl{w}$, put
$$O_w=\{w\}\cap\finseq{2},\qquad
W_{O_w}=\{\sigma\in F_2:\sigma=e(w)\}.$$
The finite-word graph $e(w)$ belongs to $M$. Equality is a bounded predicate, so Separation puts this
code in $M$. Its open interpretation is $i^{-1}(\cyl{w})$: it is empty if $w$ has an entry outside
$\{0,1\}$, and otherwise it is the binary cylinder determined by $w$.
The internal open-code approximation theorem therefore handles the leaf case.

At a complement node, validity supplies a unique present child. All absent children have empty
interpretation, so the node evaluates to the complement of that child's interpretation. Apply the
complementation result of §{sec:internal-finite-measure-bounds} to the induction hypothesis at this child.
At a union node, apply the preceding theorem to the induction hypotheses at all present children.
These cases exhaust the evaluation equations and complete the induction. The root gives the final assertion.
\end{proof}

The approximation class $\mathcal R_M$ now contains every externally interpreted Borel set with a valid
internal code. The admissibility theorem converts these approximations into internal witnesses.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部符号付きBorel集合の近似とadmissibilityへの変換はinternallyApproximable_cantorSet等に対応済み。
未リンク部分は次節の有理下cut構成への案内のみ。)
--> The next section uses the inner closed codes to test the strict rational lower cut of the measure.<!--
formalization: skip-end
-->

## Internal Real Codes and Measure Values {#sec:internal-real-measure-values}

### Real Codes and Their Values {#sec:internal-borel-measure-cut}

\begin{mathmeta}
  \vars{a,b,d,m,n,N,u,v,k_*}{Nat}
  \vars{\sigma}{Set}
  \vars{r,s}{Real}
\end{mathmeta}

Keep the transitive-model hypotheses of §{sec:internal-approximation-errors}, and let
$B=\BorelInterpretation{c}{M}$ and $A=i^{-1}(\BorelValue{c})$ for a valid expression $c$ with internal label graph.
All the arithmetic and space parameters below are the fixed internal sets already constructed.
For a proposed inner-tree code, use
$$J(B,W):\equiv\mathrm{Tree}(W)\land\mathrm{Inc}(B,W,\emptyset).$$
The empty tree has no branches, so the second inclusion condition is automatic. By the shared
interpretation and inclusion theorems, $M\models J(B,W)$ holds exactly when $W=W_T$ for a downward-closed
binary tree $T$ with $\TreeBody{T}\IncludedIn A$.

For natural numbers $a,b,m,d$, compare fractions by the bounded test
$$\begin{aligned}
Q(a,b,m,d):\equiv{}&\exists u,v\in\omega\;[\\
&\Pair{\Pair{a}{d}}{u}\in G_\times\\
&{}\land\Pair{\Pair{m}{b}}{v}\in G_\times\land u\in v].
\end{aligned}$$
Its meaning is $ad<mb$, hence $a/b<m/d$ when both denominators are positive.
The common bounded-interpretation theorem supplies this meaning inside $M$ as well.
Let $H(W,m,d)$ be the closed measure lower-bound formula from §{sec:internal-finite-measure-bounds}, and put
$$\begin{aligned}
L(B,a,b):\equiv{}&\exists W\;\exists m,d\in\omega\;[\\
&J(B,W)\land0\in d\land Q(a,b,m,d)\\
&{}\land H(W,m,d)].
\end{aligned}$$
Here $0\in d$ means that the finite ordinal $d$ is positive. The quantifier on $W$ ranges over $M$
when the formula is interpreted there. The only new finite test is the cross-product comparison;
tree recognition, inclusion, and closed measure bounds are reused unchanged.

\begin{theorem*}[\termdefine{Internal rational lower cut of Borel measure}]
For $a,b\in\omega$ with $b>0$,
$$M\models L(B,a,b)\quad\Longleftrightarrow\quad\frac ab<\mu(A).$$
The right-hand side uses the full external interpretation of the code.
\end{theorem*}

\begin{proof}[Proof]
Suppose the internal formula holds, with witnesses $W,m,d$. The predicate $J$ gives an actual
downward-closed binary tree $T$ with $W=W_T\in M$ and $\TreeBody{T}\IncludedIn A$.
The arithmetic test and the closed lower-bound theorem give
$$\frac ab<\frac md\le\mu(\TreeBody{T})\le\mu(A).$$
This proves one implication.

Conversely, put $q=a/b$ and suppose $q<\mu(A)$. The internal approximation theorem gives
$W_T,W_O\in M$ with
$$\TreeBody{T}\IncludedIn A\IncludedIn U(O),\qquad
\mu(\SetDifference{U(O)}{\TreeBody{T}})<\mu(A)-q.$$
Monotonicity and subtraction of the closed inner set yield
$$\mu(A)-\mu(\TreeBody{T})
\le\mu(\SetDifference{U(O)}{\TreeBody{T}})<\mu(A)-q,$$
so $q<\mu(\TreeBody{T})$. Choose a rational $m/d$ strictly between them, with $m,d\in\omega$ and $d>0$;
this is possible because $q\ge0$. All these finite ordinals belong to $M$.
The interpretation theorems give $J(B,W_T)$ and $Q(a,b,m,d)$ inside $M$, while the closed measure
lower-bound theorem gives $H(W_T,m,d)$. These internal witnesses establish $L(B,a,b)$.
\end{proof}

\begin{corollary*}[\termdefine{Determination by internal rational cuts}]
There is a unique nonnegative external real $r$ such that, for every $a,b\in\omega$ with $b>0$,
$$M\models L(B,a,b)\quad\Longleftrightarrow\quad\frac ab<r.$$
It is $r=\mu(A)$.
\end{corollary*}

\begin{proof}[Proof]
The theorem shows that the actual measure satisfies these equivalences. If two nonnegative reals
were different, a nonnegative rational strictly between them would belong to exactly one of their
strict lower cuts. This contradicts the assumed equivalences, proving uniqueness.
\end{proof}

Thus two transitive models containing the same valid code give the same answers to these rational queries.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
2モデルの有理queryの一致はrealize_borelMeasureLowerCutFormulaの同じ外部測度による特徴付けへ対応済み。
残るのは全実数コードと通常測度の値との同定を扱う節の参照。)
--> §{sec:internal-borel-measure-cut} assembles them into a whole real code, and
§{sec:internal-borel-measure-identification} identifies this code with the model's usual measure value.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{NonnegativeRealCut}
\end{mathmeta}

For a nonnegative real $r$, encode its strict rational lower cut by
$$\NonnegativeRealCut{r}:=\{\Pair{a}{b}\in\omega\times\omega:
0<b,\ a/b<r\}.$$
Here the coordinates are finite ordinals and the brackets denote set-theoretic ordered pairs.
We retain every positive-denominator representation of a fraction; reducing fractions is unnecessary.
Negative rational queries are implicit, since every negative rational is less than $r$.
For example,
$$\NonnegativeRealCut{0}=\emptyset,\qquad
\NonnegativeRealCut{1}=\{\Pair{a}{b}\in\omega\times\omega:a<b\}.$$

\begin{proposition*}[\termdefine{Fraction cuts code nonnegative reals}]
For nonnegative reals $r,s$,
$$\NonnegativeRealCut{r}=\NonnegativeRealCut{s}\quad\Longleftrightarrow\quad r=s.$$
\end{proposition*}

\begin{proof}[Proof]
Equality of the codes gives the same answer to every positive-denominator fraction query.
The rational-density argument in §{sec:internal-borel-measure-cut} then gives equality of the two reals.
The reverse implication follows immediately from the definition.
\end{proof}

\begin{theorem*}[\termdefine{Internal real code for Borel measure}]
Under the hypotheses of §{sec:internal-borel-measure-cut}, the entire cut code belongs to the model:
$$\NonnegativeRealCut{\mu(A)}\in M.$$
\end{theorem*}

\begin{proof}[Proof]
The product $\omega\times\omega$ belongs to $M$. Apply internal Separation on this product with the formula
$$\begin{aligned}
P(B,z):\equiv{}&\exists a,b\in\omega\;[\\
&z=\Pair{a}{b}\land0\in b\land L(B,a,b)].
\end{aligned}$$
All parameters of $L$ belong to $M$. The common bounded-interpretation theorem handles the ordered pair
and the positive-denominator test. The preceding lower-cut theorem handles $L$.
Thus, for every $a,b\in\omega$,
$$M\models P(B,\Pair{a}{b})
\quad\Longleftrightarrow\quad 0<b\land a/b<\mu(A).$$
Since every element of the product is such a pair, the separated set is exactly
$\NonnegativeRealCut{\mu(A)}$. Hence it belongs to $M$.
\end{proof}

Consequently, both models contain the same entire fraction-cut code.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
両モデルの全code一致はcountableMeasure_code_borel_agreementへ対応済み。
未リンク部分は通常測度との同定の節への案内と、可算加法性を内部族に限定する前提の注意。)
--> §{sec:internal-borel-measure-identification} proves that it is the value code of their usual Cantor
probability measures. The argument uses countable additivity on internal families only.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
測度定理を内部で適用する際には全列グラフを入力にするという前提と、モデル公理・木の設定。内部clopen列の実構成は後続定理で対応済みで、
新たな反例は述べていない。)
--> To apply a measure theorem inside a model, the sequence to which it is applied must itself belong to the
model. Membership of each term separately is insufficient. We construct the whole decreasing sequence
used in the closed-tree measure formula of §{sec:coded-measure-bounds}.
Assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation, and Replacement.
Let $T\IncludedIn\finseq{2}$ have internal word code $W_T$.<!--
formalization: skip-end
-->

For each $n\in\omega$, write
$$L_n:=\{\sigma\in W_T:\sigma:n\to\omega\},\qquad k_n:=\Card{T_n}.$$
Thus $L_n$ consists of the graphs of the words in the finite level $T_n$; it includes dead ends.

\begin{proposition*}[\termdefine{Internal finite-level families}]
Both of the following entire graphs belong to $M$:
$$G_L:=\{\Pair{n}{L_n}:n\in\omega\},\qquad
G_k:=\{\Pair{n}{k_n}:n\in\omega\}.$$
\end{proposition*}

\begin{proof}[Proof]
The finite-level predicate of §{sec:internal-finite-measure-bounds} defines $L_n$ uniquely, and each $L_n$
belongs to the model by Separation. Bounded interpretation followed by graph collection gives $G_L$.
For $G_k$, use the already verified finite-cardinality formula, requiring the output to belong to $\omega$.
That formula holds exactly when the output is $k_n$. Graph collection by Replacement therefore gives $G_k$.
This uses the existing interpretation theorem for finite bijections; no new selection of bijections is needed.
\end{proof}

\begin{mathmeta}
  \define{InternalTreeLevel,InternalTreeBody}
\end{mathmeta}

Let $Y_M$ be the internal Cantor space from §{sec:internal-cantor-borel-sets}, and put
$$\begin{aligned}
\InternalTreeLevel{M}{T}{n}&:=\{g\in Y_M:\exists \sigma\in L_n\;(\sigma\IncludedIn g)\},\\
\InternalTreeBody{M}{T}&:=\{g\in Y_M:\forall n\in\omega\;(g\in\InternalTreeLevel{M}{T}{n})\}.
\end{aligned}$$
The relation $\sigma\IncludedIn g$ says that the finite word is an initial segment of the point represented by $g$.

\begin{theorem*}[\termdefine{Internal decreasing clopen approximation}]
The graph of the sequence and the intersection of its terms belong to $M$:
$$G_C:=\{\Pair{n}{\InternalTreeLevel{M}{T}{n}}:n\in\omega\}\in M,
\qquad \InternalTreeBody{M}{T}\in M.$$
For every external binary sequence $x$,
$$\begin{aligned}
g_{i(x)}\in\InternalTreeLevel{M}{T}{n}
&\longleftrightarrow g_{i(x)}\in M\ \land\ x\in C_n(T),\\
g_{i(x)}\in\InternalTreeBody{M}{T}
&\longleftrightarrow g_{i(x)}\in M\ \land\ x\in\TreeBody{T}.
\end{aligned}$$
Each $C_n(T)$ is clopen. If $T$ is downward closed, the internal sets decrease with $n$.
\end{theorem*}

\begin{proof}[Proof]
For any internal word family $W$, the predicate
$$\exists \sigma\in W\;(\sigma\IncludedIn g)$$
is bounded. Separation on $Y_M$ forms its cylinder union. Given the entire graph $G_L$, a bounded formula
reads its value at $n$ and characterizes that union by its membership condition on $Y_M$.
The same graph-collection theorem gives $G_C$.
Its range belongs to $M$, so another bounded Separation forms
$$\{g\in Y_M:\forall D\in\operatorname{ran}(G_C)\;(g\in D)\}=\InternalTreeBody{M}{T}.$$

Each element of $L_n$ is the graph of a unique binary word of length $n$. Its graph is contained in $g_{i(x)}$
exactly when it is the length-$n$ prefix of $x$. This proves the first membership equivalence.
Taking all lengths gives the second. The sets $C_n(T)$ are finite unions of clopen cylinders.
Downward closure of $T$ implies $C_{n+1}(T)\IncludedIn C_n(T)$, and the first equivalence transfers this
inclusion to their internal interpretations.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
構成済みの全clopen列を連続性の定理に渡す順序と、先に数値code演算を用意するという読み方の案内。)
--> This whole family is the input to continuity from above in §{sec:internal-finite-measure-laws}.
That section derives continuity from the model's measure axioms, using the real-code operations developed next.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
外部測度から作ったcodeと、内部で認識したcodeの外部decodingとを比較する動機付け。
必要な逆方向の実定理は直後のcut条件・decodingで別に対応。)
--> The code in §{sec:internal-borel-measure-cut} was constructed from a known external measure value.
To compare it with the value of an internal measure, we also need the converse: a set recognized internally
as a real code must determine an actual external real. We give arithmetic conditions for this recognition.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{RealCutCondition,RealCutValue}
\end{mathmeta}

Call a set $C$ a \termdefine{nonnegative real cut code} if it satisfies the following four conditions.
All variables $a,b,m,d,N$ in these conditions range over $\omega$.

1. Every member of $C$ is a pair $\Pair{a}{b}$ with $0<b$.
2. If $0<b$, $0<d$, $ad\le mb$, and $\Pair{m}{d}\in C$, then $\Pair{a}{b}\in C$.
3. If $\Pair{a}{b}\in C$, there are $m,d$ with $\Pair{m}{d}\in C$ and $ad<mb$.
4. There is an $N$ such that $\Pair{N}{1}\notin C$.

The second condition includes equality of fractions, so all representations of the same fraction give the
same membership answer. The third excludes a largest fraction. The empty code is allowed.
Write $\RealCutCondition{C}$ for the conjunction of these conditions, with the fixed parameters
$\omega,G_\times,0,1$ understood.

\begin{theorem*}[\termdefine{Decoding arithmetic fraction cuts}]
A set $C$ satisfies $\RealCutCondition{C}$ if and only if
$$C=\NonnegativeRealCut{r}$$
for a nonnegative real $r$. This real is unique and is given by
$$\RealCutValue{C}:=\sup\left(\{0\}\cup
\left\{\frac ab:\Pair{a}{b}\in C\right\}\right).$$
\end{theorem*}

\begin{proof}[Proof]
Assume the four conditions. If $\Pair{N}{1}\notin C$, every fraction in the code is strictly less than
$N$: otherwise the second condition would put $\Pair{N}{1}$ in the code. Thus the displayed set is
nonempty and bounded above. Its supremum $r$ exists and is nonnegative.
If $\Pair{a}{b}\in C$, the third condition gives a larger fraction in the code, so $a/b<r$.
Conversely, if $b>0$ and $a/b<r$, the definition of supremum gives an element of the displayed set strictly
above $a/b$. This element is not $0$, since $a/b\ge0$, so it comes from a fraction in the code.
The second condition then gives $\Pair{a}{b}\in C$. The first condition ensures that there are no
other members, proving $C=\NonnegativeRealCut{r}$.

Conversely, $\NonnegativeRealCut{r}$ satisfies the first two conditions directly. Rational density supplies
the larger fraction required in the third condition. Choose an integer $N\ge r$ for the fourth.
Uniqueness follows from §{sec:internal-borel-measure-cut}, since different nonnegative reals have different
fraction cuts. In particular, decoding $\NonnegativeRealCut{r}$ returns $r$, including $r=0$.
\end{proof}

\begin{theorem*}[\termdefine{Absolute validity of real cut codes}]
Let $M$ be transitive and contain $\omega,G_\times,0,1,C$. Then
$$M\models\RealCutCondition{C}\quad\Longleftrightarrow\quad
\exists r\ge0\;(C=\NonnegativeRealCut{r}).$$
The real on the right is an external real, and it is unique.
\end{theorem*}

\begin{proof}[Proof]
The first condition quantifies only over $C$ and $\omega$. The remaining conditions quantify only over
$\omega$. Express products by bounded lookups in $G_\times$ and comparisons by finite-ordinal membership
and equality. The ordered-pair predicates are bounded as well. Thus the shared bounded-interpretation
theorem transfers the conjunction exactly between the model and the external universe.
Apply the preceding decoding theorem. The required arithmetic parameters belong to the model under the
hypotheses used in §{sec:internal-natural-arithmetic}.
\end{proof}

\begin{proposition*}[\termdefine{Order of nonnegative real codes}]
For nonnegative reals $r,s$,
$$\NonnegativeRealCut{r}\IncludedIn\NonnegativeRealCut{s}\quad\Longleftrightarrow\quad r\le s.$$
If both codes belong to a transitive model, the same equivalence holds when the inclusion is interpreted
inside the model.
\end{proposition*}

\begin{proof}[Proof]
An inequality $r\le s$ preserves every strict lower query. If instead $s<r$, a nonnegative rational strictly
between them belongs to the cut of $r$ and not to the cut of $s$, contradicting inclusion.
Inclusion of the two internal sets is a bounded predicate, so the shared interpretation theorem also
proves the internal assertion.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前のdecodingと順序定理の利用の説明、および加法と下限の構成へ進む案内。独立した新定理は提示していない。)
--> An internally recognized cut can therefore be decoded and ordered externally without assuming its value
in advance. The next constructions provide addition and countable infima for the measure axioms in
§{sec:internal-finite-measure-laws}.<!--
formalization: skip-end
-->

### Arithmetic and Finite-Level Values {#sec:internal-real-cut-addition}

\begin{mathmeta}
  \vars{a,b,c,d,e,f,m,n,k_*,t_*}{Nat}
  \vars{r,s,r_*}{Real}
\end{mathmeta}

Finite additivity requires the sum of two coded nonnegative reals. Since the code of zero is empty,
we must allow zero as a lower approximation even when it does not belong to the strict cut.

\begin{mathmeta}
  \define{RealCutApprox,RealCutSum}
\end{mathmeta}

For $a,b\in\omega$, put
$$\RealCutApprox{C}{a}{b}\longleftrightarrow
0<b\ \land\ (a=0\ \lor\ \Pair{a}{b}\in C).$$
If $C=\NonnegativeRealCut{r}$ with $r\ge0$, every such fraction satisfies $a/b\le r$.
For every $\varepsilon>0$ one can choose such a fraction with $r-\varepsilon<a/b$:
use $0/1$ when $r<\varepsilon$, and otherwise choose a rational strictly between $r-\varepsilon$ and $r$.

Define $\RealCutSum{C}{D}\IncludedIn\omega\times\omega$ by
$$\begin{aligned}
\Pair{a}{b}\in\RealCutSum{C}{D}
&\longleftrightarrow 0<b\ \land\ \exists c,d,e,f\in\omega\;[\\
&\qquad\RealCutApprox{C}{c}{d}\ \land\ \RealCutApprox{D}{e}{f}\\
&\qquad{}\land\ a(df)<(cf+ed)b].
\end{aligned}$$
The final inequality says $a/b<c/d+e/f$. All its denominators are positive by the preceding conditions.

\begin{theorem*}[\termdefine{Addition of real cut codes}]
For nonnegative reals $r,s$,
$$\RealCutSum{\NonnegativeRealCut{r}}{\NonnegativeRealCut{s}}
=\NonnegativeRealCut{r+s}.$$
More generally, if $C,D$ are valid real cut codes, then $\RealCutSum{C}{D}$ is valid and
$$\RealCutValue{\RealCutSum{C}{D}}=\RealCutValue{C}+\RealCutValue{D}.$$
For a third valid code $E$, it follows that
$$E=\RealCutSum{C}{D}\quad\longleftrightarrow\quad
\RealCutValue{E}=\RealCutValue{C}+\RealCutValue{D}.$$
\end{theorem*}

\begin{proof}[Proof]
For $q=a/b$ with $b>0$, suppose $q<r+s$. Set $\varepsilon=(r+s-q)/3>0$ and choose lower approximations
$u=c/d$ and $v=e/f$ as above, so that
$$r-\varepsilon<u\le r,\qquad s-\varepsilon<v\le s.$$
Then $q<r+s-2\varepsilon<u+v$, giving witnesses to the defining condition.
Conversely, any witnesses give $q<u+v\le r+s$. This proves equality of the codes; both sides exclude
zero denominators. Decode arbitrary valid $C,D$ by §{sec:internal-borel-measure-cut} and apply this identity.
It gives validity and the value of the sum. The final equivalence follows by decoding the code equation
in one direction and encoding the numerical equation in the other.
\end{proof}

In particular, this definition covers $r=0$, $s=0$, and $r=s=0$ without changing the formula.
Requiring both approximations to belong to the strict cuts would fail whenever one of these cuts is empty.

\begin{theorem*}[\termdefine{Internal addition of real cut codes}]
Assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, and Separation.
If $C,D\in M$, then $\RealCutSum{C}{D}\in M$. For valid input codes, the internal result represents the
sum of their external decoded values.
\end{theorem*}

\begin{proof}[Proof]
Use the internal graphs of natural addition and multiplication from §{sec:internal-natural-arithmetic}.
The displayed membership condition has only $\omega$-bounded witnesses. To express its arithmetic comparison,
perform the following six computations:
$$\begin{aligned}
t_1&=df,& t_2&=at_1,& t_3&=cf,\\
t_4&=ed,& t_5&=t_3+t_4,& t_6&=t_5b.
\end{aligned}$$
Then test $t_2<t_6$. The outputs of the computations are also bounded by $\omega$.
The shared bounded-interpretation theorem therefore identifies this condition inside $M$ with the
external one. Separation on $\omega\times\omega$ constructs precisely $\RealCutSum{C}{D}$ in $M$.
The preceding theorem identifies its decoded value.
\end{proof}

Thus an internal sum equation transfers to an equality of decoded real values.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
内部sum等式のdecoded値への輸送はeq_sumCutCode_iffへ対応済み。残りは有限加法性への適用先の節参照。)
--> §{sec:internal-finite-measure-laws} applies this fact to the finite-additivity axiom.<!--
formalization: skip-end
-->

For continuity from above, the numerical operation we need is a countable infimum. It cannot be represented
by the plain intersection of strict lower cuts: that intersection can retain the limiting endpoint.

\begin{example*}[Why the intersection needs rounding]
Put $r_n=1/(n+1)$. Then $\inf_n r_n=0$, but for every $n$ we have
$$\Pair{0}{1}\in\NonnegativeRealCut{r_n},\qquad
\NonnegativeRealCut{0}=\emptyset.$$
Thus the intersection of these codes is not the code of their infimum.
\end{example*}

\begin{proof}[Proof]
Every $r_n$ is positive, and the sequence converges to zero. Hence $0<r_n$ for every index, whereas $0<0$
is false. The membership conditions give the stated discrepancy.
\end{proof}

\begin{mathmeta}
  \define{RealCutInfimum}
\end{mathmeta}

For a sequence $\mathcal D= \Sequence{D_n}{n \in \omega}$ of sets, define $\RealCutInfimum{ \mathcal D}
\IncludedIn \omega \times \omega$ by
$$\begin{aligned}
\Pair{a}{b}\in\RealCutInfimum{\mathcal D}
&\longleftrightarrow 0<b\ \land\ \exists m,d\in\omega\;[\\
&\qquad 0<d\ \land\ ad<mb\\
&\qquad{}\land\forall n\in\omega\;(\Pair{m}{d}\in D_n)].
\end{aligned}$$
The witness fraction $m/d$ lies strictly above $a/b$ and belongs to every cut. This common margin is what
removes a possible endpoint. The formula is meaningful for arbitrary sets $D_n$; validity is used in the
numerical identification below.

\begin{theorem*}[\termdefine{Rounded intersection of real cut codes}]
For any sequence of nonnegative reals $r_n$,
$$\RealCutInfimum{\Sequence{\NonnegativeRealCut{r_n}}{n\in\omega}}
=\NonnegativeRealCut{\inf_n r_n}.$$
More generally, if each $D_n$ satisfies $\RealCutCondition{D_n}$, then
$$\begin{gathered}
\RealCutInfimum{\mathcal D}=\NonnegativeRealCut{\inf_n\RealCutValue{D_n}},\\
\RealCutCondition{\RealCutInfimum{\mathcal D}},\qquad
\RealCutValue{\RealCutInfimum{\mathcal D}}=\inf_n\RealCutValue{D_n}.
\end{gathered}$$
No monotonicity assumption on the sequence is needed.
\end{theorem*}

\begin{proof}[Proof]
The sequence is bounded below by zero, so its infimum $r$ is a nonnegative real.
For $q=a/b$ with $b>0$, suppose $q<r$. Choose a nonnegative rational $m/d$ with
$$q<m/d<r,\qquad d>0.$$
It belongs to every cut, because $r\le r_n$ for all $n$. Conversely, a common witness $m/d$ is below every
$r_n$, hence at most their infimum; therefore $q<m/d\le r$.
These two implications prove equality of the codes, including their exclusion of zero denominators.
For an arbitrary sequence of valid codes, apply §{sec:internal-borel-measure-cut} to each term and use the
identity just proved. The same decoding theorem gives validity and the displayed value of the result.
\end{proof}

\begin{theorem*}[\termdefine{Internal infimum of real cut codes}]
Assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, and Separation.
If the whole sequence graph
$$G:=\{\Pair{n}{D_n}:n\in\omega\}$$
belongs to $M$, then $\RealCutInfimum{\mathcal D}\in M$. If the terms are valid real cut codes, this internal set
represents the infimum of their external decoded values.
\end{theorem*}

\begin{proof}[Proof]
The range $R=\operatorname{ran}(G)$ belongs to $M$. In the defining condition, replace the test in each term by
$$\forall n\in\omega\;\exists D\in R\;
[\Pair{n}{D}\in G\land\Pair{m}{d}\in D].$$
Since $G$ is the entire graph, this is exactly membership in every $D_n$.
All witnesses are bounded by $\omega$ or $R$. The cross-product comparison uses the multiplication graph
from §{sec:internal-natural-arithmetic}. Thus the shared bounded-interpretation theorem applies, and
Separation on $\omega\times\omega$ constructs exactly $\RealCutInfimum{\mathcal D}$ inside the model.
The preceding theorem identifies its decoded value. Termwise internality alone would not provide the
parameter $G$ required by this construction.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
加法と可算下限の定理を有限加法性・連続性に使う旨の節案内。数値演算の定理そのものは既に別に対応。)
--> Together with addition, this supplies the real-code operations used in §{sec:internal-finite-measure-laws} to derive
finite additivity and continuity from above.<!--
formalization: skip-end
-->

The clopen sets in §{sec:internal-borel-measure-cut} form an entire internal sequence.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
全clopen列の内部所属はinternalLevelSet_sequence_memへ対応済み。残りは次に全数値code列を作る目的、
全グラフを入力とする条件、モデル公理の再掲。)
--> We now construct the corresponding sequence of numerical value codes. This requires an internal family
of codes, rather than only the existence of each rational value in the model.
Throughout this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation,
and Replacement.<!--
formalization: skip-end
-->

\begin{proposition*}[\termdefine{Internal families of rational value codes}]
Let $m_n,d_n\in\omega$ with $d_n>0$ for every $n$. If both entire graphs
$$\{\Pair{n}{m_n}:n\in\omega\},\qquad
\{\Pair{n}{d_n}:n\in\omega\}$$
belong to $M$, then the entire graph
$$\{\Pair{n}{\NonnegativeRealCut{m_n/d_n}}:n\in\omega\}$$
also belongs to $M$.
\end{proposition*}

\begin{proof}[Proof]
For fixed $m,d\in\omega$ with $d>0$, the membership test is
$$\Pair{a}{b}\in\NonnegativeRealCut{m/d}
\quad\longleftrightarrow\quad 0<b\ \land\ ad<mb.$$
The multiplication graph expresses this condition by bounded quantifiers. Shared bounded interpretation
and Separation on $\omega\times\omega$ therefore construct the whole cut inside $M$.
A subset of $\omega\times\omega$ is uniquely determined by these pair-membership tests.
Given $n$, read $m_n,d_n$ from the two internal graphs, and characterize the output by those tests.
The shared graph-collection theorem then gives the graph of all the output cuts by Replacement.
\end{proof}

\begin{mathmeta}
  \define{TreeLevelMeasureCode}
\end{mathmeta}

For $T\IncludedIn\finseq{2}$, write $k_n=\Card{T_n}$ and define
$$\TreeLevelMeasureCode{T}{n}:=\NonnegativeRealCut{k_n/2^n}.$$
The finite-level calculation in §{sec:coded-measure-bounds} gives
$$\frac{k_n}{2^n}=\mu(C_n(T)).$$
This counts all words in $T_n$, including dead ends.

\begin{theorem*}[\termdefine{Internal sequence of finite-level measure values}]
If the word code $W_T$ belongs to $M$, then
$$G_Q:=\{\Pair{n}{\TreeLevelMeasureCode{T}{n}}:n\in\omega\}\in M.$$
Each value code is valid, and
$$\RealCutValue{\TreeLevelMeasureCode{T}{n}}=\mu(C_n(T)).$$
\end{theorem*}

\begin{proof}[Proof]
The entire count sequence $\Sequence{k_n}{n\in\omega}$ belongs to $M$ by §{sec:internal-borel-measure-cut}.
The entire sequence $\Sequence{2^n}{n\in\omega}$ belongs to $M$ by §{sec:internal-natural-arithmetic}.
Apply the preceding proposition to these sequences. Validity and the decoded values follow from
§{sec:internal-borel-measure-cut} and the finite-level measure calculation.
\end{proof}

\begin{proposition*}[\termdefine{Finite additivity of level value codes}]
If $T_n\cap S_n=\emptyset$, then
$$\TreeLevelMeasureCode{T\cup S}{n}
=\RealCutSum{\TreeLevelMeasureCode{T}{n}}{\TreeLevelMeasureCode{S}{n}}.$$
\end{proposition*}

\begin{proof}[Proof]
The finite level of the union is $T_n\cup S_n$. Since these finite sets are disjoint, their cardinalities
add. Dividing by $2^n$ gives addition of the level weights. The addition theorem in
§{sec:internal-real-cut-addition} converts this numerical equality into the stated code equality.
\end{proof}

\begin{theorem*}[\termdefine{Closed measure from the internal level-value sequence}]
Suppose $T$ is downward closed and $W_T\in M$. Then
$$\begin{gathered}
\RealCutInfimum{\Sequence{\TreeLevelMeasureCode{T}{n}}{n\in\omega}}\in M,\\
\RealCutInfimum{\Sequence{\TreeLevelMeasureCode{T}{n}}{n\in\omega}}
=\NonnegativeRealCut{\mu(\TreeBody{T})},\\
\RealCutValue{\RealCutInfimum{\Sequence{\TreeLevelMeasureCode{T}{n}}{n\in\omega}}}
=\mu(\TreeBody{T}).
\end{gathered}$$
\end{theorem*}

\begin{proof}[Proof]
The entire graph $G_Q$ is internal, so §{sec:internal-real-cut-addition} constructs its rounded infimum
inside $M$ and identifies the decoded value with $\inf_n k_n/2^n$.
By §{sec:coded-measure-bounds}, the level weights converge to $\mu(\TreeBody{T})$, and each is at least
that value. Their infimum is therefore exactly that value. The encoding and decoding identities from
§{sec:internal-real-cut-addition} give the two remaining equalities.
\end{proof}

This constructs the closed-measure code from the entire internal level-value sequence.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
全有限段階値列から閉集合measure codeを内部構成する部分はroundedInf_levelMeasureCode_memへ対応済み。
残りは測度公理から値を同定する次節の案内。)
--> The next section identifies the finite-level values from the measure graph's axioms;
§{sec:internal-finite-measure-laws} then derives continuity and identifies its closed-set value.<!--
formalization: skip-end
-->

## Measure Laws and Absoluteness {#sec:internal-measure-absoluteness}

### Measure Laws {#sec:internal-finite-measure-laws}

\begin{mathmeta}
  \vars{n,p}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

We now read the finite measure laws from a graph of values. Let $D$ be a family of subsets of an ambient
set $Y$, containing $\emptyset$ and closed under binary unions and differences. Let $R$ be a set of valid
nonnegative real cut codes, and let $F:D\to R$ be a function graph. In an internal interpretation, the
whole sets $D,R,F$ belong to the transitive model $M$. The arithmetic parameters used below also belong
to $M$ by §{sec:internal-natural-arithmetic}.

\begin{mathmeta}
  \define{MeasureValueCode,FiniteAdditivityLaw,InternalCylinder}
\end{mathmeta}

For $A\in D$, write $\MeasureValueCode{F}{A}$ for the unique code with
$\Pair{A}{\MeasureValueCode{F}{A}}\in F$, and put
$$\nu(A):=\RealCutValue{\MeasureValueCode{F}{A}}.$$
The zero clause is $\Pair{\emptyset}{\emptyset}\in F$.
The finite-additivity clause says that for $A,B,U\in D$ and $C,E,V\in R$,
$$\begin{gathered}
A\cap B=\emptyset,\qquad U=A\cup B,\\
\Pair{A}{C}\in F,\quad\Pair{B}{E}\in F,\quad\Pair{U}{V}\in F\\
\Longrightarrow\quad V=\RealCutSum{C}{E}.
\end{gathered}$$
Denote this statement by $\FiniteAdditivityLaw{D}{R}{F}$, with the fixed arithmetic parameters understood.
These are finite measure laws on the given family; countable additivity is not part of this clause.

\begin{theorem*}[\termdefine{Absolute finite-additivity axiom}]
The axiom above has a bounded formulation, and
$$M\models\FiniteAdditivityLaw{D}{R}{F}
\quad\longleftrightarrow\quad\FiniteAdditivityLaw{D}{R}{F}.$$
\end{theorem*}

\begin{proof}[Proof]
Disjointness is the bounded test $\forall x\in A\;(x\notin B)$.
The union equation says $A,B\IncludedIn U$ and $\forall x\in U\;(x\in A\lor x\in B)$.
For the equation between value codes, require $V\IncludedIn\omega\times\omega$ and, for every pair in
that ambient set, equivalence of membership in $V$ with the bounded sum condition from
§{sec:internal-real-cut-addition}. The shared extensionality argument for a boundedly specified subset
identifies this whole output set with $\RealCutSum{C}{E}$.
All remaining quantifiers are bounded by $D$ or $R$, and graph lookup is bounded.
The shared interpretation theorem therefore gives the equivalence. Function typing ensures that every
actual value of $F$ belongs to $R$, so these range bounds omit no value.
\end{proof}

\begin{theorem*}[\termdefine{Decoding finite measure axioms}]
Assume the zero and finite-additivity clauses. Then $\nu$ is nonnegative on $D$, vanishes at
$\emptyset$, and is finitely additive. In particular, for pairwise disjoint $A_0,\ldots,A_{k-1}\in D$,
$$\nu\left(\bigcup_{i<k}A_i\right)=\sum_{i<k}\nu(A_i).$$
If $A,B\in D$ and $A\IncludedIn B$, then $\nu(A)\le\nu(B)$.
If also $Y\in D$ and $\nu(Y)=1$, then for every $A\in D$,
$$\nu(\SetDifference{Y}{A})=1-\nu(A).$$
\end{theorem*}

\begin{proof}[Proof]
Validity of the value codes gives nonnegativity. The zero clause and uniqueness of the graph value give
the empty code at $\emptyset$, which decodes to zero. For two disjoint sets, the graph clause and
§{sec:internal-real-cut-addition} give addition of the decoded values. Induction on a finite list of
pairwise disjoint sets proves the displayed finite-union formula; the empty list uses the zero clause.
For $A\IncludedIn B$, split $B$ into the disjoint sets $A$ and $\SetDifference{B}{A}$ to obtain
$$\nu(A)+\nu(\SetDifference{B}{A})=\nu(B).$$
Nonnegativity gives monotonicity. Taking $B=Y$ and using $\nu(Y)=1$ gives the complement formula.
\end{proof}

For a binary word $s$, let $\InternalCylinder{M}{s}$ be its cylinder inside the internal Cantor space:
$$\InternalCylinder{M}{s}:=\{g\in Y_M:w_s\IncludedIn g\}.$$
Here $w_s$ is the graph of the binary word viewed as a finite sequence of natural numbers.
Equivalently, this is the cylinder union of §{sec:internal-borel-measure-cut} for the singleton
word family $\{w_s\}$. Its points are exactly the graphs in $M$ of external points of $\cyl{s}$.

\begin{theorem*}[\termdefine{Finite-level values from measure axioms}]
Assume the preceding finite measure laws, and assume that the basic internal cylinders belong to $D$
with the fair-coin values
$$\MeasureValueCode{F}{\InternalCylinder{M}{s}}
=\NonnegativeRealCut{2^{-\Length{s}}}.$$
Then, for every $T\IncludedIn\finseq{2}$ and $n\in\omega$,
$$\begin{gathered}
\MeasureValueCode{F}{\InternalTreeLevel{M}{T}{n}}=\TreeLevelMeasureCode{T}{n},\\
\nu(\InternalTreeLevel{M}{T}{n})=\frac{\Card{T_n}}{2^n}.
\end{gathered}$$
If $W_T\in M$ and $M$ satisfies the hypotheses of §{sec:internal-real-cut-addition}, the entire
sequence of the measure's own value codes belongs to $M$:
$$\{\Pair{n}{\MeasureValueCode{F}{\InternalTreeLevel{M}{T}{n}}}:n\in\omega\}\in M.$$
\end{theorem*}

\begin{proof}[Proof]
Enumerate the distinct words of $T_n$ and form their internal cylinders. Their finite union is exactly
$\InternalTreeLevel{M}{T}{n}$ by its membership definition. Distinct words of length $n$ have disjoint
external cylinders; restricting to the internal points preserves disjointness.
Finite additivity and the normalization give $\Card{T_n}$ summands, each equal to $2^{-n}$.
Thus the decoded value is $\Card{T_n}/2^n$. Validity of the graph value and uniqueness of real coding identify
its whole code with $\TreeLevelMeasureCode{T}{n}$.
The entire sequence is therefore the graph $G_Q$ already constructed in §{sec:internal-real-cut-addition}.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
連続性を適用する対象が内部の全列であるという範囲の注意と次節の案内。old points上の外部可算加法性を主張したり、
その反例を証明したりする箇所ではない。)
--> The next section derives continuity for the internal decreasing family from countable additivity.
Its domain consists of entire internal families; it asserts no external countable additivity on the set
of old points.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
有限測度graphの記号、モデル公理、可算加法性を内部全列だけに適用する条件の再掲。実際の列演算は続く定理で別に対応。)
--> Retain the finite measure graph $F:D\to R$ and its decoded values $\nu$ from
§{sec:internal-finite-measure-laws}. Let $M$ be transitive and satisfy Infinity, Pairing, Union, Power Set,
Separation, and Replacement. We apply countable additivity only to families whose entire sequence graph
belongs to $M$. The following constructions justify each such application.<!--
formalization: skip-end
-->

For a sequence $A=\Sequence{A_n}{n\in\omega}$, put
$$\begin{gathered}
G_A=\{\Pair{n}{A_n}:n\in\omega\},\qquad
P_n(A)=\bigcup_{i<n}A_i,\\
B_n=\SetDifference{A_n}{A_{n+1}},\qquad I=\bigcap_n A_n.
\end{gathered}$$

\begin{theorem*}[\termdefine{Internal initial unions and differences}]
If $G_A\in M$, then the entire graphs of $\Sequence{P_n(A)}{n\in\omega}$ and $\Sequence{B_n}{n\in\omega}$ belong to $M$.
Moreover, $\bigcup_n A_n$ and $I$ belong to $M$.
\end{theorem*}

\begin{proof}[Proof]
The range $\GraphRange{G_A}$ and its union belong to $M$ by the graph-range construction and Union.
Membership in $P_n(A)$ is expressed by
$$\exists i\in n\;\exists C\in\GraphRange{G_A}\;
  (\Pair{i}{C}\in G_A\land x\in C).$$
Use the union as the ambient set for Separation. For $B_n$, retrieve $A_n$ and $A_{n+1}$ from $G_A$
and separate the points of the former that do not belong to the latter. The successor relation and
these graph lookups have the bounded descriptions already established above. The common interpretation
and graph-collection lemmas therefore give both entire sequence graphs by Replacement.
Finally, separate from $A_0$ the points belonging to every member of $\GraphRange{G_A}$ to obtain $I$.
\end{proof}

\begin{lemma*}[\termdefine{Disjoint differences of a decreasing family}]
If $A_{n+1}\IncludedIn A_n$ for every $n$, the sets $B_n$ are pairwise disjoint and
$$P_n(B)=\SetDifference{A_0}{A_n},\qquad
\bigcup_n B_n=\SetDifference{A_0}{I}.$$
\end{lemma*}

\begin{proof}[Proof]
For $i<j$, $B_j\IncludedIn A_{i+1}$ whereas $B_i$ is disjoint from $A_{i+1}$.
The finite-union identity follows by induction, starting from $P_0(B)=\emptyset$.
A point of $A_0$ is outside $I$ exactly when it is outside some $A_n$; taking the union of the finite
identities gives the second equality.
\end{proof}

\begin{lemma*}[\termdefine{Unions of bounded real cuts}]
For a bounded sequence of nonnegative reals $r_n$,
$$\bigcup_n\NonnegativeRealCut{r_n}=\NonnegativeRealCut{\sup_n r_n}.$$
If the sequence is increasing, equality of this union with a valid code $V$ is equivalent to
$r_n\to\RealCutValue{V}$.
\end{lemma*}

\begin{proof}[Proof]
For $b>0$, the inequality $a/b<\sup_n r_n$ holds exactly when $a/b<r_n$ for some $n$.
This proves equality of the strict cuts. An increasing bounded real sequence converges to its supremum;
uniqueness of limits and the encoding-decoding identities prove the equivalence.
\end{proof}

Let $A_n\in D$ be pairwise disjoint and suppose $G_A\in M$. The countable-additivity clause consists
of $U:=\bigcup_n A_n\in D$ and the assertion that the value at $U$ is the sum of the values at $A_n$.
For a proposed sum code $V$, write this assertion as $V\IncludedIn\omega\times\omega$ and, for every
$p\in\omega\times\omega$,
$$\begin{aligned}
p\in V\quad\longleftrightarrow\quad
&\exists n\in\omega\;\exists B\in D\;\exists C\in R\\
&\bigl(B=P_n(A)\land\Pair{B}{C}\in F\land p\in C\bigr).
\end{aligned}$$
Here $B=P_n(A)$ abbreviates the bounded membership description in the first proof, together with
$B\IncludedIn\bigcup_n A_n$. The fixed parameters include $G_A$, its range, and its union.

\begin{proposition*}[\termdefine{Internal interpretation of a nonnegative series}]
For parameters in $M$, the displayed sum-code condition has the same truth value internally and
externally. It holds exactly when
$$V=\bigcup_n\MeasureValueCode{F}{P_n(A)}.$$
For $U\in D$ and $V=\MeasureValueCode{F}{U}$, it is equivalent to
$$\sum_{i<n}\nu(A_i)\longrightarrow\nu(U).$$
\end{proposition*}

\begin{proof}[Proof]
Apply the shared bounded interpretation theorem to the displayed formula. Extensionality and
uniqueness of graph values identify $V$ with the union of the partial-union value codes.
Finite additivity gives $\nu(P_n(A))=\sum_{i<n}\nu(A_i)$. These values increase and are bounded by
$\nu(U)$ by monotonicity, so the preceding lemma gives the convergence equivalence.
This interprets each whole internal family; it does not quantify over new external families.
\end{proof}

\begin{theorem*}[\termdefine{Continuity from above for internal families}]
Assume the internal countable-additivity clauses just described. If $A_n\in D$ is decreasing and
$G_A\in M$, then $I\in D$ and
$$\begin{gathered}
\nu(A_n)\longrightarrow\nu(I),\qquad \nu(I)=\inf_n\nu(A_n),\\
\MeasureValueCode{F}{I}
=\RealCutInfimum{\Sequence{\MeasureValueCode{F}{A_n}}{n\in\omega}}.
\end{gathered}$$
\end{theorem*}

\begin{proof}[Proof]
The differences $B_n$ belong to $D$, are pairwise disjoint, and form an entire internal sequence.
Countable additivity therefore gives $J:=\bigcup_n B_n\in D$ and
$\nu(P_n(B))\to\nu(J)$. Since $I=\SetDifference{A_0}{J}$, difference closure gives $I\in D$.
The disjoint-difference identities and finite additivity yield
$$\nu(A_n)=\nu(A_0)-\nu(P_n(B)),\qquad
\nu(I)=\nu(A_0)-\nu(J).$$
Subtract the convergent sequence from the finite real number $\nu(A_0)$.
Monotonicity then identifies the limit with the infimum. The rounded-infimum identity in
§{sec:internal-real-cut-addition} and validity of the value at $I$ give the equality of codes.
\end{proof}

\begin{theorem*}[\termdefine{Closed values from the internal measure axioms}]
Assume these measure axioms and the fair-coin cylinder normalization from
§{sec:internal-finite-measure-laws}. If $T$ is downward closed and $W_T\in M$, then
$\InternalTreeBody{M}{T}\in D$ and
$$\begin{gathered}
\MeasureValueCode{F}{\InternalTreeBody{M}{T}}=\NonnegativeRealCut{\mu(\TreeBody{T})},\\
\nu(\InternalTreeBody{M}{T})=\mu(\TreeBody{T}).
\end{gathered}$$
\end{theorem*}

\begin{proof}[Proof]
Apply continuity from above to $A_n=\InternalTreeLevel{M}{T}{n}$.
The entire decreasing family is internal by §{sec:internal-borel-measure-cut}, and its
intersection is $\InternalTreeBody{M}{T}$. Each level lies in $D$ as a finite union of basic cylinders.
Its value code is $\TreeLevelMeasureCode{T}{n}$ by §{sec:internal-finite-measure-laws}.
Consequently the code at the intersection is the rounded infimum of this sequence, which equals
$\NonnegativeRealCut{\mu(\TreeBody{T})}$ by §{sec:internal-real-cut-addition}.
Decode this equality to obtain the numerical identity.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
閉集合での値と近似定理を次節の一般Borel同定へ使う旨の案内。)
--> The next section uses these closed values and the internal approximation theorem to identify the measure
of a general Borel interpretation.<!--
formalization: skip-end
-->

### Agreement with External Borel Measure {#sec:internal-borel-measure-identification}

\begin{mathmeta}
  \vars{a,b}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
同定定理に使うモデル・measure graph・正規化の前提と点の表記を固定する導入。可算加法性を閉集合値の同定で使うという証明依存関係の説明で、
新しいmeasure存在定理ではない。)
--> Keep the transitive-model assumptions and the measure graph $F:D\to R$ of
§{sec:internal-finite-measure-laws}. Assume also Choice in $M$, and normalize the measure by
$Y_M\in D$ and $\nu(Y_M)=1$. Points of the internal Cantor space $Y_M$ are identified with their graphs
$g_{i(x)}$. The following argument uses finite measure laws and the closed values already identified;
countable additivity is needed only in that closed-value theorem.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefine{Squeezing internal values by closed approximations}]
Let $A\IncludedIn\CantorSpace$ and $X\in D$, with $X\IncludedIn Y_M$, satisfy
$$g_{i(x)}\in X\quad\longleftrightarrow\quad g_{i(x)}\in M\land x\in A.$$
Suppose $A$ has internal two-sided approximation codes as in §{sec:internal-approximation-errors}.
Suppose also that every downward-closed binary tree $T$ with $W_T\in M$ satisfies
$$\InternalTreeBody{M}{T}\in D,\qquad
\nu(\InternalTreeBody{M}{T})=\mu(\TreeBody{T}).$$
Then $\nu(X)=\mu(A)$.
\end{lemma*}

\begin{proof}[Proof]
Given $\varepsilon>0$, choose entire codes $W_T,W_O\in M$ such that
$$\TreeBody{T}\IncludedIn A\IncludedIn U(O),\qquad
\mu(\SetDifference{U(O)}{\TreeBody{T}})<\varepsilon.$$
Here $T$ is downward closed and $U(O)$ is the open set coded by $O$.
The avoidance construction in §{sec:internal-finite-measure-bounds} gives a downward-closed tree $S$
with $W_S\in M$ and $\TreeBody{S}=U(O)^c$. Restricting the two inclusions to internal points gives
$$\InternalTreeBody{M}{T}\IncludedIn X
\IncludedIn\SetDifference{Y_M}{\InternalTreeBody{M}{S}}.$$
Monotonicity, the complement formula, and the closed-value identities yield
$$\mu(\TreeBody{T})\le\nu(X)\le1-\mu(\TreeBody{S})=\mu(U(O)).$$
The external value $\mu(A)$ lies in the same interval, whose length is
$\mu(\SetDifference{U(O)}{\TreeBody{T}})<\varepsilon$.
Since $\varepsilon$ is arbitrary, the two values coincide.
\end{proof}

Let $c$ be a valid Borel code with its label graph in $M$. Write $A$ for its full external
interpretation on Cantor space and $X=\BorelInterpretation{c}{M}$ for its internal interpretation there.
For codes using the standard Baire-cylinder labels, this means first evaluating those same labels and
then intersecting with $Y_M$. Labels whose cylinders have no binary points contribute the empty set.
The internal interpretation construction and bounded Separation give $X\in M$.

\begin{theorem*}[\termdefine{Identification of the internal Borel measure}]
Assume the internal countable-additivity and fair-coin cylinder clauses of
§{sec:internal-finite-measure-laws}, and assume $X\in D$. Then
$$\nu(X)=\mu(A),\qquad
\MeasureValueCode{F}{X}=\NonnegativeRealCut{\mu(A)}.$$
In particular, the entire value code of the internal measure is the code constructed in
§{sec:internal-borel-measure-cut}.
\end{theorem*}

\begin{proof}[Proof]
The internal interpretation has the point-membership characterization required by the lemma.
§{sec:internal-approximation-errors} supplies the two-sided approximation codes, including their
external inclusions; their construction uses the inclusion transfer in §{sec:internal-closed-inclusions}.
§{sec:internal-finite-measure-laws} supplies the closed-value identities from the measure axioms.
The lemma therefore identifies the decoded value. Validity of $\MeasureValueCode{F}{X}$ and the
encoding-decoding identity in §{sec:internal-borel-measure-cut} identify the whole code.
\end{proof}

\begin{corollary*}[\termdefine{The usual measure has the internal rational cut}]
Let $B$ be the Baire-space interpretation used as the parameter in
§{sec:internal-borel-measure-cut}, and let $X$ be its restriction to $Y_M$. For $a,b\in\omega$ with $b>0$,
$$M\models L(B,a,b)\quad\longleftrightarrow\quad \frac ab<\nu(X).$$
\end{corollary*}

\begin{proof}[Proof]
The lower-cut theorem makes the left side equivalent to $a/b<\mu(A)$.
Substitute the value identity just proved. Thus the rational-cut definition and the value supplied by
the model's measure graph agree, including the case of measure zero.
\end{proof}

