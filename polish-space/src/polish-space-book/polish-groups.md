# Polish Groups {#sec:polish-groups}
\index{Polish group}

\begin{mathmeta}
  \define{InfiniteSymmetricGroup}
\end{mathmeta}

<!-- formalization: skip-begin (chapter motivation) -->

Polish groups are the bridge from definable sets to definable classification problems. A group action packages the
symmetries of a mathematical object, and its orbit equivalence relation is the quotient one would like to classify. The
topology on the group records whether those symmetries can be approximated by countable information, which is exactly
the scale descriptive set theory can control.

The chapter also supplies the main source of non-classification theorems used later. Smooth actions yield concrete
invariants; logic actions yield classification by countable structures; turbulent actions show that no such countable
invariant system can work. This is why Polish-group actions are the natural entry point to invariant descriptive set
theory and to the Borel-reducibility hierarchy of §{sec:borel-reducibility}.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter overview, references, and proof scope) -->
Many of the equivalence relations classified in §{sec:borel-reducibility} arise as orbit relations of group actions:
isomorphism of countable structures is the orbit relation of the infinite symmetric group
$\InfiniteSymmetricGroup:=\mathrm{Sym}(\NN)$ acting on the Polish space of countable structures, unitary equivalence of
self-adjoint operators is an orbit relation for the unitary group, and so on. Working with such actions descriptively
requires that the acting groups be Polish and that the actions be Borel-isomorphic to continuous ones — this is what
makes orbit relations analytic and what makes the regularity machinery of Polish-space theory available for them. The
systematic reference is [@Gao2009] and [@BeckerKechris1996]; the obstruction theory for classifiability by countable
structures is developed in [@Hjorth2000].

Proof scope: this chapter proves the local Vaught-transform identities, the elementary facts about
\termforwardas{logic action}{logic actions}, analyticity of orbit relations, and Effros's orbit theorem.
For Becker--Kechris it imports the Polish basis construction and proves continuity of the resulting action.
It proves the Lopez--Escobar theorem by constructing formulas for relativized Vaught transforms.
Hjorth's turbulence theorem is recorded as an external theorem,
with its precise role stated where it appears.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

Use Baire category from §{sec:baire-category}, Polish refinements from §{sec:polish-topology-refinement}, and
analytic projections from §{sec:analytic-sets}. For logic actions, first review structures and satisfaction in
§{sec:fol-language}; the completeness and incompleteness proofs are not needed for that entry. Begin with the
group examples, Vaught transforms, and continuous presentations of Borel actions. The countable-graph case
study shows how these tools code an actual classification problem. Turbulence and the operator examples can be
revisited after §{sec:borel-reducibility}. The goal is to recognize when isomorphism is an orbit relation and
which topology makes its symmetry data manageable.

<!-- formalization: skip-end -->

## Definition and Examples {#sec:polish-groups-defn}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{F}{Nat}
\end{mathmeta}

A \termdefine{Polish group} is a topological group $G$ whose underlying topological space is Polish. <!--
formalization: skip-begin (引用・背景説明・読書案内:
Polish群の定義と完全な整合距離の存在はPolishGroupProse.polish_group_specへ接続した。
残るBirkhoff–KakutaniはGao §2.2を引用する外部入力、
左不変性を同時に仮定できないという注意はここで具体的な反例・証明を展開しない背景説明。)
--> By the
\termdefine{Birkhoff--Kakutani theorem}, every first-countable Hausdorff topological group admits a left-invariant
compatible metric [@Gao2009, §2.2].<!--
formalization: skip-end
-->  For a Polish group a complete compatible metric exists by Polishness, <!--
formalization: skip-begin (引用・背景説明・読書案内:
Polish群の定義と完全な整合距離の存在はPolishGroupProse.polish_group_specへ接続した。
残るBirkhoff–KakutaniはGao §2.2を引用する外部入力、
左不変性を同時に仮定できないという注意はここで具体的な反例・証明を展開しない背景説明。)
--> although it
need not also be left-invariant.<!--
formalization: skip-end
-->

<!-- formalization: skip (examples introduction) -->
\begin{mathmeta}
  \define{PadicField,PadicIntegers}
\end{mathmeta}
Standard examples:

*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    Cantor群の座標wise xor・compact/Polish additive group・有限零座標の開部分群基、
    有限台置換の可算稠密族とS_inftyのinverse-pairによるPolish性、Aut(M)のPolish閉部分群を実際の証明へ接続した。
    未リンクのLie/Banach/SO(3)/unitary例は局所証明を提示しない例示であり、p-adic体・整数環のcomplete
    metric/dense Q/open compact subgroup/baseはSutherland Lectures
    8–9から引用する標準局所体の外部入力。)
    --> $\seqPower{\R}{n}$ under addition, $S^1$ under multiplication, every connected Lie group, every separable Banach
    space under addition, every finite or countable discrete group.
    A concrete compact nonabelian example is $SO(3)$, the group of rotations of $\seqPower{\R}{3}$.<!--
    formalization: skip-end
    -->
*   The \termdefine{Cantor group}: $\CantorSpace$ with coordinate-wise addition modulo $2$ and the product topology.
    It is a compact Polish abelian group. Requiring finitely many coordinates to be $0$ gives its basic open
    subgroups at the identity.
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    Cantor群の座標wise xor・compact/Polish additive group・有限零座標の開部分群基、
    有限台置換の可算稠密族とS_inftyのinverse-pairによるPolish性、Aut(M)のPolish閉部分群を実際の証明へ接続した。
    未リンクのLie/Banach/SO(3)/unitary例は局所証明を提示しない例示であり、p-adic体・整数環のcomplete
    metric/dense Q/open compact subgroup/baseはSutherland Lectures
    8–9から引用する標準局所体の外部入力。)
    --> For a prime $p$, the additive group of the \termdefineas{p-adic numbers}{$p$-adic numbers}
    $\PadicField{p}$, obtained by completing $\QQ$ for the $p$-adic absolute value.
    The \termdefineas{p-adic integers}{$p$-adic integers}
    $\PadicIntegers{p}:=\{x\in\PadicField{p}:\Abs{x}_p\le1\}$ form a compact open subgroup.
    The complete metric $d(x,y)=\Abs{x-y}_p$ and the countable dense subset $\QQ$ make $\PadicField{p}$ Polish.
    The subgroups $p^n\PadicIntegers{p}$ for $n\in\NN$ form a neighborhood base at $0$.
    These standard local-field facts are reviewed in [@Sutherland2021, Lectures 8--9].<!--
    formalization: skip-end
    -->
*   The \termdefine{infinite symmetric group} $\InfiniteSymmetricGroup$ with the topology of pointwise convergence:
    $g_n \to g$
    iff for every $k$, $g_n(k) = g(k)$ eventually, and the same for $g_n^{-1}$. The finitary permutations are dense,
    witnessing separability; a complete metric is built coordinate-wise.
*   $\mathrm{Aut}(M)$ for a countable first-order structure $M$ in the sense of Appendix
    §{sec:appendix-logic}, with the subspace topology from $\InfiniteSymmetricGroup$. This gives the natural
    Polish-group structure on automorphism groups of countable structures.
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    Cantor群の座標wise xor・compact/Polish additive group・有限零座標の開部分群基、
    有限台置換の可算稠密族とS_inftyのinverse-pairによるPolish性、Aut(M)のPolish閉部分群を実際の証明へ接続した。
    未リンクのLie/Banach/SO(3)/unitary例は局所証明を提示しない例示であり、p-adic体・整数環のcomplete
    metric/dense Q/open compact subgroup/baseはSutherland Lectures
    8–9から引用する標準局所体の外部入力。)
    --> The \termdefine{unitary group} $U(\mathcal H)$ of a separable Hilbert space, with the strong operator topology:
    $U_n\to U$
    iff $\Norm{U_n\xi-U\xi}\to0$ for every $\xi\in\mathcal H$.<!--
    formalization: skip-end
    -->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次の局所コンパクト性とnon-Archimedean性を予告する見出し相当の導入。定義や局所証明はこの文の後で別に対応している。)
--> Two structural dividing lines determine the descriptive behavior of orbit relations.<!--
formalization: skip-end
-->

A Polish group is \termdefineas{locally compact group}{locally compact} iff its identity has a compact neighborhood.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
identityのcompact
neighborhoodによる局所コンパクト性の定義・同値はPolishGroupProse.locallyCompact_iff_identityへ
接続した。残るLie群・unitary群・proper action等は証明付きの例ではなく、既出・標準的な群を比較する文脈上の例示。
局所的な構成や後続の証明の補題としては用いない。)
--> Lie groups and $\seqPower{\R}{n}$ are locally compact. The groups $\InfiniteSymmetricGroup$ and
$U(\mathcal H)$ for an infinite-dimensional separable Hilbert space are not. Automorphism groups of countable
structures can fall on either side of this distinction. Proper actions of locally compact groups have closed
orbits and Borel orbit relations.<!--
formalization: skip-end
-->

A Polish group is \termdefine{non-Archimedean} if it admits a neighborhood base at the identity consisting of *open
subgroups*.

<!-- formalization: skip (comparison of the preceding illustrative examples) -->
The Cantor group, $\PadicIntegers{p}$, and $\PadicField{p}$ are non-Archimedean.
The first two are compact, whereas $\PadicField{p}$ is locally compact but not compact.

For a subset of an open subspace, being meager in that subspace is equivalent to being meager in the ambient space.
Indeed, nowhere dense sets remain nowhere dense when included from a subspace, and intersecting a nowhere dense set
with an open subspace preserves relative nowhere density. Passing to countable unions gives the equivalence.
We use this to pass between relative and ambient category in the following proofs.

\begin{lemma*}[\termdefineas{Baire-property localization}{Baire-property localization}]
Let $A$ have the \termuse{Baire property} in a topological space, and let $U$ be open. If $A\cap U$ is non-meager in
$U$, then some nonempty open $V\IncludedIn U$ satisfies that $A\cap V$ is comeager in $V$.
\end{lemma*}

\begin{proof}[Proof]
Choose an open $O$ such that $A\mathbin{\triangle} O$ is meager. The set $O\cap U$ must be nonempty, since otherwise
$A\cap U$ would be meager. Take $V=O\cap U$. The set $\SetDifference{V}{A}$ is contained in
$A\mathbin{\triangle} O$, so it is meager in the ambient space and also in the open subspace $V$.
Thus $A\cap V$ is comeager in $V$.
\end{proof}

\begin{lemma*}[\termdefineas{Pettis theorem}{Pettis}]
If $A$ is a non-meager subset of a Polish group $G$ and has the Baire property, then $A^{-1}A$ contains an open
neighborhood of the identity.
\end{lemma*}

\begin{proof}[Proof]
By \termuse{Baire-property localization}, choose a nonempty open $U$ in which $A$ is comeager, and choose $g\in U$.
Set
$$W:=\{h\in G:gh\in U\}.$$
Left translation is a homeomorphism, so $W$ is open and contains the identity. For $h\in W$, put
$$H:=U\cap Uh^{-1},\qquad
N:=\SetDifference{U}{A}\;\cup\;(\SetDifference{U}{A})h^{-1}.$$
The open set $H$ is nonempty because it contains $g$. The set $\SetDifference{U}{A}$ is meager in $G$ by the
open-subspace observation above. Right translation preserves meagerness, so $N$ is meager.
Since a nonempty open subset of the Baire space $G$ cannot be meager, choose $a\in\SetDifference{H}{N}$.
Then $a\in A$ and $ah\in A$, hence
$$h=a^{-1}(ah)\in A^{-1}A.$$
Thus $W\IncludedIn A^{-1}A$.
\end{proof}

\begin{corollary*}[\termdefineas{closedness of Polish subgroups}{Polish subgroups are closed}]
A subgroup $H$ of a Polish group $G$ is closed whenever $H$, with the subspace topology, is Polish.
\end{corollary*}

\begin{proof}[Proof]
Let $K=\Closure{H}$, a closed subgroup of $G$ and hence a Polish group. By Alexandrov's theorem in
§{sec:alexandrov-theorem}, $H$ is a dense $\Gdelta$ subset of $K$, so it has the Baire property and is non-meager in
$K$.
Pettis's theorem gives an identity neighborhood in $K$ contained in $H^{-1}H=H$.
Translating this neighborhood by elements of $H$ shows that $H$ is open in $K$. Its other cosets are open as well,
so $H$ is also closed in $K$. As it is dense there, $H=K$, which proves that $H$ is closed in $G$.
\end{proof}

\begin{theorem*} For a Polish group $G$, the following are equivalent.

\begin{enumerate}
\item $G$ is non-Archimedean.
\item $G$ is topologically isomorphic to a closed subgroup of $\InfiniteSymmetricGroup$.
\item $G$ is topologically isomorphic to $\mathrm{Aut}(M)$ for some countable first-order structure $M$.
\end{enumerate}

\end{theorem*}

\begin{proof}[Proof] First suppose $H\leq \InfiniteSymmetricGroup$ is closed. The topology of $\InfiniteSymmetricGroup$
has a neighborhood base at the identity consisting of pointwise stabilizers of finite sets,
$$\{\sigma\in\InfiniteSymmetricGroup:\restrict{\sigma}{F}=\mathrm{id}_F\}.$$
Intersecting these stabilizers with $H$ gives a neighborhood base of open subgroups in $H$, so $H$ is non-Archimedean.

For a countably infinite structure, identify its universe with $\NN$. Its automorphism group is a closed
subgroup of $\InfiniteSymmetricGroup$. To see this, fix a finite tuple $\bar a$.
For an interpreted function $f$, the condition $\sigma(f(\bar a))=f(\sigma\bar a)$ depends only on the values of
$\sigma$ at the entries of $\bar a$ and at $f(\bar a)$. For an interpreted relation $R$, the condition
$R(\sigma\bar a)\iff R(\bar a)$ depends only on the values at the entries of $\bar a$.
Failure of either condition therefore defines an open set of permutations, so the complement of
$\mathrm{Aut}(M)$ is open. This also covers constants, viewed as functions of arity zero.
A finite structure has a finite discrete automorphism group, which embeds as a closed subgroup by permuting a
finite subset of $\NN$ and fixing all remaining points.

Conversely, let $H\leq\InfiniteSymmetricGroup$ be closed. Build a countable relational language with one $n$-ary
relation symbol $R_O$ for each $H$-orbit $O\IncludedIn \NN^n$, over all $n\geq 1$.
For each arity, the set of orbits is a quotient of the countable set $\NN^n$, so there are only countably many
symbols in total. Let $M_H$ be the structure on universe $\NN$ in which $R_O(\bar a)$ holds exactly when $\bar a\in O$.
Every element of $H$ preserves all these orbit relations, so $H\leq\mathrm{Aut}(M_H)$.
If $\sigma\in\mathrm{Aut}(M_H)$ and $F=\{a_1,\ldots,a_n\}$ is finite and nonempty, then
$\sigma(a_1,\ldots,a_n)$ lies in the same $H$-orbit as $\Tuple{a_1,\ldots,a_n}$.
Hence some $h\in H$ agrees with $\sigma$ on $F$. For the empty set, the identity already gives such agreement.
Every basic neighborhood of $\sigma$ therefore meets $H$, so $\sigma$ belongs to the closure of $H$ in
$\InfiniteSymmetricGroup$. Since $H$ is closed, $\sigma\in H$. Thus $H=\mathrm{Aut}(M_H)$.

For the remaining implication, we use the following description of permutation groups on countable sets.
For a countable discrete set $X$, the pointwise-convergence topology on $\mathrm{Sym}(X)$ has basic neighborhoods
$$N(\sigma,F):=\{\tau\in\mathrm{Sym}(X):\forall x\in F,\ \tau(x)=\sigma(x)\},\quad F\IncludedIn X\text{ finite}.$$
Inversion is continuous because $\tau^{-1}(x)=y$ is equivalent to $\tau(y)=x$. Multiplication is continuous because
fixing the values of $\tau$ on $F$ and of $\sigma$ on $\tau(F)$ fixes the values of $\sigma\tau$ on $F$.
The map $\sigma\mapsto\Pair{\sigma}{\sigma^{-1}}$ is a homeomorphism onto
$$\{\Pair{f}{h}\in\seqPower{X}{X}\times\seqPower{X}{X}:
  \forall x\in X,\ f(h(x))=x\text{ and }h(f(x))=x\}.$$
This set is closed: for each $x$, both equations are closed conditions, since evaluation is continuous when $X$
is discrete. The countable products are Polish, so $\mathrm{Sym}(X)$ is Polish as well.

It remains to embed an arbitrary non-Archimedean Polish group. Choose a decreasing countable neighborhood base
$\Sequence{V_n}{n\in\omega}$
at the identity consisting of open subgroups with $\bigcap_n V_n=\{e\}$.
Each quotient $G/V_n$ is discrete and countable,
since its cosets are pairwise disjoint open subsets of the separable space $G$. Let
$$X=\ExternalDisjointUnion_{n\in\NN} G/V_n,$$
a countably infinite set: it is countable as a countable union of countable sets, and the distinguished cosets
$\Pair{n}{V_n}$ give an injection of $\NN$ into it. Let $G$ act on $X$ by left translation,
$$\pi(g)\Pair{n}{aV_n}:=\Pair{n}{gaV_n}.$$
For each fixed $\Pair{n}{aV_n}$, this coordinate map is continuous as the composite of right translation by $a$,
the quotient map, and inclusion into the tagged summand. By the description of the topology above, we obtain a
continuous homomorphism
$$\pi:G\to\mathrm{Sym}(X)\cong\InfiniteSymmetricGroup.$$
It is injective because the intersection of the $V_n$ is trivial. Its topology is the original one because the
stabilizer of $\Pair{n}{V_n}$ pulls back to $V_n$: these stabilizers are open in the permutation group, and their
preimages form a neighborhood base at the identity in $G$. Translating this base recovers the topology at every point.

Finally, the preceding paragraph makes $\pi(G)$ a Polish subgroup of $\mathrm{Sym}(X)$ with the inherited topology.
By \termuse{closedness of Polish subgroups}, its image is closed. Thus $G$ is topologically isomorphic to a closed
subgroup of $\InfiniteSymmetricGroup$.
\end{proof}

<!-- formalization: skip (contextual consequence of the non-Archimedean characterization) -->
This characterization makes the classification of countable structures uniformly a question about
$\InfiniteSymmetricGroup$-actions and their restrictions, and is the structural reason logic actions sit at the center
of invariant descriptive set theory [@BeckerKechris1996, §1.5].

### Borel and Continuous Actions {#sec:polish-groups-actions}

A \termdefine{Borel action} of a Polish group $G$ on a standard Borel space $X$ is a Borel map $\alpha : G \times X \to
X$ satisfying $\alpha(e, x) = x$ and $\alpha(gh, x) = \alpha(g, \alpha(h, x))$. The \termdefine{continuous action}
version requires $\alpha$ to be continuous as a map of topological spaces and requires $X$ to be Polish.

## Vaught Transforms {#sec:vaught-transforms}
The \termdefineas{Vaught transform}{Vaught transforms} [@Vaught1974] are the main tool for translating
Baire-category statements about $G$ into Borel statements about $X$. They convert a Borel set $A \IncludedIn
X$ into a Borel
set
encoding "many group elements move a point into $A$."

Fix a continuous action of a Polish group $G$ on a Polish space $X$, a set $A \IncludedIn X$, and a nonempty open $U
\IncludedIn G$. Define
$$\begin{aligned}
A^{*U} &:= \{x \in X : \{g \in U : g \cdot x \in A\} \text{ is non-meager in } U\}, \\
A^{\triangle U} &:= \{x \in X : \{g \in U : g \cdot x \in A\} \text{ is comeager in } U\}.
\end{aligned}$$
The two transforms are dual:
$$\complement(A^{*U}) = (\complement A)^{\triangle U},$$
since a subset of $U$ is meager if and only if its complement in $U$ is a \termuse{comeager set}.
When $U = G$ we write simply $A^*$ and $A^{\triangle}$.

\begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
\IncludedIn
G$ be nonempty open.

\begin{enumerate}
\item For $1\le\alpha<\omegaOneOrd$, if $A\in\bSigma^0_\alpha$, then
$A^{*U}\in\bSigma^0_\alpha$ and $A^{\triangle U}\in\bPi^0_{\alpha+1}$.
If $A\in\bPi^0_\alpha$, then $A^{*U}\in\bSigma^0_{\alpha+1}$ and $A^{\triangle U}\in\bPi^0_\alpha$.
In particular, either transform raises the Borel rank by at most one.
\item $A^*$ and $A^{\triangle}$ are $G$-invariant.
\item If $A$ is open, then $A \IncludedIn A^*$.
\item If $\mathcal U$ is a countable basis for $G$ and the $A_n$ are Borel, then the two direct operation rules and the
two localization rules are
\end{enumerate}
$$
\begin{aligned}
\Big(\bigcup_n A_n\Big)^{*U}
  &= \bigcup_n A_n^{*U},
&
\Big(\bigcap_n A_n\Big)^{\triangle U}
  &= \bigcap_n A_n^{\triangle U},\\
\Big(\bigcup_n A_n\Big)^{\triangle U}
  &= \bigcap_{\substack{W\in\mathcal U\\\emptyset\ne W\IncludedIn U}}
     \bigcup_n A_n^{*W},
&
\Big(\bigcap_n A_n\Big)^{*U}
  &= \bigcup_{\substack{W\in\mathcal U\\\emptyset\ne W\IncludedIn U}}
     \bigcap_n A_n^{\triangle W}.
\end{aligned}
$$

\end{lemma*}

\begin{proof}[Proof] We first prove the operation rules and invariance; the Borel-rank claim then follows by induction.

The duality
$$\complement(A^{*U})=(\complement A)^{\triangle U}$$
is immediate from the definitions: a subset of the Baire space $U$ is non-meager iff its complement is not comeager.

For countable unions,
$$
x\in\Big(\bigcup_n A_n\Big)^{*U}
$$
means that
$$
\{g\in U:g\cdot x\in\bigcup_nA_n\}
=\bigcup_n\{g\in U:g\cdot x\in A_n\}
$$
is non-meager in $U$. A countable union is non-meager iff one term is non-meager, since countable unions of meager sets
are meager. Hence
$$
\Big(\bigcup_n A_n\Big)^{*U}=\bigcup_n A_n^{*U}.
$$
The countable-intersection rule for $\triangle$ follows by applying duality to the preceding identity.

The localization rules depend only on the Baire property of the sections. Let $C\IncludedIn G$ have the Baire
property. If $C\cap U$ is non-meager in $U$, Baire-property localization gives a nonempty open subset of $U$
on which $C$ is comeager. Choose a nonempty basic open $W$ inside that subset; then $C\cap W$ is comeager in $W$.
Conversely, if $C\cap W$ is comeager in a nonempty basic $W\IncludedIn U$ but $C\cap U$ is meager, both terms in
$$W=(C\cap W)\cup(\SetDifference{W}{C})$$
are meager, contradicting that the nonempty open subspace $W$ is a Baire space.

Also, $C\cap U$ is comeager in $U$ if and only if $C\cap W$ is non-meager in every nonempty basic $W\IncludedIn U$.
For the forward direction, the same decomposition of $W$ rules out meagerness of $C\cap W$.
For the converse, if $\SetDifference{U}{C}$ were non-meager, apply the preceding localization result to the complement
of $C$. It gives a nonempty basic $W\IncludedIn U$ on which $C\cap W$ is meager, a contradiction.

Apply the second equivalence to the section of $\bigcup_nA_n$, then use the direct union rule inside each basic $W$.
This gives the first localization formula. Apply the first equivalence to the section of $\bigcap_nA_n$ and use the
direct intersection rule for comeagerness to obtain the second formula. Borel sections have the Baire property, so
these arguments apply to the sets in the statement.

For (2), let $h \in G$ and $x \in A^*$. The set $\{g : g \cdot (h \cdot x) \in A\} = \{g : (gh) \cdot x \in A\}$ is the
right-translate by $h^{-1}$ of $\{g : g \cdot x \in A\}$, hence still non-meager in $G$, since translation is a
homeomorphism. This proves invariance of $A^*$. Applying the same result to the complement and using duality proves
invariance of $A^{\triangle}$.

For (3), if $A$ is open and $x \in A$, then $\{g : g \cdot x \in A\}$ contains the open neighborhood of $e$ obtained by
continuity of the action at $\Pair{e}{x}$, hence is non-meager.

It remains to justify Borelness. Let $A$ be open. The set
$$
R_A:=\{\Pair{x}{g}\in X\times U:g\cdot x\in A\}
$$
is open. For fixed $x$, the section $(R_A)_x$ is open in $U$, and an open subset of a Baire space is non-meager iff it
is nonempty. Thus
$$
A^{*U}=\{x:\exists g\in U,\ g\cdot x\in A\}.
$$
The right-hand side is open: for each fixed $g\in U$, the set $\{x:g\cdot x\in A\}$ is open by continuity, and
$A^{*U}$ is their union. Moreover, the section of an open $A$ is open in $U$, so it is comeager exactly when it is
dense. Therefore
$$
A^{\triangle U}
=\bigcap_{\substack{W\in\mathcal U\\\emptyset\ne W\IncludedIn U}}A^{*W},
$$
which is $\bPi^0_2$.

We now prove simultaneously, for every open $U$, that the non-meager transform preserves $\bSigma^0_\alpha$
and the comeager transform preserves $\bPi^0_\alpha$, for $1\le\alpha<\omegaOneOrd$.
The open case and its dual give the base. Suppose $\alpha>1$ and the assertion holds at every earlier level.
Write $A\in\bSigma^0_\alpha$ as $A=\bigcup_n C_n$, where $C_n\in\bPi^0_{\beta_n}$ and
$1\le\beta_n<\alpha$. Baire-property localization gives
$$
C_n^{*U}=\bigcup_{\substack{W\in\mathcal U\\\emptyset\ne W\IncludedIn U}}C_n^{\triangle W}.
$$
The induction hypothesis puts every term on the right in $\bPi^0_{\beta_n}$, so the countable union belongs to
$\bSigma^0_{\beta_n+1}$. Since $\beta_n+1\le\alpha$, monotonicity of the hierarchy and the direct union rule give
$$
A^{*U}=\bigcup_n C_n^{*U}\in\bSigma^0_\alpha.
$$
Duality now gives preservation of $\bPi^0_\alpha$ by the comeager transform.
The argument permits the $\beta_n$ to vary and therefore covers limit stages as well.

Finally, the inclusions $\bSigma^0_\alpha\IncludedIn\bPi^0_{\alpha+1}$ and
$\bPi^0_\alpha\IncludedIn\bSigma^0_{\alpha+1}$ give the two remaining bounds in (1).
Thus, for either input class at level $\alpha$, the non-meager transform belongs to
$\bSigma^0_{\alpha+1}$ and the comeager transform to $\bPi^0_{\alpha+1}$.
Every Borel set lies at a countable level, so this also proves Borelness of both transforms.
\end{proof}

\begin{lemma*}[\termdefineas{Borel category quantifiers}{Borel category quantifiers}]
Let $G$ be Polish, let $X$ be a standard Borel space, and let $R\IncludedIn G\times X$ be Borel. For every nonempty
open $U\IncludedIn G$, both sets
$$
\{x:R_x\cap U\text{ is non-meager in }U\},
\qquad
\{x:R_x\cap U\text{ is comeager in }U\}
$$
are Borel, where $R_x:=\{g:\Pair{g}{x}\in R\}$.
\end{lemma*}

\begin{proof}[Proof]
Choose a Polish topology presenting the standard Borel structure of $X$. Prove both assertions simultaneously for
all open $U$ by induction on the Borel construction of $R$. For open $R$, every section $R_x\cap U$ is open.
Its non-meagerness is equivalent to nonemptiness, an open condition on $x$; its comeagerness is equivalent to meeting
every nonempty basic $W\IncludedIn U$, a countable intersection of open conditions.

Complements exchange the two category quantifiers, so the induction hypothesis passes to complements.
For $R=\bigcup_n R_n$, the non-meager quantifier is the countable union of the corresponding quantifiers for $R_n$.
For the comeager quantifier, use the localized union rule: take the intersection over nonempty basic
$W\IncludedIn U$ of the union of the non-meager quantifiers for $R_n$ on $W$.
Each section is Borel and hence has the Baire property, as required for that rule. The induction hypothesis applies
to every such $W$, and the basis is countable, so this is again a Borel set.
This completes the Montgomery--Novikov category-quantifier argument.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Vaught-transformの議論の出典Gao §3.2を示す書誌情報。局所的な数学の主張ではない。)
--> For this argument, see [@Gao2009, §3.2].<!--
formalization: skip-end
-->

<!-- formalization: skip (transition and applications of Vaught transforms) -->
The Vaught transform is the categorical analogue of the measure-theoretic operation "saturate up to a null set." It is
used below to refine topologies, prove the Becker--Kechris and Effros theorems, and produce $G$-invariant Borel sets
from arbitrary Borel sets.

## Making Borel Actions Continuous {#sec:polish-group-continuization}

Every Borel action admits a compatible Polish topology that makes the action continuous. We use the Polish
basis construction from the proof of [@BeckerKechris1996, Theorem 5.2.1] as an external input, and verify the
continuity step below. The old topology on the space is not retained as an open subbasis; the new subbasis consists
of Vaught transforms.

<!-- formalization: skip (Becker--Kechris Polish basis theorem, cited external input) -->
\begin{theorem*}[\termdefineas{Becker--Kechris theorem}{Becker--Kechris}] Every Borel action of a Polish group $G$ on a
standard Borel space $X$ admits a Polish topology on $X$ generating the same Borel $\sigma$-algebra and making $\alpha$
continuous.

\end{theorem*}

\begin{proof}[Proof] We use a right-handed notation for the Vaught transform. For an open $U\IncludedIn G$ and a Borel
$A\IncludedIn X$, put
$$
U\star A:=\{x\in X:\{u\in U:u^{-1}\cdot x\in A\}\text{ is non-meager in }U\}.
$$
Thus $U\star A=A^{*U^{-1}}$ in the notation of §{sec:vaught-transforms}. The Borel-action form of Vaught's lemma says
that $U\star A$ is Borel whenever $A$ is Borel. Indeed,
$$
R_A:=\{\Pair{u}{x}:u^{-1}\cdot x\in A\}
$$
is Borel, and the non-meager category quantifier applied to $R_A\cap(U\times X)$ is Borel by the preceding lemma.

Choose a countable basis $\mathcal U$ for $G$, closed under finite intersections. We will use the following immediate
product-refinement fact: if $O$ is nonempty open and $gO\IncludedIn U$ with $U$ open, then there are
$V,W_0\in\mathcal U$ such that
$g\in V$, $\emptyset\ne W_0\IncludedIn O$, and $VW_0\IncludedIn U$.
Choose $w\in O$. Continuity of multiplication gives open neighborhoods $V'$ of $g$ and $W'$ of $w$
with $V'W'\IncludedIn U$. Choose basic neighborhoods $V\IncludedIn V'$ of $g$ and
$W_0\IncludedIn W'\cap O$ of $w$. These have the required properties.

<!-- formalization: skip-begin (Polish basis construction explicitly imported from Becker--Kechris) -->
We need the following basis construction. There is a countable family $\mathcal A$ of Borel subsets of $X$ such that,
if $\tau$ is the topology generated by the subbasis
$$
\mathcal S:=\{U\star A:U\in\mathcal U,\ A\in\mathcal A\},
$$
then:

\begin{enumerate}
\item $\tau$ is Polish;
\item $\mathcal B(\tau)$ is the original Borel $\sigma$-algebra on $X$;
\item $\mathcal A$ is a Boolean algebra, and whenever $U\in\mathcal U$ and $A\in\mathcal A$, both $U\star A$ and its
complement belong to $\mathcal A$.
\end{enumerate}

The existence of such a family is the Polish basis construction in
[@BeckerKechris1996, proof of Theorem 5.2.1]. We invoke that construction here, including its verification of
metrizability, completeness, and preservation of the Borel structure. Merely closing a countable Borel generator
under Boolean operations and Vaught transforms does not establish these properties.

In particular, the Polish topology generated by the transforms must be distinguished from auxiliary refinements
in which the original Borel sets become clopen. A join of such refinements need not be the transform topology,
and may destroy continuity of the action. The cited construction supplies precisely the transform topology with
the three properties above.
<!-- formalization: skip-end -->

It remains to prove that the action is continuous for this topology. It is enough to check the subbasic sets
$U\star A\in\mathcal S$. We claim that
$$
\alpha^{-1}(U\star A)
=\bigcup\{\,V\times(W\star A):V,W\in\mathcal U,\ VW\IncludedIn U\,\}.
$$
First suppose $g\in V$, $x\in W\star A$, and $VW\IncludedIn U$. For non-meagerly many $w\in W$ we have
$w^{-1}\cdot x\in A$. For those $w$, put $u=gw\in U$. Then
$$
u^{-1}\cdot(g\cdot x)=w^{-1}\cdot x\in A,
$$
and the image of a non-meager subset of $W$ under the homeomorphism $w\mapsto gw$ is non-meager in $gW\IncludedIn U$,
hence non-meager in $U$. Thus $g\cdot x\in U\star A$.

Conversely, suppose $g\cdot x\in U\star A$. Then
$$
M:=\{u\in U:u^{-1}\cdot(g\cdot x)\in A\}
$$
is non-meager in $U$. Write
$$C_x:=\{w\in G:w^{-1}\cdot x\in A\}.$$
The identity $(gw)^{-1}\cdot(g\cdot x)=w^{-1}\cdot x$ gives
$$g^{-1}M=C_x\cap g^{-1}U.$$
Left translation is a homeomorphism, so this intersection is non-meager in the open set $g^{-1}U$.
The set $C_x$ is Borel, since the action is Borel. Baire-property localization therefore gives a nonempty open
$O\IncludedIn g^{-1}U$ on which $C_x$ is comeager. Now $gO\IncludedIn U$, so product refinement gives
$V,W_0\in\mathcal U$ with $g\in V$, $\emptyset\ne W_0\IncludedIn O$, and $VW_0\IncludedIn U$.
The set $C_x\cap W_0$ is comeager, hence non-meager, in $W_0$. Thus $x\in W_0\star A$, so $\Pair{g}{x}$ belongs to the
right-hand side.

The displayed identity writes the preimage of each subbasic open set as a union of product-open sets in
$G\times\Pair{X}{\tau}$, because every $W\star A$ is itself subbasic. Therefore
$\alpha:G\times\Pair{X}{\tau}\to\Pair{X}{\tau}$ is continuous. The constructed $\tau$ is Polish and has exactly the
original Borel
$\sigma$-algebra, as required.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
同一Borel構造の下で同じ写像がBorel reductionであることの同値と、同じ作用のorbit
relationをidentityが双方向に保つことを実際の補題へ接続した。未リンク部分は直前に引用入力から構成したcompatible
Polish topologyの結論を再述し、continuous/Borel actionsの結果の読む方を案内する文で、新たな作用やbasis
constructionの証明ではない。)
--> The Becker--Kechris theorem lets us study a Borel action on a standard Borel space by choosing a compatible Polish
topology that makes the action continuous.<!--
formalization: skip-end
-->  This change preserves the $\sigma$-algebra, the orbit equivalence relation,
and Borel reducibility. <!--
formalization: skip-begin (引用・背景説明・読書案内:
同一Borel構造の下で同じ写像がBorel reductionであることの同値と、同じ作用のorbit
relationをidentityが双方向に保つことを実際の補題へ接続した。未リンク部分は直前に引用入力から構成したcompatible
Polish topologyの結論を再述し、continuous/Borel actionsの結果の読む方を案内する文で、新たな作用やbasis
constructionの証明ではない。)
--> Thus results formulated purely in terms of this Borel structure transfer from continuous
Polish-group actions to Borel actions. This is what allows §{sec:borel-reducibility} to say "Polish-group action"
without specifying Borel
or continuous.<!--
formalization: skip-end
-->

## Logic Actions {#sec:logic-actions}

A basic example of a Polish-group action in classification theory is the action of $\InfiniteSymmetricGroup$ on
the space of countable structures. Fix a countable first-order language $L$ consisting of relation symbols $R_i$
of arities $n_i$ and function symbols $f_j$ of arities $m_j$; constants are zero-ary functions.
The space of $L$-structures with universe
$\NN$ is
$$\mathrm{Mod}_L \;:=\; \prod_i 2^{\funcspace{n_i}{\NN}} \;\times\; \prod_j \funcspace{\funcspace{m_j}{\NN}}{\NN}.$$
Equip this space with the product topology on the individual table entries, indexed by a symbol and a tuple of
natural numbers of its arity. There are countably many such entries, each taking values in the discrete space $2$
or $\NN$, so $\mathrm{Mod}_L$ is Polish.
For positive arities, the displayed factors are Cantor or Baire spaces; zero-ary symbols instead give finite
or countable discrete factors. A point $M \in \mathrm{Mod}_L$ specifies the truth table of each relation symbol
and the value table of each function symbol. Conversely, any choice of these tables defines a unique $L$-structure
on $\NN$; there are no additional compatibility conditions.

The \termdefine{logic action} of $\InfiniteSymmetricGroup$ on $\mathrm{Mod}_L$ is the action by permutation of the
universe: for $\sigma \in \InfiniteSymmetricGroup$ and $M \in \mathrm{Mod}_L$,
$$(\sigma \cdot M)(R_i)\Tuple{a_1, \ldots, a_{n_i}} := M(R_i)\Tuple{\sigma^{-1}(a_1), \ldots, \sigma^{-1}(a_{n_i})}.$$
For function symbols one must also relabel the output:
$$(\sigma\cdot M)(f_j)\Tuple{a_1,\ldots,a_{m_j}}
:=\sigma\bigl(M(f_j)\Tuple{\sigma^{-1}(a_1),\ldots,\sigma^{-1}(a_{m_j})}\bigr).$$

\begin{proposition*}
The logic action is continuous, and its orbit equivalence relation is
\termdefine{isomorphism of countable structures}:
$$M \cong_L N \quad\Longleftrightarrow\quad N \in \InfiniteSymmetricGroup \cdot M.$$
Moreover, $\{\Pair{M}{N}\in\mathrm{Mod}_L\times\mathrm{Mod}_L:M\cong_L N\}$ is analytic.
\end{proposition*}

\begin{proof}
The identity and composition laws follow by substitution into the two definitions above.
For continuity, fix $\Pair{\sigma}{M}$ and an output coordinate with input tuple $\bar a$.
Put $\bar b:=\sigma^{-1}\bar a$, applying the permutation coordinatewise. In a neighborhood of $\sigma$,
require the inverse permutation to agree with $\sigma^{-1}$ on the finitely many entries of $\bar a$.
For a relation symbol, also fix its truth value in $M$ at $\bar b$. These open conditions fix the output bit.
For a function symbol $f_j$, put $c:=M(f_j)(\bar b)$, fix this value in the structure coordinate,
and require the permutation to agree with $\sigma$ at $c$. These open conditions fix the output value $\sigma(c)$.
Thus every output coordinate is continuous, and the action is continuous in the product topology.
For a zero-ary symbol the tuple is empty: a nullary relation needs only its truth value fixed, while a constant
also requires the permutation value at its interpretation to be fixed.

The permutation $\sigma$ is an isomorphism from $M$ to $\sigma\cdot M$, since it preserves the relations and
functions by the defining equations. Conversely, if $\sigma:M\to N$ is an isomorphism, apply its preservation
conditions to $\sigma^{-1}\bar a$. They give the defining equations for $N=\sigma\cdot M$ at every table entry.
Hence the orbits are exactly the isomorphism classes.

In $(\mathrm{Mod}_L\times\mathrm{Mod}_L)\times\InfiniteSymmetricGroup$, put
$$C:=\{\Pair{\Pair{M}{N}}{\sigma}:N=\sigma\cdot M\}.$$
The two maps $\Pair{\Pair{M}{N}}{\sigma}\mapsto N$ and $\Pair{\Pair{M}{N}}{\sigma}\mapsto\sigma\cdot M$ are continuous
into the
Hausdorff space $\mathrm{Mod}_L$, so their equality set $C$ is closed. It is therefore Polish, and its continuous
projection onto $\Pair{M}{N}$ has image exactly the isomorphism relation. This image is analytic by
§{sec:analytic-sets}.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
empty languageでの自明なisomorphismはLogicActions.emptyLanguageIsoに接続済み。
残りは例の位置付けとCantorのback-and-forthという標準定理、Friedman–Stanleyを明示引用する外部完全性結果。
ここでその証明を提示していない。)
--> \begin{mathmeta}
  \forward{BorelReducesTo,EventualRowEqualityER}
\end{mathmeta}
This is a standard example of an orbit equivalence relation for a non-locally-compact Polish group.
The complexity of $\cong_L$ depends on $L$.<!--
formalization: skip-end
-->
For the empty language any bijection witnesses isomorphism, so the relation is trivial.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
empty languageでの自明なisomorphismはLogicActions.emptyLanguageIsoに接続済み。
残りは例の位置付けとCantorのback-and-forthという標準定理、Friedman–Stanleyを明示引用する外部完全性結果。
ここでその証明を提示していない。)
--> For $L=\{<\}$ on dense linear orders without endpoints there is a single class by Cantor's back-and-forth
theorem.
For the graph language, $\cong_L$ is $\bSigma^1_1$-complete as a subset of the product and is Borel-complete:
it is universal under $\BorelReducesTo$ among isomorphism relations of countable structures [@FriedmanStanley1989].<!--
formalization: skip-end
-->

### Lopez--Escobar Theorem {#sec:lopez-escobar-theorem}

\begin{mathmeta}
  \define{LCountableInfinitaryLogic}
  \vars{b,e,k,m,n}{Nat}
\end{mathmeta}

The logic action has an exact syntactic counterpart in the infinitary logic $\LCountableInfinitaryLogic$.
We first specify its formulas and their interpretation.

\begin{definition*}
For each $n\in\omega$, consider formulas whose free variables are among $x_0,\ldots,x_{n-1}$.
They are generated simultaneously for all $n$ by the following rules:
\begin{enumerate}
\item $\bot$, equations between $L$-terms in these variables, and applications of relation symbols to such terms
are formulas in this context.
\item If $\varphi$ is a formula in this context, so is $\neg\varphi$.
\item If every $\varphi_k$, for $k\in\omega$, is a formula in this same context, then
$\bigwedge_{k\in\omega}\varphi_k$ is a formula in this context.
\item If $\psi$ is a formula in the context $x_0,\ldots,x_n$, then $\exists x_n\,\psi$ is a formula
in the context $x_0,\ldots,x_{n-1}$.
\item Only expressions generated by the preceding rules are formulas.
\end{enumerate}
A formula in the empty context is a sentence. Countable disjunction and universal quantification are defined by
De Morgan duality. Thus a countable conjunction must have only finitely many free variables in total,
although its conjuncts need not have a common finite bound on their quantifier depths.
\end{definition*}

Interpretation is defined by structural recursion. Terms and atomic formulas have their usual first-order
interpretations; $\bot$ is false, negation reverses truth, and a countable conjunction holds exactly when all its
conjuncts hold. An existential formula holds under a given assignment exactly when some value for the last variable
makes its body true. This definition applies to any $L$-structure.
Free variables may be renamed or identified: under a map from one finite variable context to another, rename the
variables in each term, commute the operation with negation and conjunction, and keep each newly bound variable fresh.
Structural induction shows that evaluating the renamed formula under an assignment gives the same truth value as
evaluating the original formula under the pulled-back assignment.

\begin{proposition*}
Fix a finite tuple $\bar a$ of natural numbers. For every formula $\varphi$ in the corresponding context,
the set of $M\in\mathrm{Mod}_L$ satisfying $\varphi$ under $\bar a$ is Borel.
In particular, every sentence $\varphi$ defines an isomorphism-invariant Borel set
$$\mathrm{Mod}(\varphi):=\{M\in\mathrm{Mod}_L:M\models\varphi\}.$$
\end{proposition*}

\begin{proof}
For a fixed assignment, the value of each term depends continuously on $M$. For a variable this is constant.
For a function application, first fix the values of its finitely many argument terms in a neighborhood of $M$,
and then fix the single function-table coordinate at that tuple. Induction on terms proves the assertion,
including nested function applications. Equality and relation formulas therefore define clopen sets.

Now use structural induction on formulas. Falsity gives the empty set, negation gives complement,
and countable conjunction gives countable intersection. Existential quantification gives a countable union:
for each $b\in\NN$, extend the fixed assignment by assigning $b$ to the last variable and apply the induction
hypothesis to the body. Thus each satisfaction set is Borel.

An isomorphism preserves term values and atomic truth. Structural induction extends this to negation and countable
conjunction. At an existential quantifier, transport a witness by the isomorphism; the reverse implication uses
its surjectivity. Hence truth is preserved when the assignment is transported by an isomorphism.
Sentences have no assigned free variables, so their satisfaction sets are isomorphism-invariant.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Lopez–Escobarへの歴史的帰属と原論文の出典表示。定理・局所証明そのものは別に対応済み。)
--> The invariant-definability result is due to Lopez--Escobar [@LopezEscobar1965].<!--
formalization: skip-end
-->

\begin{theorem*}[\termdefineas{Lopez--Escobar theorem}{Lopez--Escobar}] If
$A\IncludedIn\mathrm{Mod}_L$ is Borel and invariant under the $\InfiniteSymmetricGroup$ logic action, then there is an
$\LCountableInfinitaryLogic$ sentence $\varphi_A$ such that
$$A=\mathrm{Mod}(\varphi_A).$$

\end{theorem*}

\begin{proof}[Proof]
\begin{mathmeta}
  \define{TupleAgreementCoset}
\end{mathmeta}
We use the relativized Vaught induction. For finite tuples $\bar a$ and $\bar s$ of the same length, put
$$
\TupleAgreementCoset{\bar a}{\bar s}
:=\{\sigma\in\InfiniteSymmetricGroup:\sigma(\bar a)=\bar s\}.
$$
If both tuples are injective, this coset is nonempty: the finite bijection $a_i\mapsto s_i$ extends to a permutation
of $\NN$. The coset is clopen because it imposes finitely many coordinate equalities. The cosets with injective
source and target tuples form a basis: every neighborhood of a permutation contains a finite-agreement cylinder,
obtained by enumerating its finite set of specified inputs as $\bar a$ and their images as $\bar s$.
For every Borel $B\IncludedIn\mathrm{Mod}_L$ and every finite $\bar s$, the induction simultaneously constructs formulas
$\varphi^{\bar s}_{B,*}(\bar x)$ and $\varphi^{\bar s}_{B,\triangle}(\bar x)$ such that
$$
\begin{aligned}
M\models\varphi^{\bar s}_{B,*}(\bar a)
&\quad\Longleftrightarrow\quad
\{\sigma\in \TupleAgreementCoset{\bar a}{\bar s}:\sigma\cdot M\in B\}
   \text{ is non-meager in }\TupleAgreementCoset{\bar a}{\bar s},\\
M\models\varphi^{\bar s}_{B,\triangle}(\bar a)
&\quad\Longleftrightarrow\quad
\{\sigma\in \TupleAgreementCoset{\bar a}{\bar s}:\sigma\cdot M\in B\}
   \text{ is comeager in }\TupleAgreementCoset{\bar a}{\bar s}.
\end{aligned}
$$
The same construction allows repeated entries: an empty coset gives a false non-meager condition and a true
comeager condition. The crucial point is that the coset varies with $\bar a$. Consequently these conditions are
invariant under the diagonal action on $\mathrm{Mod}_L\times\NN^{\Length{\bar s}}$; a fixed basic group neighborhood
would
not have this invariance.

For the basic clopen case, let $B$ be given by finitely many relation-bit and function-value conditions.
Choose a tuple $\bar t=\Tuple{t_0,\ldots,t_{m-1}}$ listing, without repetition, all the entries of $\bar s$ and all the
natural numbers named in these conditions, including function outputs. Write $s_i=t_{e(i)}$ for $i<n$.
Replacing each named value $t_j$ by $y_j$ gives a finite conjunction $\psi(\bar y)$ of atomic or negated atomic
formulas such that
$$M\in B\quad\Longleftrightarrow\quad M\models\psi(\bar t).$$
A relation bit gives $R(y_{j_1},\ldots,y_{j_k})$ or its negation; a function value gives
$f(y_{j_1},\ldots,y_{j_k})=y_\ell$. Nullary symbols and the empty conjunction are allowed.

\begin{mathmeta}
  \define{InverseTupleFormula}
\end{mathmeta}
Define the formula
$$
\begin{aligned}
\InverseTupleFormula{e}{\psi}(\bar x):={}&\exists y_0\cdots\exists y_{m-1}\\
&\Bigl[\bigwedge_{j<k<m}y_j\ne y_k\\
&\qquad\land\bigwedge_{i<n}y_{e(i)}=x_i\land\psi(\bar y)\Bigr].
\end{aligned}
$$
The bound variables are chosen fresh. The free variables of this formula are among $x_0,\ldots,x_{n-1}$.
Finite conjunction and the displayed finite block of quantifiers are built from the constructors above.

For any formula $\psi$ in the context of $\bar t$, the meaning of this construction is
$$
\begin{aligned}
&M\models\InverseTupleFormula{e}{\psi}(\bar a)\\
&\quad\Longleftrightarrow\quad
\exists\sigma\in\TupleAgreementCoset{\bar a}{\bar s}\;
\sigma\cdot M\models\psi(\bar t).
\end{aligned}
$$
Indeed, given such a $\sigma$, put $b_j=\sigma^{-1}(t_j)$. The $b_j$ are distinct and satisfy $b_{e(i)}=a_i$;
isomorphism invariance with the assignment transported by $\sigma$ gives $M\models\psi(\bar b)$.
Conversely, a tuple $\bar b$ satisfying the formula defines a finite bijection $b_j\mapsto t_j$.
Extend it to a permutation $\sigma$. Then $\sigma(\bar a)=\bar s$ and the same invariance gives
$\sigma\cdot M\models\psi(\bar t)$.

For the finite diagram defining $B$, the action section is clopen in $\TupleAgreementCoset{\bar a}{\bar s}$.
A nonempty open subset of this Baire space is non-meager, so its non-meager transform is given by
$\InverseTupleFormula{e}{\psi}$. Applying the same argument to the complementary clopen condition and using duality
therefore gives the two formulas
$$
\begin{aligned}
\varphi^{\bar s}_{B,*}(\bar x)&:=\InverseTupleFormula{e}{\psi}(\bar x),\\
\varphi^{\bar s}_{B,\triangle}(\bar x)&:=\neg\InverseTupleFormula{e}{\neg\psi}(\bar x).
\end{aligned}
$$
In particular, the base case gives actual formulas with only the original finite tuple of free variables.

Finite coordinate diagrams form a basis for the logic space. To see this, take a neighborhood of a structure.
It contains a neighborhood fixing finitely many relation-table and function-table entries. Choose a natural number
$m$ larger than every value in their argument tuples and every specified function output. All these conditions
then use names below $m$ and form a finite diagram. Enlarging the range of names merely renames its variables;
after placing two diagrams in a common range, their intersection is represented by concatenating their lists of
conditions. Each diagram defines a clopen set.

Since $\mathrm{Mod}_L$ is second countable, every open set $U$ is a countable union of such cylinders:
$$U=\bigcup_{j\in J}D_j,$$
where $J$ is countable and may be empty. For a fixed target tuple $\bar s$, enlarge the name range of each diagram
to include all entries of $\bar s$. Thus $D_j$ is defined by a formula $\psi_j$ at the tuple
$\bar t_j=\Sequence{r}{r<m_j}$, and we may regard $e_j(i)=s_i$ as an index below $m_j$.
The formula for the open non-meager transform is
$$
\varphi^{\bar s}_{U,*}(\bar x)
:=\bigvee_{j\in J}\InverseTupleFormula{e_j}{\psi_j}(\bar x).
$$
The empty disjunction is false. A disjunction over any countable $J$ can be written as one indexed by $\omega$,
putting $\bot$ at unused indices. Although the finite blocks of bound variables may have different lengths,
each disjunct has the same original finite context of free variables.

Indeed, the section of $U$ inside $\TupleAgreementCoset{\bar a}{\bar s}$ is open, so it is non-meager exactly when
some permutation in this coset sends $M$ into $U$. Such a permutation sends $M$ into some $D_j$, and the preceding
finite-diagram construction expresses precisely this condition by $\InverseTupleFormula{e_j}{\psi_j}(\bar a)$.
Conversely, any disjunct supplies a permutation sending $M$ into $D_j\IncludedIn U$.
This proves the asserted interpretation of $\varphi^{\bar s}_{U,*}$.
For a closed set $C$, duality gives
$$\varphi^{\bar s}_{C,\triangle}(\bar x):=\neg\varphi^{\bar s}_{\complement C,*}(\bar x).$$

We next express localization using the same finite-variable construction. Write $n$ for the length of $\bar s$.
For each $m\in\omega$ with $s_i<m$ for all $i<n$, put
$$\bar t_m:=\Sequence{j}{j<m},\qquad e_m(i):=s_i.$$
If $\bar b$ is injective and $b_{e_m(i)}=a_i$ for all $i<n$, then
$$\TupleAgreementCoset{\bar b}{\bar t_m}\IncludedIn\TupleAgreementCoset{\bar a}{\bar s}.$$
These subcosets suffice to refine every nonempty open subset $V$ of the original coset. Indeed, choose
$\sigma\in V$ and finitely many inputs $u_j$ such that agreement with $\sigma$ on those inputs implies membership
in $V$. Choose $m$ larger than all entries of $\bar s$ and all values $\sigma(u_j)$, and put
$b_r:=\sigma^{-1}(r)$ for $r<m$. Then $b_{e_m(i)}=a_i$, and a permutation sending every $b_r$ to $r$ agrees
with $\sigma$ on the specified inputs. Hence its coset is contained in $V$.

Suppose the formulas $\varphi^{\bar t}_{B,*}$ are available for every finite tuple $\bar t$, and write
$\theta_m:=\varphi^{\bar t_m}_{B,*}$. The localization rule in Vaught's lemma says that the section of the Borel
set $B$ is comeager in $\TupleAgreementCoset{\bar a}{\bar s}$ exactly when it is non-meager in every nonempty
basic refinement. It suffices to check the subcosets just constructed: non-meagerness in a smaller open set
implies non-meagerness in a larger one. Thus the comeager transform is expressed by
$$
\varphi^{\bar s}_{B,\triangle}(\bar x)
:=\neg\bigvee_{\substack{m\in\omega\\\forall i<n\;s_i<m}}
\InverseTupleFormula{e_m}{\neg\theta_m}(\bar x).
$$
Indeed, the disjunction asserts that for some admissible $m$ there is an injective tuple $\bar b$ with
$b_{e_m(i)}=a_i$ for all $i<n$ and $M\not\models\theta_m(\bar b)$, exactly a failure of the localized condition.
The disjunction is countable, and each disjunct binds only finitely many extra variables. The original finite
context remains the full set of free variables.

We can now complete the simultaneous Borel induction. For open sets, the preceding construction gives the
non-meager formula, and localization gives the comeager formula. For complements, duality gives
$$
\varphi^{\bar s}_{\complement B,*}:=\neg\varphi^{\bar s}_{B,\triangle},
\qquad
\varphi^{\bar s}_{\complement B,\triangle}:=\neg\varphi^{\bar s}_{B,*}.
$$
For $B=\bigcup_k B_k$, the non-meager union identity gives
$$\varphi^{\bar s}_{B,*}:=\bigvee_k\varphi^{\bar s}_{B_k,*}.$$
Apply localization to these newly constructed non-meager formulas to obtain the comeager formulas for $B$.
Every step uses only the constructors of $\LCountableInfinitaryLogic$ and preserves the finite free-variable context.
This completes the induction for every Borel set.

Finally take $\bar s$ empty. Then $\TupleAgreementCoset{\emptyset}{\emptyset}=\InfiniteSymmetricGroup$.
If $A$ is invariant, the section
$\{\sigma:\sigma\cdot M\in A\}$ is the whole group when $M\in A$ and empty otherwise. Hence the sentence
$\varphi^{\emptyset}_{A,\triangle}$ defines precisely $A$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
相対化された帰納のGao/Vaughtへの出典表示。帰納の局所的な内容は直前で別に対応している。)
--> The relativized induction is developed in [@Gao2009, Theorem 11.3.6; @Vaught1974].<!--
formalization: skip-end
-->

<!-- formalization: skip (semantic consequences of Lopez--Escobar and Scott-sentence context) -->
Thus invariant Borel information about countable structures is exactly infinitary first-order information. This theorem
is the semantic reason Vaught's conjecture can be read descriptively: elementary classes, and more generally
$\LCountableInfinitaryLogic$-definable classes, are precisely the Borel invariant pieces of the logic action. The
theorem also
explains why Scott sentences fit so naturally here: each countable structure has an $\LCountableInfinitaryLogic$
sentence
defining its single isomorphism class inside $\mathrm{Mod}_L$.

<!-- formalization: skip-begin (Vaught-conjecture survey and cited counterexample) -->

### Vaught's Conjecture {#sec:vaught-conjecture}
\index{Vaught's conjecture}
\index{logic action!Vaught's conjecture}

\termdefine{Vaught's conjecture} is the cardinality problem attached to the logic action. Let $T$ be a complete
first-order theory in a countable language $L$, and let
$$
\mathrm{Mod}(T):=\{M\in\mathrm{Mod}_L:M\models T\}
$$
be the Borel set of its countable models with universe $\NN$. The conjecture says that the quotient
$$
\mathrm{Mod}(T)/{\cong_L}
$$
has cardinality at most countable or exactly $2^{\alephNull}$. Equivalently, the number of countable models of a
complete countable first-order theory, counted up to isomorphism, should never be an intermediate uncountable cardinal.

A stronger, perfect-set version of the conjecture asks for a dichotomy inside a special invariant Borel
subspace of a \termuse{logic action}. If $\mathrm{Mod}(T)$ has uncountably many isomorphism classes, the conjectural
conclusion is stronger than mere cardinality:
there should be a nonempty perfect set $P\IncludedIn\mathrm{Mod}(T)$ whose members are pairwise
non-isomorphic. Then the quotient
has continuum size for the descriptive reason that a Cantor family of genuinely different countable models has been
built inside the model space.

This formulation makes the analogy with Silver's dichotomy precise but also shows why Silver's theorem does not settle
the conjecture. Silver applies to coanalytic equivalence relations. The isomorphism relation $\cong_L$ on a general
logic space is analytic and can be $\bSigma^1_1$-complete, so the coanalytic-rank argument of
§{sec:silver-dichotomy} is unavailable.
<!-- formalization: skip-end -->

The set $\mathrm{Mod}(T)$ is Borel because first-order satisfaction over the
fixed universe $\NN$ is Borel,
but the orbit equivalence relation restricted to $\mathrm{Mod}(T)$ is still the analytic relation generated by the
$\InfiniteSymmetricGroup$ action.

<!-- formalization: skip-begin (Vaught conjecture syntax, formulations, and cited status) -->
Lopez--Escobar gives the syntactic side of the same problem. By §{sec:lopez-escobar-theorem}, every invariant Borel
subset of $\mathrm{Mod}_L$ is definable by an $\LCountableInfinitaryLogic$ sentence. In particular, a Borel union of
isomorphism
classes is not an arbitrary descriptive object; it is infinitary first-order information. Conversely, each single
isomorphism class of a countable structure is defined by its Scott sentence, an $\LCountableInfinitaryLogic$ sentence
whose
models are exactly the copies of that structure. Thus the obstruction in Vaught's conjecture is not the absence of
syntax. The difficulty is to pass from many definable orbits to a perfect family of mutually inequivalent orbits.

The cardinality formulation and its perfect-set strengthening can be expressed as follows.

*   **Model-theoretic formulation.** Up to isomorphism, a complete countable theory should have either at most countably
    many countable models or exactly continuum many. This is the classification-theoretic form:
    either the theory admits a small list of countable models up to isomorphism, or it is too rich for any intermediate
    cardinal behavior.
*   **Descriptive-set-theoretic formulation.** The logic action should not realize a Borel invariant elementary class
    with uncountably many orbits but no perfect antichain. This is the stronger orbit-equivalence formulation,
    parallel to the
    countable-versus-perfect alternatives in §{sec:perfect-set-theorem} and §{sec:silver-dichotomy}.

The first-order conjecture remains open as of October 2026. Its extension from elementary classes to arbitrary
invariant Borel classes, however, has a different status. Ackerman, Freer, and Knight's October 2026 preprint
[@AckermanFreerKnight2026] constructs a sentence of $\LCountableInfinitaryLogic$ with exactly $\alephCard{1}$
isomorphism classes of countable models and no nonempty perfect set of pairwise non-isomorphic models.
This is a counterexample to the perfect-set version for infinitary logic, not to the first-order conjecture above.

Through the correspondence with $\InfiniteSymmetricGroup$ actions, the same result refutes the topological
Vaught conjecture: a continuous action of a Polish group on a Polish space can have uncountably many orbits
without a nonempty perfect set meeting each orbit in at most one point [@AckermanFreerKnight2026].
The distinction between cardinality and perfect sets matters here. If $\alephCard{1}<2^{\alephNull}$, this example
also has strictly between countably many and continuum many orbits. Under the continuum hypothesis, its
$\alephCard{1}$ orbits have continuum cardinality, but the perfect-set conclusion still fails.

Thus the first-order restriction is essential to the remaining question; being an invariant Borel class alone
does not ensure the conjectured dichotomy. Effros's theorem, treated next, describes when individual orbits
are topologically well behaved, while Hjorth's turbulence detects actions whose orbit equivalence relations
cannot be classified by countable structures.
<!-- formalization: skip-end -->

An equivalence relation $E$ on a standard Borel space is \termdefine{classifiable by countable structures} if
$E \BorelReducesTo {\cong_L}$ for some countable language $L$. The relation itself need not be Borel.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
classifiable by countable
structuresの定義はPolishGroupProse.ClassifiableByCountableStructuresへ接続した。
残りはGaoを引用する可算Borel関係の外部coding結果と、裸の可算集合だけではcodingにならないという注意・後続節への案内。
ここでcoding構成を展開していない。)
--> All countable Borel equivalence relations have this property, by the standard coding of their countable classes
with enough additional structure to distinguish different classes [@Gao2009]. Countability of each class alone
is not such a coding: bare countably infinite sets are all isomorphic. The benchmarks are developed in
§{sec:above-e0}, and §{sec:polish-groups-turbulence} gives obstructions to classification of this kind.<!--
formalization: skip-end
-->

<!-- formalization: skip (external universal logic-action coding theorem) -->
A closed subgroup $G \le \InfiniteSymmetricGroup$ is non-Archimedean Polish and is $\mathrm{Aut}(M)$ for some countable
structure $M$. More generally, the universal logic-action coding theorem says that every continuous action of such a
closed subgroup is Borel reducible to isomorphism of countable structures [@BeckerKechris1996, Theorem 2.7.3]. This is
the precise sense in which logic actions organize non-Archimedean Polish-group actions.

## Case Study: Countable Graphs {#sec:countable-graphs-case-study}
\index{countable graph}
\index{graph isomorphism}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
この節で示すグラフ例の構成と解析性、および後で外部定理として引用するuniversalityを予告する節導入。
具体的な符号化・作用・局所証明は後続で個別に接続している。)
--> Countable graphs are the cleanest running example of the preceding machinery. They require no algebraic or analytic
background, but they already exhibit the full pattern: a Polish parameter space of objects, a continuous
$\InfiniteSymmetricGroup$-action by relabeling, an analytic orbit relation, and a universality theorem saying that graph
isomorphism is as complicated as isomorphism of arbitrary countable structures.<!--
formalization: skip-end
-->

Let $[\NN]^2$ be the set of two-element subsets of $\NN$. A simple undirected graph on vertex set $\NN$ is a function
$$
G:[\NN]^2\to 2,
$$
where $G(\{i,j\})=1$ means that $i$ and $j$ are adjacent. The graph space is therefore
$$
\mathrm{Graphs}_\NN:=2^{[\NN]^2}.
$$
The set $[\NN]^2$ is countable and is infinite because $n\mapsto\{0,n+1\}$ is injective.
Choose an enumeration without repetitions $e:\NN\to[\NN]^2$. Then
$$G\longmapsto(n\longmapsto G(e(n)))$$
is a homeomorphism from $\mathrm{Graphs}_\NN$ to $\CantorSpace$: both it and its inverse just reindex the discrete
coordinates. A basic clopen neighborhood specifies finitely many edges and non-edges.

The infinite symmetric group acts by relabeling:
$$
(\sigma\cdot G)(\{i,j\})
:=
G(\{\sigma^{-1}(i),\sigma^{-1}(j)\}).
$$

\begin{proposition*} The relabeling action
$$
\InfiniteSymmetricGroup\times\mathrm{Graphs}_\NN
\longrightarrow
\mathrm{Graphs}_\NN
$$
is continuous, and its orbit equivalence relation is graph isomorphism.

\end{proposition*}

\begin{proof}[Proof] Continuity is a finite-coordinate check. To decide whether $(\sigma\cdot G)(\{i,j\})=1$, one only
needs the two values $\sigma^{-1}(i)$ and $\sigma^{-1}(j)$ and the single edge coordinate
$G(\{\sigma^{-1}(i),\sigma^{-1}(j)\})$. In the topology of pointwise convergence on $\InfiniteSymmetricGroup$, the
conditions $\sigma^{-1}(i)=a$ and $\sigma^{-1}(j)=b$ define a clopen neighborhood of $\sigma$, and the condition
$G(\{a,b\})=\epsilon$ defines a clopen neighborhood of $G$. Hence every edge coordinate of the output is locally
constant, so the action is continuous.

Two graphs $G,H\in\mathrm{Graphs}_\NN$ lie in the same orbit exactly when there is a permutation
$\sigma\in\InfiniteSymmetricGroup$ such that $H=\sigma\cdot G$. This says
$$
H(\{i,j\})=G(\{\sigma^{-1}(i),\sigma^{-1}(j)\})
\qquad(i\ne j),
$$
which is precisely that $\sigma^{-1}$ is an isomorphism from $H$ to $G$, equivalently that $\sigma$ is an isomorphism
from $G$ to $H$. Thus the orbit relation is graph isomorphism.
\end{proof}

The graph-isomorphism relation is therefore
$$
G\cong_{\mathrm{Graph}}H
\quad\Longleftrightarrow\quad
\exists\sigma\in\InfiniteSymmetricGroup\; H=\sigma\cdot G.
$$
To verify analyticity, in $(\mathrm{Graphs}_\NN\times\mathrm{Graphs}_\NN)\times\InfiniteSymmetricGroup$ put
$$C:=\{\Pair{\Pair{G}{H}}{\sigma}:H=\sigma\cdot G\}.$$
Each edge coordinate imposes equality of two continuous Boolean-valued functions, so $C$ is an intersection of
closed sets. Hence $C$ is a closed subspace of a Polish space and is itself Polish. The continuous projection
$$\pi:C\to\mathrm{Graphs}_\NN\times\mathrm{Graphs}_\NN,\qquad\pi(\Pair{G}{H},\sigma):=\Pair{G}{H}$$
has image exactly $\{\Pair{G}{H}:G\cong_{\mathrm{Graph}}H\}$. This continuous image of a Polish space is analytic by
§{sec:analytic-sets}.

This example is the concrete model for the phrase "classification by countable structures." A graph is already a
countable structure in the one-relation language $\{E\}$, with $E$ binary, symmetric, and irreflexive. A Borel reduction
$$
f:X\to\mathrm{Graphs}_\NN
$$
from an equivalence relation $E$ on $X$ to graph isomorphism assigns to each object $x$ a countable graph $f(x)$ such
that
$$
x\mathrel E y
\quad\Longleftrightarrow\quad
f(x)\cong_{\mathrm{Graph}}f(y).
$$
Thus the graph becomes a complete countable invariant for the original object.

<!-- formalization: skip-begin (external Friedman--Stanley coding theorem and construction summary) -->
\begin{theorem*}[\termdefineas{Friedman--Stanley theorem}{Friedman--Stanley}] For every countable language $L$,
isomorphism of countable $L$-structures Borel-reduces to graph isomorphism:
$$
\cong_L \BorelReducesTo \cong_{\mathrm{Graph}}.
$$
\end{theorem*}

**Reference and discussion.** The construction replaces each relation and function symbol of a
countable structure by a
uniform countable graph gadget attached to tuples of elements. The gadgets are chosen rigidly enough that every graph
isomorphism must preserve the original element sort, the tuple sort, the symbol labels, and the incidence relations;
conversely, every isomorphism of the original structures extends to an isomorphism of the coded graphs. Because only
countably many finite tuples and symbols are involved, the assignment from the atomic diagram of a structure to the edge
relation of its graph is Borel, indeed coordinate-wise finite. The full proof is a careful gadget construction, not a
new descriptive-set-theoretic principle.

See the original Friedman--Stanley paper and a standard treatment in Gao [@FriedmanStanley1989; @Gao2009].
<!-- formalization: skip-end -->

\begin{corollary*} Every equivalence relation on a standard Borel space that is classifiable by countable structures
Borel-reduces to graph isomorphism. Thus graph isomorphism is universal for classification by countable structures.
\end{corollary*}

\begin{proof}[Proof from cited results] Let $E$ be such an equivalence relation on $X$. By the definition of
classification by countable structures, there are a countable language $L$ and a Borel reduction $f$ from $E$ to
$\cong_L$. Apply the Friedman--Stanley theorem to $L$ to obtain a Borel reduction $g$ from $\cong_L$ to
$\cong_{\mathrm{Graph}}$. The composite $g\circ f$ is Borel, and for all $x,y\in X$,
$$
x\mathrel E y \quad\Longleftrightarrow\quad f(x)\cong_L f(y)
\quad\Longleftrightarrow\quad g(f(x))\cong_{\mathrm{Graph}}g(f(y)).
$$
Hence $g\circ f$ is the required reduction. In Lean, the Friedman--Stanley statement is an explicit hypothesis
of this derivation.
\end{proof}

<!-- formalization: skip-begin (contextual consequences of Lopez--Escobar and graph classification) -->
Lopez--Escobar also has a transparent graph reading. An isomorphism-invariant Borel subset of $\mathrm{Graphs}_\NN$ is
exactly the class of countable graphs satisfying some $\LCountableInfinitaryLogic$ sentence in the graph language. Thus
a Borel
property of countable graphs that does not depend on the labeling is infinitary first-order information about the graph
itself. This is the syntactic counterpart to the orbit statement above.

Countable graphs therefore form the preferred case study for §{sec:borel-reducibility}. Smoothness asks whether a graph
classification problem can be reduced all the way to equality on reals. Borel reducibility asks whether another
classification problem can be coded by graphs. Turbulence gives a way to prove that certain analytic or
operator-algebraic classification problems cannot even reach this graph-coded countable-invariant level.
<!-- formalization: skip-end -->

## Orbit Equivalence Relations {#sec:polish-group-orbit-er}

\begin{mathmeta}
  \define{OrbitER}
\end{mathmeta}
For a Borel action of a Polish group $G$ on a standard Borel space $X$, the
\termdefine{orbit equivalence relation} is
$$\OrbitER{G}{X} := \{\Pair{x}{y} \in X \times X : y = g \cdot x \text{ for some } g \in G\}.$$
The existential quantification over $G$ uses a Polish parameter space, so projection makes $\OrbitER{G}{X}$ analytic
($\bSigma^1_1$). <!--
formalization: skip-begin (引用・背景説明・読書案内:
存在量化による一般Borel作用の解析性はPolishGroupProse.analyticSet_orbitRelationでBorel
witness relationの射影から証明した。残る「Borelかどうかは軌道による」は後続のEffrosの判定への案内で、
追加の独立した証明を述べていない。)
--> Whether it is Borel depends on the orbits.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のEffros定理の導入文。数学的な仮定・結論・証明は定理本体で別に対応している。)
--> The basic structural theorem governing orbit topology is:<!--
formalization: skip-end
-->

\begin{theorem*}[\termdefineas{Effros's orbit theorem}{Effros}] For a continuous action of a Polish group $G$ on a
Polish space $X$, the following are equivalent for an orbit $G \cdot x$:

\begin{enumerate}
\item $G \cdot x$ is \textbf{non-meager in its closure}: a non-meager subset of $\Closure{G \cdot x}$.
\item $G \cdot x$ is $\Gdelta$ in $X$.
\item $G \cdot x$ is $\Gdelta$ in $\Closure{G \cdot x}$.
\item The orbit map $\pi_x : G/G_x \to G \cdot x$ defined by $g G_x \mapsto g \cdot x$ is a homeomorphism, where $G_x :=
\{g : g \cdot x = x\}$ is the stabilizer.
\end{enumerate}

\end{theorem*}

<!-- formalization: skip (standard theorem on quotients by closed subgroups, cited as external infrastructure) -->
\begin{recall*}[Polish quotients]
If $H$ is a closed subgroup of a Polish group $G$, then $G/H$ is Polish and the quotient map $G\to G/H$ is open.
\end{recall*}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Polish quotientのGao Theorem 2.2.10への出典表示。明示的に引用する外部インフラの書誌情報である。)
--> This is [@Gao2009, Theorem 2.2.10].<!--
formalization: skip-end
-->

\begin{proof}[Proof] The stabilizer $G_x$ is closed in $G$ as the preimage of $\{x\}$ under the continuous map $g
\mapsto g \cdot x$.
<!-- formalization: skip-begin (Polish quotient theorem cited above) -->
The Polish-quotient theorem therefore makes $G/G_x$ Polish,
<!-- formalization: skip-end -->
and $\pi_x$ is a continuous bijection
onto $G \cdot x$.

\emph{(2) $\Leftrightarrow$ (3).} Put $Y:=\Closure{G\cdot x}$. Since $Y$ is closed in the metrizable space $X$,
it is $\Gdelta$ in $X$.
Every relatively open subset of $Y$ is the intersection of $Y$ with an open subset of $X$.
Consequently, a subset of $Y$ is $\Gdelta$ in $Y$ if and only if it is $\Gdelta$ in $X$.

\emph{(4) $\Rightarrow$ (2).} If $\pi_x$ is a homeomorphism, $G \cdot x$ is Polish in the subspace topology from $X$,
hence $\Gdelta$ in $X$ by Alexandrov's theorem in §{sec:alexandrov-theorem}.

\emph{(3) $\Rightarrow$ (1).} The orbit $G\cdot x$ is dense in $Y$ by definition of closure.
Write $G\cdot x=\bigcap_n U_n$, where each $U_n$ is open in $Y$. Every $U_n$ is dense in $Y$, so
$$\SetDifference{Y}{(G\cdot x)}=\bigcup_n\SetDifference{Y}{U_n}$$
is meager in $Y$. Thus the orbit is comeager there. Since the nonempty Polish space $Y$ is a Baire space,
the orbit cannot also be meager.

\emph{(1) $\Rightarrow$ (4).} It suffices to show that $\pi_x$ is open onto its image. We use the following orbit form
of Pettis's lemma.

\begin{lemma*}[Pettis lemma for orbit maps]
Assume $G\cdot x$ is non-meager in $Y:=\Closure{G\cdot x}$. If $V\ni e$ is
open in $G$, then $V\cdot x$ contains a relative neighborhood of $x$ in the orbit $G\cdot x$.
\end{lemma*}

\begin{proof}[Proof of the lemma] Choose a symmetric open $W\ni e$ with $W^{-1}W\IncludedIn V$. We first show that
$W\cdot
x$ is non-meager in $Y$. Let $\{g_n:n\in\omega\}$ be a countable dense subset of $G$. Since $\bigcup_n g_nW=G$, we have
$$G\cdot x=\bigcup_n g_nW\cdot x.$$
If every $g_nW\cdot x$ were meager in $Y$, the orbit would be meager, contrary to the hypothesis. Thus some $g_nW\cdot
x$ is non-meager. Applying the homeomorphism $g_n^{-1}:Y\to Y$ shows that $W\cdot x$ is non-meager.

The set $W\cdot x$ is analytic, hence has the Baire property by §{sec:regularity-independence}. Baire-property
localization therefore gives a nonempty relatively open $\Omega\IncludedIn Y$ such that $W\cdot x$ is comeager in
$\Omega$. Pick $k\in W$ with $k\cdot x\in\Omega$, and set
$$O:=k^{-1}\Omega.$$
Then $O$ is a relatively open neighborhood of $x$ in $Y$.

We claim that
$$O\cap(G\cdot x)\IncludedIn W^{-1}W\cdot x\IncludedIn V\cdot x.$$
Let $y\in O\cap(G\cdot x)$ and put
$$H:=W\cap\{h\in G:h\cdot y\in\Omega\}.$$
Continuity of the action makes $H$ open. Since $k\in W$ and $k\cdot y\in\Omega$, it contains $k$, and by definition
$$H\cdot y\IncludedIn\Omega.$$
The set $H\cdot y$ is non-meager in $Y$: if $\{r_n\}$ is dense in $G$, then $\bigcup_n r_nH\cdot y=G\cdot y=G\cdot x$,
and otherwise the non-meager orbit would be a countable union of meager sets.

Thus $H\cdot y$ is non-meager in $\Omega$, while $W\cdot x$ is comeager there. Their
intersection is nonempty. Choose $h\in H$ and $w\in W$ with
$$h\cdot y=w\cdot x.$$
Then
$$y=h^{-1}w\cdot x\in W^{-1}W\cdot x\IncludedIn V\cdot x.$$
This proves the claim and hence the lemma. 
\end{proof}

To prove openness, let $O\IncludedIn G$ be open and $h\in O$. Choose an open identity neighborhood $V$ with
$hV\IncludedIn O$. The lemma shows that $hV\cdot x$ contains a relative neighborhood of $h\cdot x$ in the orbit.
Thus every point of $O\cdot x$ is an interior point of that set, so $O\cdot x$ is open in the orbit.
Applying this to the inverse image of an open subset of the quotient proves that
$\pi_x:G/G_x\to G\cdot x$ is open. It is already a continuous bijection, hence a homeomorphism.
\end{proof}

If an orbit is meager in its closure, the equivalent conditions of Effros's theorem fail for that orbit.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
meager in
closureからEffrosの条件が失敗することはPolishGroupProse.not_isGdelta_of_meagre_in_closur
eへ接続した。残るdensityとmeagernessだけではturbulenceを保証しないという文は、
具体例や独立した証明を展開しない適用上の注意。局所軌道条件の定義自体は別に対応済み。)
--> Density and meagerness alone do not imply turbulence; the local-orbit condition below is essential.<!--
formalization: skip-end
-->
Every individual orbit is nevertheless Borel: the continuous bijection from the Polish quotient by its
stabilizer has Borel image by the Lusin--Souslin theorem. This does not force the orbit equivalence relation
$\OrbitER{G}{X}$ to be Borel; it may be properly analytic.

\begin{corollary*} If every orbit of a continuous Polish-group action is non-meager in its closure, then
$\OrbitER{G}{X}$ is
Borel.

\end{corollary*}

\begin{proof}[Proof]
Let
$$
R:=\{\Pair{x}{y}:y\in\Closure{G\cdot x}\}.
$$
If $\{B_n\}$ is a countable basis of $X$, then $y\in\Closure{G\cdot x}$ iff, for every $n$ with $y\in B_n$, some
$g\in G$ satisfies $g\cdot x\in B_n$. For each $n$, the set of such $x$ is open, so $R$ is Borel.
Indeed, if
$$
O_n:=\{x\in X:\text{some }g\in G\text{ satisfies }g\cdot x\in B_n\},
$$
then each $O_n$ is open and
$$
R=\bigcap_n\bigl((X\times\SetDifference{X}{B_n})\cup(O_n\times B_n)\bigr).
$$

We claim that
$$
x\mathrel{\OrbitER{G}{X}}y
\quad\Longleftrightarrow\quad
\Pair{x}{y}\in R\text{ and }\Pair{y}{x}\in R.
$$
The forward implication is immediate. Conversely, if $y\in\Closure{G\cdot x}$, invariance of this closed set implies
$$\Closure{G\cdot y}\IncludedIn\Closure{G\cdot x}.$$
The other membership condition gives the reverse inclusion, so the orbit closures are equal.
Effros's theorem makes each orbit comeager in this common closure, because it is dense and $\Gdelta$ there. The
two orbits therefore intersect and hence coincide. Thus $\OrbitER{G}{X}=R\cap R^{-1}$ is Borel.
\end{proof}

The hypothesis is automatic for closed orbits, <!--
formalization: skip-begin (引用・背景説明・読書案内:
closed orbitからBorel relationを得る局所的な帰結とcompact
groupの場合はEffrosOrbitRelationsへ接続した。残りはproper
actionをclosed-orbit状況の標準例として挙げるだけで、propernessからの閉性の証明はこの章で展開していない。)
--> including proper actions of locally compact groups.<!--
formalization: skip-end
-->  It also holds for
actions of compact groups, because every compact-group orbit is compact and therefore closed. In these settings every
orbit is at most $\bPi^0_2$ in its closure, and the orbit relation is Borel rather than properly analytic.

<!-- formalization: skip-begin (motivation for turbulence and its role in classification) -->

## Turbulence {#sec:polish-groups-turbulence}

Hjorth's \termdefine{turbulence} [@Hjorth2000] is the analytic obstruction to classification by countable
structures. It belongs exactly at the point where the tame logic-action world stops being adequate. If an equivalence
relation is classifiable by countable structures, then each object can be assigned, in a Borel way, a countable
structure whose isomorphism type is a complete invariant. The target equivalence relation is then an orbit relation of
$\InfiniteSymmetricGroup$, a non-Archimedean Polish group with many open subgroups and a strongly countable local
geometry.

General Polish-group actions need not have that local geometry. Groups such as Banach spaces under addition, unitary
groups, and homeomorphism groups have small neighborhoods of the identity that are not open subgroups; applying small
elements repeatedly can move a point through a complicated local region without ever producing a discrete countable
approximation. Turbulence isolates the dynamical pattern behind this behavior. Where Effros locates well-behaved orbits
by asking whether an orbit is non-meager in its closure, turbulence studies the opposite situation: orbits are globally
dense but meager, and yet every sufficiently small local motion spreads through a nontrivial open region.

The point is not merely that the orbit relation is nonsmooth. Nonsmoothness only rules out real-valued complete
invariants; classification by countable structures is a much larger target. Hjorth's theorem says that turbulent actions
are still too complicated for that larger target. Thus turbulence is a practical non-classification criterion: after
verifying a local dynamical condition, one obtains a strong lower bound in the Borel-reducibility hierarchy.
<!-- formalization: skip-end -->

Fix a continuous action of a Polish group $G$ on a nonempty Polish space $X$. For $x \in X$, an open $U
\IncludedIn X$ with $x
\in
U$, and an open $V \IncludedIn G$ with $e \in V$, the \termdefine{local orbit} $\mathcal O(x, U, V)$ is the smallest set
containing $x$ with the closure property
$$y \in \mathcal O(x, U, V) \text{ and } g \in V \text{ and } g \cdot y \in U \;\Longrightarrow\; g \cdot y \in \mathcal
O(x, U, V).$$
This is the directed reachability set generated by the moves $y\mapsto g\cdot y$ with $g\in V$. When $V$ is symmetric,
it is equivalently the connected component of $x$ in the undirected graph on $U$ whose edges join $y$ to $g\cdot y$
when both endpoints lie in $U$. Local orbits sit between the singleton $\{x\}$ and the full orbit $G\cdot x\cap U$,
and they refine to the orbit as $U \uparrow X$ and $V \uparrow G$.

\begin{definition*}[Hjorth] The action of $G$ on $X$ is \termdefine{turbulent} if:

\begin{enumerate}
\item Every orbit is dense in $X$.
\item Every orbit is meager in $X$.
\item For every $x \in X$, every open $U \ni x$, and every open $V \ni e$, the local orbit $\mathcal O(x, U, V)$
is \textbf{somewhere dense}: its closure has nonempty interior.
\end{enumerate}

\end{definition*}

A point $x \in X$ is a \termdefine{turbulent point} if condition (3) holds locally at $x$ — for every $U \ni x$ and $V
\ni e$, the local orbit $\mathcal O(x, U, V)$ is somewhere dense.

The combination of conditions is delicate. Density and meagerness together rule out the Effros regime: by (1) every
orbit has closure $X$, and by (2) every orbit is meager in $X$, so no orbit is non-meager in its closure. <!--
formalization: skip-begin (引用・背景説明・読書案内:
denseかつmeagerならclosure内でもmeagerであるという局所的な帰結はPolishGroupProse.dense_meagre_i
n_closureへ接続した。残る「small movesでlocal
orbitが広がる」は既に接続したIsTurbulentPointの条件の解釈で、新たな形式的条件や局所証明ではない。)
--> Condition
(3) is what makes the failure of Effros uniform: locally one cannot trap a point inside a small open piece of its own
orbit, because applying small group elements forces the local orbit to spread out.<!--
formalization: skip-end
-->

<!-- formalization: skip (conceptual lead-in to the external Hjorth theorem) -->
The structural consequence is Hjorth's central non-classification theorem. The theorem is best read as a comparison
between two kinds of orbit equivalence relations. On one side are logic actions of $\InfiniteSymmetricGroup$, whose
invariants are countable structures. On the other side are turbulent actions, whose local orbits spread too much to be
coded by the open-subgroup approximations available in $\InfiniteSymmetricGroup$. A Borel reduction from a turbulent
orbit relation to a logic action would have to turn those locally spreading approximate orbits into stable countable
structural data. Hjorth's analysis proves that any such Borel assignment collapses on a large set, so it cannot separate
all orbits.

<!-- formalization: skip-begin (external Hjorth turbulence theorem and reference discussion) -->
\begin{theorem*}[\termdefineas{Hjorth theorem}{Hjorth}] If a continuous action of a Polish group $G$ on a
nonempty Polish space
$X$ is turbulent, then $\OrbitER{G}{X}$ is \emph{not} classifiable by countable structures: there is no countable
language $L$
with $\OrbitER{G}{X} \BorelReducesTo {\cong_L}$.

\end{theorem*}

**Reference and discussion.** This is Hjorth's turbulence theorem, used here as an external theorem. Its
proof combines local-orbit Baire category, Hjorth's analysis of approximate orbits, and an absoluteness argument showing
that any attempted Borel reduction to a logic action must collapse on a comeager set. Those ingredients are beyond the
present text's proof spine. The theorem is used here as a named obstruction principle: once an action is verified
turbulent, classification by countable structures is impossible. The contrast with non-Archimedean groups is sharp:
if $G$ is a closed subgroup of $\InfiniteSymmetricGroup$, then $\OrbitER{G}{X} \BorelReducesTo {\cong_L}$ for some $L$
depending on $G$.
<!-- formalization: skip-end -->

Consequently no such action can satisfy all three turbulence hypotheses.

<!-- formalization: skip-begin (interpretation of the non-Archimedean contrast) -->
Turbulence cleanly separates the
non-Archimedean and "wild" sides of the Polish-group landscape.\termref{absoluteness}

For the full theorem and proof, see [@Hjorth2000].
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (external examples and further nonclassification results) -->
Standard turbulent examples:

*   $\ell^p$ acting on $\RealSequenceSpace$ by translation, $1 \le p < \infty$: every orbit is the coset $a +
    \ell^p$, dense and meager in $\RealSequenceSpace$, and finite chains of sufficiently small
    $\ell^p$-perturbations have somewhere-dense local orbits [@Hjorth2000].

Further non-classification results show that isomorphism of separable Banach spaces and isomorphism of separable
$C^*$-algebras are not classifiable by countable structures [@FerencziLouveauRosendal2009; @Sabok2016]. Their proofs
use stronger coding and completeness arguments, so they are consequences of the broader obstruction theory rather than
unproved turbulent examples asserted here.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (reducibility survey and chapter summary) -->

## Polish Groups in the Reducibility Picture {#sec:polish-groups-reducibility}

The interaction with §{sec:borel-reducibility} is now visible.

*   **Glimm--Effros**, §{sec:e0-glimm-effros}, was originally proved [@Glimm1961; @Effros1965] for orbit relations of
    Polish-group actions. In the modern formulation, the smoothness alternative says that a Borel complete invariant
    separates the orbits;
    in the other alternative, $\EventualEqualityER$ Borel reduces to the orbit relation. Harrington--Kechris--Louveau
    extended it to all
    Borel equivalence relations via the Gandy--Harrington topology, but the Polish-group context remains the historical
    motivation.
*   **$\EventualRowEqualityER$**, §{sec:above-e0}, is *not induced by any Polish-group action* [@KechrisLouveau1997]: no
    Polish group $G$
    produces $\EventualRowEqualityER$ as $\OrbitER{G}{X}$ for any Borel action. This structural rigidity result
    separates orbit-equivalence
    relations from general Borel equivalence relations and explains why the orbit-equivalence story has its own internal
    hierarchy distinct from the general Borel-reducibility hierarchy.
*   **Logic actions**, §{sec:logic-actions}, organize the non-Archimedean side: every closed subgroup of
    $\InfiniteSymmetricGroup$ acts on a logic space, and isomorphism of countable structures is the universal
    $\InfiniteSymmetricGroup$-orbit relation. Turbulence is the obstruction to "$\OrbitER{G}{X} \BorelReducesTo
    {\cong_L}$" for general
    Polish-group orbit relations.
*   **Universal analytic equivalence relations** sit above all Polish-group orbit relations: every $\OrbitER{G}{X}$ for
    $G$ a
    Polish group is $\BorelReducesTo$-below the universal analytic equivalence relation [@LouveauRosendal2005].
*   **Vaught's conjecture**, §{sec:vaught-conjecture}, asks for a countable-versus-continuum dichotomy for the
    isomorphism classes of countable models of a complete countable first-order theory. It is the model-theoretic
    analogue of Silver's dichotomy in §{sec:silver-dichotomy} inside the logic-action setting. This first-order
    problem remains open as of October 2026; the infinitary and topological perfect-set versions have a
    counterexample [@AckermanFreerKnight2026].

A complementary program of Ding--Zheng assigns to each Polish group $G$ the right-coset equivalence relation
$E(G)$ on $\funcspace{\omega}{G}$ modulo the subgroup $c(G)$ of convergent sequences. Borel comparisons between
these relations detect structural properties of the groups: if $H$ admits a compatible two-sided invariant
metric and $G$ does not, then $E(G)$ is not Borel reducible to $E(H)$ [@DingZheng2025TSI]. Thus one canonical
relation attached to each group already records an obstruction coming from invariant metrizability.
The survey [@DingZheng2026] develops this program and its rigidity results further.

The systematic reference is [@Gao2009] and [@BeckerKechris1996]; turbulence and obstruction theory are developed in
[@Hjorth2000].

<!-- formalization: skip-end -->
