# Preface {#sec:front-matter .unnumbered}

## Introduction {#sec:introduction}

\begin{mathmeta}
  \forward{BaireSpace,alephNull,NN,QQ,R,Fsigma,Gdelta,SetDifference,Sequence,IncludedIn,PartialFunctionMap}
  \forward{NamePair,NatPair}
  \vars{n}{Nat}
  \vars{p}{Rat}
\end{mathmeta}

When is a condition defining a set simple? On the real line, consider the rationals and the irrationals:
$$
\QQ = \bigcup_{q\in\QQ}\{q\}, \qquad
\SetDifference{\R}{\QQ} = \bigcap_{q\in\QQ}(\SetDifference{\R}{\{q\}}).
$$
Each singleton is closed, so the first expression displays the rationals as a countable union of closed sets,
an $\Fsigma$ set. Its complement is a countable intersection of open sets, a $\Gdelta$ set. These descriptions
illustrate how operations used to build or define a set measure its descriptive complexity. A set can have
many descriptions; we ask how simple a description it admits.

For a subset $A\IncludedIn\R$, consider its \termforward{indicator function} $\IndicatorFunction{A}$:
$$
\IndicatorFunction{A}(x)=\begin{cases}
1 & x\in A, \\
0 & x\notin A.
\end{cases}
$$
Can continuous real-valued functions approximate $\IndicatorFunction{A}$ pointwise? For a nonempty
closed set $F$, the answer is yes:
$$
u_{F,n}(x)=\max\{0,1-n d(x,F)\}\longrightarrow \IndicatorFunction{F}(x).
$$
The distance to $F$ is continuous. At a point of $F$ each approximant equals $1$; outside $F$, the positive
distance makes the approximants eventually $0$.

The indicator of the rationals behaves differently: no sequence of continuous real-valued functions
converges to it at every point. The obstruction comes from the complexity of inverse images. For any
pointwise limit of continuous functions, the inverse image of an open set is $\Fsigma$. But
$$
\IndicatorFunction{\QQ}^{-1}\bigl((-1/2,1/2)\bigr)=\SetDifference{\R}{\QQ},
$$
and the irrationals are not $\Fsigma$, as the Baire category theorem shows. Thus the complexity of a set can
rule out a proposed continuous approximation.

Two successive stages of pointwise limits do suffice. Enumerate the rationals and let $F_n$ consist of the
first $n+1$ of them. Each $\IndicatorFunction{F_n}$ is a pointwise limit of continuous functions by the closed-set
construction, and $\IndicatorFunction{F_n}$ in turn converges pointwise to $\IndicatorFunction{\QQ}$. The
number of successive limit stages
is recorded by the Baire classes of functions: $\IndicatorFunction{\QQ}$ has class $2$ and cannot have class $1$.
§{sec:baire-class-functions} proves these claims and relates the Baire classes to the Borel complexity of
inverse images. The distinction between one limit and two is a concrete consequence of that complexity.

<!-- formalization: skip-begin (preface roadmap and background vocabulary) -->

This is the definability line of the book. Starting from open intervals with rational endpoints, repeated
complements and countable unions generate the \termforwardas{Borel set}{Borel sets}. A
\termforward{Borel code} records such a construction as a countable, well-founded tree: leaves specify basic
open sets, and the other nodes specify complements or countable unions. Well-foundedness means that following
successive subcodes cannot continue indefinitely. The complexity of these constructions gives the Borel hierarchy.

Projecting closed subsets of products of Polish spaces gives analytic sets; iterating projection and
complement leads to the projective hierarchy. Effective descriptive set theory adds algorithmic restrictions
on codes and defining predicates. The allowed parameters must also be specified: the relative versions permit
computations using a fixed parameter, without requiring that parameter itself to be computable.

<!-- formalization: skip-end -->

For example, consider the natural-number codes of programs that return a natural number on input 0.
Finite computations witnessing an output let us computably enumerate the members, although no program decides
membership in every case. In the discrete topology on the natural numbers, however, every subset is open and
closed, including this one. Its computational difficulty is therefore not a high level of the ordinary Borel
hierarchy. The effective hierarchy distinguishes the existence of a computable enumeration from computable
decidability. The same set thus makes visible the difference between topological and effective complexity.

<!-- formalization: skip-begin (preface introduction and forward references) -->

Codes describe sets. To develop the second line, realizability, we turn to the approximation data that
represent individual points.
A real number $x$ can be represented by rational approximations: choose, for each
$n\in\NN$, a rational number $q_n$ with error at most $2^{-n}$. The sequence $\Sequence{q_n}{n\in\NN}$ then
represents $x$. Data representing an object under a specified rule are called a
\termforwardas{represented-space name}{name} of that object. Different names may represent the same real
number; the object and its name must be distinguished.

Along the realizability line, does every real number $x$ admit a program that, on input $n$, outputs a rational
approximation with error at most $2^{-n}$? A real number $x$ with such a program is computable. Every real
number has an approximation sequence, but not every real number is computable. For computations that use a
name already supplied as input, a program requests values at specified indices. A terminating computation of
one output coordinate reads only finitely many input coordinates. Later chapters formalize this access using
lambda terms and beta/query reductions.

Assigning natural-number codes to rationals lets us regard approximation sequences as points of
\termforward{Baire space} $\BaireSpace$, the space of infinite sequences of natural numbers. Its basic open
sets are \termforwardas{cylinder}{cylinders}, obtained by fixing a finite initial segment. A
\termforward{representation} of a space $X$ is a partial map $\PartialFunctionMap{\delta}{\BaireSpace}{X}$
that supplies at least one name for every point: $\delta(p)=x$ means that $p$ names $x$. Several names may
have the same image. A transformation of names is continuous when, at each input name, every finite output
segment is determined by some finite input segment. Continuity of such a transformation and continuity of a
map between the represented spaces are related only after the representations have been specified.

For a concrete example, restrict to $x\in[0,1]$ and consider changing an approximation name into a
\termforward{binary expansion}. At points with two expansions, either is permitted as an output. For each
desired number $n$ of fractional digits, does knowing $q_0,\ldots,q_m$ for some finite $m$ determine a valid
output prefix? The required $m$ may depend on both $n$ and the input name. This is a continuity question on
the space of names, rather than a question about a function whose input is the real number alone.

Away from dyadic rationals, any fixed number of binary digits can be determined from sufficiently precise
approximations, but the required input precision has no bound depending only on the number of output digits.
At an interior dyadic boundary such as $1/2$, every finite prefix of a suitable approximation name is
compatible with values on both sides. Consequently no translator can continuously select a binary expansion on
all valid input names, even though either expansion is allowed at a point with two.
\termforwardas{signed-digit representation}{Signed-digit representations} allow overlapping digit choices and
remove this obstruction: they and Cauchy names can be translated computably in both directions.
§{sec:cauchy-representation-admissibility} proves the topological distinction, and
§{sec:tte-binary-signed-digit} constructs the lambda programs. This single example
shows how changing a representation changes the operations that can be realized.

Selection from a defined relation connects the two lines. Rounding a real number to the nearest integer,
choosing the larger integer at a tie, gives a Borel measurable rule with jump discontinuities. More generally,
let each input $x\in X$ have a nonempty set of permitted outputs $A_x\IncludedIn Y$. A selector is a function
satisfying $f(x)\in A_x$. When can it be Borel measurable, and when can a program transform an input name into
a name of a selected output? A Borel relation alone does not guarantee Borel uniformization in general;
theorems guaranteeing Borel selectors impose further conditions on sections or on how they vary measurably.
Part II studies which such conditions make selection possible.

Polish spaces provide a common setting because they contain rich analytic examples while admitting
approximation and coding by countable data. A \termforward{Polish space} is \termforward{separable} and
\termforward{completely metrizable}. Separability supplies a countable dense set, and a compatible complete
metric ensures that Cauchy approximations have limits in the space. These are existence assertions:
separability alone supplies neither a computable enumeration of the dense set nor an algorithm for its
distances or for approximating a given point. Those require additional effective structure.

The book has five parts. Part I develops the topological tools for moving between spaces and their codes. It
establishes the behavior of Polish, Baire, and Cantor spaces, then builds the Borel hierarchy and the basic
naming and refinement constructions. Its purpose is to make later changes of presentation precise: which
information is retained, which maps are continuous, and when the Borel sets remain the same.

Part II studies the consequences of definability for regularity, selection, and classification. Projection
leads from Borel sets to analytic sets, and separation and uniformization provide tools for recovering
information and choosing witnesses. Measures, games, and group actions supply applications in which these
tools reveal both regular behavior and obstructions to classification. The comparison of classification
problems uses \termforward{Borel reducibility}. Results proved here are distinguished from deeper results used
from the literature.

Part III, Effective Definability and Forcing, studies how definability depends on the ambient universe and
on restrictions on definitions and parameters. Forcing constructs extensions of set-theoretic models and
examines preservation and independence. Effective descriptive set theory develops lightface hierarchies,
ranks, and refinement tools, culminating in proofs of the Silver and Harrington--Kechris--Louveau (HKL)
dichotomies used in Part II. These are two continuations of the definability line; the effective proofs do
not require the forcing chapter.

Part IV, Computation and Realizability, develops the realizability line through computations on names.
Type-2 Theory of Effectivity (TTE) supplies the realizer language for computable analysis, algorithmic randomness,
and Weihrauch reducibility. In Type-2 computation, a program queries entries of an infinite input name as needed.
Domain theory studies spaces of partial information, and the realizability chapters
interpret mathematical statements and maps through their realizers. This part can be entered from the naming
and representation tools of Part I, with additional prerequisites indicated along the reading paths below.

Part V consists of an outlook and appendices. The outlook returns to the relation between definitions, names,
and constructions developed throughout the book. The appendices collect the background needed to cross between
the topological, set-theoretic, logical, and computational settings, and can be consulted along the reading
paths given below.

<!-- formalization: skip-end -->

## How This Book Differs {#sec:how-this-book-differs}

<!-- formalization: skip-begin (preface comparison with related books, not a proof obligation) -->

Several standard books already cover major parts of this terrain with greater depth in their own directions. Kechris
[@Kechris1995] remains the central reference for classical descriptive set theory on Polish and standard Borel spaces.
Moschovakis [@Moschovakis2009] develops the projective and effective hierarchies with a much fuller recursion-theoretic
apparatus. Gao [@Gao2009] is the natural reference for invariant descriptive set theory, especially Polish-group actions
and Borel reducibility. Kunen [@Kunen1980] and Jech [@Jech2003] give forcing and modern set theory at a level far beyond
what is needed here. Weihrauch [@Weihrauch2000] develops computable analysis through representations, while
van Oosten [@vanOosten2008] develops the categorical theory of realizability.

This book has a different purpose. It treats Polish spaces as a common language linking topology, definability, forcing,
classification, and computability. The early chapters therefore spend more time on concrete coding spaces, trees,
cylinders, Cauchy names, and topology-refinement lemmas than a specialized set-theory or analysis text usually would.

The bridge is built by following the constructions across these subjects. A point becomes a name, a closed set becomes
a tree, and a map is studied through translations of names. The computable constructions are backed by lambda terms
and beta/query derivations. A companion Lean development links statements and proof steps to formal declarations;
the prose remains readable without Lean, and cited external results are identified separately.

A reader who wants the full specialist theories should continue to the references above. The aim here is to make their
shared infrastructure usable: to recognize what a code preserves, which parameters a construction needs, and where an
existence argument requires more information than a computation can obtain.

<!-- formalization: skip-end -->

## Proof Conventions {#sec:proof-conventions}

<!-- formalization: skip-begin (preface proof conventions, not a proof obligation) -->

The book distinguishes results proved here from results whose proofs are left to the literature. We use the
following conventions throughout:

*   **Proof.** The argument derives the stated conclusion from its hypotheses, earlier results, the background
    specified in §{sec:expected-reader}, and explicitly cited external theorems. The main construction and essential
    implications are given in the text. Routine verifications may be compressed, but an essential case, a new lemma,
    or an additional hypothesis must not be hidden in an omitted step.
*   **Reference and discussion.** The proof is left to the cited literature. The passage identifies the result being
    used and explains its role and, where useful, the ideas behind its proof. Such an explanation does not claim to
    provide the proof itself.

The external results used or stated in the book are listed in §{sec:external-results}, independently of the
heading under which they appear.

Using an external theorem does not make a proof incomplete. The text states the form of the theorem needed,
identifies its source, and checks its hypotheses in the application. A heading such as **Proof from cited results**
emphasizes this dependence; it has the same standard of completeness as **Proof**. Any additional set-theoretic
assumption is stated explicitly. The heading describes the argument presented in that passage, not whether all of
its ingredients are proved in this book.

For constructions, the text specifies the parameters and choices on which the result depends. Existence of an
object is distinct from a procedure for selecting one. A claim of uniformity requires a single construction that
works for all the stated inputs, and a claim of computability requires the lambda terms and beta/query derivations
used to justify it.

The Lean development checks the statements and proof steps linked to it. A formal proof does not replace the
explanation in the text, and importing a checked external theorem does not mean that its proof has been reproduced
here. The connection between an imported theorem and the book's definitions must also be justified.

When the text derives a consequence from an external theorem whose proof is not available in Lean, the formalization
takes the required external statement as an explicit hypothesis and verifies the derivation from it. The statement
retains the hypotheses needed for the application. This checks the local implication, not the external theorem
itself; the dependency remains visible in the resulting Lean theorem.


### External Results {#sec:external-results}

The following inventory separates inputs to arguments given here from results stated without proof. Each reference
points to the passage that specifies the result and its source. The elementary prerequisites in
§{sec:expected-reader} are not listed theorem by theorem; specialist background and research surveys are
identified separately below.

**Inputs to proofs and constructions.**

*   Lusin--Novikov countable-section decomposition in §{sec:uniformization}. We derive the partial Borel maps from
    the decomposition and Lusin--Suslin.

*   Coanalytic scales, their closure property, and norm comparisons in §{sec:scales-pi11-uniformization}. We use
    these to construct the selector in Kondo uniformization.

*   Compactness and the Hausdorff--Vietoris topology of the closed-set hyperspace of a compact metric space in
    §{sec:effros-borel}. These supply the compact ambient hyperspace in the Effros--Borel argument.

*   Prokhorov--Varadarajan, completeness of the Lévy--Prokhorov metric, and Portmanteau in
    §{sec:prob-measure-space}. These are the weak-convergence inputs to §{sec:prokhorov}.

*   Conditional expectation and its measurable factorization in §{sec:disintegration}. We construct and verify the
    probability kernel from these scalar inputs.

*   Kuratowski--Ulam in §{sec:zero-one-laws}, used for the category counterpart of the zero-one laws.

*   Choquet metrization in §{sec:topological-infinite-games}: the converse from a winning strong-Choquet strategy
    to a compatible complete metric.

*   Martin's Borel determinacy and the closed-set covering construction in §{sec:martin-borel-det}. Lean imports
    Manthe's checked proof; the book proves the strategy transport to its own game convention.

*   Harrington's covering-game lemma excluding a winning strategy for Player I in §{sec:covering-game}. The
    coding, covering estimate, and deduction of measurability are proved here.

*   The Becker--Kechris Polish basis construction in §{sec:polish-group-continuization}. It supplies a Polish
    topology with the original Borel sets; we prove continuity of the action for that topology.

*   The Polish quotient theorem for closed subgroups in §{sec:polish-group-orbit-er}. Quotient Polishness is an
    input to the individual-orbit and Effros arguments.

*   The \termforward{Friedman--Stanley theorem} in §{sec:countable-graphs-case-study}. Composition with its graph
    coding gives universality for classification by countable structures.

*   \termforwardas{Hjorth theorem}{Hjorth's turbulence theorem} in §{sec:polish-groups-turbulence}, together with
    the closed-subgroup logic-action coding of §{sec:logic-actions}. We derive the incompatibility of turbulence
    with that classification.

*   The cylinder-density theorem in §{sec:random-forcing-detail}. We use its almost-everywhere conclusion to show
    that the density-exception set is null and hence avoided by the random generic point.

*   The Kondo--Addison basis theorem and agreement of relative constructible hierarchies in
    §{sec:forcing-absoluteness}. Shoenfield absoluteness is derived from these inputs and the locally proved tree
    absoluteness.

*   The projectively definable well-order in the constructible universe in §{sec:forcing-independence-regularity}.
    The Vitali-selector argument is proved from a supplied well-order and its definability.

*   Density of compactly supported continuous functions in $L^1$ in §{sec:tte-fourier-norm-names}. This supplies
    existence of interval-step names; their transformations are constructed locally.

*   Diaconescu's theorem in §{sec:effective-topos-internal-logic}. Its implication from full choice to excluded
    middle gives failure of full choice after failure of excluded middle has been established.

*   Numeralwise representability, finite-numeral arithmetic, and effective proof-certificate coding in
    §{sec:first-incompleteness}. The Rosser separation argument is proved from these arithmetization inputs.

**Results stated without their proofs.** The following statements and comparisons are also external. They must not
be counted as proved here merely because a nearby construction or a special case is formalized.

*   The \termforward{Lebesgue--Hausdorff theorem}, converse direction, in §{sec:baire-class-functions};
    completeness of the set of valid Borel codes in §{sec:borel-codes-pi11}; and strictness of the projective
    hierarchy in §{sec:projective-hierarchy}.

*   The Fell-topology comparison and Kuratowski--Ryll-Nardzewski selection theorem in §{sec:effros-borel}.

*   The analytic perfect-set and regularity results recorded in §{sec:regularity-independence}; the
    Martin--Harrington sharp characterization in §{sec:analytic-projective-det}; and the Martin--Steel--Woodin and
    Martin--Steel theorems in §{sec:axiom-of-determinacy} and §{sec:martin-steel-pd}.

*   Strictness of the difference hierarchy in §{sec:hausdorff-difference-hierarchy}, and the Steel--Van Wesep
    structure theorem and exact ordinal length of the Borel Wadge hierarchy in §{sec:wadge-borel-hierarchy}. Wadge
    semi-linearity and Martin--Monk well-foundedness are proved here.

*   Birkhoff--Kakutani in §{sec:polish-groups-defn}; the \termforward{Feldman--Moore theorem}, universality of the
    free-group shift, and the Dougherty--Jackson--Kechris hyperfiniteness results in
    §{sec:countable-borel-er-hyperfinite}.

*   The Solovay model and projective-regularity consistency results, and Shelah's lower consistency bound, in
    §{sec:regularity-independence} and §{sec:forcing-independence-regularity}.

*   Kleene's tree theorem in §{sec:lightface-boldface}; completeness of Kleene's ordinal-notation set and Spector
    uniqueness across notations in §{sec:edst-ordinal-notations}; and Spector--Gandy in §{sec:edst-spector-gandy}.

*   The valuation--integral characterization of computable probability measures and the strict distinctions
    between the randomness notions in §{sec:tte-algorithmic-randomness}; computability of the unitary $L^2$
    Fourier transform and inverse in §{sec:tte-representation-strength}.

*   The de Brecht characterizations, closure results, and generalized hierarchy theorems in
    §{sec:quasi-polish-spaces}, and the Schröder--de Brecht admissible representation theorem in
    §{sec:domains-tte-equivalence}.

*   The general Hyland--Johnstone--Pitts tripos-to-topos theorem in §{sec:realizability-tripos} and the
    localic-topos identification in §{sec:localic-tripos-forcing-extensions}. The concrete effective-topos
    category, finite limits, exponentials, and classifier are constructed here.

*   The standard realizability validations of Church's Thesis, Markov's Principle, and the Continuity Principle in
    §{sec:effective-topos-internal-logic}, including the Kreisel--Lacombe--Shoenfield/Ceitin theorem. These are
    distinct from the finite-use theorem for TTE realizers proved here.

**Specialist background and surveys.** The examples also use Anderson and Anderson--Kadec homeomorphism theorems
in §{sec:sequence-spaces}, local-field facts in §{sec:polish-groups-defn}, and spectral and operator-algebra
results in §{sec:borel-reducibility} and §{sec:banach-spaces-case-study}. General categorical facts, including
Yoneda and the standard theory of adjunctions and topos logic, are recalled in
§{sec:appendix-category-realizability}. These backgrounds are not additional local proofs.

The classification landmarks in §{sec:above-e0}, the Vaught-conjecture and Ding--Zheng discussions in
§{sec:polish-groups}, the large-cardinal and forcing developments in §{sec:martin-steel-pd} and
§{sec:forcing-absoluteness}, the true-stage applications in §{sec:edst-true-stages}, and the
realizability-subtopos research in §{sec:weihrauch-lpo-choice} and §{sec:effective-topos-index-zero-selection} are
cited surveys. Their cited classifications and model constructions are not used as unmentioned steps in the local
proofs.

The Lean boundary is recorded separately from this expository boundary: an external ingredient may be an explicit
theorem hypothesis, a checked library theorem, or a cited statement with no local formalization. A list of Lean
axioms does not enumerate theorem hypotheses, and a matched booklink does not certify every sentence in a linked
paragraph. The inventory therefore uses both the formal statements and the cited passages, rather than inferring
external dependencies from coverage alone.

<!-- formalization: skip-end -->

## Expected Reader {#sec:expected-reader}

<!-- formalization: skip-begin (preface reader prerequisites, not a proof obligation) -->

The starting prerequisites are **standard undergraduate point-set topology and a first course in measure theory**.
On the topology side, this means
metric spaces, completeness, compactness, separability, Baire category, continuous functions, homeomorphisms, and
ordinary comfort with the real numbers and $\varepsilon$-$\delta$ arguments. On the measure side, it means
$\sigma$-algebras, measurable functions, finite measures, Lebesgue integration and the standard convergence theorems,
product measures, and basic independence.

The later chapters are at graduate level. The appendices supply definitions and background arguments, but the proofs
of Silver's dichotomy and the HKL dichotomy, the internal forcing constructions,
and the realizability chapters require sustained work with several layers of coding. On a first reading,
it is reasonable to learn the statements and applications
of these results before studying their proof constructions. The reading paths below indicate where to return.

No prior graduate course in real analysis, functional analysis, or category theory is required for the core
development. Later specialist applications import conditional-expectation and disintegration machinery, compact
spectral and operator-algebra facts, and categorical metatheorems.
Polish-space-specific measure tools, such as regularity, probability measures
on Polish spaces, disintegration, zero-one laws, and measure algebras, are developed or stated where they are used in
§{sec:borel-measures}.

For the later chapters, the appendices collect the background used from set theory, computability, and
category theory. They are concise guides for review and reference. Readers new to one of these subjects
should first learn its foundations from an introductory textbook before following the reading path that
uses it. The appendices then help locate the definitions and results needed here:

*   §{sec:appendix-metric-spaces} — basic definitions of metrics and topology, and metric-space cover refinements.
*   §{sec:appendix-logic} — first-order syntax, deduction, semantics, and Gödel completeness.
*   §{sec:appendix-set-theory} — ZFC, ordinals, transfinite recursion, cardinality, the cumulative hierarchy, universe
    conventions, and the Lévy hierarchy.
*   §{sec:appendix-internal-models} — transitive models, internal constructions, ranks, recursion,
    and ordinal enumerations.
*   §{sec:appendix-forcing-background} — forcing notions, names, the forcing theorem, and generic extensions.
*   §{sec:appendix-borel-absoluteness} — internal Borel interpretations, rank certificates, and closed inclusions.
*   §{sec:appendix-measure-absoluteness} — internal approximations, real measure values, and measure absoluteness.
*   §{sec:appendix-random-forcing} — internal measure algebras, Borel truth, and random generic points.
*   §{sec:appendix-lambda-computability} — lambda calculus, numerical computation, program indices,
    and universal evaluation.
*   §{sec:appendix-type-two-computation} — input names, relative computation, and represented-space realizers.
*   §{sec:appendix-effective-computations} — programs for metric tests, trees, jumps, ordinals, and
    Borel codes.
*   §{sec:appendix-category-realizability} — categories, toposes, and partial combinatory algebras.

A reader can work through an appendix before the chapter that depends on it, or use the cross-references as a glossary
while reading.

<!-- formalization: skip-end -->

## Reading Paths {#sec:reading-paths}

<!-- formalization: skip-begin (preface reading guidance, not a proof obligation) -->

**Shared core.** Read Polish spaces, cylinders and trees, the Borel hierarchy, perfect sets, and the
definition and concrete examples of standard Borel spaces. Continue through Cauchy names and Polish
embeddings/refinements to analytic sets and Lusin--Suslin. Then read
§{sec:standard-borel-classification-closed-sets} to see how Lusin--Suslin completes the proof that all
uncountable standard Borel spaces are Borel-isomorphic. The longer concrete-model
constructions and Baire-class refinements can be revisited for their applications.

**Measures or games.** For probability, continue to §{sec:borel-measures}; use the chapter entry guide for the
conditional-expectation input to disintegration. To compare sets by Wadge reducibility, read strategies and
the Borel determinacy statement in §{sec:determinacy}, then §{sec:wadge}. The full determinacy proof can be deferred.
Neither route requires the other in full: only the measure-regularity game needs the indicated measure
background.

**Classification and its proofs.** Read §{sec:polish-groups} and §{sec:borel-reducibility}, using the zero-one
law in §{sec:zero-one-laws} for nonsmoothness. First use the Silver and HKL statements to understand their
classification consequences. For the proofs, continue through §{sec:effective-dst} and the boundedness,
separation, and uniform-code tools in §{sec:effective-dst-ranks} to §{sec:effective-dst-dichotomies}, then
return to the classical deductions. The numerical and input-query prerequisites are specified at the
effective-DST chapter entries; forcing extensions are not needed for this proof route.

**Names and computation.** From §{sec:cauchy-representation-admissibility}, especially the binary and
signed-digit examples, go directly to §{sec:computable-polish-tte}. Use §{sec:lambda-calculus},
§{sec:lambda-basic-data}, and §{sec:lambda-input-realizers} for the computation conventions. Read the
input/output guarantees first and consult reduction-certificate and program-construction proofs when verifying
implementations. Then choose §{sec:computable-analysis} for compactness, measures, and Fourier examples,
§{sec:computational-choice-randomness} after the cylinder-measure algorithms, or §{sec:weihrauch-reducibility} directly
from represented maps. The effective-DST rank and dichotomy chapters can be skipped on this route.

**Forcing.** After category, Borel codes, and measure algebras, read §{sec:forcing}. Use the names and truth
statements in §{sec:forcing-names-valuation} and §{sec:forcing-relation} first. To check the internal
constructions, return through §{sec:appendix-logic}, §{sec:appendix-set-theory}, and §{sec:appendix-internal-models},
then follow §{sec:appendix-borel-absoluteness}, §{sec:appendix-measure-absoluteness}, and
§{sec:appendix-random-forcing} in order. §{sec:forcing}
identifies which examples require each layer.

**Domains and realizability.** From admissible representations and the TTE foundations, proceed to
§{sec:domain-theory-quasi-polish}. Use §{sec:cat-basics} and §{sec:cat-equivalences} for the representation
comparison. For §{sec:effective-topos} and §{sec:inside-effective-topos}, add finite limits, exponentials,
internal logic, PCAs, and assemblies from the indicated sections of §{sec:appendix-category-realizability}.
The tripos-to-topos metatheorem can be used as a stated result. Numerical indices, rather than arbitrary
external names, are essential for the effective-topos interpretation.

The following diagram records chapter references. A reference may supply a proof prerequisite, an application,
or a comparison; the routes above and the chapter entry guides distinguish those roles. The diagram is not a
requirement to read every earlier chapter.

\begin{center}
\DependencyGraph
\end{center}

<!-- formalization: skip-end -->

## Terminology {#sec:terminology}

\begin{mathmeta}
  \vars{n}{Nat}
  \vars{x}{Real}
\end{mathmeta}

<!-- formalization: skip-begin (preface notation conventions, not a proof obligation) -->

This section records only global conventions used throughout the text. Topic-specific notation is introduced where it
first becomes active.

*   **Canonical.** This emphasizes independence from arbitrary auxiliary choices, relative to the specified objects
    and structure. When this independence holds only up to isomorphism, we specify the intended identification.
*   **Standard.** This indicates an established convention or a designated reference construction. The word alone
    does not assert uniqueness or independence of choices.
*   **Natural.** In mathematical usage, this emphasizes compatibility with the relevant maps. When naturality is
    meant in the categorical sense, we specify the maps and the commutativity condition. Ordinary uses, such as
    *natural entry point* for a suitable place to begin, are also allowed.

These are distinctions of emphasis, and a construction can be both canonical and natural. Established technical
terms, such as standard Borel space, retain their specific definitions.

*   **Countability.** A set is \termdefine{countable} if it admits an injection into $\omega$. This includes finite sets
    and the empty set. An infinite countable set is called \termdefine{countably infinite}.

*   **Spaces and separation axioms.** Topological spaces may be empty. Separation axioms such as the Hausdorff
    property are assumed only when stated or implied by other hypotheses. In particular, Polish spaces are Hausdorff
    because they are metrizable.

*   **Neighborhoods.** A neighborhood of a point is a set containing an open set that contains that point. A
    neighborhood need not itself be open; when this is required, we say "open neighborhood."

*   **Compactness.** Compact means that every open cover has a finite subcover. The word itself does not include
    a Hausdorff assumption. A compact subset is compact with its subspace topology.

*   **Subspaces and products.** Unless another topology is specified, subsets of topological spaces carry the
    subspace topology, and products carry the product topology.

*   **Monotonicity.** Increasing and decreasing allow equality. We use "strictly increasing" and "strictly
    decreasing" when strict inequalities are required.

\begin{mathmeta}
  \define{IncludedIn,StrictlyIncludedIn,PowerSet}
\end{mathmeta}

*   **Subset ($A \IncludedIn B$).** We use $A \IncludedIn B$ for inclusion, which allows equality, and $A
    \StrictlyIncludedIn B$ for strict inclusion. We do not use $\subset$.
\begin{mathmeta}
  \define{setminus,SetDifference}
\end{mathmeta}

*   **Power set ($\PowerSet{A}$).** We write $\PowerSet{A}$ for the set of all subsets of $A$.
*   **Set difference ($\SetDifference{A}{B}$).** We write $\SetDifference{A}{B}$ for the elements of $A$ that are not in
    $B$; in particular, $\SetDifference{A}{\{x\}}$ removes the point $x$ from $A$.
\begin{mathmeta}
  \define{disjointUnion,ExternalDisjointUnion,internalDisjointUnion,InternalDisjointUnion}
\end{mathmeta}

*   **External disjoint union ($A \disjointUnion B$).** We write $A \disjointUnion B$ when the two summands are treated
    as tagged, disjoint copies even if the underlying sets overlap.
    For indexed external sums, we write $\ExternalDisjointUnion_{i\in I} A_i$.
*   **Internal disjoint union ($A \internalDisjointUnion B$ and $\InternalDisjointUnion_{i\in I} A_i$).** We use the
    $\uplus$ notation for an ordinary union to indicate explicitly that the constituent sets are pairwise disjoint. No
    tags
    are added.
\begin{mathmeta}
  \define{NN,ZZ,QQ,R}
\end{mathmeta}

*   **Number sets ($\NN$, $\ZZ$, $\QQ$, $\R$).** Natural numbers, integers, rationals, reals. We take $\NN = \{0, 1, 2,
    \ldots\}$, including $0$.
\begin{mathmeta}
  \define{Pair,Tuple,OpenInterval,SingletonSeq,ClosedInterval,LeftClosedInterval,RightClosedInterval}
\end{mathmeta}

*   **Pairs, tuples, and intervals ($\Pair{a}{b}$, $\Tuple{a,b,c}$, $\OpenInterval{a}{b}$).** Ordered pairs
    and tuples are written with angle brackets. $\Pair{a}{b}$ is the pair of two objects: a point of a product,
    the coordinates of a point, or a structure such as $\Pair{X}{\tau}$, a set equipped with a topology; tuples
    of three or more components, such as the language $\Tuple{\mathrm{Rel}_L,\mathrm{Fun}_L,\mathrm{ar}_L}$,
    are written $\Tuple{a,b,c}$ in the same way. Read set-theoretically, the pair is the Kuratowski pair
    $\Pair{a}{b} = \{\{a\}, \{a, b\}\}$ of §{sec:zfc-axioms}; the angle-bracket form is used for
    pairs in every reading. Parentheses are reserved for the open interval: $\OpenInterval{a}{b}$ is the set
    $\{x \in \R : a < x < b\}$ in $\R$. Two further operators print in the same angle brackets and are
    told apart by the sorts of their entries, recorded with each operator's type signature in the notation
    registry: the pairing of names $\NamePair{p}{q}$ is a name of the pair, and the recursive pairing of
    numbers $\NatPair{m}{n}$ is a number. The one-term sequence is written $\SingletonSeq{a}$.
    Intervals with endpoints included are written $\ClosedInterval{a}{b}$, $\LeftClosedInterval{a}{b}$,
    and $\RightClosedInterval{a}{b}$; brackets are used for no other purpose.
\begin{mathmeta}
  \define{Length,Abs,Card,UnderlyingSet,Floor}
\end{mathmeta}

*   **Lengths, absolute values, cardinalities, and underlying sets ($\Length{s}$, $\Abs{x}$, $\Card{X}$,
    $\UnderlyingSet{X}$).** Vertical bars carry four different operators, told apart by the sort of the
    argument: $\Length{s}$ is the length of a finite sequence or word, $\Abs{x}$ is the absolute value
    (or modulus) of a number, $\Card{X}$ is the cardinality of a set, and $\UnderlyingSet{X}$ is the
    underlying set of a structured object such as an assembly or a tripos object. The floor of a real
    number is $\Floor{x}$.
\begin{mathmeta}
  \define{RestrictedSet}
\end{mathmeta}

*   **Restriction subscripts.** We use subscript conditions to restrict an ambient set:
    $\RestrictedSet{\NN}{\ge 1} = \{n \in \NN : n \ge 1\}$, $\RestrictedSet{\R}{>0} = \{x \in \R : x > 0\}$, and so on.
    More generally, if $R$ is a relation on $P$ and $t\in P$, then
    $$\RestrictedSet{P}{R t}:=\{s\in P:s\,R\,t\}.$$
    For an ordered set $\Pair{P}{\le}$, this gives the lower and upper sections
    $$\RestrictedSet{P}{\le t}=\{s\in P:s\le t\},
    \qquad
    \RestrictedSet{P}{\ge t}=\{s\in P:s\ge t\}.$$
\begin{mathmeta}
  \define{Ball,MetricBall,AmbientBall,Closure,AmbientClosure}
\end{mathmeta}

*   **Metric balls ($\Ball{x}{r}$, $\MetricBall{d}{x}{r}$).** For a metric space $\Pair{X}{d}$, write
    $$\Ball{x}{r}:=\{y\in X:d(x,y)<r\}$$
    for the open ball with center $x$ and radius $r>0$.
    When the metric must be shown, write $\MetricBall{d}{x}{r}$; when the ambient space must be shown, write
    $\AmbientBall{X}{x}{r}$.
*   **Closures ($\Closure{A}$).** For a subset $A$ of a topological space, write
    $\Closure{A}$ for its closure. When the ambient space must be shown,
    write $\AmbientClosure{X}{A}$ for the closure of $A$ inside $X$.
\begin{mathmeta}
  \define{Diameter,MetricDiameter}
\end{mathmeta}

*   **Diameters ($\Diameter{A}$, $\MetricDiameter{d}{A}$).** For a bounded subset $A$ of a metric space with the ambient
    metric fixed by context, $\Diameter{A}$ denotes its diameter. The empty set has diameter $0$. For a nonempty bounded
    set, when the metric must be shown explicitly, write
    $$\MetricDiameter{d}{A}:=\sup\{d(x,y):x,y\in A\}.$$
    We describe an unbounded set as having infinite diameter rather than assign it a real-valued supremum.
*   **Ordinals.** We use the von Neumann convention throughout, so each ordinal is the set of strictly smaller ordinals:
    $\alpha = \{\beta : \beta < \alpha\}$. In particular, $0 = \emptyset$, $1 = \{0\}$, $2 = \{0, 1\}$, and $\omega =
    \NN$. Although $\omega$ and $\NN$ are literally the same set, we usually write $\NN$ when arithmetic is in play and
    $\omega$ when ordinal structure or tree indexing is in play. For background, see
    §{sec:ordinals-von-neumann}--§{sec:ordinals-cofinality}.
\begin{mathmeta}
  \define{Sequence,IndexedFamily}
\end{mathmeta}

*   **Sequences and indexed families.** A sequence in $X$ is a function $x:\omega\to X$.
    We write $\Sequence{x_n}{n\in\omega}$ for this function,
    where $x_n=x(n)$ is its $n$th term. The subscript specifies the index range; for example,
    $\Sequence{x_n}{n\ge1}$ starts at $1$. We write $\IndexedFamily{U_i}{i\in I}$ for a family with index set $I$.
    When this notation is used as a set, it means the range $\{U_i:i\in I\}$, so repeated members occur only once.
\begin{mathmeta}
  \define{DomainOf,PartialFunctionMap,RelationComposition,InjectionMap,SurjectionMap}
\end{mathmeta}

*   **Domain ($\DomainOf{f}$).** The domain of a function $f$.
*   **Partial functions ($\PartialFunctionMap{f}{X}{Y}$).** This means that $f$ is a single-valued partial function
    whose domain is some subset of $X$. We use this notation instead of the harpoon notation common in computability
    texts.
*   **Composition ($\RelationComposition{S}{R}$).** For relations $R \IncludedIn X\times Y$ and $S \IncludedIn Y\times
    Z$, write
    $$\RelationComposition{S}{R}:=\{\Pair{x}{z}:\exists y\in Y\ (\Pair{x}{y}\in R\text{ and }\Pair{y}{z}\in S)\}.$$
    Function composition is the special case where $R$ and $S$ are graphs of functions; thus for $f:X\to Y$ and $g:Y\to
    Z$, $\RelationComposition{g}{f}$ sends $x$ to $g(f(x))$.
*   **Injections ($\InjectionMap{f}{X}{Y}$).** This means that $f$ is one-to-one as a map into $Y$.
*   **Surjections ($\SurjectionMap{f}{X}{Y}$).** This means that $f$ is onto $Y$.
\begin{mathmeta}
  \define{funcspace,seqPower}
\end{mathmeta}

*   **Function powers ($\funcspace{B}{A}$).** The notation $\funcspace{B}{A}$ means the set of all functions $B \to A$;
    the exponent is the domain and the base is the codomain. When $B$ is an ordinal $\beta$, we read a function in
    $\funcspace{B}{A}$ as a $\beta$-indexed sequence. Thus $\seqPower{A}{n}$ denotes the set of sequences of
    length $n$ with entries in $A$, for $n < \omega$, while $\seqPower{A}{\omega}$ is the space of infinite sequences
    with alphabet $A$. This notation collides with ordinal exponentiation when both $A$ and $B$ are ordinals. In the
    main text, $\omega^\omega$ denotes Baire space, the set of functions $\omega \to \omega$; §{sec:ordinals-arithmetic}
    explicitly marks the different ordinal-arithmetic reading.
<!-- Author note: Readers do not see the source-level macro call, only the rendered notation A^B. \funcspace{B}{A}
renders as A^B. First arg is the domain (= the exponent in the rendered output); second arg is the codomain (= the
base). The macro intentionally takes the domain first so that the macro-argument order matches the visual position of
the exponent in A^B. -->
\begin{mathmeta}
  \define{restrict}
\end{mathmeta}

*   **Restriction ($\restrict{f}{A}$).** For a function $f : X \to Y$ and a subset $A \IncludedIn X$, $\restrict{f}{A} :
    A \to Y$ denotes the restriction of $f$ to $A$.

<!-- Lean notation correspondence for the global notation above.

| Book notation | Lean notation |
| --- | --- |
| $A \IncludedIn B$ | `Set.Subset A B` |
| $A \StrictlyIncludedIn B$ | proper subset order on sets |
| $\PowerSet{A}$ | `Set alpha` for the power set of a type's carrier; if `A : Set alpha`, then `Set.powerset A` or
`{s : Set alpha // s ⊆ A}` |
| $\SetDifference{A}{B}$ | `Set.diff A B` |
| $A \disjointUnion B$ | `Sum alpha beta` |
| $\ExternalDisjointUnion_{i\in I} A_i$ | indexed `Sigma`/topological sum |
| $A \internalDisjointUnion B$ | `Set.union A B` plus disjointness |
| $\InternalDisjointUnion_{i\in I} A_i$ | `Set.iUnion A` plus disjointness |
| $\NN$, $\ZZ$, $\QQ$, $\R$ | `Nat`, `Int`, `Rat`, `Real` |
| $\RestrictedSet{P}{\le t}$ and variants | `setOf`, `Set.Iic`, `Set.Ici`, `Set.Iio`, `Set.Ioi` |
| $\Ball{x}{r}$, $\MetricBall{d}{x}{r}$ | `Metric.ball x r` |
| $\Closure{A}$ | `closure A` |
| $\Diameter{A}$ | `Metric.diam A` for bounded sets; `Metric.ediam A` for the extended diameter |
| ordinals | `Ordinal` |
| $\PartialFunctionMap{f}{X}{Y}$ | usually a domain predicate/subtype; `Part` when partiality is the object |
| $\RelationComposition{S}{R}$ | `Relation.Comp` |
| function composition | `Function.comp g f` |
| $\InjectionMap{f}{X}{Y}$ | `Function.Injective f` |
| $\SurjectionMap{f}{X}{Y}$ | `Function.Surjective f` |
| $\funcspace{B}{A}$ | function type `B -> A` |
| $\seqPower{A}{n}$ | function type `Fin n -> A` |
| $\restrict{f}{A}$ | `Set.restrict A f` |
-->

<!-- formalization: skip-end -->

\part{Polish Spaces and Borel Structure}\label{part-topological-core}
