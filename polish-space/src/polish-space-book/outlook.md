# Outlook {#sec:outlook}

<!-- formalization: skip-begin (survey chapter; claims are cited or refer back to their proof chapters) -->
The preceding sections developed \termuseas{Polish space}{Polish spaces} as a common infrastructure for topology,
measure, definability, \termuse{forcing}, computability, and classification. The point is not just that these subjects
share examples such as $\R$, $\CantorSpace$, or $\BaireSpace$. They share a technical language:
\termuseas{standard Borel space}{standard Borel spaces}, \termuseas{analytic set}{analytic sets}, games, regularity,
\termuse{Borel reducibility}, \termuseas{Polish group}{Polish-group} actions, and effective representations.

## The Common Language {#sec:fr-common-language}

Classical descriptive set theory begins with definable subsets of \termuseas{Polish space}{Polish spaces}:
\termuseas{Borel set}{Borel sets}, \termuseas{analytic set}{analytic sets}, projective sets, and their regularity
properties. The later sections show that this same language also controls objects that are not merely subsets. A
probability measure on a \termuse{Polish space}, a \termuse{forcing} notion built from
\termuseas{Borel set}{Borel sets} modulo null or meager ideals, a \termuse{represented space} in computable analysis,
and an orbit equivalence relation of a \termuseas{Polish group}{Polish-group} action all rely on the same
standard-Borel and analytic machinery.

This is why \termuseas{Polish space}{Polish spaces} serve as the base category for so many different theories. Their
topology is rich enough for analysis, their Borel structure is rigid enough for classification, and their definable
sets are stable enough to support games, \termuse{absoluteness}, and effective coding.

## Two Internal Readings: Forcing and Realizability {#sec:fr-forcing-realizability}

The same descriptive machinery supports two foundational lenses developed throughout the text:

*   **\termuseas{forcing}{Forcing}** extends a ground model of ZFC by adjoining generic objects. Suitable choices
    of forcing can give extensions satisfying principles such as $\neg$CH. The classical theory of
    \termuseas{Polish space}{Polish spaces} holds in the extension, but a ground-model code must be interpreted there:
    its associated completion can contain new points. Cardinalities and higher projective regularity can also change.
*   **The \termuse{effective topos}** interprets mathematics using natural-number realizers. The computable-point
    assemblies of §{sec:inside-effective-topos} connect it to \termuseas{Polish space}{Polish spaces} equipped with
    computable presentations. This connection does not retain all external points or identify the internal universe
    with TTE. Internally, excluded middle and full choice fail, while Church's Thesis and the stated Continuity
    Principle hold for the specified internal objects.

Both frameworks turn *external* facts about Polish spaces — which reals are random, which functions are computable —
into *internal* statements within a model. Forcing changes which sets exist around the Polish space; realizability
changes what counts as evidence for maps, points, and predicates inside it. In both cases, descriptive set theory
supplies the translation layer between external presentations and internal mathematics.

## From Definable Sets to Classification Problems {#sec:fr-classification-shift}

The modern development of descriptive set theory also shifts the main object of study. Classical DST asks how
complicated a definable set $A \IncludedIn X$ is. Invariant DST asks how complicated a quotient-like object $X/E$ is,
where $E$ is an equivalence relation such as isomorphism, conjugacy, unitary equivalence, or orbit equivalence.

Kechris's "new directions" survey frames this as the study of *singular spaces* $X/E$ and Borel reducibility
[@Kechris1999]. A classification theorem is no longer just a list of invariants; it is a statement that the equivalence
relation sits below some benchmark in the Borel-reducibility hierarchy. Conversely, a non-classification theorem says
that no invariant of a prescribed type can separate the classes.

## Modern Research Programs {#sec:fr-modern-dst}

The survey literature from 2000 onward shows that contemporary descriptive set theory is best understood as
several linked programs, not as a single linear extension of the classical Borel/projective hierarchy.

**Invariant descriptive set theory.** Becker--Kechris, Becker, Hjorth, and Gao organize the program around Polish-group
actions, orbit equivalence relations, logic actions, turbulence, and the question of when a classification problem
admits concrete invariants [@BeckerKechris1996; @Becker2001; @Hjorth2000; @Gao2009]. This is the conceptual home of
§{sec:borel-reducibility} and §{sec:polish-groups-reducibility}.

**Countable Borel equivalence relations.** Jackson--Kechris--Louveau isolate the countable-Borel-equivalence-relation
program: hyperfiniteness, amenability, treeability, universality, and the structure of equivalence relations generated
by countable group actions [@JacksonKechrisLouveau2002]. Kechris--Miller connects that Borel theory to measured orbit
equivalence, cost, and rigidity [@KechrisMiller2004]. Hjorth's Handbook survey presents Borel equivalence relations as a
crossroads of dynamics, ergodic theory, group theory, functional analysis, model theory, and inner-model questions about
definable cardinality [@Hjorth2010].

**Descriptive combinatorics.** The later landscape moves the same machinery into graph-theoretic form. Descriptive graph
combinatorics asks which constructions survive when colorings, matchings, tilings, independent sets, or transversals
must be Borel, measurable, or Baire measurable [@KechrisMarks2016; @Pikhurko2021; @Marks2022]. Hyperfiniteness and Borel
asymptotic dimension turn orbit-equivalence questions into large-scale graph invariants
[@ConleyJacksonMarksSewardTuckerDrob2023].

**Effective and generalized extensions.** Effective and quasi-Polish DST pushes the same hierarchies through computable
names, domains, and non-Hausdorff spaces, connecting the classical Polish-space theory to computable analysis and
semantics [@Selivanov2023]. Recent effectivization and priority-method work shows that separation, Wadge-theoretic, and
Borel-combinatorial arguments can have new computability-theoretic proofs [@Thornton2025;
@DayGreenbergHarrisonTrainorTuretsky2024]. Generalized descriptive set theory pushes in the opposite direction, asking
which parts of the Polish-space template survive when $\omega$ is replaced by larger cardinals [@Iannella2024;
@DimonteMottoRos2025].

## Case Study: Operator Algebras {#sec:fr-operator-algebras}

Operator-algebra classification is one of the largest external consumers of Polish-space descriptive set theory, and was
historically one of its main motivations.

This section is a survey bridge, not a development of operator-algebra machinery. It records where the
descriptive-set-theoretic tools of the book enter classification problems for C\*-algebras and factors, and it points to
the specialist literature for the operator-algebraic proofs.

**Borel reducibility on classification problems.** The space of separable C\*-algebras carries a natural
standard Borel structure. Isomorphism is universal, under Borel reducibility, among orbit equivalence relations
of Polish-group actions, already for separable nuclear C\*-algebras [@Sabok2016]. Thus every turbulent orbit
benchmark reduces to it; universality does not assert a strict inequality above every such benchmark.
The *Elliott classification program* uses K-theory, traces, and their pairings to obtain complete invariants
on suitable classes of C\*-algebras. A classification by these invariants does not by itself give a Borel
reduction: one must also specify the coding and equivalence relation for the invariants and verify that the
assignment is Borel. The obstruction methods of §{sec:polish-groups-turbulence} and §{sec:borel-reducibility}
address these definability requirements.

**Hjorth turbulence on $\mathrm{II}_1$ factors.** Isomorphism of $\mathrm{II}_1$ factors is not classifiable
by countable
structures [@SasykTornquist2009]: turbulent benchmark actions in the sense of §{sec:polish-groups-turbulence}
Borel-reduce into the isomorphism relation. Isomorphism of separable Banach spaces is likewise not classifiable by
countable structures; more strongly, every analytic equivalence relation Borel-reduces to it
[@FerencziLouveauRosendal2009].

**Historical lineage.** The \termuse{Glimm--Effros dichotomy} of §{sec:e0-glimm-effros} and the
\termuseas{Effros's orbit theorem}{Effros theorem} on orbit topology from §{sec:polish-group-orbit-er} were both
developed for operator algebras. Glimm and Effros studied the orbit relation of $U(\mathcal H)$ acting on irreducible
representations of a separable C\*-algebra, using all finite Hilbert dimensions as well as the countably infinite
dimension. The dichotomy characterizes the type-I algebras as exactly those with smooth
dual; otherwise $\EventualEqualityER$ embeds. The descriptive-set-theoretic generalization to all Borel equivalence
relations came
nearly three decades later.

**Infinite games.** §{sec:det-implies-regularity} relates \termuseas{Banach--Mazur game}{Banach--Mazur games}
to the Baire property. Each orbit of a continuous Polish-group action is Borel, so its Baire property already
follows in ZFC. For more general projective sets arising in classification, the additional hypothesis of
projective determinacy in §{sec:analytic-projective-det} gives regularity principles. The need for such an
additional hypothesis depends on the particular definability question; it does not follow merely from
passing beyond type-I algebras.

The interface text [@Farah2019] synthesizes model theory, Polish-space descriptive set theory, and operator algebras;
[@KechrisMiller2004] gives the orbit-equivalence side.

## What Each Part Buys You {#sec:fr-what-each-part-buys}

The shared core supplies spaces, names, trees, and Borel structure. The later parts develop routes from that
core rather than a single chain of prerequisites. Measures support probability and random forcing; games
support Wadge comparison; group actions support classification. Cauchy representations lead directly to TTE,
whose foundational chapter supports separate chapters on computable analysis, randomness, and Weihrauch
reducibility. The effective-DST route supplies the Silver and HKL proofs, while domains and realizability
compare different forms of computational evidence. The chapter entry guides specify where these routes meet.

+---------------------------+--------------------------------------+-------------------------------------------------+
| Part                      | Main tools                           | What it lets you say                            |
+===========================+======================================+=================================================+
| Polish spaces and Borel   | Polish spaces, Baire space, standard | The familiar spaces of analysis admit           |
| structure                 | Borel spaces, coding, and admissible | countable descriptions. Points, closed sets,    |
|                           | representations                      | Borel sets, and maps can be coded without       |
|                           |                                      | losing the topology that matters.               |
+---------------------------+--------------------------------------+-------------------------------------------------+
| Definability and          | Analytic sets, Lusin--Suslin, Borel  | Definable sets have regularity properties, game |
| classification            | measures, determinacy, Wadge rank,   | characterizations, ranks, and closure behavior  |
|                           | Polish groups, and Borel             | strong enough to support classification and     |
|                           | reducibility                         | probability.                                    |
+---------------------------+--------------------------------------+-------------------------------------------------+
| Effective definability    | Forcing, lightface hierarchies,      | One can test which constructions are absolute   |
| and forcing               | recursive ordinals, ranks, and       | or generic and how restricting definitions and  |
|                           | effective separation and refinement  | parameters yields effective classification      |
|                           |                                      | proofs.                                         |
+---------------------------+--------------------------------------+-------------------------------------------------+
| Computation and           | TTE, computable analysis,            | One can distinguish continuous transformations  |
| realizability             | randomness, Weihrauch reducibility,  | of names from computable ones and compare       |
|                           | domains, tripos-to-topos, and the    | different forms of computational evidence.      |
|                           | effective topos                      |                                                 |
+---------------------------+--------------------------------------+-------------------------------------------------+
| Outlook and appendices    | Set theory, computability, category  | The foundations become explicit, so the reader  |
|                           | theory, and realizability background | can distinguish topological,                   |
|                           |                                      | descriptive-set-theoretic, set-theoretic, and    |
|                           |                                      | computational arguments.                        |
+---------------------------+--------------------------------------+-------------------------------------------------+

Read this table from left to right as the book's thesis. Polish spaces provide the common arena. Standard Borel coding
makes that arena portable. Analytic and Borel hierarchies measure definability inside it. Games and Wadge ranks organize
the resulting complexity. Measures and category say which definable objects are regular enough for analysis. Borel
reducibility and Polish-group actions then turn this machinery toward classification problems outside descriptive set
theory itself. Forcing tests which conclusions depend on the universe of sets. Computability, domains, and realizability
test which conclusions have effective content.

That is why the same few spaces keep reappearing. $\BaireSpace$ supplies universal coding, $\CantorSpace$ supplies
compact zero-dimensional coding, $\R$ supplies the analytic example, and standard Borel spaces supply the invariant
measurable skeleton. The later theories do not replace this core; they add interpretations of it.

## Closing Perspective {#sec:fr-closing-perspective}

Definability imposes conditions beyond mere existence. A selection function may be required to be Borel or measurable;
a point may be required to be generic over a specified ground model; a construction may be required to be computable
from the given data. In a classification problem, one may prescribe the kind of complete invariants allowed. The
remaining appendices give the logical background needed to formulate and compare these requirements.
<!-- formalization: skip-end -->
