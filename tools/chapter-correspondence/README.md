# Chapter correspondence

Run the complete migration gate for the Polish Spaces chapter:

```sh
make validate-correspondence CHAPTER=polish-spaces
```

The gate builds the shared parser and the configured Lean modules, checks every
source formula and interpretation fragment, and inspects operator heads, explicit
and implicit arguments, and semantic requirements. It exits unsuccessfully for
stale review, unresolved variables/scopes, rejected expressions, missing operator
traces, or changed evidence. Each run writes a separate
`build/validation/correspondence-polish-spaces-*/report.json` with its formula and
operator reports. Successful expression typing is not proof of a displayed
assertion or automatic approval of its mathematical interpretation.

Only `chapters/polish-spaces.json` is registered. The configuration owns the
canonical source, Lake project, imports, open namespaces and review file. Other
chapters retain their existing checks. To migrate a later chapter, register its
configuration, add source-owned bindings and any missing shared notation rules,
review its interpretations and run this same gate; never copy this chapter's
review or mark unsupported formulas as exempt. The transport currently serves
the book's shared `polish-space` Lake project and rejects other project names.

`tools/book-filter/MathSyntax.hs` owns the shared lossless parser and renderer.
`LocatedMath.hs` attaches typed, half-open source spans in Unicode code points.
The chapter API invokes this parser directly and keeps intermediate located
syntax inside Haskell. The `math-syntax-located` and unlocated `math-syntax`
interfaces remain available to existing consumers.
`SemanticExpr.hs` owns the nine shared semantic macro lowerings as an algebraic
data type and rejects unknown operations and wrong arities. `Correspondence.hs`
serves newline JSON requests through `book-filter chapter-correspondence`. `native.py` keeps one
worker alive per Python process; it contains transport and registry adaptation,
not a Python lowering fallback.

`ProofContexts.hs` owns inspection and replay of original Lean contexts, including
hygienic names, local definitions, explicit unfolding and typed kernel paths.
Its context bridge checks original binder identities, local values and proof-path
prefixes; the Python adapter transports only the relevant binder records.
`OperatorProbe.hs` generates instrumented Lean probes; `ContextTemplates.hs` and
`ProbeTemplates.hs` own their Lean programs. `OperatorEvidence.hs` checks targets,
operands, implicit telescope coverage and semantic requirements, and aggregates
multiple calls without hiding a failed call.

## Haskell migration

The Haskell semantic core shares the parser and an internal semantic expression
AST. Python retains CLI/configuration, execution scheduling, Lean server
transport, dependency caches, progress and report persistence. Haskell owns meaning
and correspondence decisions. There is no cross-language AST schema generator.

The semantic layer has four responsibilities:

| Module                   | Responsibility                                                                                                                                                                            |
| ------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `SemanticAST.hs`         | Common expression types and explicit elaboration plans, without JSON encoding or rendering.                                                                                               |
| `ChapterMappingRules.hs` | The Polish Spaces choices of types, Lean realizers and source roles. Further chapters select their own rules here rather than adding mathematical expression constructors for a spelling. |
| `SemanticTrace.hs`       | Source derivations and premise provenance. These annotate evidence and cannot replace the expected Lean function, ordered operands or kernel obligations.                                 |
| `SemanticExpr.hs`        | Review boundaries and the shared ordinary/instrumented renderer.                                                                                                                          |

Rational casts and images use typed coercion/range operations; rational singleton
families use typed lambdas, ordinary singletons and indexed aggregation. Their
Rat/Real domains are selected in the chapter mapping rules. Dependent conditionals
carry their result type explicitly, including the type of each proof branch.
Literal values use one constructor with inferred, fixed, instance, context-witness
or sequence-codomain evidence. A prefix comparison uses a typed operator section;
its implicit argument is no longer a radius-specific AST node. Comparison lists,
shared membership domains and scalar comparison witnesses annotate ordinary
operations with source derivations. Existing report rule names and provenance
keys are preserved for consumers and comparison with reviewed evidence.

Generated ball families still require an explicit chapter recognizer, which
checks the displayed metric, subset, lexical binders and the original premise.
The common AST receives existential binders, set predicates, metric operations
and guarded unions. Premise provenance carries named source references and syntax,
without mandatory ball/radius/diameter fields in the common expression interface.
The metric/subtype adapters and nonemptiness/boundedness proof obligations remain
explicit. Recognition of a familiar notation never supplies a missing proof.

`analyzeChapter` accepts source text, source-owned scopes, notation configuration
and one table of original Lean signatures. `ChapterPreparation.hs` scans Markdown
math, invokes the shared parser, normalizes source evidence, resolves lexical
bindings and splits independent expressions. It then builds the semantic AST and
returns both renderings and source evidence in the same transaction. Python does
not manage or round-trip an intermediate meaning AST. Expression-level batches
serve operator probes. Fine-grained adapters remain for compatibility tests and
inspection utilities; the chapter pipeline does not call them.

`SemanticExpr.hs` owns recursive, ordered macro expressions and distinct
`Candidate a` and `Reviewed a` types with hidden constructors. `review` requires
matching source, rules and Lean fingerprints. Probe rendering accepts candidates;
it cannot produce a reviewed value. The existing Python review gate now delegates
fingerprint comparison to this core. This is not yet an end-to-end typed review
pipeline: report assembly and execution scheduling still run in Python.

`StructuralSyntax.hs` owns token refinement, natural sequence binder candidates,
starred and numeric-subscript names, numeric powers, map signatures, conjunctions,
source-preserving integer-exponent tokens and two-branch cases with hygienic proof names,
map-arrow expressions, bounded infima, convergence candidates, aligned rows/expression lists, literal natural lower bounds, finite/infinite/tail summation bodies, predicate-set generators and typed identity-singleton families, generated metric-ball families and natural-indexed product/disjoint-union/set-family candidates. Its lexical walker
extracts identifier/decorated-name occurrences and unreviewed binder guards in one
native traversal, without assigning Lean binder identities. `extractBindings` then
registers grammar-owned binders for families, comprehensions, sums, infima, maps
and convergence. It retains unapproved guards and candidate metadata until an
explicit rule supersedes the exact source span. Python `leaves` is only an adapter. Recognition cannot approve an
interpretation. Source normalization annotations stay inside the Haskell chapter
transaction. The structural inspection plan also supplies visible operator
candidates and the expressions eligible for nested inspection, preserving their
source spans even when a translation is unsupported.

`SemanticTranslation.hs` builds typed expressions directly over the shared
`LocatedMath` syntax for resolved scalar references, nonnegative numeral literals, parentheses,
four arithmetic operations, unary negation, scalar comparisons/comparison chains,
subscript/superscript application, explicitly bound subscript/starred names and seven basic macros. Resolved Greek-command references,
subtype projections and natural-index offsets retain their source/context identities.
Ordinary function applications retain the source callee identity, exact callee span,
ordered arguments and nested traces. Metric applications preserve independently
sourced carrier/instance expectations and point adapters, including indexed metric
families. Metric evaluation distinguishes a second point from a source-classified
set; the distance-to-set nonemptiness requirement remains kernel checked. Subtype
point applications retain the local-membership adapter. Subtype-range lowering
requires the source set to name the actual predicate of the function's domain,
retaining the function operand and independent domain/codomain expectations.
Decorated range callees are traversed once, so no unused marker is reported.
Unported set syntax and proof-branch equality transport still use the remaining
interpreter; their obligations are not erased by the native path.
Set intersection, union, inclusion, membership, product and difference use ordered
AST operands. Carrier operands retain the explicit universal-set conversion;
indexed carriers retain repeated-call validation. Membership keeps source spans
in point/set order while recording Lean operands in set/point order, with the
independent source-set point adapter and membership instance. Set/carrier equality
retains the distinct source set interpretation. Each expression job carries the
constant registry selected by chapter configuration. Native constant lookup never
invents unregistered declarations, and the registry is included in the cache key.
The real/rational set convention retains the explicit rational embedding and
source operands; the TwoPointSpace macro retains its Bool operator evidence.
Sequence macros build lambda expressions with source binder identities, domain
spans, binding components and declared index origins. Recognition reuses the native
sequence candidate grammar; only resolved lexical binders can become lambda binders.
Map-arrow expressions share that lambda renderer, retaining the resolved source
domain context and lexical identity. Expression jobs distinguish their root from
nested subexpressions; nested arrows cannot introduce unregistered binders.
Defining equalities preserve both source sides, their full source span and an
independently sourced value-type expectation; their proof obligation remains
kernel checked. Empty sets retain the other source set as an ambient witness,
with independent type/instance expectations and no extra witness trace.
Unbounded real intervals retain the endpoint span and order instance, while explicit
nonnegative dimension levels retain their Nat literal and instance evidence.
Positive numeral bases with integer exponents use source-typed Nat-to-Int casts,
integer literals and arithmetic; unary negation and power instances are checked
independently. Multidigit bases remain one source operand.
Real lp sequence spaces retain their Nat index, real coordinates, normed-group
instance and source-typed extended-nonnegative-real exponent. Extended comparison
literals take their domain from resolved source operands; unknown domains cannot
silently select ENNReal. Function declarations retain their domain, codomain and
function as separate source operands. Typed-map equations retain their source-owned
input binder and subspace domain, sharing its ordinary rendering without duplicating
the domain trace. Homeomorphisms retain both spaces and their topology instances.
Finite and indexed coordinate spaces preserve their index/dimension operand and
avoid names already present in the original context; binary sequence alphabets
carry the configured real-sequence embedding explicitly.
Natural-indexed products, dependent disjoint unions and indexed set intersections/unions
now build semantic binders and operations together. Products of subsets retain their
explicit subspace carrier and repeated-call checks. Restricted index domains preserve
the source lower-bound spelling, predicate spans and subtype projection; their
independent lattice/index expectations are generated from the AST. Carrier and set
classification also recognizes these source families when they occur in membership
or set operations. Repeated-coordinate tuples retain their displayed operands and
an ordinary-only type witness, so a typed diagonal-map signature and its defining
equation can use the same native renderer without duplicating witness traces.
Root convergence expressions retain the lexical natural index, source index origin,
sequence body, limit, arrow and binder-component spans. Numeric limits derive their
type and numeral instance from an ordinary-only source sequence witness; the AST
renders both filter expectations independently. Nested arrows cannot introduce
convergence binders, and limits cannot mention their bound sequence index.
Finite, infinite and tail sums build semantic operands over grammar-owned source
ranges, including separate source bounds and real-valued summand lambdas. Tail
reindexing preserves the source index as a local definition. Weighted metric
juxtaposition retains its zero-width source boundary and independent real
multiplication instance. Summability remains a separate kernel-checked requirement.
Explicit-metric balls and diameters retain the actual metric operand, point/set
adapters and independently sourced carrier/instance expectations. Ambient closure
keeps its carrier, topology and subset distinct. Real scalar normalization inserts
source-typed casts for numeric radii and distance/diameter comparisons; only the
outermost comparison treats its final comma or period as sentence punctuation.
Restrictions and compositions preserve the conversion between metric values,
uncurried functions and curried interfaces, including dependent metric families.
Pointwise metric bounds retain their selected source domain and hygienic point
binders. Domain comparisons use identities in the source AST rather than generated
Lean text. Explicit whole-symbol bindings for hatted and primed references retain
their exact spans, and resolving them cannot bypass index-origin restrictions.
Set comprehensions and infimum images share bound-function expressions for their
predicate/image bodies. They retain the resolved lexical binder, original domain
context, optional displayed carrier and all binder/domain/delimiter spans.
Infimum recognition precedes ordinary comprehension recognition, so an image
`\inf\{s:s\in C\}` keeps its image interpretation. Nested comprehensions and
comprehensions inside indexed sets or sums preserve their distinct binders.
Constructed sets also retain their semantic set role in metric applications;
distance to a comprehension uses `Metric.infDist` and still needs independently
checked nonemptiness evidence. The old point interpretation of that formerly
rejected combination is covered by a negative kernel regression. Image-domain,
image-codomain and infimum-instance expectations come from the source AST, while
nonemptiness, lower-bound and defining-equality requirements remain separate.
Two-branch real cases retain source conditions, values, separators and hygienic
proof binders in the AST. Repeated condition evaluations retain all call checks.
Metric points and explicit-metric ball centers in the first branch carry the
scoped equality witness; Lean checks the direction of transport between fibers.
The proof does not escape its branch, and noncomplementary conditions still fail
kernel typing. Tagged dependent pairs retain the source tag and point together
with the unique Nat-indexed family found in the point's original context.
Expression jobs carry the available original binder names/types for dependent
families and explicit numeral witnesses. Chapter reports translate their jobs in
one source transaction with a shared signature table. Single-expression probes
also select their context inside Haskell. The transport excludes declaration proof
bodies and includes the source signatures in its cache key. Batch context selection
runs in Haskell using the original binder names, types, instance flags and local
values, preserving the checks against incompatible proof-context prefixes.
Source-owned numeral domains, radius predicates and contextual literal
interpretations are decoded explicitly. Numeral witnesses retain their original
context and source span; unrelated or missing declarations cannot authorize them.
Shared membership, variable-list order comparisons and point singletons use the
same semantic AST and renderer. General comparisons retain their original source
types; Lean checks that the selected operation and implicit instance exist.
Equality/membership chains retain their own point adapters and ambient evidence;
canonical inclusion maps retain a kernel-checked subset proof. Indexed set
families can occur inside equations, membership and other set operations.
Repeated binary operations separate the source operation, index range, family
and grouping from the selected Lean realizer. Registered intersection and union
folds share the same finite-range renderer and preserve both endpoints and index
origins. An ellipsis cannot select a rule for subtraction or supply an empty
fold's identity. Decreasing families remain a separate order assertion.
Rational singleton unions retain their explicit Real ambient, rational binder,
cast and all source components. Generated set unions retain the displayed
predicate and the bounded-trace source premise, including the metric/subset
identities and the exact trace expression. Their existential predicate uses
typed binders and proof domains in the semantic AST.
Unregistered syntax and binding forms remain explicit unsupported results.
Nested indexed applications retain the independently rendered callee and argument.
Family-origin reindexing requires a source-proved lower bound and retains both
the original operand span and the zero-based target index. Superscripts require
an explicit source selector and a Nat-indexed family. Decorated names require
the exact whole-symbol binding and retain their original context identity. `renderPair` generates the
ordinary term, instrumented term and operator expectations in one traversal.
Operator and operand spans are retained in the AST; expected operands use ordinary
child expressions, while instrumentation uses instrumented children. Domain witnesses
come from source references in the AST, not from inspecting generated Lean syntax.
`translateBatch` accepts multiple expression jobs. The Python adapter caches both
forms together, so the existing ordinary/traced calls reuse the same native result.
Unported syntax and construction annotations explicitly
return `supported: false`; the Python adapter reports them as unsupported. Neither
unsupported results nor transport errors select another interpreter. The old Python
translation function is frozen under `tests/fixtures/` as an independent differential
oracle, never imported by production. Negative tests alter returned candidate terms
while retaining the independent source operands and implicit-instance expectations.
The public macro registry is read-only and delegates rendering to Haskell.

`SourceScopes.hs` normalizes source-owned binding identities, occurrence selectors,
qualified/structured/constant targets and offset/projection constraints. It also
collects required Lean declarations, including proof-only and literal-consumer
contexts. Proof-path validation is shared with `ProofContexts.hs`. The metadata
stage validates literal consumers, explicit numeric/predicate witnesses, rational
ambient declarations, premise text/spans and duplicate/crossing scope intervals.
`sourceScopes` also scans raw source annotations in Haskell. `SourceJSON.hs` uses
Aeson for JSON decoding and audits raw tokens for duplicate keys (including escaped
Unicode keys) and strict integer fields. Unrelated numeric metadata is preserved.
Python `scopes` is only a transport adapter.

`SourceNormalization.hs` attaches explicit literal interpretations, rational
ambient choices, numeric-domain witnesses and source-approved prefix predicates.
It also resolves generated-family restrictions from exact forward premise spans,
rejecting ambiguous premises. Comparison normalization merges only contiguous
source numerals and uses explicit numeric witnesses or source-resolved scalar
types for real/extended-nonnegative-real operands; observed Lean calls supply no
interpretation evidence.
It retains all literal alternatives, selects the innermost numeric scope and keeps
exact numeral/operator spans. These operations do not approve an interpretation.

`VariableResolution.hs` resolves explicit outer source bindings by scope and
occurrence selector against actual Lean telescope/constant records. It preserves
numeric-subscript naming, constant restrictions, scalar index offsets and subtype
projection evidence. Its lexical stage applies local shadowing, hygienic source-based
names, inferred source domains and index-offset cleanup, returning updated binding
effects for later checks. Its domain stage checks source carrier/subset types,
Nat-indexed family kinds, lower bounds and convergence index origins.
`resolveVariables` runs all three stages in Haskell in one transaction; Python
only supplies compact records and retains the updated effect list.

Construction-specific normalization, the remaining `translate`/`traced` rules and coverage assembly still run
in Python. Execution orchestration remains there permanently.
`ExplicitLean` in the native expression type marks that migration boundary;
wrapping a pre-rendered term does not establish structural correspondence.
Migrating these remaining stages is tracked in `todo.md`. Binder/context identities,
ambient carriers, index origins and premises must survive that migration.

The nine registered macro lowerings, context/probe generation and operator evidence
checks already run in Haskell. Lean success remains separate from source-meaning
review. No recognizer, macro lowering or evidence check may grant approval from a
successful Lean result alone. Explicit semantic macros and source-owned metadata
remain preferable to ambiguous presentation-based guesses, regardless of language.

For migration comparisons, run:

```sh
python3 tools/chapter-correspondence/compare_revision.py \
  --revision <reviewed-commit> --baseline <validated-formulas.json>
```

This compares every formula, interpretation and operator trace using the baseline
Lean evidence. It does not perform fresh Lean validation or update review approval.
The revision's interpreter is executed locally; use a trusted repository revision.
After review, run the complete correspondence gate for current Lean evidence.

`notation_rules.py` holds operator heads and named notation profiles and exposes
the native macro registry. Its supported vocabulary grew from Polish Spaces and
does not claim complete coverage for other chapters. Generalizing a rule requires
positive and negative regressions and interpretation review. Chapter settings,
all native modules, Python interpretation code and export transport participate
in the review fingerprint.

Polish Spaces no longer has legacy `\vars` sort annotations. Its natural-number
indices, binder scopes and nested products are checked through the source syntax
and actual Lean contexts. `lean_export.py` owns the shared transport, independent
of `check_sort_pilot.py` and `tools/sort-pilot/`. The latter are compatibility clients
for chapters not yet migrated. New probes use `BOOK_LEAN_EXPORT`; the transport
also accepts the old wire prefix for those clients.

For repeated checks, start `python3 tools/lean_export_server.py serve` and set
`BOOK_LEAN_EXPORT_BACKEND=server`. The daemon retains imports and uses versioned
Lean document changes. The gate still builds the selected modules incrementally and generates a new
report. It reuses successful Lean probes only against the identical generated
input and transitive dependency environment. Restart the daemon after transport
changes.

The lower-level `check.py --chapter polish-spaces` produces the formula report
only; `operator_evidence.py --chapter polish-spaces --report FILE --all --output
FILE` inspects operators. Use the complete gate to establish migration readiness.
Neither command updates `review.json`: a reviewer must examine changed source,
rules and Lean evidence before recording new fingerprints.

## Adding a chapter without copying the checker

Create `chapters/<chapter>.json` with `chapter`, canonical `source`, `leanProject`,
`leanModules`, `openNamespaces`, `notationProfiles`, and a separate `review` path.
The selected Lean modules must import the mathematical infrastructure used by the
shared adapters. `core` provides common constants and operations; `polish-spaces`
adds the book's named-space conventions. Profiles compose explicitly and reject
unknown names, duplicates and conflicting symbol meanings. Implement missing
operators once in the shared engine and registry, with negative regressions;
chapter identity is never a branch in the translation rules.

Generate a draft from the selected modules' current booklinks:

```sh
make suggest-correspondence CHAPTER=polish-spaces
```

This writes `build/chapter-correspondence/polish-spaces/candidates.json`. It
rematches booklinks against the saved source rather than trusting an old sourcemap,
resolves qualified declarations from compiled Lean inventories, and proposes
same-spelling binder matches using exported Lean telescopes. Each candidate has
its source span, declaration evidence, proposed scope/context/bindings, and
unresolved choices. Anonymous/ambiguous declarations and unmatched source spans
stay unresolved. A spelling match is not semantic approval: review lexical
shadowing, the scope boundary, proof-local lets, and the intended construction.
The command never inserts markers or modifies a review/translation file.

## Incremental and full verification

```sh
make validate-correspondence CHAPTER=polish-spaces
make validate-correspondence CHAPTER=polish-spaces CORRESPONDENCE_FLAGS=--full
```

The first command reconstructs the current source inventory and checks review
freshness every time. It reuses individual successful Lean probes from
`build/chapter-correspondence/cache/`. The key includes the exact generated Lean
input, transport implementation and complete transitive import environment.
Module edges come from `.ilean` inventories; the environment fingerprints the
compiled public/private/server/IR artifacts, available dependency sources,
project configuration, toolchain binary and shared libraries. A missing dependency
fails the run. Dependency changes during the run invalidate its result.

A changed expression reexecutes its changed probes; unchanged probes are reused.
An unrelated module outside the import closure does not invalidate the cache.
Changing an imported module invalidates all dependent probes conservatively:
new instances, notation or elaborators can affect expressions that do not name
the changed declaration. Moving a source binder can also change its generated
identity and require rechecking. This is not yet declaration-level dependency
tracking inside a Lean module.

The `--full` command bypasses cache reads and writes newly checked evidence.
Both modes apply the same completeness gate and keep all source formulas in the
report. Neither mode promotes a stale interpretation review. Errors and warnings
are never cached as successful results. Corrupt cache entries are reexecuted.
`report.json` records reused/executed probe counts; `dependencies.json` records
the import closure; `probes.json` and each checked expression/operator's
`validationOrigin` identify the exact executed or reused input. Cache storage is
local build data and can be deleted to force fresh execution.

## Rule and evidence reference

Run `python3 tools/chapter-correspondence/check.py` from a provisioned checkout.
It builds the shared book filter, validates the two imported Lean modules, and
writes `build/chapter-correspondence/polish-spaces/formulas.json`. The report retains every
mathematical occurrence, including headings, examples, index display strings,
and passages marked as formalization skips. It does not use booklink coverage
as expression evidence.

During iteration, run the tests for the changed rule and inspect the affected
formula with `operator_evidence.py --formula-index`. Run `--all` after a stable
batch or a chapter milestone, rather than after each local edit. Reports remain
bound to their source and rule hashes; a partial check does not refresh or
approve a whole-chapter report. Do not edit rules while a report run is active.

Proof-context evidence is fetched in one batch per request, with each root's
proof emitted once. Exact kernel paths prune unrelated branches and stop at
the selected binder. Name-based discovery still searches the whole proof, so
prefer a known path once it has been located. This optimization retains the original let values. The integrated validator
can reuse this probe under the dependency checks described below.

Products `\prod X_n` and `\prod_{n \in \omega} X_n` bind a fresh local
natural-number index when `X` is explicitly mapped to a Nat-indexed type
family. The `binder:product` rule emits a dependent function type and checks
its domain and fiber independently against Lean’s `forallE` node. Range
markers retain their source spans. Other ranges and set-valued products remain
unresolved; a nearby outer index never supplies the omitted binder.

A literal star decoration such as `x^*` or `x^{*}` identifies a named object
only through an explicit binding for `x^*`. It never inherits the binding for
bare `x` or the sequence-superscript selector. The `name:star` trace checks the
actual Lean variable or constant and retains the full decoration span.

A type-family index used as a carrier can occur in several implicit arguments
after elaboration. Its source operator retains every observed call, with
independent target and operand checks; one failed call fails the aggregate.
Other duplicated instrumentation markers remain errors.

An explicit `unfold` path step enters the proof of the constant at that exact
application, substituting its actual universe and term arguments. Normal name
searches never unfold referenced declarations. For bounded discovery, pass
`root.<path>.unfold::localName` to `proof_contexts.py`, then retain the returned
exact path in source metadata. Each unfolded declaration is emitted once per
root batch; its full signature and body participate in the context fingerprint.
Hygienic Lean binder names receive collision-safe names while retaining their
original names in the evidence.
When joining a declaration's telescope to its proof-local prefix, the bridge
compares these original names. A printable hygiene alias alone does not change
binder identity; types, instance flags, let values, and ancestry must still
match.

For repeated checks, start `python tools/lean_export_server.py serve` in a
long-lived process. `status` reports the live process and `stop` shuts it down.
The exporter automatically uses this local daemon when accessible; otherwise
it retains subprocess execution. `BOOK_LEAN_EXPORT_BACKEND=server` requires the
daemon, while `subprocess` explicitly selects the original backend. Restricted
sandboxes may require permission to use the owner-only local Unix socket.
Runtime sockets are outside build caches and are isolated by checkout path.

The daemon uses Lean's versioned `waitForDiagnostics` protocol, rejects errors
and warnings, and never builds or downloads dependencies. It checks compiled
artifacts, including transitive package artifacts, before and after each probe;
changes close and reopen document workers with monotone versions while the
server stays running; changes during a check invalidate its result. Changing daemon
implementation code requires restarting it. Ordinary `make validate-lean`
remains the build gate. The server retains at most four import environments.

Use `inspect_many` for independent formula probes to share one Lean startup.
Whole-chapter inspection batches eight root expressions and isolates failed
probes without dropping rows or subexpression fallback. Each probe retains its
own reference-expression comparison, operator markers, and argument checks.
Run Ruff directly on changed Python during iteration; avoid overlapping a
translation synchronization with another `make` command, which can trigger
duplicate generated-manifest work.

The Markdown delimiter scanner only locates formulas. TeX syntax comes from
`book-filter math-syntax`, which exports the existing `MathExpr` and
`parseMathExpr` tree. The consumer derives exact Unicode character spans by
walking that lossless tree. Unmatched delimiters, grouping braces, and failed
round trips remain unsupported rows. Structural parsing does not establish an
interpretation of a formula.

The chapter's `chapter-correspondence` comments own declaration identities and
scope boundaries. An inner proof scope shadows the enclosing section. Every
local symbol has either a named Lean binder target or an explicit unresolved
reason; `\hat d` has a separate identity from `d`. Binder types, instance status,
and argument positions come from fresh Lean telescopes. Explicit `\Sequence{...}{n\in\omega}` binders have lexical identities and
Lean-checked natural-number lambda binders. Nested binders shadow outer names.
Other local or dependent binding effects remain unresolved, preventing capture
by outer declarations. Unknown symbols and operations also remain
visible.

Literal primes attached to an identifier are part of its source identity:
`d`, `d'` and `d''` require separate bindings, and the full decorated token span
is retained for function calls. A prime before a subscript belongs to the
family name, as in `x'_n`; a prime after the whole indexed expression is not
silently reassigned to the index. Derivative notation has no operation rule.
The open-subspace mappings keep the metric-definition points separate from
the topology-comparison sequence and limit. Its Lean topology construction
now uses the reciprocal-distance sequence argument before applying the
sequential criterion to obtain the required neighborhood condition.
The completeness argument now starts with an arbitrary Cauchy sequence, proves
that its reciprocal-distance sequence is Cauchy and bounded, and projects the
sequence into the ambient complete space. Its source scopes distinguish the
ambient limit `x` from the subtype point `limitInU` used in the final convergence
statement. The pointwise bound supplies the actual natural-number binder for
unbound prose occurrences of the sequence index.

The disjoint-union and product proofs now obtain their coordinate metrics from
`complete_compatible_metric_bounded_by_one`, with `MetricSpace.replaceTopology`
preserving the original topology. The sum uses the chosen distance within each
component; the product sums the weighted chosen distances. There is no second
inline truncation by `min dist 1`. The product construction's source scope names
these actual local metrics and point families. The product topology proof also constructs the finite-sum neighborhood `V`
and tail cutoff `M` explicitly. Indexed metric evaluation obtains its dependent
domain from Lean’s inferred `MetricSpace` type, and checks both the selected
metric instance and the point arguments. The same convention supports
pointwise bounds such as `d_n ≤ 1`. An explicit natural-number specialization
of the general disjoint-union context remains correspondence work.

Shared operation rules construct candidate Lean expressions. Lean checks them
in their originating declaration's context, specialized to universe zero.
Generated abbreviations retain the entire context; unused context parameters
are deliberate. Repeated identical candidates share a check, and a rejected
batch is bisected so one failure cannot conceal other results. The source,
checker and proof-context extraction rules, and Lean declaration signatures and
actual proof bodies are pinned in `review.json`. Any change
invalidates reviewed typing statuses while preserving the fresh inventory.
Updating these pins requires reviewing the changed correspondence; the checker
has no automatic acceptance switch.

The report distinguishes three totals:

- `parsing`: structural TeX parsing, including unsupported or unclosed formulas.
- `variableResolution`: recognized identifier occurrences resolved to scoped
  Markdown declarations and actual Lean binders. Unparsed formulas cannot
  contribute an invented identifier count.
- `expressionTypes`: every formula is `typechecked` or `unresolved`, with the
  inferred type or a reason and, where applicable, Lean diagnostics.

A typechecked proposition is neither a proof nor a certificate that its
interpretation is the author's intended statement. The pinned review covers
the earlier rules and sample mappings; changed rules require a new interpretation
review before whole-formula typing statuses can be accepted.

Positive integral numeral bases with scalar integer exponents, such as
`2^{-n}` and `12^{-(n+10)}`, are interpreted as real integer powers. Natural
exponent variables are explicitly embedded into integers before arithmetic;
`n-1` is therefore not truncated at zero. The negative sign and the power have
separate source spans, independently checked arguments, and checked numeric
instances. This rule does not interpret superscripts on variables such as
`x^k`, which may denote sequence indices. A weighted metric term such as
`2^{-n}d_n(x_n,y_n)` records juxtaposition as multiplication. Its operator span
is the zero-width boundary after the power, with `lowering: juxtaposition`;
its two operands retain their full original spans. Unsupported juxtaposition
candidates remain visible with `notation: juxtaposition` and an empty source
operator string rather than an invented glyph.
A regression test also reopens the source-owned product construction context
and proves that the translated weighted metric expression equals its original
Lean `term x y n`, retaining the chosen metrics and all proof-local lets.

Natural-number sums `\sum_{n\in\omega}`, `\sum_{n<M}`, and `\sum_{n\ge M}` bind the
following multiplicative term or explicitly grouped body. They lower to
`tsum` and `Finset.sum (Finset.range M)` with a real-valued lambda. The
index declaration, range and body retain source spans; the upper bound is
outside the new binder, so the bound in `\sum_{n<n}` refers to the outer
`n`. Targets, explicit arguments and the natural/real instances are checked
separately. An infinite sum additionally records a kernel-checked `Summable`
requirement; successful elaboration of `tsum` alone never discharges it.
The source-owned product definition also checks the weighted sum against its
original local `dPi` and proves summability from the retained `term_summable`
fact. Real-valued local definitions are unfolded explicitly, and local
summability facts are supplied to proof search even when the extracted
context marks them as implementation details. A tail sum uses a fresh natural
offset `k` and retains the source index as `let n := k + M`. The lower bound
is outside that binding, including in `\sum_{n\ge n}`. The shifted function
and bound retain their source spans, and a mutation of the bound is rejected
by the operand check. A kernel-checked equivalence proves that this shift
indexes exactly the subtype `{n : ℕ // M ≤ n}`; summability remains a separate
requirement. Other index domains remain unresolved. The product-topology scope
retains the original cutoff, neighborhood, points and radius. A regression
check proves the translated finite-plus-tail bound using that context's
`hpartial`, `htail`, and `hM`, as well as checking its individual calls. The
single-generator predicate set defining `V` lowers to `Set.ofPred`. Its generator
gets a fresh lexical identity and a domain from the source-owned Lean mapping;
this includes function-valued product points. The opening brace records the
constructor call, while the generator, colon and closing brace record binding
components. The predicate argument and implicit domain are checked separately.
A regression test proves that the translated source definition equals the
original local `V`. Nested generators shadow independently, and occurrences
outside the braces keep their outer identities. Unknown brace-and-colon
comprehensions, including multiple generators, still register an unresolved
binding effect rather than capturing outer names.

## Current unresolved interpretations

The JSON report is the exhaustive list, with source spans and individual
reasons. The principal limitations are:

- Local proof constructions are generally not theorem parameters. Their
  identities are recorded, but their Lean targets remain unresolved.
- Sequence, sum, product, intersection, and comprehension binders require
  scoped or dependent interpretation rules. Subscripts on resolved function-valued
  families are applications with Lean-checked index types. The shared parser’s
  text chunks are refined at exact character offsets so scripts attach to the
  final character, while a numeral power retains the final digit run as its
  base. Superscripts on variables, nonintegral exponent expressions, decorated expressions and definitions that
  introduce unregistered identities remain unsupported. Explicit parenthesized
  application is supported for function binders and two-point evaluation of a
  metric binder, using its distance projection; Lean checks argument types.
  Parenthesis sizing commands such as `\bigl(` and `\bigr)` preserve the
  original operator and argument offsets while contributing no mathematical
  operation. A final comma after a top-level relation is sentence punctuation;
  bare comma-separated identifiers and scalar subscripts are recorded as
  `expressionFragments`, each with its own source span and independently checked
  type. The list is not lowered to a Lean pair or assigned a single type.
  Application arguments and comparison lists retain their distinct rules.
- A book carrier such as `X` is a Lean type. `C \IncludedIn X` and
  `\SetDifference{X}{U}` use the registered carrier-to-set convention
  `(Set.univ : Set X)` when the scoped identifier is known to denote a carrier.
  A single equality or inequality between a known set and its carrier uses
  the same convention; equality between two carriers remains type equality.
  This convention remains an interpretation to review, not a consequence of
  successful type checking.
- Bare `\QQ` denotes the rational carrier. In exactly
  `\SetDifference{\R}{\QQ}`, it denotes the range of the rational embedding
  into the real line, whose complement is checked as a real subset. Other mixed
  carrier/subset expressions still need explicit rules. Real intervals with an
  infinite upper endpoint use `Set.Ioi` or `Set.Ici`.
- Bare bounded-lemma `d` denotes a `MetricSpace` structure. Metric evaluation
  uses its distance projection. `d\le 1` and comparisons of two distance
  functions use the pointwise order on functions into the reals.
  The other proofs choose or construct fresh metrics. They have separate
  identities and remain unresolved when no exact binder is available.
- `\Pair{n}{x}` in a disjoint union requires a dependent Sigma tag, not `Prod`.
  `C\times C` uses `Set.prod` when the operands are known sets; products of
  carriers still require their own rules. Natural-indexed dependent families
  use the product and Sigma rules described below.
- Predicate notation used as prose modifiers, infinity endpoints, bare
  numerals without an ambient number type, and unsupported semantic macros
  retain explicit reasons.

Legacy natural-index annotations have been removed from Polish Spaces. The
complete gate checks the replacement source binders, metric identities, and
product structure against Lean; other chapters retain their current audits.

Regression checks:

```sh
python3 -m unittest discover -s tests -p 'test_correspondence_migration.py'
python3 -m unittest discover -s tests -p 'test_chapter_correspondence.py'
python3 -m unittest discover -s tests -p 'test_lean_export_server.py'
make validate-correspondence CHAPTER=polish-spaces
```

## Inspecting proof-local constructions

`proof_contexts.py` retrieves named lambda and let binders from an elaborated
Lean proof, with their enclosing context and let values intact. For example:

```sh
python3 tools/chapter-correspondence/proof_contexts.py \
  PolishSpaceBook.complete_compatible_metric_bounded_by_one boundedDist \
  --output build/chapter-correspondence/bounded-dist-contexts.json
```

The output includes the actual theorem body, using `allowOpaque := true`, and
structural paths that distinguish same-named binders. This is inspection
evidence only; it does not grant reviewed correspondence status. Contexts
must retain let definitions when used for expression checking. Proof paths
must be reviewed again when the proof body changes.

The checker accepts `declaration@proof-path/binder` targets. It opens the
original kernel context and retains its let values. Duplicate printed binder
names receive deterministic fresh aliases; evidence retains their original
names and structural paths so shadowed variables remain distinguishable.
This mechanism still requires reviewed source mappings. The reported expression
type removes only the adapter’s context parameters, preserving function-valued
results such as `Y → Y → ℝ`.

A source scope may provide a `context` object with `declaration` and `path`.
Short binding targets then name binders within that exact context. Expressions
can combine an ancestor telescope with a descendant proof context only when
the declaration and every preceding binder type, name, instance flag and let
value agree. Sibling proof paths remain separate, even if their binders have
the same printed names and types. The bounded-metric lemma and proof use this
rule for `x`, `y`, the original metric, and the constructed bounded distance.

Standalone `\Gdelta` and `\Fsigma` class labels denote the polymorphic
predicates `IsGδ` and `PolishSpaceBook.IsFsigma`. Their definitions are pinned
as interpretation dependencies. A class label does not assert that a particular
set has the property; surrounding prose remains a separate obligation.
Top-level comparison chains denote conjunctions of adjacent comparisons,
preserving each operator and operand. Parenthesized applications and macro
arguments retain their own comparison boundaries.

The full-natural-number sequence rule binds only the explicitly named index
within that sequence’s body and index declaration. Free symbols still resolve
through source-owned scopes. Generated binder names avoid every name in the
original Lean contexts. Nested sequences may shadow the same printed index;
their identities and offsets remain distinct. Other index ranges remain
unresolved until an appropriate domain rule is reviewed.

For `x_n\to x` and `f(x_n)\to f(x)`, the convergence rule binds a single
simple subscript index only on the left of the top-level arrow. Every indexed
family must resolve to a Lean function with natural-number domain before the
index receives a resolved status. The rule rejects multiple indices, shifted
indices, nested binding constructs and a limit containing that index. Sequence
and point occurrences of `x` retain separate source identities. The continuity
mapping uses `u` and `x` in the forward implication of the metrizable continuity
theorem, preserving its original space parameters and hypotheses.

The arrow lowers to `Filter.Tendsto` applied to the indexed lambda, `Filter.atTop`
and `nhds` of the limit. All three explicit arguments are checked independently.
The source-filter expectation has `sourceOperand: null` because `atTop` is
introduced by the convergence convention, not by a separate printed operand.
The `Filter.Tendsto`, `Filter.atTop`, `nhds` and `SeqContinuous` definitions are
included in interpretation evidence. Changing the limit or replacing `atTop`
with the principal filter on the whole domain fails operand checks even though
the result type and outer call head remain unchanged.

## Operator evidence from the shared parser

`operator_evidence.py` consumes the existing MathExpr nodes and their located
spans. It instruments supported semantic macro subexpressions, elaborates them
in the recorded context, and records the actual application head, ordered
arguments, implicit arguments, typeclass instances and kernel expression trees.
It also records the weak-head-reduced expression without treating reduction as
proof of the intended interpretation. The inspection checks that the Markdown
and Lean declaration evidence still match the input inventory.
Rule and extractor hashes identify the code loaded at the start of the run.
The command refuses to save a report if that code changes during inspection.

Use `--translation-inventory` instead of `--formula-index` or `--all` to list
translation candidates without running operator inspection. This inventory
counts every source occurrence, checks all members of an expression list or
all rows of an aligned display, and marks the whole occurrence unresolved if
any member fails. It preserves unparsed occurrences as failures. Its summary
reports candidate availability only: it does not grant kernel validation or
semantic approval. Counting failures of `translate` on the unsplit parent
would incorrectly classify supported expression lists and aligned displays.

For the fraction in the bounded-metric definition:

```sh
python3 tools/chapter-correspondence/operator_evidence.py \
  --report build/chapter-correspondence/polish-spaces/formulas.json \
  --formula-index 37 \
  --output build/chapter-correspondence/operator-example.json
```

Offsets in this output are absolute Unicode character offsets in the canonical
Markdown. The operator token and enclosing subexpression each have a span.
A traced subexpression does not approve its enclosing formula. Supported nodes include the macros in `MACROS`, ordinary arithmetic, scalar
comparisons, set relations and difference, function/metric application, family
indexing and full-natural-number sequence binders. Text-leaf operators retain the shared
parser’s offsets, with standard precedence and parentheses respected. Other binding constructs and specialized interpretation rules still need
instrumentation. Comparison chains trace each adjacent relation separately. Known operator candidates without traces remain
listed in `untracedOperators`; this list is not an exhaustive semantic parser. This is a
separate evidence path, not a new success status in the whole-formula totals.
Regression tests deliberately replace division with multiplication and reverse
its operands: equal result types do not hide the changed head or arguments.

`targetStatus` compares the observed constant, scoped function variable, or
lambda binder against the rule’s declared target. Function-variable targets
retain their source context; sequence targets check the fresh binder name and
its `Nat` domain. Kernel trees preserve lambdas, let values and body variables.
`operandStatus` independently translates each source operand and elaborates it
against the actual argument's expected type in the same local context. Lean checks
definitional equality, including inserted coercions; `operandChecks` retains both
kernel trees. `expectedOperands.sourceOperand` indexes `operandSpans`, and entries
follow the explicit Lean argument order. Membership reverses the source order;
`GT.gt` and `GE.ge` preserve it. Family indexing checks the base as the callee.
Sequence operands are checked as `lambda.body` and `lambda.domain`: the body
is elaborated with the actual bound variable in scope, and the domain is compared
with the rule's explicit `Nat`. `bindingComponents` maps the source index name,
`\in` and `\omega` spans to the lambda binder/domain, rather than inventing a
membership call. Nested sequence binders preserve distinct lexical identities.
Regression tests reject a shifted sequence body and an integer index domain.

This verifies faithful application of the registered operand interpretation,
not the mathematical adequacy of that interpretation or of the context mapping.
The expected type comes from the actual call, so this does not independently
certify every ambient type or implicit typeclass instance. Metric evaluation
additionally checks the domain and metric projection supplied by the source
metric's own binder, independently of the observed call. These checks are
recorded in `expectedImplicitArguments` and `implicitArgumentChecks`; a mismatch
also fails `operandStatus`. Other unregistered implicit arguments retain
`implicitArgumentStatus: unreviewed`.
Swapped fraction operands and altered coerced interval endpoints are regression
cases: their call heads match while their operand checks fail.
Set inclusion records `LE.le` together with the `LE (Set X)` instance.

For a metric binder, a set-valued second argument selects `Metric.infDist`,
while point arguments select `Dist.dist`. Set variables and the registered
set-valued semantic macros supply that distinction, and Lean checks the
arguments against the chosen metric's domain. Metric point operands elaborate
as either points of that domain or their canonical `Subtype.val` projections.
Both choices must typecheck in Lean, and the independent operand check repeats
this restriction rule. The resulting kernel tree retains any projection.
The term elaborator first checks identity of the point's type with the metric
domain, then checks the canonical subtype projection if needed.
The book defines distance to a
nonempty set; the adapter therefore records a separate `nonempty-set` semantic
requirement rather than silently accepting `infDist`'s empty-set extension.
It attempts a proof from the original context, closes that proof over its local
binders and lets, and kernel-checks the resulting theorem. Missing evidence
remains `requirementStatus: unresolved` even if the call and argument checks
match. The open-subspace proof now separates `U = X` and supplies nonempty
complement evidence in the remaining branch.

The convergence rule accepts both `\to` and `\longrightarrow`, with a final
sentence comma or period excluded from the limit operand. Pure spacing commands
such as `\,` and `\;` preserve all surviving source offsets. Tests substitute a
different metric while keeping the call head and points unchanged, and also
check that an empty set is not reported as satisfying the nonempty requirement.

The image-set infimum rule supports `\inf\{f(s):s\in S\}` when `S` is a
resolved set and `s` is one scalar binder. It lowers the braces to `Set.image`
and the infimum to `InfSet.sInf`. The binder's domain comes from the recorded
set type; its scope includes the image expression and binder declaration, but
not the outer expression or the set domain. Both the image function and its
domain are checked as actual Lean arguments. Nested/dependent generators and
other comprehension forms remain unresolved. Nonemptiness and a lower bound
are separate kernel-checked requirements. For distances, the nonnegativity
proof uses the matching metric structure in the original context, even when
that structure is an explicit parameter rather than the active instance.

`:=` relates two already mapped expressions; it does not invent a new source
binding. Its `defining-equality` requirement checks a proof of their equality,
including the point-to-set distance infimum identity. An equally typed but
false proposed definition remains unresolved. This is distinct from ordinary
`=` propositions, which are not automatically treated as proved statements.

For `z\mapsto ...`, a source-owned mapping must supply the domain through an
existing Lean binder. The source binder then receives a fresh lexical identity;
its body and domain are checked independently against the resulting Lean lambda.
The reciprocal-distance function in the open-subspace argument has subtype
domain, while the distance-to-set function has ambient domain. A missing domain
or an unsupported nested arrow is not inferred from the printed variable name.

Membership projects a subtype point into the independently translated set's
ambient type. Metric comparisons similarly compare both distance functions on
the common domain, projecting arguments to an ambient metric when the other
operand is a distance function on a subtype. The pointwise domain and order
instance are checked separately. A comparison of incompatible domains fails.

Restriction uses `Set.domRestrict`, whose argument order is set then function.
For a binary distance function, `Function.uncurry` supplies a function on pairs;
`\restrict{d}{U\times U}` consequently has domain the subtype of `U ×ˢ U`.
The product operator, function, argument order, ambient pair type and real
codomain remain visible in the evidence. This preserves the distinction between
restriction to a set of pairs and evaluation on two subtype points.

To inspect the complete chapter with the same parser-node evidence:

```sh
python3 tools/chapter-correspondence/operator_evidence.py \
  --report build/chapter-correspondence/polish-spaces/formulas.json \
  --all --output build/chapter-correspondence/polish-spaces-operators.json
```

The report retains every formula, including unresolved formulas and formulas with
no traced nodes. Its summary counts observed targets, untraced known syntax and
failed subexpressions separately. It does not promote target matches into semantic
approval or reuse the inventory's old type-status totals as fresh validation.
Markdown and Lean evidence are checked once before the chapter traversal.

## Same letter used for a sequence and a point

Source bindings may specify `"occurrence": "subscript-base"` or
`"occurrence": "unsubscripted"`. Thus the base `x` in `x_n` can map to a Lean
sequence `u`, while standalone `x` maps to a point. Classification uses the
existing MathExpr script node, preserving the original offsets. Omitting the
selector means all occurrences; overlapping selectors in one scope are rejected.
Inner scopes override only the occurrence class they declare, and lexical
sequence binders still take precedence. A sequence base cannot resolve to a scalar.

Proof-path contexts are opened directly from the original Lean declaration body.
The adapter follows the recorded path, elaborates in its actual local context,
and closes the result with the original lambda binders and let values. Lean's
kernel checks the resulting declaration. Display strings are diagnostic evidence,
not code used to reconstruct the original proof. Incomplete elaboration is rejected.
Synthetic contexts without an original proof path still reject `⋯` omission markers.
Shadowed local names receive deterministic aliases derived from their context
slot, with collision checks against earlier binders. The extractor and replay
share that algorithm. Each binder retains its original name in `originalName`;
source targets use the unique `name` plus the proof path. This distinguishes
both nested `y` binders and repeated anonymous `this` instances without dropping
their original values or confusing dependent references.

For bindings whose proof paths differ within one source scope, `target` can be
an object with `declaration`, `path` and `binder`. A path may be a string or a
list of path fragments joined by dots; this keeps long structural paths readable.
Targets normalize to the same `declaration@path/binder` identity. They do not
relax context compatibility: only ancestor contexts may be combined within one
expression, and sibling proof branches remain incompatible. The Cauchy sequence
and its distances use their common ancestor context, while epsilon and eventual
indices use the context that proves the Cauchy estimate; the limit witness keeps
its separate context.

A binding may target a named Lean function using
`"target": {"constant": "PolishSpaceBook.boundedMetricTransform"}`. The inventory
records the full declaration type and body; the function does not introduce a
spurious local parameter context. Application traces check its actual constant
head and arguments. Lexical binders shadow constant targets as well as local
variables. The bounded metric now uses this same quotient function, so the
source's `\phi` refers to the function in the actual construction.

Finish the relevant Lake builds before running correspondence exports or their
Lean-backed tests. Lake replaces dependency artifacts during rebuilding; readers
must not treat temporarily missing `.olean` files as mathematical failures.
The shared exporter raises an infrastructure error for missing dependency objects,
so chapter inspection aborts instead of writing misleading unresolved counts.

A source operator can produce several elaborated calls. Each report node's
`calls` retains all of them, including distinct operand spans and individual
statuses. The node status is successful only when every call succeeds; a later
matching call cannot hide an earlier mismatch. `tracedOperators` counts source
operator positions and `elaboratedCalls` counts calls separately. Adjacent
comparison chains can repeat a middle subexpression. A comma-separated list of
single-letter variables with `<`, `>`, `≤` or `≥` lowers to a conjunction of
individual comparisons, recorded as `variable-list-conjunction`; other comma
comparison forms remain unsupported.

The natural-indexed type constructions `\prod_{n \in \omega} X_n` and
`\ExternalDisjointUnion_{n \in \omega} X_n` share lexical index binding.
The latter maps to `Sigma (fun n : Nat => X n)`: the Sigma application and its
family lambda are recorded separately, with independent checks of the lambda's
index domain and fiber body. The disjoint-union source family is the `Y` binder
of `countable_disjoint_union_polish_nat`; a kernel equality check identifies the
translated carrier with `Sigma Y`. The metric-definition scope also maps its tagged points to `Sigma.mk`.
The rule accepts a point in a named Nat-indexed family, checks the explicit tag
and point, and separately checks the implicit index type and family. The
kernel rejects tags incompatible with the point's dependent fiber. Its distance
application resolves to the original `dSigma`. Two-row real-valued `cases`
expressions lower to `dite`: each condition and branch body is checked, and Lean
requires the second condition to complement the first. Within an equality
branch, an explicit `Eq.mp` transports a point between fibers of the same
family using that branch proof. The report retains the transport and its
proof name. A kernel identity check verifies the entire distance definition;
changing the cross-component value is rejected even though it still typechecks.
Operators in dependent binder domains are inspected as well as in bodies;
condition copies retain their individual checks.

The triangle proof has source-owned scopes for its three displayed chains.
The original proof names the tagged points `p`, `q`, and `r`; each branch maps
to the actual aliases after index substitution. Tests prove all three chains
and the point definitions in those original contexts, and reject a same-type
point substitution. The standalone `1` in the intervening prose has an explicit
source-owned numeral domain:

```json
"numerals": {"type": "Real", "from": "metric-d"}
```

`from` names a binding in that same scope. The exporter checks that the original
Lean witness's result type is `Real`, then elaborates the numeral in that type.
The trace checks `OfNat.ofNat`, its literal Nat argument, the ambient type, and
the chosen `OfNat` instance separately. This metadata applies to standalone
unsigned numerals, standalone numeric arithmetic such as `1/3`, and wholly
numeric scalar operands in comparison chains,
including arithmetic such as `1 ≤ 1+1`. Contiguous digits retain their original
source span. Indices, exponents, and arguments within other terms do not inherit
this scalar convention. A witness may be an original local binder or an
explicitly registered Lean constant; the constant case checks its result type
without inventing a local proof context. Scalar arithmetic on these witnessed
values independently checks its operand types and arithmetic instance. The
distance-one and radius-one-third non-example uses `Dist.dist`; the bounded
metric proof uses `boundedMetricTransform`, and its radius paragraph uses the
original `r`. The evidence survives report serialization. Numerals
outside an annotated scope retain their unresolved status; no default Nat type
is assumed.

Proof-only prose scopes also contribute their original Lean contexts to the
inventory, even when `bindings` is empty and the prose has no inline formula.
`scopeContexts` records their source span, context identity, and whether the
context evidence is present. This is context resolution, not semantic review.
The disjoint-union completeness and separability sentences point both to their
final local proofs and to the Cauchy-tail and dense-union constructions. Kernel
checks preserve the original component metrics, the eventual tag and lift,
component convergence, and the actual countable dense union. The topology
comparison names the original family of topological-space instances explicitly.

An omitted radius in the source expression `< 1` is handled only in an explicitly
annotated scope:

```json
"predicates": {"type": "Real", "witness": "dSigma"}
```

The witness is a local binder in that scope's original Lean context. The parser's
comparison token and unsigned numeric bound lower to a real-valued radius binder,
`LT.lt`, and `OfNat.ofNat`; the bound's type is checked against the witness's
result type. The report preserves separate checks for the binder domain, both
comparison arguments, the order instance, and the numeral. Without this source
annotation the incomplete comparison stays unresolved. The source test proves
that this predicate makes every corresponding metric ball stay in one summand.

Equality and order comparisons with a resolved source operand now obtain their
ambient type by elaborating that operand independently, without the observed
comparison's expected type. The comparison's implicit type must match it; order
comparisons also check the corresponding `LT` or `LE` instance in the original
context. A reversed order instance is rejected even when the callee and explicit
arguments match. Pure numeric expressions still require separate type evidence;
this rule does not infer a domain from the observed call or grant blanket
approval to implicit numeric coercions.

Implicit-argument expectations are elaborated independently before their types
and values are compared with the observed arguments. A type disagreement, such
as `LT Real` versus `LE Real`, is recorded as a mismatch with `typeStatus`,
rather than forcing the expectation into the observed type or aborting the
whole comparison. Invalid expectation syntax and unresolved elaboration still
fail the probe; they are not accepted as correspondence evidence.

Natural dependent sums additionally check `Sigma`'s implicit index type against
`Nat`, independently of the explicit family check. Real-valued cases check both
the result type and the `Decidable` argument against `Classical.propDecidable`
applied to the independently translated source condition. A different index
type or a decision for another proposition is rejected even if the operator
name matches.

For homogeneous scalar `+`, `-`, `*`, and `/`, a resolved source operand supplies
the domain independently of the observed application. The checks cover both
input types, the result type, and the corresponding `HAdd`, `HSub`, `HMul`, or
`HDiv` instance. This convention does not approve heterogeneous arithmetic or
infer the intended number system for a standalone numeric expression.

Set equality, inclusion, intersection, union, and difference obtain their set
type from an independently translated source operand. The corresponding `LE`,
`Inter`, `Union`, or `SDiff` instance is also checked where applicable. Membership
checks the element type, container type, and `Membership` instance against the
source set; set products check each factor's domain separately, allowing the
two domains to differ. Adversarial tests replace union by intersection and
membership by nonmembership without changing the instance types.

The same independent arithmetic checks apply to `\frac`. Absolute value checks
the operand type, lattice, and additive group; finite interval macros check
their prescribed real domain and preorder; closure checks the source set's
domain and topology. Tests also reject reverse division, dual orders, and a
different topology even when the replacement instance has the same Lean type.

Auxiliary requirement proofs use the universe parameters of their own probe
declaration. They do not depend on a fixed first-probe declaration: a batch may
start with an expression having no traceable operators and still kernel-check
later defining equalities and nonemptiness witnesses.

Sequence convergence checks its natural-number domain and independently derives
the codomain from the source sequence. Image sets similarly derive both types
from the source function. Defining equality checks the left-hand term's type;
infimum checks the source set's element type and `InfSet` instance. These checks
are separate from the kernel proofs of defining equality, nonemptiness, and
boundedness; matching implicit arguments does not discharge those obligations.

Composition `f\circ g` traces `Function.comp`, the source functions in their
original order, and its domain, middle type, and codomain. For a source metric,
the rule composes on distances via `Function.uncurry` and restores the binary
interface with `Function.curry`; both adapters are recorded in `lowering`.
A registered binary real-valued distance function can use the same convention
with a registered real-to-real outer function. Ordinary composition with a
function-valued middle type retains its unary interpretation. Composition
chains require explicit grouping. The source test proves that the chapter's
`\hat d=\phi\circ d` is the original proof-local bounded distance by `rfl`.

Sequence powers `\seqPower{A}{I}` lower to the function type `I → A` when both
arguments are registered carriers. The forall node checks its domain and body
against those source arguments independently. The binary alphabet `\{0,1\}`
has the existing book convention `Bool`, recorded as `false ↦ 0`, `true ↦ 1`
with `bounded_binary_sequence` as its real-sequence embedding. The alphabet
and power retain distinct source markers. Tests verify identity with
`cantor_space`, the embedding's coordinate values, and its distance-one theorem.
Other finite-set literals and numeric index cardinalities remain unsupported.

Finite carrier powers such as `\R^n` and `\QQ^n` use `Fin n → A`.
The exponent must be a resolved natural-number variable or a natural literal,
including zero. The trace checks `Fin` and its dimension operand separately
from the function type's domain and coordinate carrier. Kernel tests identify
`\R^n` with the original `euclidean_space n` and verify that coordinatewise
rational-to-real coercion has dense range. Real, integer, and set-valued
exponents are rejected rather than treated as dimensions.
A standalone declaration `f:X\to Y` uses the existing `bookHasType` rule:
Lean checks the actual `f` against `X → Y`, and the arrow trace independently
checks both carriers. This shares the typed-map rules without manufacturing a
point binder for a declaration that has no written input variable.

Natural products accept an omitted index or a matching explicit index, as in
`\prod X_n`, `\prod_n X_n`, and `\prod_{n\in\omega} X_n`. The family must
have a registered `Nat → Type` or `Nat → Set X` type. For a set family, each
fiber lowers explicitly to `Subtype (U n)`: the subtype predicate and ambient
type are checked separately, as are the product's domain and body. This
set-to-carrier conversion is recorded at the source family occurrence. The
Alexandrov source tests identify the resulting product with the original
diagonal map's codomain. A mismatched index, non-natural index domain, or
scalar-valued family is not accepted.

For `f(A)` with a named set `A` and a registered function whose domain is the
subtype defined by that same set, the expression denotes `Set.range f`.
The elaborator rechecks the subtype-domain identity before constructing the
range; a textual signature alone cannot authorize a different source set.
The trace checks `f`, the codomain, and the domain derived from the source `A`
independently. The Alexandrov source tests identify `\iota(A)` with the actual
`Set.range diag`. A function taking sets as ordinary arguments still uses
ordinary application. Images of arbitrary subsets of a function's domain
require a separate rule and are not inferred by this convention.

The Alexandrov closed-sequence scope uses the actual chosen preimage sequence
`a` and product limit `b`. Its superscript selector distinguishes `a^k` from
scalar powers. The common-limit scope retains `x = ↑(b 0)` and the subtype
point `xA = ⟨x, hx⟩` from the original proof. Tests check the coordinate sequence,
membership of `x` in the source set, and the equality `b = diag xA`. An ambient
point is not silently accepted where `diag` requires a subtype point; that
promotion must retain its membership proof in the expression correspondence.
Unary application to a registered subtype-domain function now permits this
promotion only when the original local context contains a proof of the exact
predicate at the source point. `bookSubtypeArgument%` checks the ambient type,
constructs `Subtype.mk`, and preserves already correctly typed arguments.
The application trace checks the promoted argument independently and records
the membership proof as a kernel-checked semantic requirement. In the final
Alexandrov chain this is the original `hx`, and the full conjunction is proved
from `hb` and the original diagonal witness. Missing membership, membership
of another point or another set, and unrelated ambient types are rejected.

An equality/membership chain `x = y ∈ A` lowers to the conjunction of equality
in the ambient type of `A` and membership in `A`. Each relation retains its own
source operator span. Equality checks both points and its implicit ambient
type independently; subtype points use only the canonical value projection.
The Alexandrov source instance is proved using the original common-limit
equality and coordinate membership, with negative tests for changed operands,
changed equality types, and points from an unrelated carrier.

For the Alexandrov converse, `bookSmallTraceIff` relates the extended-diameter
bound to boundedness together with the real-diameter bound. Its metric is an
explicit argument, and its bornology is explicitly the one induced by that
metric. In particular, the subtype bornology inherited from the ambient space
must not replace the bornology of the separately chosen complete metric on `A`.
Kernel tests reconstruct the original context containing `hVopen`, including
the actual metric choices, `bound`, `smallTrace`, and `V`. They prove the trace
identity for `S ∩ A`, the reciprocal bound after positive-index reindexing,
the equality of the reindexed intersections, and the equality of the entire
ball-union construction with the bounded real-diameter formulation. A negative
case proves that an unbounded set can satisfy the real-diameter inequality
while failing the extended-diameter inequality. These are semantic bridge
checks; the converse's Markdown operator bindings still need to use them.
The `alexandrov-converse-metrics` source scope binds `d` and `\rho` to the
original local `MetricSpace X` and `MetricSpace A` choices. Its English and
Japanese metadata are synchronized through the PO catalog. Tests check every
standalone occurrence and prove each distinct metric equals the selected
upgraded metric and induces the original ambient or subspace topology.
The chapter uses zero-based indices throughout this construction: source `V_n`,
`B_n`, and `a_n` use the original Lean family index directly, with reciprocal
bounds `1/(n+1)`. No Alexandrov source binding requires `indexOrigin` or
`indexOffset`. The generic adapter still supports `indexOrigin: 1` for a
separately reviewed positive-index source, where `n` denotes index `n - 1`. The subscript trace retains this lowering
and independently checks the shifted operand. A restricted binder must establish
the declared lower bound; literal indices below it, unrestricted indices, and
bare reindexed families remain unsupported rather than silently using truncated
subtraction at zero. Tests prove the source intersection is definitionally the original `V`
intersection. Generic adapter tests also reject an off-by-one operand expectation.
For a free positive index, a scalar binding can declare `indexOffset: 1`:
the source `n` then denotes the original natural-number binder plus one.
Combined with the family's `indexOrigin: 1`, `V_n` denotes the original
`V ((n + 1) - 1)`. Kernel tests prove this is `V n` and that the source
index is positive. Lexical binders shadow this offset; non-natural binders,
constant targets, nonpositive offsets, and simultaneous origin/offset metadata
on one binding are rejected.
The `alexandrov-chosen-neighborhoods` and `alexandrov-shrunk-neighborhoods`
source scopes distinguish the original `U` and `W` families. They use the
actual `N` binder in the selected-point membership proof to interpret source
`n` directly as `N`. Tests translate
the source's standalone indices and neighborhoods and prove they equal
`N`, `U N`, or `W N` as appropriate. The shrinking scope also names the
original `aSeq` for subscripted `a`. The following limit paragraph has its
own original-proof scopes as described below. Separate original-context kernel checks prove that `W` is
decreasing, `W n ⊆ U n`, its ambient diameter is at most `2 * bound n`, its
subspace trace retains boundedness and strict diameter bound, and `aSeq n`
belongs to `W n ∩ A`. The source selected-point membership also passes
operator and implicit-argument checks and is proved from the original choice
witness. The complete decreasing-chain/convergence display now translates to
`And (Antitone ...) (Filter.Tendsto ...)`. A top-level `\text{and}` separates
lexical scopes, so a convergence binder cannot capture a same-named free
variable in the other clause. A decreasing chain requires consecutive literal
indices and one resolved natural-indexed set family; the infinite tail retains
the declared family origin. Its source subscripts, both inclusions, and ellipsis
are recorded as one decreasing-tail lowering. All calls and implicit arguments
are checked. The kernel proof establishes monotonicity of the original `W`,
derives boundedness from containment in its defining ball, and squeezes the
diameter between zero and `2 * bound n`, which tends to zero. It proves the
entire source conjunction, not just its clauses in isolation.
For convergence of reindexed families, the lexical natural-number binder starts
at the maximum declared family origin. This offset comes from the participating
families, replacing any same-named free-index binding. Families with different
origins keep their individual shifts. Tests prove that a positive-index family
converges exactly when the original Lean sequence does and that mixing origins
preserves the required shift of each family. A numeric limit of a metric
diameter is explicitly real-valued, avoiding Lean's default natural numeral.
The explicit `MetricBall` macro now passes the source metric, center, and
real-valued radius to `Metric.ball`; its implicit carrier and metric instance
are independently checked. Tests reject an unrelated center type and another
metric on the same carrier. In the finite-intersection display, its source
radius `1/(n+1)` produces exactly the original
`Metric.ball x (bound N)`. A kernel bridge identifies the zero-based
finite intersection intersected with this source ball with `W N`. The checker
also has an implemented ellipsis rule for the whole displayed expression.
Finite intersections of the form `B_l \cap \cdots \cap B_n` lower to
`iInf` over `Fin (n - l + 1)`. The rule requires a literal lower endpoint,
source evidence that the upper endpoint is at least it, including the intrinsic
nonnegativity of a natural index when the lower endpoint is zero, and the same resolved
natural-indexed set family at both ends. Family origins are subtracted only
after establishing that the entire interval lies above the origin. The trace
records both endpoint subscripts, both intersection separators, and the
ellipsis as one finite-range lowering, and independently checks the generated
family and every implicit `iInf` argument. Kernel tests cover singleton and
noninitial intervals, reject reversed or unbounded endpoints and different
families, and detect an off-by-one expected index type. The complete source
finite-intersection display, including its metric ball, is proved equal to
original `W N`; no subexpression is omitted from that proof.
The chosen-neighborhood diameter inequality now has a complete source trace:
its six operators, explicit operands, and implicit arguments match. Scalar
arithmetic compared with `MetricDiameter` is interpreted in `Real`, casting
natural indices before division; this prevents instrumentation from changing
`1/n` into natural-number division. The bound requirement normalizes the
subtype trace and proves finite extended diameter from the original
`hUsmall N`. A separate kernel test derives the source inequality itself from
that same proof via `bookSmallTraceIff`, without an index shift.
The operator walker excludes proof arguments, where elaboration may duplicate
marked set expressions. Containment and boundedness proofs remain separately
kernel-checked and retained in `semanticRequirements`; their embedded copies
are not additional Markdown operator occurrences.
The nested `alexandrov-converse-point` scope binds the reverse-inclusion point
to the original `x` carrying `hx` and `hx_closure`. Source tests prove the
translated intersection membership and closure membership from these exact
assumptions. Separate tests enter the original final `h_eq` context, verify
its compatibility with the source context, and prove the two displayed set
equalities and the forward inclusion with the original natural indices. A terminal period or
comma on a top-level membership/inclusion is treated as sentence punctuation;
interior commas still require an explicit expression rule.
The `alexandrov-converse-limits` scope connects the final sequence paragraph
to the original context containing `aSeq`, `a`, `ha_lim`, and `ha_lim_X`.
Subscripted `a` uses the original zero-based family; bare `a` initially denotes
the subtype point. The nested `alexandrov-converse-ambient-limit` scope explicitly
requests `Subtype.val` for bare `a`, retaining both its original subtype and
projected ambient type in variable evidence. Only a local binder in a named
subset supports this projection; unrelated scalar types and combinations with
index-shifting metadata are rejected. Convergence to an ambient point uses the
canonical projection of sequence values, while convergence within a subtype
continues to require the original subtype or a proved inclusion.
Source tests prove all nineteen expressions in this paragraph, including both occurrences of `a_n → a`,
from their respective original convergence proofs; the final `a_n → x`, `a=x`,
and `x ∈ A` use the compatible final `hax` context. The zero-based sequence
is identified with `aSeq` and inherits the original `haSeq_cauchy`. An explicit
`Sequence` range `n ≥ m` binds a fresh natural index and shifts it by `m`,
independently of an outer free-index binding. Tests check starts 1, 2, and 10,
and reject starts below a reindexed family's origin.
The standalone zero takes its real type from the original `bound` function.
The ambient diameter limit follows from `diam (W n) ≤ 2 * bound n`.
A separate original-context proof derives convergence of the lifted trace
diameters to zero from `hUsmall`, retaining boundedness in the chosen complete
metric on `A`, rather than the ambient metric's inherited bornology.
The `alexandrov-closed-distance` scope uses the original nonempty branch of
`isGδ_of_isClosed_metric_neighborhoods`. Its nonempty-set assertion and displayed
countable intersection are proved from `hne` and `hcov`. The Alexandrov converse
calls this explicit metric-neighborhood proof; the Borel chapter retains its
existing declaration as a wrapper around the same proof.
An explicit generator `{x ∈ X : P}` gets its domain from the source-owned carrier
`X`, overriding a same-spelled outer point binding. A natural-indexed intersection
or union of such sets binds its index separately from the point generator.
Both binders, the written domain relations, and the indexing subscript retain
source spans. A set-valued `X` is rejected rather than silently treated as a
carrier. Scalar arithmetic compared with a metric evaluation is elaborated in
the reals, including casts of natural indices, so operator instrumentation
preserves the original expression.
For the generated ball family defining `V_n`, `candidateGenerator` retains
its generated ball, point-domain clause, positive-radius clause, diameter clause,
and separators, with spans relative to the formula's `bodyStart`. A scope's
`restrictions` entry connects the bounded trace to a named
`chapter-correspondence-premise` range in the following prose, with explicit
metric and subset binding IDs. The resolver requires a unique nonempty range
inside the scope and the same generated ball, metric, and trace subset in the
diameter condition. It retains the premise text and absolute source offsets as
`sourceRestriction`. English and Japanese use identical premise identifiers
around their own prose.
With this premise attached, lowering registers separate lexical point and real
radius binders and constructs `Set.sUnion` of a `Set.ofPred` family. Its predicate
retains positivity, boundedness in the chosen subtype metric, equality to the
generated ball, and the written diameter bound. The trace checks the entire
predicate and union operands, including implicit arguments. The duplicated
positivity markers in the existential domain and lambda binder are checked by
the existing condition-binder rule. Synthetic copies used by the boundedness
guard do not create extra written operator occurrences. Missing premises and
changed metric bindings are rejected; removing the guard leaves the diameter's
boundedness obligation unresolved.
The `alexandrov-ball-union` scope selects the original natural index inside
`hVopen`; source `V_n` is directly `V n`, with bound `1/(n+1)`. An
original-context kernel test proves the entire translated source equality using
`bookSmallTraceIff`. The surrounding prose uses that same original natural
binder for its standalone `n` and `V_n` occurrences. Its metric and family
bindings come from the common context immediately before `hVopen`, so they
share an actual context prefix with the index inside that proof. Sibling-context
checks remain enforced. The inclusion `A ⊆ V n` is independently proved for
every natural index using the original `hA_subset_V` witness. Source operator tracing independently checks every written
operator and the boundedness obligation. These checks do not approve the
chapter's semantic review automatically.
An indexed singleton union such as `\bigcup_{q \in \QQ} \{q\}` retains
`candidateSingletonFamily`: union marker, index declaration, domain relation,
domain, subscript, singleton braces, and element, all with formula-relative
spans. The source scope's `rationalSingletons: {"ambient": "Real"}` explicitly
selects the real line while the written index domain remains rational. Without
this metadata the binder stays unresolved, including when an outer variable
has the same name. Unsupported ambient metadata is rejected.
For the complete rational singleton-union equality, lowering registers the
lexical rational index, interprets the left-hand rationals as the range of
`Rat.cast`, and traces the element coercion, `Singleton.singleton`, the lambda
family, `iSup`, and equality. The indexed union retains `sourceAmbient` with
the source scope and its absolute bounds. Every implicit type and instance
argument is checked independently. Kernel tests prove the translated equality
and identify this real-valued indexed union with the set-of-singletons
construction in `rationals_are_fsigma`. Negative tests reject a changed cast
operand, singleton carrier, or index type. An intrinsic union in `Set ℚ` does
not replace the statement in the real line.

For a diameter measured on a subtype, `bookMetricSet%` accepts an ambient set
only with a proof that it is contained in the subtype's defining set. It then
uses `bookSubtypeSet`, the preimage under `Subtype.val`, retaining the containment
proof. The diameter trace checks the lifted set and the metric's actual domain
independently and kernel-checks containment separately from boundedness in the
chosen metric. An unknown containment is rejected; a known containment without
boundedness remains unresolved. Original-context tests identify the adapter's
trace of `S ∩ A` with the precise preimage used by `smallTrace`.

An equality with `\Tuple{p,p,\ldots}` on the right constructs a natural-number
coordinate function. Its product type comes from the left operand, but its
values come from every displayed tuple operand. At least two points must be
displayed and Lean must verify that they are definitionally equal. The finite
displayed prefix is retained as coordinate branches and the final point is
repeated thereafter. Each coordinate uses the same checked subtype-inclusion
conversion as convergence. The tuple trace checks the lambda body and natural
index type independently; tests reject distinct points, an unproved inclusion,
and other index types. The Alexandrov chosen-preimage instance is proved equal
to the actual diagonal by function extensionality.

A combined unary declaration `f : A \to B, f(x) = ...` binds `x` only in the
defining equation. For a registered source subset `A`, its input type is
`Subtype A`; a same-spelled outer variable cannot supply the input. The colon
lowers to `bookHasType` with the explicit function type and function as operands.
This proposition records a successful Lean type ascription, while the defining
equation is universally quantified and remains a separate proof obligation.
The arrow traces the function type's domain and codomain independently, and
the equation traces its own operators. The Alexandrov declaration is checked
against `diag` and its original product of subspaces, and its defining equation
is proved coordinatewise. Negative tests replace the domain, codomain, and
function independently and check rejection of an incompatible actual signature.

Sequence convergence also accepts a superscript index when the source binding
explicitly registers that family with `superscript-base`. The index is bound
lexically, and ordinary powers are not accepted as sequence applications.
The limit determines the convergence space independently. When source points
belong to a different subtype of the same ambient space, `bookConvergencePoint%`
requires a proved inclusion and uses `Set.inclusion`; the inclusion proof is
recorded and kernel-checked. The Alexandrov instance thus converges in `U n`,
as proved from the original product convergence `hyb` and preimage equations
`ha`, rather than merely after projection to the ambient space.

An inclusion arrow between two registered subsets of the same ambient type
lowers to `Set.inclusion`. The source set, target set, and ambient type are
checked as implicit arguments; the subset proof is an explicit argument and
is separately kernel-checked and saved as a semantic requirement. Bounded
proof search may use the original hypotheses, including a countable-intersection
presentation. Without a proof the expression remains unresolved. This rule
does not infer an arbitrary embedding between two types. The Alexandrov test
checks equality with the original diagonal coordinate and its topological
embedding property.

Indexed intersections and unions of a single registered family, such as
`\bigcap_n G_n` and `\bigcup_{n\in\omega}G_n`, bind a fresh natural-number
index. The family's recorded type must be `Nat → Set X`; an outer variable
with the same spelling cannot supply the binder. The trace checks the family
lambda, `iInf`/`iSup`, the set type, index type, and lattice instance separately.
The source Baire-family test identifies the intersection with the original
theorem's intersection and applies its density conclusion. Parenthesized
composite bodies such as `\bigcap_n(G_n\cap U)` retain their lexical boundary.
Every family referenced at the bound index must be a registered Nat-indexed
set family, and the body must itself elaborate to a set of the same carrier.
The Baire intersection-distribution formula is kernel-proved in the original
global-family context, retaining its open test set `U`.
Literal lower bounds `n\ge k` additionally use the subtype `{n : Nat // k ≤ n}`.
The bound, predicate, and binder spans are retained; source index occurrences
project with `Subtype.val` before applying the original Nat-indexed family.
Independent lambda-domain and indexed-operation checks reject a changed bound.
A kernel proof identifies membership in the restricted intersection with the
original universally quantified condition. Nested binding constructs, symbolic
bounds, and other restricted ranges remain unresolved.

Empty-set notation in set comparisons obtains its carrier from the other source
operand. The trace checks `EmptyCollection.emptyCollection`, its set type, and
its instance independently. Two untyped empty sets and scalar/empty-set
comparisons remain unresolved; no default carrier is invented.

An explicitly named closure `\AmbientClosure{U}{A}` uses the registered carrier
`U`, its active topology, and the source set `A`. The trace checks the carrier
and topology as implicit arguments of `closure` and the set as its explicit
argument. A set-valued first operand is not silently promoted to a subspace.
In the relative Baire argument, `U` maps to the original proof's `relativeSpace`
let, whose value is the subtype of the ambient open set. The family `N` consists
of sets in that subtype; the proof retains their images in the ambient space
separately. Kernel checks identify the translated cover with `hNcover` and the
relative-closure complement with `H n`. Equality with a registered natural
union or intersection also uses the carrier-to-universal-set convention.

Open balls use the ambient pseudometric on the source center's type. The trace
checks `Metric.ball`, its center and radius, and both implicit arguments. A
regression enters the actual Baire small-ball call through an explicit unfold
path, retaining the chosen radius and its dependence on the induction index.
The initial diameter bound has its own numeral scope: its real-number witness
is the radius in the first ball selection, with value `min (r₀ / 2) (1 / 2)`.
The later recursive radii do not determine this initial bound's context.

A fixed numeric subscript can be a name only through an explicit binding such
as `r_0`. Its complete source span maps to the named Lean binder. Without that
binding, `r_0` remains an application of the registered family `r`; a scalar `r`
does not supply a fallback. Distinct numeric spellings and compound indices
are not silently identified.

Metric diameter explicitly uses the source `MetricSpace` argument, even when a
different ambient instance is available. Its trace independently checks the
carrier, metric, and set. Because Lean's real-valued diameter is zero on
unbounded sets, semantic acceptance additionally requires a kernel-checked
boundedness proof under that same metric; missing evidence remains unresolved.

A complete single-column `aligned` display is retained as one formula occurrence,
with each source row checked separately. Row breaks and alignment tabs do not
become mathematical operations. The row spans retain their original offsets;
ambiguous multi-column layouts and empty rows remain unsupported. The Baire
nesting and diameter rows are checked against the original `hnest` and `hV`
proofs, including the diameter's boundedness requirement.

A shared membership condition `x,y\in X` lowers to the conjunction of the two
memberships. The comma traces `And`, and the written membership symbol retains
two calls, each with its own point and the same domain. A carrier domain uses
its universal set; a set domain stays the written set. All membership implicit
arguments are checked. Failed calls remain visible when the shared source
operator is aggregated. This rule is limited to two simple identifiers and
does not turn a bare expression list into an ordered pair.

The introductory standard-real-distance formula binds `d` to `Real.metricSpace`
and its points to the arguments of `Real.dist_eq`. The trace checks that metric,
both real points, subtraction, absolute value, and equality; a kernel test
proves the translated formula with the original distance theorem.
A singleton `\{x\}` with a resolved point lowers to `Singleton.singleton`.
Its element type comes from that source point, and both the set type and the
singleton instance are checked independently. The closing brace retains its
source span. The isolated-point paragraph binds `x` to the original
`IsIsolatedPointByOpenSingleton` parameter; a kernel test identifies openness
of the translated singleton with that definition. This does not enable empty
or multi-element set literals. The rational-family singleton rule uses the same
operand-derived type checks after its explicit real coercion.

The introductory `C(\ClosedInterval{0}{1})` uses the source binding
`PolishSpaceBook.real_continuous_functions`, a general construction of
real-valued continuous functions on a real subset. The ordinary application
rule traces this constructor and the exact interval argument, while the interval
rule checks both endpoints, the real carrier, and its order instance. A kernel
test identifies the translated type with `ContinuousMap closed_unit_interval ℝ`
and applies `continuous_unit_interval_polish`. That theorem supplies the actual
complete, separable continuous-function-space instances to the book's Banach
space theorem; it does not assume those properties of this example.

The real sequence-space rule translates `\ell^p` to the carrier of
`lp (fun _ : ℕ => ℝ) p`. The exponent is retained as an explicit argument:
`\infty` resolves to `Top.top : ENNReal`, natural literals to `OfNat.ofNat`,
and a variable is accepted only with a resolved `ENNReal` binder. The trace
checks the `Nat` index, real coordinate family and its normed-group instance,
as well as every implicit argument of the exponent constructor. A kernel test
identifies the source `\ell^\infty` with `PolishSpaceBook.ell_infty` and applies
its completeness and nonseparability proofs. Changing the expected exponent
fails operand checking. The source `\ell^2` is a checked space expression;
this does not prove the cited homeomorphism.

For the finite-exponent example, source `p` is the binder of
`PolishSpaceBook.real_lp_polish`. Its separability proof uses the countable
coordinate unit vectors, separability of their real linear span, and
`lp.hasSum_single` to show that span is dense. Completeness comes from the
actual `lp` instance. The comparison rule uses the resolved `ENNReal` operand
to type its neighboring numerals and infinity; it does not assign a global
meaning to infinity. Kernel tests apply the Polish theorem to the translated
space and prove the translated range condition from the same original
`Fact (1 ≤ p)` and finite-exponent hypotheses.

The two-point discrete space is written with the semantic macro
`\TwoPointSpace`, which still renders as `2`. Its `type:binary-alphabet` rule
resolves to `Bool` and retains the alphabet convention `0 ↦ false`,
`1 ↦ true`. Both standalone source occurrences are traced. Kernel tests check
its cardinality, Polish and compact instances, and definitional equality of
its natural-number power with `cantor_space`. An unannotated scalar `2` does
not acquire this space interpretation.

Booklink prose matching ignores `chapter-correspondence` metadata while retaining
exact offsets into the original Markdown. The matcher caches a projection and
sparse segment offsets per source snapshot; it never uses a string inside the
metadata as matching prose. Excerpts still have to match the actual mathematical
text, up to whitespace. The Polish Spaces proof excerpts are synchronized with
the current source, including semantic notation and zero-based constructions.
Tests cover inline metadata, boundary offsets, Unicode, and unrelated comments.

`\Homeomorphic{X}{Y}` renders the usual congruence sign but specifies the
relation as `Nonempty (Homeomorph X Y)`. The trace separates the homeomorphism
type from its inhabitation proposition, checks both spaces and their inferred
topologies, and recursively traces constructions such as the `lp` exponent.
Changing the expected topology fails implicit-argument checking. The chapter's
Anderson statement is checked against an explicit input of
`banach_homeomorphic_real_sequences_of_anderson_kadec`. That theorem retains
the infinite-dimensional separable complete real normed-space hypotheses and
composes the two assumed homeomorphisms to prove the local consequence. It does
not supply an external Anderson or Anderson--Kadec proof.

The four dimension numerals use `\NonnegativeDimensionLevel{0}`. This is a
nonnegative finite level `n : Nat`, the shared parameter of
`smallInductiveDimension_le_iff`, `largeInductiveDimension_le_iff` and
`coveringDimension_le_iff`. It is not the codomain of all three dimension
functions. Kernel tests use each source occurrence in its corresponding bound:
small dimension embeds `n` into `WithBot ENat`, large and covering dimensions
embed it into `WithTop Int`, and the large-dimension recursion uses `n + 1`.
The zero bounds are checked against the book's zero-dimensionality predicates.
For the reference to value zero, the test preserves the nonempty-space premise
of `dimensions_zero_of_clopen_basis`. Operator evidence checks the natural
literal's value, type and instance; a wrong level fails, and negative, fractional
or infinite levels are rejected. Bare numerals still require their own source
interpretation.

Real intervals whose upper endpoint is `\infty` lower to `Set.Ioi` or `Set.Ici`,
not to a finite interval with an invented real infinity. The
`set:real-upper-ray` trace retains both source endpoint spans and records that
the upper endpoint is unbounded. Its actual Lean argument is the finite lower
endpoint; the real carrier and order instance are checked independently.

Implicit-argument coverage is checked against Lean's complete elaborated
application telescope. `not-required` means that the observed application has
no implicit arguments, with no implicit expectations or checks. It does not
mean that evidence was omitted. A missing telescope or an unchecked implicit
position remains `unreviewed`; duplicate or unexpected positions, missing check
results, and failed comparisons are rejected. The report records actual,
expected, missing and unexpected positions, so a passing subset of checks cannot
mask an unchecked instance. Merged calls retain any incomplete or failed check.

A natural numeral used as a sequence limit takes its type from the source
sequence's codomain, via `bookSequenceCodomain%`, before Lean elaborates the
numeral. The `literal:sequence-limit` rule traces the numeral's source span,
value, inferred carrier and `OfNat` instance. This prevents a bare limit zero
from defaulting to Nat for a real-valued distance sequence, without hardcoding
all limits as real numbers. Nondependent numeric codomains are required; no
numeric interpretation is invented for a Bool-valued sequence. The source
regression compares the distance-limit expression with its intended real-valued
proposition in the original local Lean context.

A `literalInterpretations` scope can assign several explicit interpretations to
one bare source numeral. Each interpretation has a distinct `id`, a named Lean
`constant`, and a `consumer` containing `declaration`, `callee` and the zero-based
`argumentPosition` in the fully applied Lean call. The formula remains one
source occurrence. Every interpretation becomes a separate validation unit with
the same source span; the formula is unresolved if any unit cannot translate.

The initial-symbol zero in the Cantor/Baire paragraph uses `Bool.false` and
`Nat.zero`. For each interpretation the inspector reads the actual closed
non-connectedness proof, checks that it calls
`not_connected_of_initialSymbolCylinder`, and compares argument 3 with the
independently interpreted source constant, including its type. The other
constant sequence is argument 4; substituting that position fails. The recorded
consumer application retains its kernel arguments, so these are links into the
real proof, not an inferred correspondence from matching names. Missing,
duplicate or malformed interpretation metadata is rejected. Shared source
spans never cause one interpretation to hide the other in operator reports.

For expression lists, aligned rows and contextual interpretations, the parent
formula's `typeStatus` becomes `typechecked` only when every fragment is
`typechecked`. `inferredTypes` retains the separate types; no single `lean` term
or invented tuple type is assigned to the parent. A stale or failed fragment
keeps the parent unresolved. Expression typing still does not replace consumer
checks, side-condition proofs, or interpretation review.
