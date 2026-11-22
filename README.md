# Mathematical Books

A collection of mathematical books written in Markdown and compiled to PDF via Pandoc and a custom Haskell filter, with accompanying Lean formalizations and a browser-based formalization viewer.

The formalization viewer is published live at <https://sunaemon.dev/math/>.

The public export includes the [complete English book](https://sunaemon.dev/math/polish-space/)
and the [first-chapter excerpt](https://sunaemon.dev/math/polish-space-ch1/).
From the private checkout, run `tools/publish_math.sh ../math` to prepare both
editions in the public checkout. Pages deployment uses locally built assets;
pushing source changes does not start a remote Lean/TeX rebuild.

After merging the public source update, run this from a configured local checkout:

```sh
tools/publish_pages_local.sh pages-YYYYMMDD-HHMMSS
```

This builds both English mounts with complete chapter PDFs and Lean hover caches, packages
only those mounts, uploads `pages.tar.gz` to a public GitHub Release, and dispatches
the Pages workflow. Actions verifies the archive SHA-256 and deploys it without
installing the build toolchain. Use a fresh release tag for each deployment.
Unchanged local Lean caches are reused. To publish text and PDFs before hover
cache generation finishes, add `--without-hover`; rerun later with a new tag and
without that option to include all hover data. Japanese editions and print artifacts
are excluded from this package.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/sunaemon/math)

Launch a cloud dev environment from the badge above; it provisions the toolchain automatically (the devcontainer runs `make setup-run` on create). Pick at least an 8-core machine; the default 2-core Codespace makes provisioning (TeX Live, GHC, and friends) painfully slow.

## Setup

Preview the one-time setup commands:

```sh
make setup
```

Run the setup for real:

```sh
make setup-run
```

Check that the setup is already usable:

```sh
make doctor
```

The underlying `setup.sh` script is dry-run by default; the Makefile exposes that as `make setup`.

`mise` must be on your `PATH` for `make` to work; if `make` reports it missing, re-run setup and restart your shell.

The Codex bootstrap pins mise 2026.10.19. Local setup and CI accept an existing
mise installation; `make doctor` checks that it can run the pinned tools.

### Saved Codex cloud environment

The saved Debian 13 x86_64 environment can use its **system Pandoc and
LuaLaTeX**, without installing the mise-pinned Pandoc or the repository's TeX Live
snapshot. From the private checkout, run:

```sh
bash tools/setup_codex.sh
make doctor
```

This is a separate core build/test profile. It installs the pinned GHC, Cabal,
po4a, Lean, TypeScript, esbuild, and Prettier tools. It uses the image's Python
3.12+ and Node 24+; the ordinary `mise.toml` pins and CI setup remain unchanged.
Missing gettext, Perl modules, LuaTeX-ja, luaotfload, texfot, selnolig, and Harano
Aji fonts are extracted from checksum-locked official Debian packages under
`build/codex/system`. The renderer binaries remain `/usr/bin/pandoc` and
`/usr/bin/lualatex`. No root access or separate TeX distribution is required.
This supplemental package set is specific to Debian 13, amd64, and its Perl/TeX
ABI; the script rejects a different image rather than mixing distributions.
Allow at least 12 GiB of free space for a cold installation, including GHC's
temporary unpacked copies. Use `/workspace`; this image's smaller `/tmp`
filesystem can fill during installation. Mathlib caches need additional space.

The script generates ignored `build/codex.mk` and `build/codex/env.sh`. The
Makefile loads the former, so ordinary `make` works in a new shell without a
custom `PATH` or `TEXMFVAR`. For direct commands such as `lake`, source
`build/codex/env.sh`. `make clean` preserves the Codex tool installation.
Rerun setup after moving the checkout or manually removing `build/`.
Downloads and toolchains stay inside `build/codex/`; TeX caches use
`build/texmf-*` and Lake dependencies use each book's `.lake/` directory.
The setup is repeatable: Debian archives and direct releases have checksums,
the ghcup plugin is pinned, and the repository controls the GHC/Cabal/po4a/Lean
versions. The system renderer and image Python/Node versions are deliberately
not pinned by this profile. Updating `lean-toolchain` also requires reviewing
the direct-release URL/checksum in `tools/setup_codex.sh`.

To make this persistent, first make these repository changes available in the
environment's checkout. In **Settings > Codex Cloud > Environments > … > Edit**,
use this **Install script**:

```sh
set -euo pipefail
cd /workspace/math-private
bash tools/setup_codex.sh
make doctor
make build/book-filter
```

Use this **Start skill** instruction:

> Work in `/workspace/math-private`. Read `AGENTS.md`, run `make doctor`, and
> use plain `make` for builds. Source `build/codex/env.sh` only for direct tool
> commands. Use `make validate-tex` during editing and `make validate-debug`
> after commits affecting rendered inputs. Build chapter previews only when
> explicitly requested. If toolchain pins changed,
> rerun `bash tools/setup_codex.sh` and report any failed download. No service
> needs to start for ordinary book or Lean work.

Save and **Republish**, then verify in a new task. A successful install in an
existing task only fixes that task's container; it does not update the saved
environment. No additional environment variables or secrets are needed. Keep
the existing network/access settings; setup does not change them. See the
[official cloud environment guide](https://learn.chatgpt.com/docs/environments/cloud-environments)
for the distinction between saved settings and published filesystem state.

Validate the checkout with:

```sh
make test
make lint-tsc lint-translation
make polish-space/build/polish-space-book.tex
make polish-space-ch1/build/polish-space-ch1-preview-polish-spaces.pdf
make lean LAKE_PROJECTS=polish-space-ch1
```

The full-book Lean check is `make lean LAKE_PROJECTS=polish-space`. Each Lake
project has a separate mathlib checkout/cache, so provision only the project
you intend to work on when disk space is limited. The core profile does not
install the optional watch and full-lint executables (lefthook, ruff, fourmolu,
hlint, oxlint, shfmt, shellcheck, taplo, actionlint, tree-sitter, watchexec, gh).
Their GitHub discovery endpoints are unavailable in this saved environment;
`make lint` is not part of the core setup's success claim. The vendored browser
highlight checks do not require the tree-sitter CLI.

Lean's compiler and Lake can be installed, but this environment currently
returns HTTP 403 for both official mathlib cache hosts,
`lakecache.blob.core.windows.net` and `mathlib4.lean-cache.cloud`. Consequently
`make lean LAKE_PROJECTS=polish-space-ch1` cannot complete its cache step.
The setup deliberately does not change network policy. If access is separately
authorized and configured, rerun that command in the environment edit flow
before republishing to include the downloaded mathlib cache. Compiling all
mathlib dependencies from source is a substantially larger build.

## Building

Build everything:

```sh
make
```

Build a single document (run `make list-books` to see the available `<book>` and `<stem>` names):

```sh
make <book>/build/<stem>.pdf
```

The normal `build/*.pdf` targets are release builds: they omit SyncTeX debug output and clear stale SyncTeX sidecars.
Use `make validate-debug BOOKS="<stem>"` after commits affecting rendered inputs. It builds the debug PDF with visible hyperlink borders and checks current diagnostics.

Generate debug PDFs for every discovered book manifest:

```sh
make debug-pdfs
```

Render a single chapter for a fast preview (a few pages via `\includeonly`, split
from the debug tex), or pre-warm every book's preview cross-reference aux:

```sh
make <book>/build/<stem>-preview-<chapter>.pdf
make preview-warm
```

Clean build artifacts:

```sh
make clean
```

## Checks and tools

Run the Haskell golden tests and Python unit tests:

```sh
make test
```

Run the source linter and viewer TypeScript check:

```sh
make lint
```

Apply automatic lint fixes where supported:

```sh
make lint-fix
```

Run the formalization viewer:

```sh
make formalization-viewer
```

It prints the URL it bound to and serves every discovered project at its own mount.

### Mathematical sort declarations

The sort system has two goals: detect conflicting mathematical meanings assigned
to a variable, and extend mechanical correspondence between the book and Lean.
Notation selection is a consumer of this information. Lean owns mathematical
typing and proof obligations; the filter records a small structural description
and evidence about the identity and role of a book variable.

The optional `book-filter lint --sort-audit --macros=polish-space/tex/macros.tex`
check reads scoped declarations in `mathmeta` blocks. Use structured sorts to
keep a function, a family entry, and a container distinct:

```tex
\begin{mathmeta}
  \vars{\sigma}{Fun(Seq(Nat),Nat)}
  \vars{s}{Seq(Nat)}
  \vars{U_*}{Set(Name)}
  \vars{a_*}{Nat}
  \vars{a_0}{Int}
  \vars{A}{Set(Name)}
  \vars{x}{Elem(A)}
\end{mathmeta}
```

Here `\sigma(s)` has sort `Nat`, `s_i` is a natural number, and every `U_i`
is a set of names. The wildcard `a_*` describes indexed entries without
assigning a sort to the unindexed `a`; the exact declaration for `a_0`
overrides it, including when the source writes `a_{0}`. Exact declarations
and wildcard declarations follow the existing section and `\scopebegin` /
`\scopeend` scopes. A local wildcard changes the family default; declare a
local exact entry as well when overriding an inherited exception.

`Elem(A)` resolves the element sort of a declared `Set(...)` or `Seq(...)`.
Nested containers such as `Set(Set(Real))` retain their element types.
Missing or cyclic element declarations remain unknown. Use `Fun(domain,codomain)`
for functions; the audit checks known input sorts and propagates the output
sort. Ordinary pairs have sort `Prod(a,b)`; the old `Pair(a,b)` spelling is
accepted as an alias. For a product domain, `f(x,y)` unpacks only the outer
product. A single product-valued argument stays intact, and nested products
are never flattened. Explicit three-component domains use `Prod(a,b,c)`.
Commas inside indices, macro arguments, or nested calls stay with that argument.
`Name` and `Fun(Nat,Nat)` agree, but a real-valued function is not a name.
A declared `Name` also has natural-number coordinates `p(n)`; a
`Seq(Real)` has real coordinates `s(n)`. The sort checker does not prove
coordinate bounds for finite sequences. The DSL audit uses the same declarations for function arguments,
indexed entries, and membership in parameterized sets. These declarations
are metadata and do not change the printed mathematics.

#### Identity, role, and Lean correspondence

The migration direction is to retain the existing mathematical syntax parser,
source locations and notation checks, while deriving types from Lean rather than
extending the independent sort vocabulary. Markdown owns variable identities and
explicit scopes. The next bounded migration is the Polish Spaces chapter; the
Sol assignment, Astra escalation criteria and completion checks are in `todo.md`.

The structural-sort discussion below documents existing behavior and the earlier
design constraints. It is not a mandate to add more sorts. Legacy checks remain
until their useful protections have replacements. The general sort audit still
has no integrated Lean exporter or complete variable coverage check; the pilots
below exercise these separately. Existing booklinks associate passages with Lean
declarations but do not by themselves identify variables or type every formula.

Keep four pieces of information separate:

| Information                    | Purpose                                               | Example                                                                          |
| ------------------------------ | ----------------------------------------------------- | -------------------------------------------------------------------------------- |
| Declaration identity           | Track one mathematical variable across its uses       | A binder in a particular theorem, with its lexical scope                         |
| Structural sort                | Check the shape of an object or operation             | `Nat`, `Prod(a,b)`, `Fun(a,b)`                                                   |
| Semantic role and dependencies | Distinguish meanings with the same shape              | A program index, an input number, or a name for the representation `delta`       |
| Lean binding and evidence      | Check the correspondence against elaborated Lean data | A fully qualified declaration and binder position, or a named expression adapter |

A role is descriptive metadata, not a new subtype with executable predicates.
For example, a program index and an input number both have Lean type `Nat`.
Their structural sorts agree, but a variable silently changing from one role
to the other still needs review. Conversely, a numeral can legitimately be
used in both roles through an explicitly documented construction. Role names
alone must not make those uses contradictory. Preserve the source occurrence,
its declaration, and the reason for each role assignment.

Assign identities from actual mathematical binding and scope, not from a printed
letter alone. The same letter in independent theorems need not denote the same
object. Within one continuing argument, a second incompatible declaration must
produce a diagnostic with both source locations. Explicit rebinding is valid
when the mathematical text introduces a new object; adding a metadata scope just
to suppress a collision is not. Indexed families retain their parent declaration,
index roles, and exact-entry overrides. Do not prefill semantic identity from
same-letter uses elsewhere in a chapter.

For Lean correspondence, extend the existing booklink relationship with explicit
book-variable mappings. Use Lean's elaborated declaration type and local binder
context, exported by Lean tooling, rather than extracting types from printed
Lean source. Binder positions must be checked against the declaration signature
and recorded source provenance so that edits invalidate stale mappings. Display
names alone are insufficient. Proof-local variables need a captured local context
or a small named Lean interface; a theorem's top-level type cannot describe them.
Mappings may be partial or many-to-one, and must record that limitation.

Project only supported Lean structures to the structural sort vocabulary.
Retain the actual carrier identity and references to dependent binders alongside
the projection: two unrelated carrier types must not match merely because both
were displayed as `Point`. A representation domain, computability, well-foundedness,
and other hypotheses remain Lean expressions or linked predicates. The filter
may compare supported projections and explicit dependency references, but does not
prove these hypotheses or implement refinement entailment. Unsupported expressions
remain unresolved instead of being assigned a convenient generic sort.

When representations differ, use an explicit adapter with evidence checked in
Lean. For example, a set-theoretic ordered pair and a Lean product are different
encodings. A book equality between a partial program and a total name corresponds
to a computation predicate, not necessarily to a Lean equality expression.
Do not make every `ZFSet` a typed subset or every numeral a certified program by
an automatic coercion. Function spaces and products can remain structural sorts
without implementing a second dependent-type elaborator.

The computable-point assembly provides the first bounded integration case:

| Book object    | Lean evidence                           | Information needed beyond the structural sort                    |
| -------------- | --------------------------------------- | ---------------------------------------------------------------- |
| `e`            | `e : Nat` in `ComputesName`             | Program-index role and the relevant computation relation         |
| `p`            | `p : Nat -> Nat`, or `p : delta.domain` | Total name, the particular representation, and domain membership |
| `x`            | `x : X`                                 | Identity of the carrier `X`                                      |
| `delta`        | `Representation X`                      | Domain, carrier, and the representation structure's fields       |
| `varphi_e = p` | `ComputesName e p`                      | `App e n (p n)` for every input, rather than sort equality       |
| `A_delta`      | `computablePointAssembly delta`         | Carrier subtype `HasComputableName delta` and realizability data |

These are correspondence specifications to implement and check, not evidence that
the current sort audit verifies the last column. Definitions live in
`CauchyNamesPolishRepresentations.lean` and `LambdaComputablePointAssemblies.lean`
under `polish-space/lean/PolishSpaceBook/`.

Report independent outcomes: a structural mismatch, a semantic-role conflict,
a missing declaration, an unresolved Lean mapping, or a stale mapping. Successful
projection does not imply role consistency; absence of a mismatch does not imply
complete coverage. Report resolved occurrences and eligible occurrences separately,
excluding identified constants and syntax tokens. Heuristic inference must retain
its provenance and must not silently overwrite explicit declarations or Lean evidence.

Implement in this order, with regression cases at each step:

1. Introduce declaration identities and evidence provenance; detect incompatible
   redefinitions and same-sort role changes without confusing legitimate rebinding.
2. Export and bind Lean evidence for the computable-point assembly example; test
   correct matches, carrier mismatches, missing hypotheses, unsupported mappings,
   and invalidation after a Lean signature change.
3. Extend the correspondence and coverage report to further passages. Split coarse
   sorts such as finite/infinite sequences or typed subsets/ZFC sets where actual
   collision or correspondence evidence requires it. Avoid broad taxonomy changes
   solely to resemble Lean's type language.

#### Computable-point assembly pilot

Run `python3 tools/check_sort_pilot.py --self-test` from the repository root.
The command first performs the targeted incremental Lean validation, then runs
`tools/sort-pilot/Export.lean` against those fresh imports. It writes the elaborated
evidence, findings, and mutation results to `build/sort-pilot/report.json`.
It is an explicit experiment, not part of the general lint gate.

The sidecar `tools/sort-pilot/assembly.json` maps six existing book declarations
(`X`, `delta`, `x`, `p`, `e`, and `A_delta`) to binder positions or a result in
three Lean definitions. Five declaration fingerprints additionally cover
`Representation` and its constructor, so changes to its fields and hypotheses
invalidate the reviewed correspondence. Three Lean adapters check the defining
computation predicate, the domain-restricted existential, and the assembly's
realization relation by definitional equality. The bridge from a Lean carrier
`X` to the book's `X : Set(Point)` is an explicit convention for this passage.
It is not a global type erasure rule.

The experiment detects:

- Swapping the `e` and `p` binder mappings: structural sort mismatch.
- Replacing `delta(p)=x` with `delta(e)=x` in the passage: source correspondence
  becomes stale and requires review; this is not automatic parsing of the equality.
- Removing the declaration of `e`: a missing declaration, separately from staleness.
- Missing exported Lean evidence: an unresolved mapping.
- Adding a Lean hypothesis: a changed elaborated signature/body fingerprint.
- Replacing total computation with computation on one input: rejection of the
  proposed adapter by Lean, despite unchanged variable types.

The mutation checks use temporary sources/evidence and leave the book and Lean
library unchanged. Fingerprints are conservative: formatting in the selected book
passage or elaborator/version changes can request review too. A fingerprint is a
freshness guard, not a proof of correspondence. Review the passage, exported
binders, and adapters before manually updating the recorded fingerprints; the
runner deliberately has no automatic accept/update mode.

Annotation cost for this pilot is six mapping entries, five Lean fingerprints,
one passage fingerprint, and three short Lean adapters. It reuses the book's
existing sort declarations and adds no prose or translation annotations. The
`varphi_*` declaration is not mapped to a binder: the expression `varphi_e=p` is
covered by the computation adapter. Six checked mappings are not coverage of
all variable occurrences. Same-type role swaps, arbitrary prose, and proof-local
binding identities remain outside the pilot. The domain dependencies are checked
by the Lean adapters and fingerprints, not by a general dependency projector.

The result supports extending small Lean-backed interfaces before implementing
an unrestricted semantic-role taxonomy. Next, add scope/identity diagnostics and
explicit reporting for unsupported mappings; expand only when a concrete example
shows a useful error that the pilot cannot detect.

#### Additional expression correspondence trials

The same `python3 tools/check_sort_pilot.py --self-test` command also checks
`tools/sort-pilot/Correspondences.lean` and the three `case-*.json` sidecars.
Each sidecar records a bounded source passage, explicit variable/binder mappings,
exact book expressions, their named Lean adapters, and reviewed fingerprints.
The report includes each case separately. Expression matching is explicit and
anchor-based; it is not an automatic translation of arbitrary book formulas.

| Case                             | Mapped distinction                                           | Checked interface                                                                           |
| -------------------------------- | ------------------------------------------------------------ | ------------------------------------------------------------------------------------------- |
| Forcing ordinal preservation     | Name, evaluated set, and ordinal rank represented as a set   | `valuation`, the rank bound, `Ordinal.toZFSet`, and check-name evaluation with nonempty `G` |
| Internal finite-list coding      | `List Nat`, its `ZFSet` function graph, and its numeric code | Encoding/decoding graph membership and inverse coding                                       |
| Borel-expression chain witnesses | Witness digits, decoded finite words, and child indices      | Child-chain row equivalence and the non-well-foundedness witness                            |

For ordinal preservation, the [Markdown source](polish-space/src/polish-space-book/appendix-forcing.md)
owns the variable mapping in a `lean-correspondence` JSON comment before the
proposition. Its matching `lean-correspondence-end` comment closes the scope.
Each binding is one pair, for example `"name": ["\\tau", "bound.τ"]`:
`name` is the stable source identity, `\\tau` is the JSON spelling of the TeX
symbol, and `bound.τ` selects binder `τ` of the declaration aliased as `bound`.
The resulting identity is `ordinal-preservation/name`. There are no handwritten
sorts, Lean types, or argument positions; these are resolved from Lean by name.
The two aliases reference existing library theorems, not the pilot wrappers.

Run the command above to generate the [readable report](build/sort-pilot/forcing.html)
and `report.json`. The latter contains the resolved bindings, an identity on each
source occurrence, and a `reverseBindings` index from Lean binders to source IDs.
Existing Lean-to-Markdown booklinks remain theorem/proof links; they do not need
a duplicate variable mapping. The [sidecar](tools/sort-pilot/case-forcing.json)
retains reviewed formula interpretations, premise/application provenance and
freshness fingerprints. Its variable mappings and all handwritten Lean types
have been removed. The report covers all 14 dollar-delimited formulas, all
33 occurrences of six variables, 11 proof hypotheses and all 11 arguments of
`ordinal_valuation_mem_ground`.

Scope boundaries, unique declaration IDs, unique source spellings, and unique
Lean binders are checked. The pilot rejects nested scopes rather than guessing
shadowing behavior. It does not infer quantifier bindings or semantic roles
from prose. A change of target, even to a binder of the same type, invalidates
the reviewed annotation fingerprint; this requests review rather than claiming
to prove that the new correspondence is wrong. Reordering Lean parameters needs
no handwritten slot update, although the changed Lean signature still requires
freshness review. Structural sorts elsewhere in the book remain unchanged.

The report separately enumerates every formula occurrence and records
`typechecked` or `unresolved`. A booklink or matching declaration is not enough
for `typechecked`: a reviewed `term` is elaborated in Lean with variables obtained
from the Markdown bindings, and Lean supplies the inferred type. No expected
type is handwritten. Section variables let Lean handle local binders inside the
interpretation. The pilot uses universe 0, as do its existing proof adapters.
Failed or missing interpretations remain in the denominator with a reason and,
for Lean failures, diagnostics. Stale source/mapping evidence grants no checked
status. Type checking a proposition does not prove it, nor does it prove that
the interpretation matches the prose.

Currently all 14 formulas are inventoried, 12 interpretations elaborate, and two
remain unresolved: the ordinal/set conversion in `α ≤ rank(τ)` and the binding
effect of `β := rank(τ) ∈ M`. Their proof infrastructure exists; the missing
piece is an explicit expression-level interpretation convention. Thus 100%
mapping coverage is distinct from the current 12/14 expression type coverage.
This experiment checks registered interpretations, not a general TeX-to-Lean
translator. The generated JSON exposes each occurrence, context, Lean expression,
inferred type or unresolved reason; the HTML presents the same distinction.

`ordinalSourceProof` checks both inclusions with the printed hypotheses and the
explicit specialization `β := τ.rank.toZFSet`. `ordinalSourceClasses` checks the
resulting equality of external ordinal subclasses; `internalOrdinal` checks the
bounded-predicate interpretation for transitive domains. The interpretation of
printed `Ord` as that predicate remains a reviewed source correspondence.
The bounded lexer rejects unfamiliar mathematical tokens; it does not parse
general TeX or variables spelled only in prose. Missing formulas, variables,
hypotheses and arguments are errors. Mutation checks require review after retargeting between
two `ZFSet` binders and reject using `α` as the rank witness despite its matching type.
This complete coverage claim is restricted to this proposition and proof;
the other trials still use selected mappings.

The list trial exposed a notation collision: the internal-list-coding section
used `s,t` for both finite words and their set-theoretic graphs. It now reserves
`s,t` for words and `g,h` for graphs, with explicit structural declarations.
The corresponding Japanese catalog and Lean booklink excerpts use the same
names. The theorem and its mathematical hypotheses did not change.

The additional mutation checks swap binder positions in each case and ask Lean
to reject a natural-number code used as a set-theoretic graph, a whole word used
as a child number, and an ordinal rank used without its set conversion. These
exercise actual elaboration failures, in addition to source/signature freshness.
The adapters retain the difference between existence of a chain witness and
computable selection of one. The forcing check-name adapter requires a nonempty
`G` contained in `P`, without assuming genericity.

The broader proof obligations remain in the imported book library. In particular,
the graph-entry adapter requires the explicit identification `C = listCodeGraph`;
it does not infer that identification from the letter `C`. The sidecars also pin
the full internal graph-membership and ordinal-preservation theorem signatures,
so their hypotheses are visible in exported evidence. Same-type semantic swaps
still need a role/dependency check or a suitable Lean adapter; two arbitrary
`ZFSet` objects are not distinguished by their type alone. These trials do not
claim complete coverage of their passages or surrounding chapters.

## Pipeline

```
<book>/src/<stem>.json + <book>/src/<stem>.md + chapter inputs
  → pandoc (with book-filter + citeproc)
  → <book>/build/<stem>.tex
  → <book>/build/<stem>.pdf (via lualatex and makeindex when needed)
```

Every `*/src/*.json` manifest defines one book. The manifest names the master source and chapter inputs, and `make` discovers these manifests automatically; run `make list-books` to see the discovered book projects.

`tools/book-filter/Main.hs` is a custom pandoc filter that checks watched notation, emits notation index entries and hyperlinks, resolves `§{sec:...}` section references, and supports local mathematical declaration metadata. Each book carries its own TeX support under `<book>/tex/` (`macros.tex`, `references.bib`); an excerpt book symlinks its `tex/` at the book it extracts.

## License

Different parts of this repository are licensed under different terms, with vendored third-party components retaining their own upstream licenses:

- **Source code** (build tooling, `tools/`, Lean and Python sources) — MIT License, see [LICENSE-MIT](LICENSE-MIT).
- **Written content** (Markdown book sources, TeX prose, figures, and rendered PDFs) — Creative Commons Attribution 4.0 International (CC BY 4.0), see [LICENSE-CC-BY-4.0](LICENSE-CC-BY-4.0).
- **Third-party components** under `tools/formalization-viewer/vendor/` are not covered by the above; see [tools/formalization-viewer/vendor/THIRD-PARTY-NOTICES.md](tools/formalization-viewer/vendor/THIRD-PARTY-NOTICES.md).

See [LICENSE](LICENSE) for the overview.
