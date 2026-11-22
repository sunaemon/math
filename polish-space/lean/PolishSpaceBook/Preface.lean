module

@[expose] public section

/-!
# Preface

Organizational entry for `polish-space/src/polish-space-book/preface.md`.

## Terminology and notation

The preface mostly fixes global notation rather than proving mathematical
claims. The corresponding Lean objects are usually mathlib primitives or syntax.

| Book notation | Lean counterpart |
| --- | --- |
| `A \IncludedIn B` | predicate `Set.Subset A B` |
| `A \StrictlyIncludedIn B` | proper subset order on sets |
| `\PowerSet{A}` | `Set alpha` for the power set of a type's carrier; if `A : Set alpha`, then `Set.powerset A` or `{s : Set alpha // s ⊆ A}` |
| `\SetDifference{A}{B}` | `A \ B`, with definition `Set.diff` |
| `A \disjointUnion B` | tagged sums `Sum alpha beta` |
| `\NN`, `\ZZ`, `\QQ`, `\R` | `Nat`, `Int`, `Rat`, `Real` |
| `\RestrictedSet{P}{\le t}` and variants | set-builder notation `{x : P | ...}`, plus `Set.Iic`, `Set.Ici`, `Set.Iio`, `Set.Ioi` |
| `\Ball{x}{r}` | `Metric.ball x r` |
| `\Closure{A}` | `closure A` |
| `\Diameter{A}` | `Metric.diam A` for bounded sets; `Metric.ediam A` for the extended diameter |
| ordinals | `Ordinal` |
| partial functions | usually a domain predicate/subtype, or `Part` when partiality is the object |
| relation composition | `Relation.Comp` |
| function composition | `Function.comp g f` |
| injections and surjections | `Function.Injective`, `Function.Surjective` |
| function powers `\funcspace{B}{A}` | function types `B -> A` |
| finite sequence spaces `\seqPower{A}{n}` | functions `Fin n -> A` |
| restrictions `\restrict{f}{A}` | `Set.restrict A f` |
-/

namespace PolishSpaceBook

end PolishSpaceBook
