module

public import PolishSpaceBook.StrongChoquetGdelta
public import PolishSpaceBook.StrongChoquetTransport
public import PolishSpaceBook.PolishSpaces
public import Mathlib.Topology.MetricSpace.Completion

@[expose] public section

/-! # The converse strong Choquet characterization of Polish spaces

Embed a separable metrizable space into its metric completion. Transfer the
strategy to the image, construct its ambient G-delta representation, and apply
the chapter's Alexandrov theorem in that Polish completion.
-/
noncomputable section
namespace PolishSpaceBook.StrongChoquetGame
open Set Topology TopologicalSpace UniformSpace
universe u
variable {X : Type u} [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]

/-- The completion construction proves the converse using the actual strategy. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The forward implication follows from the \termuse{metric strong Choquet strategy} above.
    For the converse, fix a compatible metric on the separable metrizable space $X$, embed it in its completion
    $\widehat X$, and transport a winning strategy $\sigma$ to the image. We construct ambient open covers of $X$
    tagged by finite histories following $\sigma$.
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    We have proved
    $$X=\bigcap_{n\in\omega}G_n.$$
    The completion $\widehat X$ is Polish because the original metric is separable. Thus $X$ is $\Gdelta$ in a
    Polish space, and \termuse{Alexandrov's theorem} in §{sec:alexandrov-theorem} shows that $X$ is Polish.
    \end{proof}
-/
theorem polish_of_strongChoquet (hX : IsStrongChoquet X) : PolishSpace X := by
  let := metrizableSpaceMetric X
  let e : X ≃ₜ range ((↑) : X → Completion X) :=
    (Completion.coe_isometry : Isometry ((↑) : X → Completion X)).isEmbedding.toHomeomorph
  have hRange : IsStrongChoquet (range ((↑) : X → Completion X)) := hX.of_homeomorph e.symm
  have hG := isGdelta_of_strongChoquet hRange
  let : PolishSpace (range ((↑) : X → Completion X)) := gdelta_subspace_polish hG
  exact e.isClosedEmbedding.polishSpace

/-- On separable metrizable spaces, the two game and metric characterizations agree. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  excerpt: |
    \begin{claim*} A separable metrizable space is Polish iff it is strong Choquet.
    
    \end{claim*}
-/
theorem polish_iff_strongChoquet : PolishSpace X ↔ IsStrongChoquet X := by
  constructor
  · intro h
    let := h
    exact polish_isStrongChoquet
  · exact polish_of_strongChoquet

end PolishSpaceBook.StrongChoquetGame
