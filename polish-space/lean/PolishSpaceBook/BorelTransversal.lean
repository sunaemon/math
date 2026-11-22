module

public import PolishSpaceBook.BorelReducibilitySynthesis
public import PolishSpaceBook.UniformizationFromBorelGraphs

@[expose] public section

/-! # Borel representatives from a Borel transversal

The projection of the representative graph is injective. The book's
Lusin--Suslin construction supplies its measurable inverse, whose second
coordinate is the representative map.
-/
namespace PolishSpaceBook
noncomputable section
open Set MeasureTheory

variable {X : Type} [MeasurableSpace X] [StandardBorelSpace X]

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: proof
  excerpt: |
    For the corollary, let $T$ be a Borel transversal and define $c(x)$ to be the unique point of $T$ in the $E$-class of
    $x$. The graph of $c$ is
    $$
    \{(x,t)\in X\times T:x\mathrel E t\}.
    $$
    Equivalently, it is the Borel subset $E\cap(X\times T)$ of $X\times X$. Its vertical section over $x$ is the singleton
    consisting of the unique representative of the $E$-class of $x$ in $T$. Applying the
    \termuse{Lusin--Suslin theorem} from §{sec:lusin-souslin-theorem} to the injective projection
    $$
    E\cap(X\times T)\longrightarrow X,\qquad (x,t)\longmapsto x,
    $$
    shows that its image is Borel and that the inverse map $x\mapsto (x,c(x))$ is Borel. The image is all of $X$ because $T$
    meets every class, so $c$ is Borel and separates exactly the $E$-classes.
    \end{proof}
-/
/-- A Borel transversal yields a measurable representative map and complete invariant. -/
theorem borel_representative_of_transversal {E : X → X → Prop}
    (hE : Equivalence E) (hB : MeasurableSet {p : X × X | E p.1 p.2})
    {T : Set X} (hT : MeasurableSet T)
    (hrep : ∀ x, ∃! t, t ∈ T ∧ E x t) :
    ∃ c : X → X, Measurable c ∧ (∀ x, c x ∈ T ∧ E x (c x)) ∧
      CompleteInvariant E c := by
  let := upgradeStandardBorel X
  let G : Set (X × X) := {p | E p.1 p.2 ∧ p.2 ∈ T}
  have hG : MeasurableSet G := hB.inter (hT.preimage measurable_snd)
  have hi : InjOn Prod.fst G := by
    intro p hp q hq he
    apply Prod.ext he
    exact (hrep p.1).unique ⟨hp.2, hp.1⟩ ⟨hq.2, he.symm ▸ hq.1⟩
  obtain ⟨_, f, hf, hgraph⟩ := borel_map_of_singleton_sections hG hi
  have hdom (x : X) : x ∈ Prod.fst '' G := by
    obtain ⟨t, ht, _⟩ := hrep x
    exact ⟨(x, t), ⟨ht.2, ht.1⟩, rfl⟩
  let q : X → (Prod.fst '' G) := fun x => ⟨x, hdom x⟩
  have hq : Measurable q := measurable_id.subtype_mk
  let c : X → X := f ∘ q
  have hc (x : X) : E x (c x) ∧ c x ∈ T := by
    have hg : (x, c x) ∈ range (fun z => (z.val, f z)) := ⟨q x, rfl⟩
    rw [hgraph] at hg
    exact hg
  refine ⟨c, hf.comp hq, fun x => ⟨(hc x).2, (hc x).1⟩, ?_⟩
  intro x y
  constructor
  · intro hxy
    exact (hrep x).unique ⟨(hc x).2, (hc x).1⟩
      ⟨(hc y).2, hE.trans hxy (hc y).1⟩
  · intro he
    exact hE.trans (hc x).1 (by rw [he]; exact hE.symm (hc y).1)

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: statement
  kind: corollary
  title: Transversal criterion
-/
/-- The representative map is the standard-Borel complete invariant used in the book. -/
theorem smooth_of_borel_transversal {E : X → X → Prop}
    (hE : Equivalence E) (hB : MeasurableSet {p : X × X | E p.1 p.2})
    {T : Set X} (hT : MeasurableSet T)
    (hrep : ∀ x, ∃! t, t ∈ T ∧ E x t) : Smooth E := by
  obtain ⟨c, hc, _, hcomplete⟩ := borel_representative_of_transversal hE hB hT hrep
  exact smooth_of_standardBorel_completeInvariant hc hcomplete

end
end PolishSpaceBook
