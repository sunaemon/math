module

public import PolishSpaceBook.LusinSuslinRefinement

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The local consequence of the cited Lusin--Novikov decomposition

The decomposition into singleton-section Borel sets is an external theorem.
Given those pieces, the book's Lusin--Suslin construction turns each into a
partial Borel function, with exactly the prescribed graph.
-/
namespace PolishSpaceBook

noncomputable section
open Set MeasureTheory

variable {X Y : Type} [TopologicalSpace X] [PolishSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Y] [BorelSpace Y]

/-- A Borel relation with at most one point in each vertical section is the
graph of a Borel map on its Borel projection. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    Applying this decomposition lemma to $A$ gives Borel sets $G_n\IncludedIn A$ whose vertical sections have size at most
    one and whose union is $A$. For each $n$, let
    $$D_n:=\pi_X(G_n).$$
    The first projection is injective on $G_n$. The Lusin--Suslin theorem in §{sec:lusin-souslin-theorem} therefore makes
    $D_n$ Borel and the inverse $D_n\to G_n$ Borel. Composing that inverse with the second projection gives the unique
    Borel map $f_n:D_n\to Y$ with graph $G_n$.
-/
theorem borel_map_of_singleton_sections {G : Set (X × Y)}
    (hG : MeasurableSet G) (hi : InjOn Prod.fst G) :
    MeasurableSet (Prod.fst '' G) ∧ ∃ f : (Prod.fst '' G) → Y,
      Measurable f ∧ range (fun x => (x.val, f x)) = G := by
  obtain ⟨hD, hm⟩ := lusinSuslin_via_prefix_refinement hG measurable_fst hi
  let q : (Prod.fst '' G) → range (G.domRestrict Prod.fst) := fun x =>
    ⟨x.val, by rcases x.property with ⟨p, hp, hpx⟩; exact ⟨⟨p, hp⟩, hpx⟩⟩
  have hq : Measurable q := measurable_subtype_coe.subtype_mk
  let v := hm.equivRange.symm ∘ q
  have hv : Measurable v := hm.equivRange.symm.measurable.comp hq
  have hfst : ∀ x, (v x).val.1 = x.val := by
    intro x
    simpa only [MeasurableEmbedding.equivRange_apply, Set.domRestrict, Function.comp_def, v, q] using
      congrArg Subtype.val (hm.equivRange.apply_symm_apply (q x))
  let f : (Prod.fst '' G) → Y := fun x => (v x).val.2
  have hgraph : ∀ x, (x.val, f x) ∈ G := by
    intro x
    have heq : (x.val, f x) = (v x).val := Prod.ext (hfst x).symm rfl
    rw [heq]
    exact (v x).property
  refine ⟨hD, f, measurable_snd.comp (measurable_subtype_coe.comp hv), ?_⟩
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact hgraph x
  · intro hp
    let x : (Prod.fst '' G) := ⟨p.1, ⟨p, hp, rfl⟩⟩
    exact ⟨x, hi (hgraph x) hp rfl⟩

/-- Once the cited decomposition is supplied, the partial maps enumerate the
whole relation, rather than merely selecting one point in each section. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    Since the pieces cover $A$, these partial Borel functions satisfy
    $$A=\bigcup_n \mathrm{graph}(f_n).$$
-/
theorem borel_enumeration_of_singleton_decomposition {A : Set (X × Y)}
    (G : ℕ → Set (X × Y)) (hG : ∀ n, MeasurableSet (G n))
    (hi : ∀ n, InjOn Prod.fst (G n)) (hcover : (⋃ n, G n) = A) :
    ∃ f : (n : ℕ) → (Prod.fst '' G n) → Y,
      (∀ n, MeasurableSet (Prod.fst '' G n) ∧ Measurable (f n)) ∧
      (∀ n, range (fun x => (x.val, f n x)) ⊆ A) ∧
      (⋃ n, range (fun x => (x.val, f n x))) = A := by
  choose hD f hf hgraph using fun n => borel_map_of_singleton_sections (hG n) (hi n)
  refine ⟨f, fun n => ⟨hD n, hf n⟩, ?_, ?_⟩
  · intro n
    rw [hgraph n, ← hcover]
    exact subset_iUnion G n
  · simp only [hgraph, hcover]

end

noncomputable section
open Set MeasureTheory

/-- The cited decomposition input is needed only for Polish presentations. -/
def PolishSingletonDecomposition : Prop :=
  ∀ (S T : Type) [TopologicalSpace S] [PolishSpace S]
    [TopologicalSpace T] [PolishSpace T] [MeasurableSpace S] [BorelSpace S]
    [MeasurableSpace T] [BorelSpace T] (B : Set (S × T)),
    MeasurableSet B → (∀ x, {y | (x, y) ∈ B}.Countable) →
    ∃ G : ℕ → Set (S × T), (∀ n, MeasurableSet (G n)) ∧
      (∀ n, InjOn Prod.fst (G n)) ∧ (⋃ n, G n) = B

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    \begin{proof}[Proof from the decomposition lemma] Reduce first to the case $X,Y$ are Polish spaces with their
    Borel $\sigma$-algebras,
    by the definition of a standard Borel space in §{sec:standard-borel-spaces}. The nontrivial step
    is the Lusin--Novikov decomposition lemma: a Borel set $B\IncludedIn X\times Y$ with countable vertical sections can be
    split into countably many Borel pieces, each having at most one point in every vertical section. Equivalently, $B$ is a
    countable union of graphs of partial Borel functions.
-/
/-- Install compatible Polish topologies, apply the cited decomposition, and
use Lusin--Suslin on each injective projection to enumerate every section. -/
theorem borel_enumeration_of_countable_sections
    {S T : Type} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace T] [StandardBorelSpace T]
    (decompose : PolishSingletonDecomposition)
    {A : Set (S × T)} (hA : MeasurableSet A)
    (hsections : ∀ x, {y | (x, y) ∈ A}.Countable) :
    ∃ G : ℕ → Set (S × T), ∃ f : (n : ℕ) → (Prod.fst '' G n) → T,
      (∀ n, MeasurableSet (Prod.fst '' G n) ∧ Measurable (f n)) ∧
      (∀ n, range (fun x => (x.val, f n x)) ⊆ A) ∧
      (⋃ n, range (fun x => (x.val, f n x))) = A := by
  let := upgradeStandardBorel S
  let := upgradeStandardBorel T
  obtain ⟨G, hG, hi, hcover⟩ := decompose S T A hA hsections
  obtain ⟨f, hmeas, hsub, heq⟩ :=
    borel_enumeration_of_singleton_decomposition G hG hi hcover
  exact ⟨G, f, hmeas, hsub, heq⟩

end
end PolishSpaceBook
