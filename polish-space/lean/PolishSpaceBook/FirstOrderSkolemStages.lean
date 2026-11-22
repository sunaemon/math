module

public import Mathlib.ModelTheory.Skolem
public import PolishSpaceBook.FirstOrderTarskiVaught

@[expose] public section

/-!
# Finite-stage closure under the original and chosen Skolem functions

Each successor stage adjoins all function values on finite tuples in the
previous stage. A tuple from the union lies in one common stage, so the union
is a substructure. Countability follows at each stage and at the union.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

/-- One closure step, allowing nullary function symbols as well. -/
def operationStep (L : Language.{u,v}) {M : Type w} [L.Structure M] (A : Set M) : Set M :=
  A ∪ ⋃ f : Σ n, L.Functions n, Set.range (fun s : Fin f.1 → A => Structure.funMap f.2 (Subtype.val ∘ s))

def operationStages (L : Language.{u,v}) {M : Type w} [L.Structure M] (X : Set M) : ℕ → Set M
  | 0 => X
  | n + 1 => operationStep L (operationStages L X n)

theorem operationStages_mono (X : Set M) : Monotone (operationStages L X) :=
  monotone_nat_of_le_succ (fun _ => Set.subset_union_left)

theorem countable_operationStep [Countable (Σ n, L.Functions n)] {A : Set M} (hA : A.Countable) :
    (operationStep L A).Countable := by
  let : Countable A := hA.to_subtype
  exact hA.union (Set.countable_iUnion (fun _ => Set.countable_range _))

theorem countable_operationStages [Countable (Σ n, L.Functions n)] {X : Set M} (hX : X.Countable) (n : ℕ) :
    (operationStages L X n).Countable := by
  induction n with
  | zero => exact hX
  | succ n ih => exact countable_operationStep ih

/-- Every finite tuple in the union occurs in a common finite stage. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Every finite tuple from $B$ lies in one $B_n$: choose a stage for each entry and take the maximum, or use stage zero
    for the empty tuple. Applying any $F\in\mathcal F$ to this tuple gives an element of $B_{n+1}$.
    Consequently $B$ is closed under the original function interpretations and under the chosen Skolem functions.
-/
theorem tuple_in_operationStage (X : Set M) {n : ℕ} (s : Fin n → M)
    (hs : ∀ i, s i ∈ ⋃ k, operationStages L X k) :
    ∃ k, ∀ i, s i ∈ operationStages L X k := by
  classical
  choose k hk using (fun i => Set.mem_iUnion.mp (hs i))
  refine ⟨Finset.univ.sup k, fun i => ?_⟩
  exact operationStages_mono X (Finset.le_sup (Finset.mem_univ i)) (hk i)

/-- The union of the explicitly constructed stages, with its restricted interpretations. -/
def operationSubstructure (X : Set M) : L.Substructure M where
  carrier := ⋃ k, operationStages L X k
  fun_mem := by
    intro n f s hs
    obtain ⟨k, hk⟩ := tuple_in_operationStage X s hs
    apply Set.mem_iUnion.mpr
    refine ⟨k + 1, Set.mem_union_right _ ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨⟨n, f⟩, ⟨fun i => ⟨s i, hk i⟩, rfl⟩⟩

theorem subset_operationSubstructure (X : Set M) : X ⊆ operationSubstructure (L := L) X :=
  fun _ hx => Set.mem_iUnion.mpr ⟨0, hx⟩

theorem countable_operationSubstructure [Countable (Σ n, L.Functions n)] {X : Set M} (hX : X.Countable) :
    (operationSubstructure (L := L) X : Set M).Countable :=
  Set.countable_iUnion (countable_operationStages hX)

end PolishSpaceBook.NamedFirstOrder
