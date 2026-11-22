module

public import PolishSpaceBook.CantorBaireSpace
public import PolishSpaceBook.ForcingPolishSpaces
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Topology.Sets.Opens

@[expose] public section

/-! # The external regular-open completion of Cohen forcing

This is the ordinary external completion. It does not identify all external
regular opens with the internally computed completion of a ground model.
-/

noncomputable section
namespace PolishSpaceBook
open Set TopologicalSpace

abbrev RegularOpen (X : Type*) [TopologicalSpace X] := Heyting.Regular (Opens X)

/-- Regularization is a Galois insertion; arbitrary joins and meets therefore
exist in the regular-open Boolean algebra. -/
instance regularOpenCompleteBooleanAlgebra (X : Type*) [TopologicalSpace X] :
    CompleteBooleanAlgebra (RegularOpen X) := by
  let C : CompleteLattice (Heyting.Regular (Opens X)) := Heyting.Regular.gi.liftCompleteLattice
  exact { (inferInstance : BooleanAlgebra (Heyting.Regular (Opens X))) with
    sSup := C.sSup
    isLUB_sSup := C.isLUB_sSup
    sInf := C.sInf
    isGLB_sInf := C.isGLB_sInf }

theorem opens_double_complement {X : Type*} [TopologicalSpace X] (U : Opens X) :
    ((Uᶜᶜ : Opens X) : Set X) = interior (closure (U : Set X)) := by
  rw [Opens.coe_compl_eq_interior_compl, Opens.coe_compl_eq_interior_compl,
    ← closure_eq_compl_interior_compl]

theorem regularOpen_eq_interior_closure {X : Type*} [TopologicalSpace X] (U : RegularOpen X) :
    interior (closure (U.val : Set X)) = (U.val : Set X) := by
  rw [← opens_double_complement]
  exact congrArg (fun V : Opens X => (V : Set X)) U.property

/-- The arbitrary join is regularization of the union, as in the topological
regular-open completion. -/
theorem regularOpen_sSup_coe {X : Type*} [TopologicalSpace X] (S : Set (RegularOpen X)) :
    ((sSup S).val : Set X) = interior (closure (⋃ U ∈ S, (U.val : Set X))) := by
  change (((sSup ((fun U : RegularOpen X => U.val) '' S) : Opens X)ᶜᶜ : Opens X) : Set X) = _
  rw [opens_double_complement, Opens.coe_sSup]
  simp only [Set.biUnion_image]

theorem regularOpen_complement_coe {X : Type*} [TopologicalSpace X] (U : RegularOpen X) :
    (Uᶜ.val : Set X) = interior (U.val : Set X)ᶜ :=
  Opens.coe_compl_eq_interior_compl

/-- A clopen set is already regular, so its cylinder does not change under
regularization. -/
def clopenRegularOpen {X : Type*} [TopologicalSpace X] (s : Set X) (hs : IsClopen s) : RegularOpen X :=
  ⟨⟨s, hs.isOpen⟩, by
    apply Opens.ext
    rw [opens_double_complement]
    change interior (closure s) = s
    rw [hs.isClosed.closure_eq, hs.isOpen.interior_eq]⟩

def cohenCylinder (s : CohenCondition) : RegularOpen (ℕ → Bool) :=
  clopenRegularOpen (cyl s) (isClopen_cyl s)

theorem cohenCylinder_ne_bot (s : CohenCondition) : cohenCylinder s ≠ ⊥ := by
  intro he
  have hz : cyl s = ∅ := congrArg (fun U : RegularOpen (ℕ → Bool) => (U.val : Set (ℕ → Bool))) he
  exact (cyl_nonempty s).ne_empty hz

theorem cohenCylinder_le_iff (s t : CohenCondition) :
    cohenCylinder s ≤ cohenCylinder t ↔ CohenStronger s t :=
  cyl_subset_iff_prefix

/-- The finite-string order embeds with its stronger-than convention intact. -/
def cohenRegularOpenEmbedding : @OrderEmbedding CohenCondition (RegularOpen (ℕ → Bool))
    cohenOrder.toLE inferInstance where
  toFun := cohenCylinder
  inj' := by
    intro s t h
    apply cyl_injective
    exact congrArg (fun U : RegularOpen (ℕ → Bool) => (U.val : Set (ℕ → Bool))) h
  map_rel_iff' := fun {s t} => cohenCylinder_le_iff s t

/-- Every nonzero regular open contains a nonempty cylinder. This is density
in the positive algebra, not merely density of a union in Cantor space. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The original finite-string order for Cohen forcing embeds densely in its completion.
-/
theorem cohenCylinder_dense (U : RegularOpen (ℕ → Bool)) (hU : U ≠ ⊥) :
    ∃ s : CohenCondition, cohenCylinder s ≤ U := by
  have hne : (U.val : Set (ℕ → Bool)).Nonempty := by
    by_contra hn
    have he : (U.val : Set (ℕ → Bool)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    apply hU
    apply Subtype.ext
    exact Opens.ext he
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, _, hs⟩ := exists_cyl_subset_of_mem_open hx U.val.isOpen
  exact ⟨s, hs⟩

end PolishSpaceBook
