module

public import PolishSpaceBook.EffrosOrbitMaps
public import PolishSpaceBook.LusinSuslinRefinement

/-! # Borelness of each individual orbit

This application is kept after the Lusin--Suslin prefix construction in the
public import graph; the early Polish-group API is itself used by that construction.

@[expose] public section
The cited Polish-quotient theorem is an explicit external premise.
-/

namespace PolishSpaceBook
open Set Topology TopologicalSpace

section IndividualOrbit
variable {G : Type} {X : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [PolishSpace X] [MulAction G X] [ContinuousSMul G X]
  [MeasurableSpace X] [BorelSpace X]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Every individual orbit is nevertheless Borel: the continuous bijection from the Polish quotient by its
    stabilizer has Borel image by the Lusin--Souslin theorem. This does not force the orbit equivalence relation
    $\OrbitER{G}{X}$ to be Borel; it may be properly analytic.
-/
/-- Individual orbits are Borel even when the orbit relation is not.
Use the book's injective-image construction on the Polish quotient. -/
theorem measurableSet_orbit_of_polish_quotient (x : X)
    [PolishSpace (G ⧸ MulAction.stabilizer G x)] :
    MeasurableSet (MulAction.orbit G x) := by
  borelize (G ⧸ MulAction.stabilizer G x)
  let f : (G ⧸ MulAction.stabilizer G x) → X :=
    fun q => ((MulAction.orbitEquivQuotientStabilizer G x).symm q : X)
  have hf : Continuous f :=
    continuous_subtype_val.comp (continuous_quotientStabilizerOrbitMap x)
  have hi : Function.Injective f :=
    Subtype.val_injective.comp (MulAction.orbitEquivQuotientStabilizer G x).symm.injective
  have hm := (lusinSuslin_via_prefix_refinement MeasurableSet.univ hf.measurable hi.injOn).1
  have he : f '' univ = MulAction.orbit G x := by
    ext y
    constructor
    · rintro ⟨q, _, rfl⟩
      exact ((MulAction.orbitEquivQuotientStabilizer G x).symm q).property
    · intro hy
      obtain ⟨q, hq⟩ :=
        (MulAction.orbitEquivQuotientStabilizer G x).symm.surjective ⟨y, hy⟩
      exact ⟨q, mem_univ _, congrArg Subtype.val hq⟩
  rwa [he] at hm

end IndividualOrbit

end PolishSpaceBook
