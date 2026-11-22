module

public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-! # Local topological deductions used in the introductory chapters -/
namespace PolishSpaceBook
open Filter Set TopologicalSpace Topology

/-- An isolated singleton would itself be a compact neighborhood. -/
/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    Such a space is automatically \termuseas{perfect space}{perfect}: an isolated point would have its singleton as a
    compact neighborhood.
-/
theorem NoCompactNeighborhoods.perfectSpace {Y : Type*} [TopologicalSpace Y]
    (hY : NoCompactNeighborhoods Y) : PerfectSpace Y := by
  apply (isPerfectSpaceByNoIsolatedPoint_iff_perfectSpace Y).mp
  intro y hy
  exact hY y ⟨{y}, isCompact_singleton, hy.mem_nhds (mem_singleton y)⟩

end PolishSpaceBook
