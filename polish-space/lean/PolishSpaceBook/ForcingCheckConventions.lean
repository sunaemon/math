module

public import PolishSpaceBook.ForcingAtomicTruth

@[expose] public section

/-! # Comparing the two check-name conventions

The all-conditions name and the name using only a weakest condition are both
names for the same ground-model set. Upward closure puts the weakest condition
in every nonempty filter, so the already proved valuation calculation applies.
-/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open ZFSet ForcingAtomic
universe u

/-- Check names using only a weakest condition have the same value as all-conditions names. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For the weakest-condition convention, the same argument uses $1_P\in G$, which holds for every nonempty filter
    by upward closure.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The two constructions need not give the same name, but they have the same valuation under every nonempty filter.
-/
theorem check_weakest_convention (P : ZFSet.{u}) [Preorder (Condition P)]
    (one : Condition P) (hone : ∀ p : Condition P, p ≤ one)
    (G : Order.PFilter (Condition P)) (x : ZFSet.{u}) :
    IsName P (check ({one.val} : ZFSet.{u}) x) ∧
      valuation (chosen P G) (check ({one.val} : ZFSet.{u}) x) = x ∧
      valuation (chosen P G) (check ({one.val} : ZFSet.{u}) x) =
        valuation (chosen P G) (check P x) := by
  obtain ⟨p, hp⟩ := G.nonempty
  have honeG : one ∈ G := G.mem_of_le (hone p) hp
  have hchosen : one.val ∈ chosen P G := ⟨one, honeG, rfl⟩
  have hs := valuation_check ({one.val} : ZFSet.{u}) (chosen P G)
    ⟨one.val, hchosen, by simp⟩ x
  have ha := valuation_check P (chosen P G) ⟨one.val, hchosen, one.property⟩ x
  refine ⟨check_isName_of_subset ?_ x, hs, hs.trans ha.symm⟩
  intro q hq
  have he : q = one.val := mem_singleton.mp hq
  exact he ▸ one.property

end PolishSpaceBook.ForcingNames
