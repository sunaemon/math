module

public import PolishSpaceBook.LambdaKernelComplexity
public import PolishSpaceBook.LambdaCatalogProjections

@[expose] public section

/-!
# The actual kernels as conditions in the fixed-parameter catalog

Nonemptiness and relative analyticity now supply the initial conditions.
The hereditary conclusions apply to every stronger catalog condition,
without separately assuming that the kernels have relative codes.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    First work on Baire space. Code pairs by coordinatewise numerical pairing, choose a closed witness
    presentation of the nonrelation of $E$, and put its finite node tests in one parameter as in
    §{sec:edst-generic-conditions}. The kernel construction then gives $H$ a pair-tree presentation at
    that same parameter, and uncountably many classes imply $H\ne\emptyset$. Thus the kernel itself is
    a condition in the fixed-parameter order. Enumerate the node witness tests and the product tests
    from the splitting lemma as $\Sequence{D_n}{n\in\omega}$ and $\Sequence{J_n}{n\in\omega}$. Replace each family by the
    intersection of its first
    $n+1$ members, and include diameter at most $2^{-n}$ in $D_n$.
-/
noncomputable def parameterSilverKernelCondition (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    [Uncountable (Quotient E)] : (parameterAnalyticCatalog ε).Condition :=
  parameterCondition ε (silverKernel ε E)
    (projected_silverKernel ε E hneE)
    (silverKernel_nonempty ε E)

theorem parameterSilverKernelCondition_not_homogeneous (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    [Uncountable (Quotient E)] (A : (parameterAnalyticCatalog ε).Condition)
    (hA : A ≤ parameterSilverKernelCondition ε E hneE) : ¬ ERHomogeneous E A.val.val :=
  silverKernel_not_homogeneous E hneE (parameterCondition_projected ε A) A.val.property.2 hA

noncomputable def parameterHKLKernelCondition (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hns : ¬ Smooth E.r) : (parameterAnalyticCatalog ε).Condition :=
  parameterCondition ε (equivalenceGapKernel E (invariantSetoid ε E))
    (projected_hklKernel ε E hE hneE) (invariantKernel_nonempty ε E hns)

/-- Every stronger HKL condition contains distinct points related by the
actual auxiliary relation and inequivalent under the original relation. -/
theorem parameterHKLKernelCondition_distinct_related (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hns : ¬ Smooth E.r) (A : (parameterAnalyticCatalog ε).Condition)
    (hA : A ≤ parameterHKLKernelCondition ε E hE hneE hns) :
    ∃ x ∈ A.val.val, ∃ y ∈ A.val.val,
      (invariantSetoid ε E).r x y ∧ ¬ E.r x y ∧ x ≠ y := by
  obtain ⟨x, hx, y, hy, hxy, hn⟩ := hkl_hereditary ε E hE hneE
    (parameterCondition_projected ε A) A.val.property.2 hA
  exact ⟨x, hx, y, hy, hxy, hn, fun he => hn (he ▸ E.refl x)⟩

end LambdaTree
end PolishSpaceBook
