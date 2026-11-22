module

public import PolishSpaceBook.LambdaZeroSelection
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace PolishSpaceBook
open Set

/-- The promised continuous functions have individual zeros, independently of
whether there is a uniform procedure selecting those zeros. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    The intermediate value theorem guarantees existence, but does not supply one procedure for selecting an exact zero
    from every named function. We prove this distinction with one explicit family. The input functions below are defined
    on $\R$, so their names provide even more information than their restrictions to $[0,1]$.
-/
theorem continuous_sign_change_has_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : f 0 < 0) (h1 : 0 < f 1) : ∃ x ∈ Icc (0 : ℝ) 1, f x = 0 := by
  exact intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf.continuousOn ⟨h0.le, h1.le⟩

end PolishSpaceBook
