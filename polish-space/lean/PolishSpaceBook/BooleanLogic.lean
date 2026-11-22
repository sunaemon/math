module

public import Mathlib.Order.BooleanAlgebra.Basic

@[expose] public section

namespace PolishSpaceBook

/-- The Boolean interpretation of excluded middle has top truth value. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    For a complete Boolean algebra $\mathbb B$, forcing is classical. The Boolean operations decide every truth value by
    $$
    [\![\varphi\lor\neg\varphi]\!]=1_{\mathbb B}.
    $$
-/
theorem boolean_excluded_middle {B : Type*} [BooleanAlgebra B] (b : B) :
    b ⊔ bᶜ = ⊤ := sup_compl_eq_top

end PolishSpaceBook
