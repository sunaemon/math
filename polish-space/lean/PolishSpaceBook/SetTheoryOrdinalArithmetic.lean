module

public import PolishSpaceBook.SetTheoryOrdinalBookBasics
public import Mathlib.SetTheory.Ordinal.Principal

@[expose] public section

/-! # The book's right-recursive ordinal arithmetic -/

namespace PolishSpaceBook.SetTheoryModels
open Order
universe u

/-- Addition recurses on its right argument. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Sum, product, and exponentiation of ordinals are defined by transfinite recursion:
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
theorem ordinal_add_recursion (a b : Ordinal.{u}) :
    a + 0 = a ∧ a + (b + 1) = (a + b) + 1 := by
  exact ⟨add_zero a, (add_assoc a b 1).symm⟩

/-- At a nonzero limit, addition is the supremum of earlier right arguments. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
theorem ordinal_add_limit (a l : Ordinal.{u}) (hl : IsSuccLimit l) :
    a + l = ⨆ b : Set.Iio l, a + b.val := by
  apply le_antisymm
  · apply (Ordinal.add_le_iff_of_isSuccLimit hl).mpr
    intro b hb
    exact Ordinal.le_iSup (fun b : Set.Iio l => a + b.val) ⟨b, hb⟩
  · exact Ordinal.iSup_le (fun b => add_le_add_right b.property.le a)

/-- Multiplication stacks one further copy of the left factor at a successor. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Sum, product, and exponentiation of ordinals are defined by transfinite recursion:
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
theorem ordinal_mul_recursion (a b : Ordinal.{u}) :
    a * 0 = 0 ∧ a * (b + 1) = a * b + a :=
  ⟨mul_zero a, mul_add_one a b⟩

/-- Multiplication at a limit collects all earlier stacks, including the zero-factor case. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
theorem ordinal_mul_limit (a l : Ordinal.{u}) (hl : IsSuccLimit l) :
    a * l = ⨆ b : Set.Iio l, a * b.val := by
  apply le_antisymm
  · apply (Ordinal.mul_le_iff_of_isSuccLimit hl).mpr
    intro b hb
    exact Ordinal.le_iSup (fun b : Set.Iio l => a * b.val) ⟨b, hb⟩
  · exact Ordinal.iSup_le (fun b => mul_le_mul_right b.property.le a)

/-- Exponentiation uses ordinal exponents and recurses on the right. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Sum, product, and exponentiation of ordinals are defined by transfinite recursion:
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
theorem ordinal_power_recursion (a b : Ordinal.{u}) :
    a ^ (0 : Ordinal) = 1 ∧ a ^ (b + 1) = a ^ b * a :=
  ⟨Ordinal.opow_zero a, Ordinal.opow_add_one a b⟩

/-- The book restricts the limit formula to bases at least one. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
theorem ordinal_power_limit (a l : Ordinal.{u}) (ha : 1 ≤ a) (hl : IsSuccLimit l) :
    a ^ l = ⨆ b : Set.Iio l, a ^ b.val :=
  Ordinal.opow_limit (ne_of_gt (lt_of_lt_of_le zero_lt_one ha)) hl

/-- The sum is the order type of the left block followed by the right block. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Ordinal arithmetic is non-commutative: $1 + \omega = \omega \ne \omega + 1$, and $2 \cdot \omega = \omega \ne \omega
    \cdot 2$. The recursion is on the right argument: in $\alpha+\beta$, the initial $\alpha$-block is laid down first and
    then extended by $\beta$; in $\alpha\cdot\beta$, the construction stacks $\beta$ many copies of $\alpha$ from left to
    right. This is the source of the asymmetry.
-/
theorem ordinal_sum_type {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
    [IsWellOrder α r] [IsWellOrder β s] :
    Ordinal.type (Sum.Lex r s) = Ordinal.type r + Ordinal.type s :=
  Ordinal.type_sum_lex r s

/-- The product consists of right-factor-many copies of the left factor. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
        \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
        $\beta$.
    *   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
        \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
        $\beta$ copies of $\alpha$ stacked end-to-end.
    *   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
        \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Ordinal arithmetic is non-commutative: $1 + \omega = \omega \ne \omega + 1$, and $2 \cdot \omega = \omega \ne \omega
    \cdot 2$. The recursion is on the right argument: in $\alpha+\beta$, the initial $\alpha$-block is laid down first and
    then extended by $\beta$; in $\alpha\cdot\beta$, the construction stacks $\beta$ many copies of $\alpha$ from left to
    right. This is the source of the asymmetry.
-/
theorem ordinal_product_type {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
    [IsWellOrder α r] [IsWellOrder β s] :
    Ordinal.type (Prod.Lex s r) = Ordinal.type r * Ordinal.type s :=
  Ordinal.type_prod_lex r s

/-- The concrete addition and multiplication examples distinguish the two argument orders. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Ordinal arithmetic is non-commutative: $1 + \omega = \omega \ne \omega + 1$, and $2 \cdot \omega = \omega \ne \omega
    \cdot 2$. The recursion is on the right argument: in $\alpha+\beta$, the initial $\alpha$-block is laid down first and
    then extended by $\beta$; in $\alpha\cdot\beta$, the construction stacks $\beta$ many copies of $\alpha$ from left to
    right. This is the source of the asymmetry.
-/
theorem ordinal_noncommutative_examples :
    1 + (Ordinal.omega0 : Ordinal.{u}) = (Ordinal.omega0 : Ordinal.{u}) ∧
    (Ordinal.omega0 : Ordinal.{u}) ≠ (Ordinal.omega0 : Ordinal.{u}) + 1 ∧
    (2 : Ordinal.{u}) * (Ordinal.omega0 : Ordinal.{u}) = (Ordinal.omega0 : Ordinal.{u}) ∧
    (Ordinal.omega0 : Ordinal.{u}) ≠ (Ordinal.omega0 : Ordinal.{u}) * 2 := by
  refine ⟨Ordinal.one_add_omega0, ne_of_lt (lt_add_one _), ?_, ?_⟩
  · exact_mod_cast (Ordinal.natCast_mul_omega0 (n := 2) (by decide))
  · have h : (Ordinal.omega0 : Ordinal.{u}) < (Ordinal.omega0 : Ordinal.{u}) + (Ordinal.omega0 : Ordinal.{u}) :=
      lt_add_of_pos_right _ Ordinal.omega0_pos
    simpa only [show (2 : Ordinal.{u}) = 1 + 1 from by exact_mod_cast (show (2 : ℕ) = 1 + 1 from rfl),
      mul_add_one, mul_one] using ne_of_lt h

end PolishSpaceBook.SetTheoryModels
