module

public import PolishSpaceBook.SetTheoryCofinalityExamples
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section

/-! # The two least-order-type descriptions of cofinality -/

namespace PolishSpaceBook.SetTheoryModels
open Cardinal Ordinal Order
universe u

/-- A cofinal subset attains the cofinality's ordinal representative. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{cofinality} $\cf(\alpha)$ of a limit ordinal $\alpha$ is the least order type of an unbounded subset of
    $\alpha$. Equivalently, the least $\kappa$ such that $\alpha = \sup\{\beta_\xi : \xi<\kappa\}$ for some increasing
    sequence in $\alpha$ indexed by $\kappa$.
-/
theorem cofinal_subset_attains (a : Ordinal.{u}) :
    ∃ s : Set a.ToType, IsCofinal s ∧ typeLT s = a.cof.ord := by
  simpa only [Ordinal.cof_toType] using (Ordinal.exists_ord_cof_eq a.ToType)

/-- Every cofinal subset has at least this order type. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{cofinality} $\cf(\alpha)$ of a limit ordinal $\alpha$ is the least order type of an unbounded subset of
    $\alpha$. Equivalently, the least $\kappa$ such that $\alpha = \sup\{\beta_\xi : \xi<\kappa\}$ for some increasing
    sequence in $\alpha$ indexed by $\kappa$.
-/
theorem cofinal_subset_type_lower_bound (a : Ordinal.{u}) (s : Set a.ToType)
    (hs : IsCofinal s) : a.cof.ord ≤ typeLT s := by
  rw [Cardinal.ord_le, Ordinal.card_type]
  rw [← Ordinal.cof_toType]
  exact Order.cof_le hs

/-- At a limit, a strictly increasing sequence of length cf(a) has supremum a. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{cofinality} $\cf(\alpha)$ of a limit ordinal $\alpha$ is the least order type of an unbounded subset of
    $\alpha$. Equivalently, the least $\kappa$ such that $\alpha = \sup\{\beta_\xi : \xi<\kappa\}$ for some increasing
    sequence in $\alpha$ indexed by $\kappa$.
-/
theorem cofinal_increasing_sequence_attains (a : Ordinal.{u}) (ha : IsSuccLimit a) :
    ∃ f : Set.Iio a.cof.ord → Set.Iio a,
      StrictMono f ∧ (⨆ i, (f i).val) = a := by
  obtain ⟨f, hf⟩ := Ordinal.exists_isFundamentalSeq (o := a) rfl
  refine ⟨f, hf.strictMono, hf.iSup_eq ?_⟩
  simpa only [Cardinal.ord_one] using
    (Cardinal.ord_strictMono (Ordinal.one_lt_cof_iff.mpr ha))

/-- Even without monotonicity, a sequence with supremum a cannot have shorter index ordinal. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{cofinality} $\cf(\alpha)$ of a limit ordinal $\alpha$ is the least order type of an unbounded subset of
    $\alpha$. Equivalently, the least $\kappa$ such that $\alpha = \sup\{\beta_\xi : \xi<\kappa\}$ for some increasing
    sequence in $\alpha$ indexed by $\kappa$.
-/
theorem cofinal_sequence_length_lower_bound {a k : Ordinal.{u}}
    (f : Set.Iio k → Set.Iio a) (hsup : (⨆ i, (f i).val) = a) : a.cof.ord ≤ k := by
  by_contra hn
  have hk : k.card < a.cof := Cardinal.lt_ord.mp (lt_of_not_ge hn)
  have hsmall : (⨆ i, (f i).val + 1) < a :=
    Ordinal.lift_iSup_add_one_lt_of_lt_cof
      (by simpa only [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, ← Ordinal.lift_cof,
        Cardinal.lift_lt] using hk) (fun i => (f i).property)
  have hle : a ≤ ⨆ i, (f i).val + 1 := hsup.ge.trans
    (Ordinal.iSup_le (fun i => (le_add_right (le_refl (f i).val)).trans
      (Ordinal.le_iSup (fun i => (f i).val + 1) i)))
  exact (not_lt_of_ge hle) hsmall

/-- Both descriptions in the book have the same least ordinal, not merely the same cardinality. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{cofinality} $\cf(\alpha)$ of a limit ordinal $\alpha$ is the least order type of an unbounded subset of
    $\alpha$. Equivalently, the least $\kappa$ such that $\alpha = \sup\{\beta_\xi : \xi<\kappa\}$ for some increasing
    sequence in $\alpha$ indexed by $\kappa$.
-/
theorem cofinality_two_minima (a : Ordinal.{u}) (ha : IsSuccLimit a) :
    IsLeast {k : Ordinal.{u} | ∃ s : Set a.ToType, IsCofinal s ∧ typeLT s = k} a.cof.ord ∧
    IsLeast {k : Ordinal.{u} | ∃ f : Set.Iio k → Set.Iio a,
      StrictMono f ∧ (⨆ i, (f i).val) = a} a.cof.ord := by
  constructor
  · refine ⟨cofinal_subset_attains a, ?_⟩
    rintro k ⟨s, hs, hk⟩
    simpa only [hk] using cofinal_subset_type_lower_bound a s hs
  · refine ⟨cofinal_increasing_sequence_attains a ha, ?_⟩
    rintro k ⟨f, _, hsup⟩
    exact cofinal_sequence_length_lower_bound f hsup

end PolishSpaceBook.SetTheoryModels
