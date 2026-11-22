module

public import PolishSpaceBook.FirstOrderFunctionElimination

@[expose] public section

/-!
# Comparison beneath two blocks of fresh witnesses

Corresponding positions are bound together; all names outside the two blocks
retain their original relation. The order matches existsBlock exactly.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
open NamedLambda.Term (bindNames)
universe u v
variable {L : Language.{u,v}}

/-- Name comparison after entering matching blocks of existential quantifiers. -/
def bindBlock (R : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | 0, _, _ => R
  | n+1, B, C => bindBlock (bindNames R (B+n) (C+n)) n B C

theorem bindBlock_outside {R : ℕ → ℕ → Prop} (n B C a b : ℕ)
    (ha : a ∉ AlphaFormula.temporaryNames n B) (hb : b ∉ AlphaFormula.temporaryNames n C)
    (h : R a b) : bindBlock R n B C a b := by
  induction n generalizing R with
  | zero => exact h
  | succ n ih =>
    have ha' : a ≠ B+n ∧ a ∉ AlphaFormula.temporaryNames n B := by simpa using ha
    have hb' : b ≠ C+n ∧ b ∉ AlphaFormula.temporaryNames n C := by simpa using hb
    exact ih ha'.2 hb'.2 (Or.inr ⟨ha'.1,hb'.1,h⟩)

theorem bindBlock_below {R : ℕ → ℕ → Prop} (n B C a b : ℕ)
    (ha : a < B) (hb : b < C) (h : R a b) : bindBlock R n B C a b := by
  apply bindBlock_outside n B C a b _ _ h
  · rw [AlphaFormula.mem_temporaryNames_iff]; omega
  · rw [AlphaFormula.mem_temporaryNames_iff]; omega

theorem bindBlock_position (R : ℕ → ℕ → Prop) (n B C : ℕ) (i : Fin n) :
    bindBlock R n B C (B+i.val) (C+i.val) := by
  induction n generalizing R with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    by_cases hi : i.val < n
    · exact ih (bindNames R (B+n) (C+n)) ⟨i.val,hi⟩
    · have he : i.val = n := by have := i.isLt; omega
      rw [he]
      apply bindBlock_outside n B C (B+n) (C+n) _ _ (Or.inl ⟨rfl,rfl⟩)
      · rw [AlphaFormula.mem_temporaryNames_iff]; omega
      · rw [AlphaFormula.mem_temporaryNames_iff]; omega

namespace AlphaFormula.Corresponds

theorem conjoin {R : ℕ → ℕ → Prop} (n : ℕ) (φ ψ : Fin n → AlphaFormula L)
    (h : ∀ i, Corresponds R (φ i) (ψ i)) :
    Corresponds R (AlphaFormula.conjoin n φ) (AlphaFormula.conjoin n ψ) := by
  induction n with
  | zero => exact binary .imp (falsum R) (falsum R)
  | succ n ih => exact binary .conj (h 0) (ih _ _ (fun i => h i.succ))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Compare two terms under an arbitrary relation $R$ on names, with output names also related by $R$.
    Choose fresh starting indices $B,C$ on the two sides. At an application with $n$ arguments, pair the witnesses
    $v_{B+i}$ and $v_{C+i}$ for each $i<n$. Under their existential quantifiers, repeatedly update the name relation
    by the bound-name rule used in the comparison lemma. Each pair of witnesses then corresponds.
    A name outside the left block and a name outside the right block retain their original relation.
    The original term variables and output names are outside their respective blocks by freshness.
-/
theorem existsBlock {R : ℕ → ℕ → Prop} (n B C : ℕ) (φ ψ : AlphaFormula L)
    (h : Corresponds (bindBlock R n B C) φ ψ) :
    Corresponds R (AlphaFormula.existsBlock n B φ) (AlphaFormula.existsBlock n C ψ) := by
  induction n generalizing R with
  | zero => exact h
  | succ n ih => exact quant .ex (ih h)

end AlphaFormula.Corresponds
end PolishSpaceBook.NamedFirstOrder
