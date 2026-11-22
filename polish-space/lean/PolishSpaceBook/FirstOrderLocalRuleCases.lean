module

public import PolishSpaceBook.FirstOrderUnannotatedTrees

@[expose] public section

/-! # Arity decomposition of the original local inference relation -/
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
noncomputable local instance localCaseDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _

def NullaryCases (Γ : Context L) (a : AlphaFormula L) : Prop :=
  a ∈ Γ ∨ (∃ t, a = equal t t) ∨ ∃ φ, a = binary .disj φ (neg φ)

def UnaryCases (Γ : Context L) (a : AlphaFormula L) (Δ : Context L) (b : AlphaFormula L) : Prop :=
  (Δ = Γ ∧ ∃ ψ, b = binary .conj a ψ) ∨
  (Δ = Γ ∧ ∃ φ, b = binary .conj φ a) ∨
  (Δ = Γ ∧ ∃ ψ, a = binary .disj b ψ) ∨
  (Δ = Γ ∧ ∃ φ, a = binary .disj φ b) ∨
  (∃ φ, a = binary .imp φ b ∧ Δ = insert φ Γ) ∨
  (Δ = Γ ∧ b = falsum) ∨
  (Δ = Γ ∧ ∃ x, a = quant .all x b ∧ x ∉ Γ.fv) ∨
  (Δ = Γ ∧ ∃ φ x t, b = quant .all x φ ∧ a = φ.subst x t) ∨
  (Δ = Γ ∧ ∃ φ x t, a = quant .ex x φ ∧ b = φ.subst x t)

def BinaryCases (Γ : Context L) (a : AlphaFormula L) (Δ : Context L) (b : AlphaFormula L)
    (Θ : Context L) (c : AlphaFormula L) : Prop :=
  (Δ = Γ ∧ Θ = Γ ∧ a = binary .conj b c) ∨
  (Δ = Γ ∧ Θ = Γ ∧ b = binary .imp c a) ∨
  (Δ = Γ ∧ a = c ∧ ∃ φ x y, b = quant .ex x φ ∧ Θ = insert (φ.subst x (.var y)) Γ ∧
    y ∉ Γ.fv ∪ a.fv ∪ (quant .ex x φ).fv) ∨
  (Δ = Γ ∧ Θ = Γ ∧ ∃ (φ : AlphaFormula L) (x : ℕ) (t r : L.Term ℕ),
    b = φ.subst x t ∧ a = φ.subst x r ∧ c = equal t r)

def TernaryCases (Γ : Context L) (a : AlphaFormula L) (Δ : Context L) (b : AlphaFormula L)
    (Θ : Context L) (c : AlphaFormula L) (Λ : Context L) (d : AlphaFormula L) : Prop :=
  Δ = Γ ∧ c = a ∧ d = a ∧ ∃ φ ψ, b = binary .disj φ ψ ∧ Θ = insert φ Γ ∧ Λ = insert ψ Γ

theorem localRule_nullary_iff (Γ : Context L) (a : AlphaFormula L) :
    LocalRule [] (Γ, a) ↔ NullaryCases Γ a := by
  constructor
  · intro h; cases h <;> simp [NullaryCases] <;> aesop
  · rintro (h | ⟨t, rfl⟩ | ⟨φ, rfl⟩)
    · exact .hyp _ _ h
    · exact .eqIntro _ _
    · exact .excludedMiddle _ _

theorem localRule_unary_iff (Γ : Context L) (a : AlphaFormula L) (Δ : Context L) (b : AlphaFormula L) :
    LocalRule [(Δ, b)] (Γ, a) ↔ UnaryCases Γ a Δ b := by
  constructor
  · intro h; cases h <;> simp [UnaryCases] <;> aesop
  · intro h
    rcases h with ⟨rfl, ψ, rfl⟩ | ⟨rfl, φ, rfl⟩ | ⟨rfl, ψ, rfl⟩ | ⟨rfl, φ, rfl⟩ |
      ⟨φ, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, x, rfl, hx⟩ |
      ⟨rfl, φ, x, t, rfl, rfl⟩ | ⟨rfl, φ, x, t, rfl, rfl⟩
    · exact .andLeft _ _ _
    · exact .andRight _ _ _
    · exact .orLeft _ _ _
    · exact .orRight _ _ _
    · exact .impIntro _ _ _
    · exact .falseElim _ _
    · exact .allIntro _ _ _ hx
    · exact .allElim _ _ _ _
    · exact .exIntro _ _ _ _

theorem localRule_binary_iff (Γ : Context L) (a : AlphaFormula L) (Δ : Context L) (b : AlphaFormula L)
    (Θ : Context L) (c : AlphaFormula L) :
    LocalRule [(Δ, b), (Θ, c)] (Γ, a) ↔ BinaryCases Γ a Δ b Θ c := by
  constructor
  · intro h; cases h <;> simp [BinaryCases] <;> aesop
  · intro h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, φ, x, y, rfl, rfl, hy⟩ | ⟨rfl, rfl, φ, x, t, r, rfl, rfl, rfl⟩
    · exact .andIntro _ _ _
    · exact .impElim _ _ _
    · exact .exElim _ _ _ _ _ hy
    · exact .eqElim _ _ _ _ _

theorem localRule_ternary_iff (Γ : Context L) (a : AlphaFormula L) (Δ : Context L) (b : AlphaFormula L)
    (Θ : Context L) (c : AlphaFormula L) (Λ : Context L) (d : AlphaFormula L) :
    LocalRule [(Δ, b), (Θ, c), (Λ, d)] (Γ, a) ↔ TernaryCases Γ a Δ b Θ c Λ d := by
  constructor
  · intro h; cases h; simp [TernaryCases]; aesop
  · rintro ⟨rfl, rfl, rfl, φ, ψ, rfl, rfl, rfl⟩
    exact .orElim _ _ _ _

theorem LocalRule.length_le_three {ps : List (Sequent L)} {s : Sequent L} (h : LocalRule ps s) :
    ps.length ≤ 3 := by cases h <;> simp

end PolishSpaceBook.NamedFirstOrder
