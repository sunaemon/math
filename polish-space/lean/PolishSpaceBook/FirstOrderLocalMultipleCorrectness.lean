module

public import PolishSpaceBook.FirstOrderLocalContextualTests

@[expose] public section

/-! # Two- and three-premise alternatives of the actual local checker -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
namespace LocalRulePrograms

theorem binary_parsed (s p q : P) (n : ℕ) (Γ Δ Θ : List FOL) (A B C : FOL)
    (hsΓ : parseContext (s.value n).unpair.1 = some Γ)
    (hpΔ : parseContext (p.value n).unpair.1 = some Δ)
    (hqΘ : parseContext (q.value n).unpair.1 = some Θ)
    (hsA : parseCode (s.value n).unpair.2 = some A)
    (hpB : parseCode (p.value n).unpair.2 = some B)
    (hqC : parseCode (q.value n).unpair.2 = some C) :
    (binary s p q).value n ≠ 0 ↔
      BinaryCases (ContextPrograms.context Γ) (AlphaFormula.mk A)
        (ContextPrograms.context Δ) (AlphaFormula.mk B) (ContextPrograms.context Θ) (AlphaFormula.mk C) := by
  classical
  have hA := FormulaRep.of_parse hsA
  have hB := FormulaRep.of_parse hpB
  have hC := FormulaRep.of_parse hqC
  have hctxP := (parseContext_equal hsΓ hpΔ).trans eq_comm
  have hctxQ := (parseContext_equal hsΓ hqΘ).trans eq_comm
  have hand := binary_match hA hB hC .conj
  have himp := binary_match hB hC hA .imp
  have heq := equality_elim_match hA hB hC
  have hex := existential_elim_match hsΓ hqΘ hB hA
  have hac := formulaRep_alpha_iff hA hC
  simp only [connectiveCode] at hand himp
  simp only [EigenvariablePrograms.exInput] at hex
  have hex' : (HasTag (p.value n).unpair.2 7 ∧
      (Term.decode (s.value n).unpair.2).Alpha (Term.decode (q.value n).unpair.2) ∧
      EigenvariablePrograms.exSearchValue (Nat.pair (s.value n).unpair.1
        (Nat.pair (q.value n).unpair.1 (Nat.pair (rawRight (p.value n).unpair.2)
          (Nat.pair (s.value n).unpair.2 (rawLeft (p.value n).unpair.2))))) ≠ 0) ↔
      AlphaFormula.mk A = AlphaFormula.mk C ∧
      ∃ (φ : AlphaFormula membershipLanguage) (x y : ℕ), AlphaFormula.mk B = AlphaFormula.quant .ex x φ ∧
        ContextPrograms.context Θ = insert (φ.subst x (.var y)) (ContextPrograms.context Γ) ∧
        y ∉ (ContextPrograms.context Γ).fv ∪ (AlphaFormula.mk A).fv ∪ (AlphaFormula.quant .ex x φ).fv := by
    rw [and_left_comm, hac, hex]
    apply and_congr_right
    intro _
    constructor <;> rintro ⟨φ, x, y, hφ, hΘ, hy⟩ <;>
      exact ⟨φ, x, y, hφ, hΘ, by simpa only [hφ] using hy⟩
  simp only [binary, Program.any_cons_ne_zero, Program.any_nil_ne_zero, or_false,
    Program.all_cons_ne_zero, Program.alpha_ne_zero, Program.tagIs_ne_zero,
    Program.left_value, Program.right_value, Program.sameContext, Program.contextEqual_ne_zero,
    Grammar.Program.first, Grammar.Program.second, Program.exSearch, Program.call,
    Grammar.Program.pair, Program.equalitySearch, Program.atomLeft, Program.atomRight, Program.payload]
  simp only [Program.all, List.foldr_nil, Grammar.Program.const, ne_eq, Nat.one_ne_zero,
    not_false_eq_true, and_true]
  have hraw := equality_rawProgram_value (p.value n).unpair.2 (s.value n).unpair.2
    (rawLeft (q.value n).unpair.2 / 3) (rawRight (q.value n).unpair.2 / 3)
  simp only [EqualityMatcher.rawInput] at hraw
  rw [hraw]
  have bit (b : Bool) : (if b then 1 else 0 : ℕ) ≠ 0 ↔ b = true := by cases b <;> decide
  simp only [ne_eq] at bit
  rw [bit]
  simp only [and_assoc, hctxP, hctxQ, hand, himp, hex', heq, BinaryCases]

theorem binary_iff (s p q : P) (n : ℕ) (S T U : Sequent membershipLanguage)
    (hs : parseSequent (s.value n) = some S) (hp : parseSequent (p.value n) = some T)
    (hq : parseSequent (q.value n) = some U) :
    (binary s p q).value n ≠ 0 ↔ LocalRule [T, U] S := by
  obtain ⟨Γ, A, hΓ, hA, rfl⟩ := (parseSequent_some_iff _ _).mp hs
  obtain ⟨Δ, B, hΔ, hB, rfl⟩ := (parseSequent_some_iff _ _).mp hp
  obtain ⟨Θ, C, hΘ, hC, rfl⟩ := (parseSequent_some_iff _ _).mp hq
  exact (binary_parsed s p q n Γ Δ Θ A B C hΓ hΔ hΘ hA hB hC).trans (localRule_binary_iff _ _ _ _ _ _).symm

theorem ternary_parsed (s p q r : P) (n : ℕ) (Γ Δ Θ Λ : List FOL) (A B C D : FOL)
    (hsΓ : parseContext (s.value n).unpair.1 = some Γ)
    (hpΔ : parseContext (p.value n).unpair.1 = some Δ)
    (hqΘ : parseContext (q.value n).unpair.1 = some Θ)
    (hrΛ : parseContext (r.value n).unpair.1 = some Λ)
    (hsA : parseCode (s.value n).unpair.2 = some A)
    (hpB : parseCode (p.value n).unpair.2 = some B)
    (hqC : parseCode (q.value n).unpair.2 = some C)
    (hrD : parseCode (r.value n).unpair.2 = some D) :
    (ternary s p q r).value n ≠ 0 ↔
      TernaryCases (ContextPrograms.context Γ) (AlphaFormula.mk A)
        (ContextPrograms.context Δ) (AlphaFormula.mk B) (ContextPrograms.context Θ) (AlphaFormula.mk C)
        (ContextPrograms.context Λ) (AlphaFormula.mk D) := by
  have hA := FormulaRep.of_parse hsA
  have hB := FormulaRep.of_parse hpB
  have hC := FormulaRep.of_parse hqC
  have hD := FormulaRep.of_parse hrD
  have hctx := (parseContext_equal hsΓ hpΔ).trans eq_comm
  have hAC := (formulaRep_alpha_iff hA hC).trans eq_comm
  have hAD := (formulaRep_alpha_iff hA hD).trans eq_comm
  have hor := disjunction_context_match hsΓ hqΘ hrΛ hB
  simp only [ternary, Program.all_cons_ne_zero, Program.alpha_ne_zero, Program.tagIs_ne_zero,
    Program.sameContext, Program.contextEqual_ne_zero, Program.conclusionEqual,
    Grammar.Program.first, Grammar.Program.second, Program.withHyp, TemplatePrograms.Program.cons,
    TemplatePrograms.Program.binary, Program.left_value, Program.right_value]
  simp only [Program.all, List.foldr_nil, Grammar.Program.const, ne_eq, Nat.one_ne_zero,
    not_false_eq_true, and_true]
  rw [hctx, hAC, hAD]
  unfold TernaryCases
  rw [← hor]
  tauto

theorem ternary_iff (s p q r : P) (n : ℕ) (S T U V : Sequent membershipLanguage)
    (hs : parseSequent (s.value n) = some S) (hp : parseSequent (p.value n) = some T)
    (hq : parseSequent (q.value n) = some U) (hr : parseSequent (r.value n) = some V) :
    (ternary s p q r).value n ≠ 0 ↔ LocalRule [T, U, V] S := by
  obtain ⟨Γ, A, hΓ, hA, rfl⟩ := (parseSequent_some_iff _ _).mp hs
  obtain ⟨Δ, B, hΔ, hB, rfl⟩ := (parseSequent_some_iff _ _).mp hp
  obtain ⟨Θ, C, hΘ, hC, rfl⟩ := (parseSequent_some_iff _ _).mp hq
  obtain ⟨Λ, D, hΛ, hD, rfl⟩ := (parseSequent_some_iff _ _).mp hr
  exact (ternary_parsed s p q r n Γ Δ Θ Λ A B C D hΓ hΔ hΘ hΛ hA hB hC hD).trans
    (localRule_ternary_iff _ _ _ _ _ _ _ _).symm

end LocalRulePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
