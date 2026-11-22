module

public import PolishSpaceBook.FirstOrderLocalContextualTests

@[expose] public section

/-! # The nine one-premise numerical alternatives are the original local rules -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
namespace LocalRulePrograms

theorem unary_parsed (s p : P) (n : ℕ) (Γ Δ : List FOL) (A B : FOL)
    (hsΓ : parseContext (s.value n).unpair.1 = some Γ)
    (hpΔ : parseContext (p.value n).unpair.1 = some Δ)
    (hsA : parseCode (s.value n).unpair.2 = some A)
    (hpB : parseCode (p.value n).unpair.2 = some B) :
    (unary s p).value n ≠ 0 ↔
      UnaryCases (ContextPrograms.context Γ) (AlphaFormula.mk A)
        (ContextPrograms.context Δ) (AlphaFormula.mk B) := by
  have hA := FormulaRep.of_parse hsA
  have hB := FormulaRep.of_parse hpB
  have hctx := (parseContext_equal hsΓ hpΔ).trans eq_comm
  have handL := binary_left_match hA hB .conj
  have handR := binary_right_match hA hB .conj
  have horL := binary_left_match hB hA .disj
  have horR := binary_right_match hB hA .disj
  have himp := implication_intro_match hsΓ hpΔ hA hB
  have hfalse := formulaRep_alpha_iff hB formulaRep_falsum
  have hallI := raw_allIntro_class_iff hsΓ hB hA
  have hallE := raw_quantifier_instance_class_iff hB hA .all
  have hexI := raw_quantifier_instance_class_iff hA hB .ex
  simp only [connectiveCode] at handL handR horL horR
  simp only [EigenvariablePrograms.allInput] at hallI
  simp only [quantifierCode, InstancePrograms.input] at hallE hexI
  simp only [Term.decode_code] at hfalse
  simp only [unary, Program.any_cons_ne_zero, Program.any_nil_ne_zero, or_false,
    Program.all_cons_ne_zero, Program.alpha_ne_zero,
    Program.tagIs_ne_zero, Program.left_value, Program.right_value,
    Program.sameContext, Program.contextEqual_ne_zero, Grammar.Program.first, Grammar.Program.second,
    Program.withHyp, TemplatePrograms.Program.cons, TemplatePrograms.Program.binary, Grammar.Program.const, Term.decode_code,
    Program.allSearch, Program.instanceSearch, Program.call, Grammar.Program.pair]
  simp only [Program.all, List.foldr_nil, Grammar.Program.const, ne_eq, Nat.one_ne_zero, not_false_eq_true, and_true]
  simp only [hctx,
    handL, handR, horL, horR, himp, hfalse, hallI, hallE, hexI, UnaryCases]

theorem unary_iff (s p : P) (n : ℕ) (S T : Sequent membershipLanguage)
    (hs : parseSequent (s.value n) = some S) (hp : parseSequent (p.value n) = some T) :
    (unary s p).value n ≠ 0 ↔ LocalRule [T] S := by
  obtain ⟨Γ, A, hΓ, hA, rfl⟩ := (parseSequent_some_iff _ _).mp hs
  obtain ⟨Δ, B, hΔ, hB, rfl⟩ := (parseSequent_some_iff _ _).mp hp
  exact (unary_parsed s p n Γ Δ A B hΓ hΔ hA hB).trans (localRule_unary_iff _ _ _ _).symm

end LocalRulePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
