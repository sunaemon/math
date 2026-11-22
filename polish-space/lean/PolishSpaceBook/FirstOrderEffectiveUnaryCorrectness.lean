module

public import PolishSpaceBook.FirstOrderEffectiveRuleTests
public import PolishSpaceBook.FirstOrderLocalRuleCases

@[expose] public section

/-! # The actual unary rule checker over every effective signature -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open LocalRulePrograms (P)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem unary_represented (s p : P) (n : ℕ) (Γ Δ : Context L) (A B : AlphaFormula L)
    (hsΓ : S.ContextRep (s.value n).unpair.1 Γ) (hpΔ : S.ContextRep (p.value n).unpair.1 Δ)
    (hsA : S.FormulaRep (s.value n).unpair.2 A) (hpB : S.FormulaRep (p.value n).unpair.2 B) :
    (unary S s p).value n ≠ 0 ↔ UnaryCases Γ A Δ B := by
  have hctx := (S.contextRep_equal hsΓ hpΔ).trans eq_comm
  have handL := S.binary_left_match hsA hpB .conj
  have handR := S.binary_right_match hsA hpB .conj
  have horL := S.binary_left_match hpB hsA .disj
  have horR := S.binary_right_match hpB hsA .disj
  have himp := S.implication_intro_match hsΓ hpΔ hsA hpB
  have hf : S.FormulaRep (node 0 (tag 0)).code AlphaFormula.falsum := S.formulaRep_encode .falsum
  have hfalse := S.formulaRep_alpha_iff hpB hf
  have hallI := S.allSearch_iff hsΓ hpB hsA
  have hallE := S.quantifier_instance_match hpB hsA .all
  have hexI := S.quantifier_instance_match hsA hpB .ex
  simp only [connectiveCode] at handL handR horL horR
  simp only [EigenvariablePrograms.allInput] at hallI
  simp only [quantifierCode, InstancePrograms.input] at hallE hexI
  simp only [Term.decode_code] at hfalse
  simp only [unary, LocalRulePrograms.Program.any_cons_ne_zero, LocalRulePrograms.Program.any_nil_ne_zero, or_false,
    LocalRulePrograms.Program.all_cons_ne_zero, LocalRulePrograms.Program.alpha_ne_zero,
    LocalRulePrograms.Program.tagIs_ne_zero, LocalRulePrograms.Program.left_value, LocalRulePrograms.Program.right_value,
    LocalRulePrograms.Program.sameContext, LocalRulePrograms.Program.contextEqual_ne_zero,
    Grammar.Program.first, Grammar.Program.second,
    LocalRulePrograms.Program.withHyp, TemplatePrograms.Program.cons, TemplatePrograms.Program.binary,
    Grammar.Program.const, Term.decode_code, LocalRulePrograms.Program.allSearch,
    instanceSearch, run, InstancePrograms.searchProgram, LocalRulePrograms.Program.call, Grammar.Program.pair]
  simp only [LocalRulePrograms.Program.all, List.foldr_nil, Grammar.Program.const, ne_eq,
    Nat.one_ne_zero, not_false_eq_true, and_true]
  simp only [hctx, handL, handR, horL, horR, himp, hfalse, hallI, hallE, hexI, UnaryCases]

theorem unary_iff (s p : P) (n : ℕ) (T U : Sequent L)
    (hs : S.SequentRep (s.value n) T) (hp : S.SequentRep (p.value n) U) :
    (unary S s p).value n ≠ 0 ↔ LocalRule [U] T := by
  rcases T with ⟨Γ,A⟩
  rcases U with ⟨Δ,B⟩
  exact (unary_represented S s p n Γ Δ A B hs.1 hp.1 hs.2 hp.2).trans (localRule_unary_iff _ _ _ _).symm

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
