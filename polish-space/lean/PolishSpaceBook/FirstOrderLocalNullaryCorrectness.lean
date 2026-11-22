module

public import PolishSpaceBook.FirstOrderLocalRuleFormulaTests

@[expose] public section

/-! # Correctness of the three zero-premise alternatives -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.LocalRulePrograms
open FirstOrder Language NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
set_option backward.isDefEq.respectTransparency.types false

theorem reflexive_match {a : ℕ} {A : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) :
    (HasTag a 1 ∧ (Term.decode (rawLeft a)).Alpha (Term.decode (rawRight a))) ↔
      ∃ t, A = AlphaFormula.equal t t := by
  obtain ⟨φ, hφ, rfl⟩ := ha
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨s, t, rfl⟩ := (formulaTag_equal_iff φ).mp ((parsed_tag_iff hφ 1).mp ht)
    obtain ⟨hl, hr⟩ := parsed_equal_fields hφ
    rw [hl, hr, Term.decode_code, Term.decode_code, Term.alpha_iff_bindingTree] at he
    have hn : termName s = termName t := by simpa [Term.bindingTree] using he
    have hst : s = t := by rw [← term_var_name s, ← term_var_name t, hn]
    subst t
    exact ⟨s, rfl⟩
  · rintro ⟨t, he⟩
    have hshape := AlphaFormula.mk_equal_view he
    subst φ
    obtain ⟨hl, hr⟩ := parsed_equal_fields hφ
    exact ⟨(parsed_tag_iff hφ 1).mpr rfl, by rw [hl, hr]; exact .refl _⟩

theorem excludedMiddle_match {a : ℕ} {A : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) :
    (HasTag a 4 ∧ HasTag (rawRight a) 5 ∧
      (Term.decode (rawLeft a)).Alpha (Term.decode (rawLeft (rawRight a))) ∧
      (Term.decode (rawRight (rawRight a))).Alpha (encode (.falsum : FOL))) ↔
      ∃ B, A = AlphaFormula.binary .disj B (AlphaFormula.neg B) := by
  constructor
  · rintro ⟨ht, htr, hl, hr⟩
    obtain ⟨B, C, hB, hC, hA⟩ := formulaRep_binary_of_tag ha .disj ht
    obtain ⟨D, E, hD, hE, hCeq⟩ := formulaRep_binary_of_tag hC .imp htr
    have hBD := (formulaRep_alpha_iff hB hD).mp hl
    have hEf : E = AlphaFormula.falsum :=
      (formulaRep_alpha_iff hE formulaRep_falsum).mp (by simpa using hr)
    exact ⟨B, by simpa only [hCeq, ← hBD, hEf, AlphaFormula.neg] using hA⟩
  · rintro ⟨B, hA⟩
    obtain ⟨ht, hB, hC⟩ := formulaRep_binary_fields ha .disj hA
    obtain ⟨htr, hB', hF⟩ := formulaRep_binary_fields hC .imp rfl
    refine ⟨ht, htr, (formulaRep_alpha_iff hB hB').mpr rfl, ?_⟩
    simpa using (formulaRep_alpha_iff hF formulaRep_falsum).mpr rfl

theorem nullary_ne_zero_iff (s : P) (n : ℕ) {S : Sequent membershipLanguage}
    (hs : parseSequent (s.value n) = some S) :
    (nullary s).value n ≠ 0 ↔ LocalRule [] S := by
  obtain ⟨Γ, φ, hΓ, hφ, rfl⟩ := (parseSequent_some_iff _ _).mp hs
  have hrep := FormulaRep.of_parse hφ
  rw [localRule_nullary_iff]
  simp only [nullary, Program.any_cons_ne_zero, Program.any_nil_ne_zero, or_false,
    Program.all_cons_ne_zero,
    Program.tagIs_ne_zero, Program.alpha_ne_zero, Program.left_value, Program.right_value,
    Grammar.Program.second, Grammar.Program.first, Grammar.Program.const, Term.decode_code]
  simp only [Program.all, List.foldr_nil, Grammar.Program.const, ne_eq, Nat.one_ne_zero,
    not_false_eq_true, and_true]
  change ((if ContextPrograms.member (s.value n).unpair.2 (s.value n).unpair.1 then 1 else 0 : ℕ) ≠ 0 ∨
    (HasTag _ 1 ∧ _) ∨ (HasTag _ 4 ∧ _)) ↔ NullaryCases _ _
  have hb (b : Bool) : (if b then 1 else 0 : ℕ) ≠ 0 ↔ b = true := by cases b <;> decide
  rw [hb, formulaRep_context_member hrep hΓ, reflexive_match hrep, excludedMiddle_match hrep]
  rfl

end PolishSpaceBook.FirstOrderLambdaEncoding.LocalRulePrograms
