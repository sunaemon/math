module

public import PolishSpaceBook.FirstOrderEffectiveFormulaViews
public import PolishSpaceBook.FirstOrderEffectiveContextGrammar
public import PolishSpaceBook.FirstOrderLocalNullaryCorrectness

@[expose] public section

/-! # The zero-premise rules over every effective signature -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open FirstOrderLambdaEncoding.LocalRulePrograms (P HasTag rawLeft rawRight)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option backward.isDefEq.respectTransparency.types false

theorem falsum_rep : S.FormulaRep (encode (.falsum : FOL)).code (AlphaFormula.falsum : AlphaFormula L) := by
  apply (S.formulaRep_mk_iff _ .falsum).mpr
  rw [Term.decode_code]
  exact .refl _

theorem reflexive_match {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A) :
    (HasTag a 1 ∧ (Term.decode (rawLeft a)).Alpha (Term.decode (rawRight a))) ↔
      ∃ t, A = AlphaFormula.equal t t := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨t, r, hlt, hrt, hA⟩ := S.formulaRep_equal_of_tag ha ht
    have htr := (S.encodeTerm_alpha_iff t r).mp (hlt.symm.trans (he.trans hrt))
    subst r
    exact ⟨t, hA⟩
  · rintro ⟨t, hA⟩
    obtain ⟨ht, hlt, hrt⟩ := S.formulaRep_equal_fields ha hA
    exact ⟨ht, hlt.trans hrt.symm⟩

theorem excludedMiddle_match {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A) :
    (HasTag a 4 ∧ HasTag (rawRight a) 5 ∧
      (Term.decode (rawLeft a)).Alpha (Term.decode (rawLeft (rawRight a))) ∧
      (Term.decode (rawRight (rawRight a))).Alpha (encode (.falsum : FOL))) ↔
      ∃ B, A = AlphaFormula.binary .disj B (AlphaFormula.neg B) := by
  constructor
  · rintro ⟨ht, htr, hl, hr⟩
    obtain ⟨B, C, hB, hC, hA⟩ := S.formulaRep_binary_of_tag ha .disj ht
    obtain ⟨D, E, hD, hE, hCeq⟩ := S.formulaRep_binary_of_tag hC .imp htr
    have hBD := (S.formulaRep_alpha_iff hB hD).mp hl
    have hEf : E = AlphaFormula.falsum :=
      (S.formulaRep_alpha_iff hE (falsum_rep S)).mp (by simpa using hr)
    exact ⟨B, by simpa only [hCeq, ← hBD, hEf, AlphaFormula.neg] using hA⟩
  · rintro ⟨B, hA⟩
    obtain ⟨ht, hB, hC⟩ := S.formulaRep_binary_fields ha .disj hA
    obtain ⟨htr, hB', hF⟩ := S.formulaRep_binary_fields hC .imp rfl
    refine ⟨ht, htr, (S.formulaRep_alpha_iff hB hB').mpr rfl, ?_⟩
    simpa using (S.formulaRep_alpha_iff hF (falsum_rep S)).mpr rfl

theorem nullary_iff (s : P) (n : ℕ) (s₀ : Sequent L)
    (hs : S.SequentRep (s.value n) s₀) :
    (LocalRulePrograms.nullary s).value n ≠ 0 ↔ LocalRule [] s₀ := by
  rcases s₀ with ⟨Γ, A⟩
  obtain ⟨hΓ, hA⟩ := hs
  rw [localRule_nullary_iff]
  simp only [LocalRulePrograms.nullary, LocalRulePrograms.Program.any_cons_ne_zero,
    LocalRulePrograms.Program.any_nil_ne_zero, or_false, LocalRulePrograms.Program.all_cons_ne_zero,
    LocalRulePrograms.Program.tagIs_ne_zero, LocalRulePrograms.Program.alpha_ne_zero,
    LocalRulePrograms.Program.left_value, LocalRulePrograms.Program.right_value,
    Grammar.Program.second, Grammar.Program.first, Grammar.Program.const, Term.decode_code]
  simp only [LocalRulePrograms.Program.all, List.foldr_nil, Grammar.Program.const, ne_eq,
    Nat.one_ne_zero, not_false_eq_true, and_true]
  change ((if ContextPrograms.member (s.value n).unpair.2 (s.value n).unpair.1 then 1 else 0 : ℕ) ≠ 0 ∨
    (HasTag _ 1 ∧ _) ∨ (HasTag _ 4 ∧ _)) ↔ NullaryCases _ _
  have hb (b : Bool) : (if b then 1 else 0 : ℕ) ≠ 0 ↔ b = true := by cases b <;> decide
  rw [hb, S.contextRep_member hA hΓ, reflexive_match S hA, excludedMiddle_match S hA]
  rfl

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
