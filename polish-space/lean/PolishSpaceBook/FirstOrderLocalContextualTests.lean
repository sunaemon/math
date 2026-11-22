module

public import PolishSpaceBook.FirstOrderLocalRuleFormulaTests

@[expose] public section

/-! # Context-changing and equality branches of the numerical local checker -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
namespace LocalRulePrograms
noncomputable local instance contextClassDecidableEq : DecidableEq (AlphaFormula membershipLanguage) := Classical.decEq _
noncomputable local instance syntaxClassDecidableEq : DecidableEq NamedLambda.AlphaTerm := Classical.decEq _

theorem context_insert_match {e d a : ℕ} {Γ Δ : List FOL} {A : AlphaFormula membershipLanguage}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ) (ha : FormulaRep a A) :
    ContextPrograms.equalBit d (Nat.pair a e + 1) = true ↔
      ContextPrograms.context Δ = insert A (ContextPrograms.context Γ) := by
  obtain ⟨φ, hφ, rfl⟩ := ha
  have hi : parseContext (Nat.pair a e + 1) = some (φ :: Γ) := by
    simp [parseContext_cons, hφ, he]
  simpa only [ContextPrograms.context_cons] using parseContext_equal hd hi

theorem implication_intro_match {e d a b : ℕ} {Γ Δ : List FOL} {A B : AlphaFormula membershipLanguage}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ)
    (ha : FormulaRep a A) (hb : FormulaRep b B) :
    (HasTag a 5 ∧ (Term.decode b).Alpha (Term.decode (rawRight a)) ∧
      ContextPrograms.equalBit d (Nat.pair (rawLeft a) e + 1) = true) ↔
      ∃ C, A = AlphaFormula.binary .imp C B ∧
        ContextPrograms.context Δ = insert C (ContextPrograms.context Γ) := by
  constructor
  · rintro ⟨ht, hr, hc⟩
    obtain ⟨C, D, hC, hD, hA⟩ := formulaRep_binary_of_tag ha .imp ht
    have hBD := (formulaRep_alpha_iff hb hD).mp hr
    exact ⟨C, hBD ▸ hA, (context_insert_match he hd hC).mp hc⟩
  · rintro ⟨C, hA, hΔ⟩
    obtain ⟨ht, hC, hB⟩ := formulaRep_binary_fields ha .imp hA
    exact ⟨ht, (formulaRep_alpha_iff hb hB).mpr rfl, (context_insert_match he hd hC).mpr hΔ⟩

theorem disjunction_context_match {e d f a : ℕ} {Γ Δ Θ : List FOL} {A : AlphaFormula membershipLanguage}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ) (hf : parseContext f = some Θ)
    (ha : FormulaRep a A) :
    (HasTag a 4 ∧ ContextPrograms.equalBit d (Nat.pair (rawLeft a) e + 1) = true ∧
      ContextPrograms.equalBit f (Nat.pair (rawRight a) e + 1) = true) ↔
      ∃ B C, A = AlphaFormula.binary .disj B C ∧
        ContextPrograms.context Δ = insert B (ContextPrograms.context Γ) ∧
        ContextPrograms.context Θ = insert C (ContextPrograms.context Γ) := by
  constructor
  · rintro ⟨ht, hΔ, hΘ⟩
    obtain ⟨B, C, hB, hC, hA⟩ := formulaRep_binary_of_tag ha .disj ht
    exact ⟨B, C, hA, (context_insert_match he hd hB).mp hΔ, (context_insert_match he hf hC).mp hΘ⟩
  · rintro ⟨B, C, hA, hΔ, hΘ⟩
    obtain ⟨ht, hB, hC⟩ := formulaRep_binary_fields ha .disj hA
    exact ⟨ht, (context_insert_match he hd hB).mpr hΔ, (context_insert_match he hf hC).mpr hΘ⟩

theorem existential_elim_match {e d a b : ℕ} {Γ Δ : List FOL} {A B : AlphaFormula membershipLanguage}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ)
    (ha : FormulaRep a A) (hb : FormulaRep b B) :
    (HasTag a 7 ∧ EigenvariablePrograms.exSearchValue
      (EigenvariablePrograms.exInput e d (rawRight a) b (rawLeft a)) ≠ 0) ↔
      ∃ (φ : AlphaFormula membershipLanguage) (x y : ℕ),
        A = AlphaFormula.quant .ex x φ ∧
        ContextPrograms.context Δ = insert (φ.subst x (.var y)) (ContextPrograms.context Γ) ∧
        y ∉ (ContextPrograms.context Γ).fv ∪ B.fv ∪ A.fv := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨x, φ, rfl⟩ := (formulaTag_quant_iff α .ex).mp ((parsed_tag_iff hα _).mp ht)
    obtain ⟨hx, hφ⟩ := parsed_quant_fields hα
    rw [hx, raw_exSearch_iff he hd hφ hβ] at hi
    obtain ⟨y, hctx, hfree⟩ := hi
    exact ⟨AlphaFormula.mk φ, x, y, rfl, hctx, hfree⟩
  · rintro ⟨φ, x, y, heq, hctx, hfree⟩
    obtain ⟨z, ψ, rfl, hi⟩ := AlphaFormula.mk_quant_view heq
    obtain ⟨hz, hψ⟩ := parsed_quant_fields hα
    refine ⟨(parsed_tag_iff hα _).mpr rfl, ?_⟩
    rw [hz, raw_exSearch_iff he hd hψ hβ]
    refine ⟨y, ?_, hfree⟩
    change ContextPrograms.context Δ = insert (AlphaFormula.mk (ψ.subst z (.var y))) _
    rw [hi]
    exact hctx

theorem equality_elim_match {a b c : ℕ} {A B C : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (hb : FormulaRep b B) (hc : FormulaRep c C) :
    (HasTag c 1 ∧ EqualityMatcher.rawCheck b a (rawLeft c / 3) (rawRight c / 3) = true) ↔
      ∃ (φ : AlphaFormula membershipLanguage) (x : ℕ) (t r : membershipLanguage.Term ℕ),
        B = φ.subst x t ∧ A = φ.subst x r ∧ C = AlphaFormula.equal t r := by
  obtain ⟨γ, hγ, rfl⟩ := hc
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨t, r, rfl⟩ := (formulaTag_equal_iff γ).mp ((parsed_tag_iff hγ _).mp ht)
    obtain ⟨hl, hr⟩ := parsed_equal_fields hγ
    simp only [hl, hr, Term.code, Nat.mul_div_cancel_left _ (by decide : 0 < 3)] at hi
    obtain ⟨φ, x, hB, hA⟩ := (raw_equality_class_iff hb ha _ _).mp hi
    exact ⟨φ, x, .var (termName t), .var (termName r), hB, hA, by simp only [term_var_name]; rfl⟩
  · rintro ⟨φ, x, t, r, hB, hA, hC⟩
    have hγeq := AlphaFormula.mk_equal_view hC
    subst γ
    obtain ⟨hl, hr⟩ := parsed_equal_fields hγ
    refine ⟨(parsed_tag_iff hγ _).mpr rfl, ?_⟩
    simp only [hl, hr, Term.code, Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
    apply (raw_equality_class_iff hb ha _ _).mpr
    exact ⟨φ, x, by simpa only [term_var_name] using hB, by simpa only [term_var_name] using hA⟩

theorem equality_rawProgram_value (a b t r : ℕ) :
    EqualityMatcher.rawProgram.value (EqualityMatcher.rawInput a b t r) =
      if EqualityMatcher.rawCheck a b t r then 1 else 0 := by
  simp only [EqualityMatcher.rawProgram, EqualityMatcher.bindingProgram, EqualityMatcher.checkProgram,
    TemplatePrograms.Program.binary, Grammar.Program.pair, Grammar.Program.first, Grammar.Program.second,
    Grammar.Program.ident, id_eq, EqualityMatcher.rawInput, EqualityMatcher.rawCheck,
    EqualityMatcher.check, Nat.unpair_pair, NatListCode.decode_encode]
  rfl

end LocalRulePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
