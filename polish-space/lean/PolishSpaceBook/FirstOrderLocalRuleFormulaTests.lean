module

public import PolishSpaceBook.FirstOrderLocalRuleNormalization
public import PolishSpaceBook.FirstOrderAlphaConstructorViews

@[expose] public section

/-! # Formula-class meaning of the concrete local tests -/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage)
namespace LocalRulePrograms

def FormulaRep (a : ℕ) (A : AlphaFormula membershipLanguage) : Prop :=
  ∃ φ, parseCode a = some φ ∧ AlphaFormula.mk φ = A

theorem FormulaRep.of_parse {a : ℕ} {φ : FOL} (ha : parseCode a = some φ) : FormulaRep a (AlphaFormula.mk φ) :=
  ⟨φ, ha, rfl⟩

theorem FormulaRep.unique {a : ℕ} {A B : AlphaFormula membershipLanguage}
    (hA : FormulaRep a A) (hB : FormulaRep a B) : A = B := by
  obtain ⟨φ, hφ, rfl⟩ := hA
  obtain ⟨ψ, hψ, rfl⟩ := hB
  have := Option.some.inj (hφ.symm.trans hψ)
  exact congrArg AlphaFormula.mk this

theorem formulaRep_alpha_iff {a b : ℕ} {A B : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (hb : FormulaRep b B) :
    (Term.decode a).Alpha (Term.decode b) ↔ A = B := by
  obtain ⟨φ, hφ, rfl⟩ := ha
  obtain ⟨ψ, hψ, rfl⟩ := hb
  exact parseCode_alpha_iff hφ hψ

theorem formulaRep_falsum : FormulaRep (encode (.falsum : FOL)).code AlphaFormula.falsum :=
  .of_parse (parseCode_encode _)

theorem formulaRep_context_member {a e : ℕ} {A : AlphaFormula membershipLanguage} {Γ : List FOL}
    (ha : FormulaRep a A) (he : parseContext e = some Γ) :
    ContextPrograms.member a e = true ↔ A ∈ ContextPrograms.context Γ := by
  obtain ⟨φ, hφ, rfl⟩ := ha
  exact parseContext_member hφ he

theorem formulaRep_binary_fields {a : ℕ} {A B C : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (c : Connective) (hA : A = AlphaFormula.binary c B C) :
    HasTag a (connectiveCode c) ∧ FormulaRep (rawLeft a) B ∧ FormulaRep (rawRight a) C := by
  obtain ⟨φ, hφ, rfl⟩ := ha
  obtain ⟨ψ, χ, rfl, rfl, rfl⟩ := AlphaFormula.mk_binary_view hA
  have hp := parsed_binary_fields hφ
  exact ⟨(parsed_tag_iff hφ _).mpr rfl, .of_parse hp.1, .of_parse hp.2⟩

theorem formulaRep_binary_of_tag {a : ℕ} {A : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (c : Connective) (ht : HasTag a (connectiveCode c)) :
    ∃ B C, FormulaRep (rawLeft a) B ∧ FormulaRep (rawRight a) C ∧ A = AlphaFormula.binary c B C := by
  obtain ⟨φ, hφ, rfl⟩ := ha
  obtain ⟨ψ, χ, rfl⟩ := (formulaTag_binary_iff φ c).mp ((parsed_tag_iff hφ _).mp ht)
  have hp := parsed_binary_fields hφ
  exact ⟨_, _, .of_parse hp.1, .of_parse hp.2, rfl⟩

theorem binary_left_match {a b : ℕ} {A B : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (hb : FormulaRep b B) (c : Connective) :
    (HasTag b (connectiveCode c) ∧ (Term.decode a).Alpha (Term.decode (rawLeft b))) ↔
      ∃ C, B = AlphaFormula.binary c A C := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨C, D, hC, _, hB⟩ := formulaRep_binary_of_tag hb c ht
    have hAC := (formulaRep_alpha_iff ha hC).mp he
    exact ⟨D, hAC ▸ hB⟩
  · rintro ⟨C, hB⟩
    obtain ⟨ht, hA, _⟩ := formulaRep_binary_fields hb c hB
    exact ⟨ht, (formulaRep_alpha_iff ha hA).mpr rfl⟩

theorem binary_right_match {a b : ℕ} {A B : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (hb : FormulaRep b B) (c : Connective) :
    (HasTag b (connectiveCode c) ∧ (Term.decode a).Alpha (Term.decode (rawRight b))) ↔
      ∃ C, B = AlphaFormula.binary c C A := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨C, D, _, hD, hB⟩ := formulaRep_binary_of_tag hb c ht
    have hAD := (formulaRep_alpha_iff ha hD).mp he
    exact ⟨C, hAD ▸ hB⟩
  · rintro ⟨C, hB⟩
    obtain ⟨ht, _, hA⟩ := formulaRep_binary_fields hb c hB
    exact ⟨ht, (formulaRep_alpha_iff ha hA).mpr rfl⟩

theorem binary_match {a b d : ℕ} {A B D : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (hb : FormulaRep b B) (hd : FormulaRep d D) (c : Connective) :
    (HasTag a (connectiveCode c) ∧ (Term.decode b).Alpha (Term.decode (rawLeft a)) ∧
      (Term.decode d).Alpha (Term.decode (rawRight a))) ↔ A = AlphaFormula.binary c B D := by
  constructor
  · rintro ⟨ht, hleft, hright⟩
    obtain ⟨C, E, hC, hE, hA⟩ := formulaRep_binary_of_tag ha c ht
    have hBC := (formulaRep_alpha_iff hb hC).mp hleft
    have hDE := (formulaRep_alpha_iff hd hE).mp hright
    exact hBC ▸ hDE ▸ hA
  · intro hA
    obtain ⟨ht, hB, hD⟩ := formulaRep_binary_fields ha c hA
    exact ⟨ht, (formulaRep_alpha_iff hb hB).mpr rfl, (formulaRep_alpha_iff hd hD).mpr rfl⟩

theorem raw_quantifier_instance_class_iff {a b : ℕ} {A B : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (hb : FormulaRep b B) (q : Quantifier) :
    (HasTag a (quantifierCode q) ∧
      InstancePrograms.searchValue (InstancePrograms.input (rawRight a) (rawLeft a) b) ≠ 0) ↔
      ∃ (φ : AlphaFormula membershipLanguage) (x : ℕ) (t : membershipLanguage.Term ℕ),
        A = AlphaFormula.quant q x φ ∧ B = φ.subst x t := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨x, φ, rfl⟩ := (formulaTag_quant_iff α q).mp ((parsed_tag_iff hα _).mp ht)
    obtain ⟨hx, hφ⟩ := parsed_quant_fields hα
    rw [hx, raw_instanceSearch_iff hφ hβ] at hi
    obtain ⟨t, ht⟩ := hi
    exact ⟨AlphaFormula.mk φ, x, .var t, rfl, (AlphaFormula.mk_eq_iff _ _).mpr ht.symm⟩
  · rintro ⟨φ, x, t, heq, hβeq⟩
    obtain ⟨y, ψ, rfl, hi⟩ := AlphaFormula.mk_quant_view heq
    obtain ⟨hy, hψ⟩ := parsed_quant_fields hα
    refine ⟨(parsed_tag_iff hα _).mpr rfl, ?_⟩
    rw [hy, raw_instanceSearch_iff hψ hβ]
    refine ⟨termName t, ?_⟩
    rw [term_var_name]
    exact (AlphaFormula.mk_eq_iff _ _).mp ((hi t).trans hβeq.symm)

theorem raw_allIntro_class_iff {e a b : ℕ} {Γ : List FOL} {A B : AlphaFormula membershipLanguage}
    (he : parseContext e = some Γ) (ha : FormulaRep a A) (hb : FormulaRep b B) :
    EigenvariablePrograms.allSearchValue (EigenvariablePrograms.allInput e a b) ≠ 0 ↔
      ∃ x, B = AlphaFormula.quant .all x A ∧ x ∉ (ContextPrograms.context Γ).fv := by
  obtain ⟨φ, hφ, rfl⟩ := ha
  obtain ⟨ψ, hψ, rfl⟩ := hb
  rw [raw_allSearch_iff he hφ hψ]
  simp only [allIntroWitness]
  constructor
  · rintro ⟨x, hx, hα⟩
    exact ⟨x, (AlphaFormula.mk_eq_iff _ _).mpr hα.symm, hx⟩
  · rintro ⟨x, heq, hx⟩
    exact ⟨x, hx, (AlphaFormula.mk_eq_iff _ _).mp heq.symm⟩

theorem raw_equality_class_iff {a b : ℕ} {A B : AlphaFormula membershipLanguage}
    (ha : FormulaRep a A) (hb : FormulaRep b B) (t r : ℕ) :
    EqualityMatcher.rawCheck a b t r = true ↔
      ∃ (φ : AlphaFormula membershipLanguage) (x : ℕ), A = φ.subst x (.var t) ∧ B = φ.subst x (.var r) := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  rw [EqualityMatcher.rawCheck_parsed_iff hα hβ]
  constructor
  · rintro ⟨φ, x, hφ, hψ⟩
    exact ⟨AlphaFormula.mk φ, x, (AlphaFormula.mk_eq_iff _ _).mpr hφ.symm,
      (AlphaFormula.mk_eq_iff _ _).mpr hψ.symm⟩
  · rintro ⟨φ, x, hφ, hψ⟩
    induction φ using Quotient.inductionOn with
    | _ φ => exact ⟨φ, x, (AlphaFormula.mk_eq_iff _ _).mp hφ.symm,
        (AlphaFormula.mk_eq_iff _ _).mp hψ.symm⟩

end LocalRulePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
