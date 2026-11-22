module

public import PolishSpaceBook.FirstOrderEffectiveLocalRules

@[expose] public section

/-! # Semantic meaning of the implemented primitive-rule tests -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open FirstOrderLambdaEncoding.LocalRulePrograms (rawLeft rawRight HasTag)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable local instance ruleTestsDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _

theorem binary_left_match {a b : ℕ} {A B : AlphaFormula L}
    (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) (c : Connective) :
    (HasTag b (connectiveCode c) ∧ (Term.decode a).Alpha (Term.decode (rawLeft b))) ↔
      ∃ C, B = AlphaFormula.binary c A C := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨C, D, hC, _, hB⟩ := S.formulaRep_binary_of_tag hb c ht
    have hAC := (S.formulaRep_alpha_iff ha hC).mp he
    exact ⟨D, hAC ▸ hB⟩
  · rintro ⟨C, hB⟩
    obtain ⟨ht, hA, _⟩ := S.formulaRep_binary_fields hb c hB
    exact ⟨ht, (S.formulaRep_alpha_iff ha hA).mpr rfl⟩

theorem binary_right_match {a b : ℕ} {A B : AlphaFormula L}
    (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) (c : Connective) :
    (HasTag b (connectiveCode c) ∧ (Term.decode a).Alpha (Term.decode (rawRight b))) ↔
      ∃ C, B = AlphaFormula.binary c C A := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨C, D, _, hD, hB⟩ := S.formulaRep_binary_of_tag hb c ht
    have hAD := (S.formulaRep_alpha_iff ha hD).mp he
    exact ⟨C, hAD ▸ hB⟩
  · rintro ⟨C, hB⟩
    obtain ⟨ht, _, hA⟩ := S.formulaRep_binary_fields hb c hB
    exact ⟨ht, (S.formulaRep_alpha_iff ha hA).mpr rfl⟩

theorem binary_match {a b d : ℕ} {A B D : AlphaFormula L}
    (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) (hd : S.FormulaRep d D) (c : Connective) :
    (HasTag a (connectiveCode c) ∧ (Term.decode b).Alpha (Term.decode (rawLeft a)) ∧
      (Term.decode d).Alpha (Term.decode (rawRight a))) ↔ A = AlphaFormula.binary c B D := by
  constructor
  · rintro ⟨ht, hl, hr⟩
    obtain ⟨C, E, hC, hE, hA⟩ := S.formulaRep_binary_of_tag ha c ht
    have hBC := (S.formulaRep_alpha_iff hb hC).mp hl
    have hDE := (S.formulaRep_alpha_iff hd hE).mp hr
    exact hBC ▸ hDE ▸ hA
  · intro hA
    obtain ⟨ht, hB, hD⟩ := S.formulaRep_binary_fields ha c hA
    exact ⟨ht, (S.formulaRep_alpha_iff hb hB).mpr rfl, (S.formulaRep_alpha_iff hd hD).mpr rfl⟩

theorem context_insert_match {e d a : ℕ} {Γ Δ : Context L} {A : AlphaFormula L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (ha : S.FormulaRep a A) :
    ContextPrograms.equalBit d (Nat.pair a e + 1) = true ↔ Δ = insert A Γ :=
  S.contextRep_equal hd (S.contextRep_insert ha he)

theorem implication_intro_match {e d a b : ℕ} {Γ Δ : Context L} {A B : AlphaFormula L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) :
    (HasTag a 5 ∧ (Term.decode b).Alpha (Term.decode (rawRight a)) ∧
      ContextPrograms.equalBit d (Nat.pair (rawLeft a) e + 1) = true) ↔
      ∃ C, A = AlphaFormula.binary .imp C B ∧ Δ = insert C Γ := by
  constructor
  · rintro ⟨ht, hr, hc⟩
    obtain ⟨C, D, hC, hD, hA⟩ := S.formulaRep_binary_of_tag ha .imp ht
    have hBD := (S.formulaRep_alpha_iff hb hD).mp hr
    exact ⟨C, hBD ▸ hA, (S.context_insert_match he hd hC).mp hc⟩
  · rintro ⟨C, hA, hΔ⟩
    obtain ⟨ht, hC, hB⟩ := S.formulaRep_binary_fields ha .imp hA
    exact ⟨ht, (S.formulaRep_alpha_iff hb hB).mpr rfl, (S.context_insert_match he hd hC).mpr hΔ⟩

theorem disjunction_context_match {e d f a : ℕ} {Γ Δ Θ : Context L} {A : AlphaFormula L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (hf : S.ContextRep f Θ) (ha : S.FormulaRep a A) :
    (HasTag a 4 ∧ ContextPrograms.equalBit d (Nat.pair (rawLeft a) e + 1) = true ∧
      ContextPrograms.equalBit f (Nat.pair (rawRight a) e + 1) = true) ↔
      ∃ B C, A = AlphaFormula.binary .disj B C ∧ Δ = insert B Γ ∧ Θ = insert C Γ := by
  constructor
  · rintro ⟨ht, hΔ, hΘ⟩
    obtain ⟨B, C, hB, hC, hA⟩ := S.formulaRep_binary_of_tag ha .disj ht
    exact ⟨B, C, hA, (S.context_insert_match he hd hB).mp hΔ, (S.context_insert_match he hf hC).mp hΘ⟩
  · rintro ⟨B, C, hA, hΔ, hΘ⟩
    obtain ⟨ht, hB, hC⟩ := S.formulaRep_binary_fields ha .disj hA
    exact ⟨ht, (S.context_insert_match he hd hB).mpr hΔ, (S.context_insert_match he hf hC).mpr hΘ⟩

theorem quantifier_instance_match {a b : ℕ} {A B : AlphaFormula L}
    (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) (q : Quantifier) :
    (HasTag a (quantifierCode q) ∧
      InstancePrograms.searchValue S (InstancePrograms.input (rawRight a) (rawLeft a) b) ≠ 0) ↔
      ∃ (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ), A = AlphaFormula.quant q x φ ∧ B = φ.subst x t := by
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨C, hC, hA⟩ := S.formulaRep_quant_of_tag ha q ht
    obtain ⟨t, ht⟩ := (InstancePrograms.searchValue_rep_iff S hC hb _).mp hi
    exact ⟨C, rawLeft a, t, hA, ht.symm⟩
  · rintro ⟨φ, x, t, hA, hB⟩
    have htag := S.formulaRep_quant_tag ha q x hA
    obtain ⟨C, hC, hAC⟩ := S.formulaRep_quant_of_tag ha q htag
    refine ⟨htag, (InstancePrograms.searchValue_rep_iff S hC hb _).mpr ⟨t, ?_⟩⟩
    exact (quant_instances_equal (hAC.symm.trans hA) t).trans hB.symm

theorem existential_elim_match {e d a b : ℕ} {Γ Δ : Context L} {A B : AlphaFormula L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) :
    (HasTag a 7 ∧ EigenvariablePrograms.exSearchValue
      (EigenvariablePrograms.exInput e d (rawRight a) b (rawLeft a)) ≠ 0) ↔
      ∃ (φ : AlphaFormula L) (x y : ℕ), A = AlphaFormula.quant .ex x φ ∧
        Δ = insert (φ.subst x (.var y)) Γ ∧ y ∉ Γ.fv ∪ B.fv ∪ A.fv := by
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨C, hC, hA⟩ := S.formulaRep_quant_of_tag ha .ex ht
    obtain ⟨y, hΔ, hy⟩ := (S.exSearch_iff he hd hC hb _).mp hi
    exact ⟨C, rawLeft a, y, hA, hΔ, by simpa only [hA] using hy⟩
  · rintro ⟨φ, x, y, hA, hΔ, hy⟩
    have htag := S.formulaRep_quant_tag ha .ex x hA
    obtain ⟨C, hC, hAC⟩ := S.formulaRep_quant_of_tag ha .ex htag
    refine ⟨htag, (S.exSearch_iff he hd hC hb _).mpr ⟨y, ?_, ?_⟩⟩
    · rw [quant_instances_equal (hAC.symm.trans hA) (.var y)]
      exact hΔ
    · simpa only [hAC] using hy

theorem equality_elim_match {a b c : ℕ} {A B C : AlphaFormula L}
    (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) (hc : S.FormulaRep c C) :
    (HasTag c 1 ∧ (EqualityPrograms.searchProgram S).value
      (EqualityPrograms.input b a (rawLeft c) (rawRight c)) ≠ 0) ↔
      ∃ (φ : AlphaFormula L) (x : ℕ) (t r : L.Term ℕ), B = φ.subst x t ∧ A = φ.subst x r ∧ C = AlphaFormula.equal t r := by
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨t, r, hleft, hright, hC⟩ := S.formulaRep_equal_of_tag hc ht
    obtain ⟨φ, x, hB, hA⟩ := (EqualityPrograms.searchProgram_iff S hb ha hleft hright).mp hi
    exact ⟨φ, x, t, r, hB, hA, hC⟩
  · rintro ⟨φ, x, t, r, hB, hA, hC⟩
    obtain ⟨ht, hleft, hright⟩ := S.formulaRep_equal_fields hc hC
    exact ⟨ht, (EqualityPrograms.searchProgram_iff S hb ha hleft hright).mpr ⟨φ, x, hB, hA⟩⟩

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
