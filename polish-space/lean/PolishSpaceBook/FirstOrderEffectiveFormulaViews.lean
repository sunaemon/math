module

public import PolishSpaceBook.FirstOrderEffectiveContexts
public import PolishSpaceBook.FirstOrderLocalRuleNormalization

@[expose] public section

/-! # Raw constructor fields over effective signatures

The views use the actual alpha relation on the lambda encoding. They therefore
allow arbitrary closed tag representatives and arbitrary bound-name choices.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open FirstOrderLambdaEncoding.LocalRulePrograms (rawField rawLeft rawRight HasTag rawField_app rawLeft_binary rawRight_binary)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

def formulaTag : Formula L → ℕ
  | .falsum => 0
  | .equal _ _ => 1
  | .rel _ _ => 2
  | .binary c _ _ => connectiveCode c
  | .quant q _ _ => quantifierCode q

theorem raw_formula_tag {a : ℕ} {φ : Formula L} (ha : (Term.decode a).Alpha (S.encodeFormula φ)) (k : ℕ) :
    HasTag a k ↔ formulaTag φ = k := by
  have hn := (Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp ha)
  have hc := Term.code_decode a
  generalize he : Term.decode a = t at hn hc ⊢
  rw [← hc]
  cases φ <;> cases hn <;>
    simp only [HasTag, rawField_app, ↓reduceIte, Term.decode_code, formulaTag] <;>
    exact alpha_tag_index_iff (source_tag_alpha (by assumption)) k

theorem formulaTag_binary_iff (A : Formula L) (c : Connective) :
    formulaTag A = connectiveCode c ↔ ∃ φ ψ, A = .binary c φ ψ := by
  cases A with
  | falsum => cases c <;> simp [formulaTag, connectiveCode]
  | equal => cases c <;> simp [formulaTag, connectiveCode]
  | rel => cases c <;> simp [formulaTag, connectiveCode]
  | binary d => cases d <;> cases c <;> simp [formulaTag, connectiveCode]
  | quant q => cases q <;> cases c <;> simp [formulaTag, connectiveCode, quantifierCode]

theorem formulaTag_quant_iff (A : Formula L) (q : Quantifier) :
    formulaTag A = quantifierCode q ↔ ∃ x φ, A = .quant q x φ := by
  cases A with
  | falsum => cases q <;> simp [formulaTag, quantifierCode]
  | equal => cases q <;> simp [formulaTag, quantifierCode]
  | rel => cases q <;> simp [formulaTag, quantifierCode]
  | binary c => cases c <;> cases q <;> simp [formulaTag, connectiveCode, quantifierCode]
  | quant r => cases r <;> cases q <;> simp [formulaTag, quantifierCode]

theorem formulaTag_equal_iff (A : Formula L) : formulaTag A = 1 ↔ ∃ s t, A = .equal s t := by
  cases A with
  | falsum => simp [formulaTag]
  | equal => simp [formulaTag]
  | rel => simp [formulaTag]
  | binary c => cases c <;> simp [formulaTag, connectiveCode]
  | quant q => cases q <;> simp [formulaTag, quantifierCode]

theorem raw_binary_fields {a : ℕ} {c : Connective} {φ ψ : Formula L}
    (ha : (Term.decode a).Alpha (S.encodeFormula (.binary c φ ψ))) :
    (Term.decode (rawLeft a)).Alpha (S.encodeFormula φ) ∧
      (Term.decode (rawRight a)).Alpha (S.encodeFormula ψ) := by
  have hn := (Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp ha)
  have hc := Term.code_decode a
  generalize he : Term.decode a = t at hn hc ⊢
  rw [← hc]
  cases hn with
  | app hk hp =>
    cases hp with
    | app hφ hψ =>
      simp only [rawLeft_binary, rawRight_binary, Term.decode_code]
      exact ⟨(Term.alpha_iff_renameEq _ _).mpr (Term.NameRel.eq_renameEq hφ),
        (Term.alpha_iff_renameEq _ _).mpr (Term.NameRel.eq_renameEq hψ)⟩

theorem formulaRep_binary_fields {a : ℕ} {A B C : AlphaFormula L} (ha : S.FormulaRep a A)
    (c : Connective) (hA : A = AlphaFormula.binary c B C) :
    HasTag a (connectiveCode c) ∧ S.FormulaRep (rawLeft a) B ∧ S.FormulaRep (rawRight a) C := by
  subst A
  induction B using Quotient.inductionOn with
  | _ φ =>
    induction C using Quotient.inductionOn with
    | _ ψ =>
      have hh := (S.formulaRep_mk_iff a (.binary c φ ψ)).mp ha
      have hfields := S.raw_binary_fields hh
      exact ⟨(S.raw_formula_tag hh _).mpr rfl,
        (S.formulaRep_mk_iff _ _).mpr hfields.1, (S.formulaRep_mk_iff _ _).mpr hfields.2⟩

theorem formulaRep_binary_of_tag {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A)
    (c : Connective) (ht : HasTag a (connectiveCode c)) :
    ∃ B C : AlphaFormula L, S.FormulaRep (rawLeft a) B ∧ S.FormulaRep (rawRight a) C ∧
      A = AlphaFormula.binary c B C := by
  induction A using Quotient.inductionOn with
  | _ α =>
    have hh := (S.formulaRep_mk_iff a α).mp ha
    obtain ⟨φ, ψ, rfl⟩ := (formulaTag_binary_iff α c).mp ((S.raw_formula_tag hh _).mp ht)
    have hf := S.raw_binary_fields hh
    exact ⟨AlphaFormula.mk φ, AlphaFormula.mk ψ, (S.formulaRep_mk_iff _ _).mpr hf.1,
      (S.formulaRep_mk_iff _ _).mpr hf.2, rfl⟩

theorem raw_equal_fields {a : ℕ} {s t : L.Term ℕ}
    (ha : (Term.decode a).Alpha (S.encodeFormula (.equal s t))) :
    (Term.decode (rawLeft a)).Alpha (S.encodeTerm s) ∧
      (Term.decode (rawRight a)).Alpha (S.encodeTerm t) := by
  have hn := (Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp ha)
  have hc := Term.code_decode a
  generalize he : Term.decode a = r at hn hc ⊢
  rw [← hc]
  cases hn with
  | app hk hp =>
    cases hp with
    | app hs ht =>
      simp only [rawLeft_binary, rawRight_binary, Term.decode_code]
      exact ⟨(Term.alpha_iff_renameEq _ _).mpr (Term.NameRel.eq_renameEq hs),
        (Term.alpha_iff_renameEq _ _).mpr (Term.NameRel.eq_renameEq ht)⟩

theorem formulaRep_equal_fields {a : ℕ} {A : AlphaFormula L} {s t : L.Term ℕ}
    (ha : S.FormulaRep a A) (hA : A = AlphaFormula.equal s t) :
    HasTag a 1 ∧ (Term.decode (rawLeft a)).Alpha (S.encodeTerm s) ∧
      (Term.decode (rawRight a)).Alpha (S.encodeTerm t) := by
  have hh := (S.formulaRep_mk_iff a (.equal s t)).mp (ha.trans (congrArg S.encodeClass hA))
  exact ⟨(S.raw_formula_tag hh _).mpr rfl, S.raw_equal_fields hh⟩

theorem formulaRep_equal_of_tag {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A) (ht : HasTag a 1) :
    ∃ s t : L.Term ℕ, (Term.decode (rawLeft a)).Alpha (S.encodeTerm s) ∧
      (Term.decode (rawRight a)).Alpha (S.encodeTerm t) ∧ A = AlphaFormula.equal s t := by
  induction A using Quotient.inductionOn with
  | _ α =>
    have hh := (S.formulaRep_mk_iff a α).mp ha
    obtain ⟨s, t, rfl⟩ := (formulaTag_equal_iff α).mp ((S.raw_formula_tag hh _).mp ht)
    have hf := S.raw_equal_fields hh
    exact ⟨s, t, hf.1, hf.2, rfl⟩

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
