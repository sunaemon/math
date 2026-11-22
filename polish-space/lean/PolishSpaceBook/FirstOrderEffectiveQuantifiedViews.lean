module

public import PolishSpaceBook.FirstOrderEffectiveFormulaViews
public import PolishSpaceBook.FirstOrderEffectiveGrammarCorrectness

@[expose] public section

/-! # Actual raw binders and bodies of quantified formula classes -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open FirstOrderLambdaEncoding.LocalRulePrograms (rawLeft rawRight HasTag rawLeft_quant rawRight_quant)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem formulaRep_quant_tag {a : ℕ} {A B : AlphaFormula L} (ha : S.FormulaRep a A)
    (q : Quantifier) (x : ℕ) (hA : A = AlphaFormula.quant q x B) : HasTag a (quantifierCode q) := by
  subst A
  induction B using Quotient.inductionOn with
  | _ φ =>
    have hh := (S.formulaRep_mk_iff a (.quant q x φ)).mp ha
    exact (S.raw_formula_tag hh _).mpr rfl

/-- The body representative uses the actual raw binder. No choice of a canonical
bound name is built into the checker or into this interpretation theorem. -/
theorem formulaRep_quant_of_tag {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A)
    (q : Quantifier) (ht : HasTag a (quantifierCode q)) :
    ∃ B : AlphaFormula L, S.FormulaRep (rawRight a) B ∧ A = AlphaFormula.quant q (rawLeft a) B := by
  induction A using Quotient.inductionOn with
  | _ α =>
    have hh := (S.formulaRep_mk_iff a α).mp ha
    obtain ⟨x, φ, rfl⟩ := (formulaTag_quant_iff α q).mp ((S.raw_formula_tag hh _).mp ht)
    have hn := (Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp hh)
    have hc := Term.code_decode a
    generalize hraw : Term.decode a = t at hn hc hh ⊢
    rw [← hc]
    cases hn with
    | app hk hp =>
      cases hp with
      | @lam _ y _ M _ hbody =>
        obtain ⟨ψ, hψ⟩ := (EffectiveGrammar.formulaBit_iff S M).mp
          (EffectiveGrammar.formulaBit_of_nameRel S φ _ M hbody)
        have hnew : (Term.app _ (.lam y M)).Alpha (S.encodeFormula (.quant q y ψ)) :=
          (source_tag_alpha hk).app (hψ.lam y)
        refine ⟨AlphaFormula.mk ψ, ?_, ?_⟩
        · simp only [rawRight_quant]
          apply (S.formulaRep_mk_iff _ _).mpr
          simpa only [Term.decode_code] using hψ
        · simp only [rawLeft_quant]
          exact (AlphaFormula.mk_eq_iff _ _).mpr
            ((S.encodeFormula_alpha_iff _ _).mp (hh.symm.trans hnew))

theorem quant_instances_equal {A B : AlphaFormula L} {q : Quantifier} {x y : ℕ}
    (h : AlphaFormula.quant q x A = AlphaFormula.quant q y B) (t : L.Term ℕ) :
    A.subst x t = B.subst y t := by
  induction A using Quotient.inductionOn with
  | _ φ =>
    induction B using Quotient.inductionOn with
    | _ ψ =>
      exact (AlphaFormula.mk_eq_iff _ _).mpr (((AlphaFormula.mk_eq_iff _ _).mp h).instantiate t)

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
