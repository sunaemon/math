module

public import PolishSpaceBook.FirstOrderEffectiveQuantifiedViews

@[expose] public section

/-! # General-signature correctness of the actual eigenvariable searches

The same closed lambda searches apply to arbitrary effective languages because
their witnesses are variable names. The bounds use the supplied raw codes.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
noncomputable local instance eigenContextDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _

theorem formulaRep_name_bound {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A)
    {x : ℕ} (hx : x ∈ A.fv) : x ≤ a := by
  have hh := raw_freeName_le_code (Term.decode a) (by rwa [S.formulaRep_fv ha])
  simpa only [Term.code_decode] using hh

theorem contextRep_name_bound {e : ℕ} {Γ : Context L} (he : S.ContextRep e Γ)
    {x : ℕ} (hx : x ∈ Γ.fv) : x ≤ e := by
  have hh := (S.contextRep_free he x).mpr hx
  simp only [ContextPrograms.hasFree, List.any_eq_true, decide_eq_true_eq] at hh
  obtain ⟨a, ha, hx⟩ := hh
  have hxa := raw_freeName_le_code (Term.decode a) hx
  have hae := ContextPrograms.member_le_listCode ha
  simp only [Term.code_decode] at hxa
  simp only [NatListCode.encode_decode] at hae
  exact hxa.trans hae

theorem quant_absent_eq (q : Quantifier) (A : AlphaFormula L) (x y : ℕ)
    (hx : x ∉ A.fv) (hy : y ∉ A.fv) : AlphaFormula.quant q x A = AlphaFormula.quant q y A := by
  induction A using Quotient.inductionOn with
  | _ φ =>
    exact (AlphaFormula.mk_eq_iff _ _).mpr
      ((Formula.Alpha.rename q φ x y hy).trans (.quant q y (Formula.alpha_subst_not_free φ x (.var y) hx)))

theorem substitute_absent_eq (A : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) (hx : x ∉ A.fv) : A.subst x t = A := by
  induction A using Quotient.inductionOn with
  | _ φ => exact (AlphaFormula.mk_eq_iff _ _).mpr (Formula.alpha_subst_not_free φ x t hx)

theorem variable_mem_substitute (A : AlphaFormula L) (x y : ℕ) (hx : x ∈ A.fv) :
    y ∈ (A.subst x (.var y)).fv := by
  induction A using Quotient.inductionOn with
  | _ φ =>
    change y ∈ (φ.subst x (.var y)).fv
    rw [Formula.mem_fv_subst]
    exact Or.inr ⟨hx, by simp⟩

theorem formulaRep_quant_code {a : ℕ} {A : AlphaFormula L} (ha : S.FormulaRep a A)
    (q : Quantifier) (x : ℕ) :
    S.FormulaRep (node (quantifierCode q) (.lam x (Term.decode a))).code (AlphaFormula.quant q x A) := by
  induction A using Quotient.inductionOn with
  | _ φ =>
    apply (S.formulaRep_mk_iff _ _).mpr
    rw [Term.decode_code]
    exact (Term.Alpha.refl _).app (((S.formulaRep_mk_iff a φ).mp ha).lam x)

theorem allTest_iff {e a b : ℕ} {Γ : Context L} {A B : AlphaFormula L}
    (he : S.ContextRep e Γ) (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) (x : ℕ) :
    EigenvariablePrograms.allTest.value (Nat.pair (EigenvariablePrograms.allInput e a b) x) ≠ 0 ↔
      B = AlphaFormula.quant .all x A ∧ x ∉ Γ.fv := by
  have hq := (S.formulaRep_alpha_iff (S.formulaRep_quant_code ha .all x) hb).trans eq_comm
  simp only [Term.decode_code, quantifierCode] at hq
  simp only [EigenvariablePrograms.allTest, Grammar.Program.mul, EigenvariablePrograms.Program.isZero,
    Grammar.Program.ifZero, Grammar.Program.const, EigenvariablePrograms.Program.contextFree,
    TemplatePrograms.Program.binary, Grammar.Program.first, Grammar.Program.second,
    Grammar.Program.ident, id_eq, EigenvariablePrograms.allInput, Nat.unpair_pair,
    Grammar.Program.alpha, EigenvariablePrograms.Program.quant_value, Term.decode_code,
    S.contextRep_free he, hq]
  by_cases hc : x ∈ Γ.fv <;> by_cases h : B = AlphaFormula.quant .all x A <;> simp [hc, h]

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    For the eigenvariable rules, an effective witness is
    either bounded by a free occurrence in the displayed data or can be replaced by a name fresh for all those data.
    Finite searches therefore also decide the free-variable side conditions of $(\forall\mathrm I)$ and
    $(\exists\mathrm E)$, including vacuous quantifiers.
-/
theorem allSearch_iff {e a b : ℕ} {Γ : Context L} {A B : AlphaFormula L}
    (he : S.ContextRep e Γ) (ha : S.FormulaRep a A) (hb : S.FormulaRep b B) :
    EigenvariablePrograms.allSearchValue (EigenvariablePrograms.allInput e a b) ≠ 0 ↔
      ∃ x, B = AlphaFormula.quant .all x A ∧ x ∉ Γ.fv := by
  rw [EigenvariablePrograms.allSearchValue, NamedLambda.AlphaTerm.boundedAnyBit_ne_zero]
  have hbound : (EigenvariablePrograms.allInput e a b).unpair.1 +
      (EigenvariablePrograms.allInput e a b).unpair.2.unpair.1 + 2 = e + a + 2 := by
    simp only [EigenvariablePrograms.allInput, Nat.unpair_pair]
  rw [hbound]
  simp only [S.allTest_iff he ha hb]
  constructor
  · rintro ⟨x, _, hx⟩; exact ⟨x, hx⟩
  · rintro ⟨x, heq, hxΓ⟩
    by_cases hx : x ∈ A.fv
    · exact ⟨x, by have := S.formulaRep_name_bound ha hx; omega, heq, hxΓ⟩
    · let z := e + a + 1
      have hzΓ : z ∉ Γ.fv := by
        intro h; have := S.contextRep_name_bound he h; dsimp [z] at *; omega
      have hzA : z ∉ A.fv := by
        intro h; have := S.formulaRep_name_bound ha h; dsimp [z] at *; omega
      exact ⟨z, by dsimp [z]; omega, heq.trans (quant_absent_eq .all A x z hx hzA), hzΓ⟩

theorem exTest_iff {e d a b : ℕ} {Γ Δ : Context L} {A B : AlphaFormula L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (ha : S.FormulaRep a A) (hb : S.FormulaRep b B)
    (x y : ℕ) :
    EigenvariablePrograms.exTest.value (Nat.pair (EigenvariablePrograms.exInput e d a b x) y) ≠ 0 ↔
      Δ = insert (A.subst x (.var y)) Γ ∧ y ∉ Γ.fv ∪ B.fv ∪ (AlphaFormula.quant .ex x A).fv := by
  have hsubst := S.contextRep_substitution he hd ha
    (r := (NamedLambda.Term.var y).code) (t := .var y)
    (by rw [Term.decode_code]; exact .refl _) x
  simp only [Term.decode_code] at hsubst
  have hf := S.formulaRep_fv (S.formulaRep_quant_code ha .ex x)
  simp only [Term.decode_code, quantifierCode] at hf
  simp only [EigenvariablePrograms.exTest, Grammar.Program.mul, EigenvariablePrograms.Program.isZero,
    Grammar.Program.ifZero, Grammar.Program.const, EigenvariablePrograms.Program.contextFree,
    EigenvariablePrograms.Program.formulaFree, EigenvariablePrograms.Program.contextEqual,
    EigenvariablePrograms.Program.substitute, TemplatePrograms.Program.binary, TemplatePrograms.Program.cons,
    Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident, id_eq,
    EigenvariablePrograms.exInput, Nat.unpair_pair, EigenvariablePrograms.Program.quant_value, Term.decode_code,
    hsubst, S.contextRep_free he, S.formulaRep_fv hb, hf, Finset.mem_union, not_or]
  by_cases hc : Δ = insert (A.subst x (.var y)) Γ <;> by_cases hΓ : y ∈ Γ.fv <;>
    by_cases hB : y ∈ B.fv <;> simp [hc, hΓ, hB]

theorem exSearch_iff {e d a b : ℕ} {Γ Δ : Context L} {A B : AlphaFormula L}
    (he : S.ContextRep e Γ) (hd : S.ContextRep d Δ) (ha : S.FormulaRep a A) (hb : S.FormulaRep b B)
    (x : ℕ) :
    EigenvariablePrograms.exSearchValue (EigenvariablePrograms.exInput e d a b x) ≠ 0 ↔
      ∃ y, Δ = insert (A.subst x (.var y)) Γ ∧ y ∉ Γ.fv ∪ B.fv ∪ (AlphaFormula.quant .ex x A).fv := by
  rw [EigenvariablePrograms.exSearchValue, NamedLambda.AlphaTerm.boundedAnyBit_ne_zero]
  simp only [S.exTest_iff he hd ha hb, raw_exBound_value]
  constructor
  · rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, hΔ, hy⟩
    by_cases hx : x ∈ A.fv
    · have hfv : y ∈ Δ.fv := by
        apply Finset.mem_biUnion.mpr
        exact ⟨A.subst x (.var y), by rw [hΔ]; simp, variable_mem_substitute A x y hx⟩
      exact ⟨y, by have := S.contextRep_name_bound hd hfv; omega, hΔ, hy⟩
    · let c := (node 7 (.lam x (Term.decode a))).code
      let z := e + b + c + 1
      have hzΓ : z ∉ Γ.fv := by
        intro h; have := S.contextRep_name_bound he h; dsimp [z] at *; omega
      have hzB : z ∉ B.fv := by
        intro h; have := S.formulaRep_name_bound hb h; dsimp [z] at *; omega
      have hzA : z ∉ (AlphaFormula.quant .ex x A).fv := by
        intro h
        have ht := S.formulaRep_name_bound (S.formulaRep_quant_code ha .ex x) h
        change z ≤ c at ht
        dsimp [z] at ht
        omega
      refine ⟨z, by dsimp [z, c]; omega, ?_, ?_⟩
      · simpa only [substitute_absent_eq A x (.var y) hx, substitute_absent_eq A x (.var z) hx] using hΔ
      · simpa only [Finset.mem_union, not_or] using And.intro (And.intro hzΓ hzB) hzA

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
