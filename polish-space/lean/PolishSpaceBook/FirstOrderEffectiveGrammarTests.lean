module

public import PolishSpaceBook.FirstOrderEffectiveGrammar
public import PolishSpaceBook.FirstOrderEffectiveGrammarCorrectness

@[expose] public section

/-! # All-input beta decisions for effective first-order syntax -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveGrammar
open FirstOrder Language NamedLambda
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem termRecognizer_correct (n : ℕ) : (termRecognizer S).value n = 1 ↔ IsTermCode S n := by
  rw [termRecognizer_value]
  exact termBit_iff S _
theorem formulaRecognizer_correct (n : ℕ) : (formulaRecognizer S).value n = 1 ↔ IsFormulaCode S n := by
  rw [formulaRecognizer_value]
  exact formulaBit_iff S _

theorem termRecognizer_reject (n : ℕ) : (termRecognizer S).value n = 0 ↔ ¬ IsTermCode S n := by
  have hb := (state_bits S (Term.decode n)).1
  have hc := termRecognizer_correct S n
  rw [termRecognizer_value] at hc ⊢
  rw [← hc]
  omega

theorem formulaRecognizer_reject (n : ℕ) : (formulaRecognizer S).value n = 0 ↔ ¬ IsFormulaCode S n := by
  have hb := (state_bits S (Term.decode n)).2.2.2.2.1
  have hc := formulaRecognizer_correct S n
  rw [formulaRecognizer_value] at hc ⊢
  rw [← hc]
  omega

open NamedLambda.AlphaTerm in
theorem termRecognizer_decides (n : ℕ) : Relation.ReflTransGen Beta
    (app (termRecognizer S).term (numeral n)) (numeral (if IsTermCode S n then 1 else 0)) := by
  have hh := (termRecognizer S).computes.2 n
  by_cases hn : IsTermCode S n
  · simpa only [ite_true, hn, (termRecognizer_correct S n).mpr hn] using hh
  · simpa only [ite_false, hn, (termRecognizer_reject S n).mpr hn] using hh

open NamedLambda.AlphaTerm in
theorem formulaRecognizer_decides (n : ℕ) : Relation.ReflTransGen Beta
    (app (formulaRecognizer S).term (numeral n)) (numeral (if IsFormulaCode S n then 1 else 0)) := by
  have hh := (formulaRecognizer S).computes.2 n
  by_cases hn : IsFormulaCode S n
  · simpa only [ite_true, hn, (formulaRecognizer_correct S n).mpr hn] using hh
  · simpa only [ite_false, hn, (formulaRecognizer_reject S n).mpr hn] using hh

open NamedLambda.AlphaTerm in
theorem termRecognizer_encode (t : L.Term ℕ) : Relation.ReflTransGen Beta
    (app (termRecognizer S).term (numeral (S.encodeTerm t).code)) (numeral 1) := by
  have h : IsTermCode S (S.encodeTerm t).code := ⟨t, by rw [Term.decode_code]; exact .refl _⟩
  simpa only [h, ite_true] using termRecognizer_decides S (S.encodeTerm t).code

open NamedLambda.AlphaTerm in
theorem formulaRecognizer_encode (φ : Formula L) : Relation.ReflTransGen Beta
    (app (formulaRecognizer S).term (numeral (S.encodeFormula φ).code)) (numeral 1) := by
  have h : IsFormulaCode S (S.encodeFormula φ).code := ⟨φ, by rw [Term.decode_code]; exact .refl _⟩
  simpa only [h, ite_true] using formulaRecognizer_decides S (S.encodeFormula φ).code

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveGrammar
