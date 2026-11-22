module

public import PolishSpaceBook.FirstOrderEffectiveInstanceBounds
public import PolishSpaceBook.FirstOrderEffectiveGrammarTests
public import PolishSpaceBook.FirstOrderEffectiveContexts
public import PolishSpaceBook.LambdaCompactCovers

@[expose] public section

/-! # Concrete bounded lambda search for general quantifier instances -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open FirstOrderLambdaEncoding.Grammar (Program)
open EffectiveGrammar QuantifierBounds
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace InstancePrograms

open FirstOrderLambdaEncoding.Grammar.Program

/-- Input pairs the `(source,binder,target)` triple with a candidate term code. -/
def testProgram : Program :=
  let p := ident.first
  let c := ident.second
  let a := p.first
  let x := p.second.first
  let b := p.second.second
  let substituted : Program :=
    ⟨numericalApply3 substitutionTerm a.term x.term c.term,
      fun n => ((Term.decode (a.value n)).subst (x.value n) (Term.decode (c.value n))).code,
      a.computes.apply3 x.computes c.computes substitutionTerm_closed
        (fun e i d => ((Term.decode e).subst i (Term.decode d)).code) substitutionTerm_apply⟩
  (QuantifierBounds.Program.call (termRecognizer S) c).mul (substituted.alpha b)

theorem testProgram_value (p c : ℕ) :
    (testProgram S).value (Nat.pair p c) = if test S p c then 1 else 0 := by
  have hb : (termRecognizer S).value c = if IsTermCode S c then 1 else 0 := by
    by_cases h : IsTermCode S c
    · rw [ite_eq_left h]
      exact (termRecognizer_correct S c).mpr h
    · rw [ite_eq_right h]
      exact (termRecognizer_reject S c).mpr h
  simp only [testProgram, mul, QuantifierBounds.Program.call, alpha, first, second, ident,
    id_eq, Nat.unpair_pair, Term.decode_code, hb, test]
  split_ifs <;> simp_all

/-- The finite bound is evaluated by the explicit syntax-code recursor. -/
def boundProgram : Program :=
  QuantifierBounds.Program.add
    (QuantifierBounds.Program.call witnessBoundProgram ident.second.second) (const 1)

theorem boundProgram_value (p : ℕ) :
    boundProgram.value p = witnessBound p.unpair.2.unpair.2 + 1 := by
  simp [boundProgram, QuantifierBounds.Program.add, QuantifierBounds.Program.call,
    second, ident, const, witnessBoundProgram_value]

def searchTerm : AlphaTerm := numericalAnyProgram (testProgram S).term boundProgram.term
def searchValue (p : ℕ) := boundedAnyBit (testProgram S).value p (witnessBound p.unpair.2.unpair.2 + 1)

theorem searchTerm_computes : NumericalComputes (searchTerm S) (searchValue S) := by
  unfold searchTerm searchValue
  simpa only [boundProgram_value] using
    numericalAnyProgram_computes (testProgram S).computes boundProgram.computes

theorem searchValue_ne_zero (p : ℕ) : searchValue S p ≠ 0 ↔
    ∃ c < witnessBound p.unpair.2.unpair.2 + 1, test S p c := by
  rw [searchValue, boundedAnyBit_ne_zero]
  simp only [testProgram_value, ne_eq, ite_eq_right_iff, Nat.one_ne_zero, imp_false, not_not]

theorem searchValue_formula_iff (a b x : ℕ) (φ ψ : Formula L)
    (hA : (Term.decode a).Alpha (S.encodeFormula φ))
    (hB : (Term.decode b).Alpha (S.encodeFormula ψ)) :
    searchValue S (input a x b) ≠ 0 ↔ ∃ r : L.Term ℕ, (φ.subst x r).Alpha ψ := by
  rw [searchValue_ne_zero]
  simpa only [input, Nat.unpair_pair] using
    (instance_witness_bounded S a b x φ ψ hA hB).symm

theorem searchValue_rep_iff {a b : ℕ} {A B : AlphaFormula L}
    (hA : S.FormulaRep a A) (hB : S.FormulaRep b B) (x : ℕ) :
    searchValue S (input a x b) ≠ 0 ↔ ∃ r : L.Term ℕ, A.subst x r = B := by
  induction A using Quotient.inductionOn with
  | _ φ =>
    induction B using Quotient.inductionOn with
    | _ ψ =>
      change searchValue S (input a x b) ≠ 0 ↔
        ∃ r : L.Term ℕ, AlphaFormula.mk (φ.subst x r) = AlphaFormula.mk ψ
      simp only [AlphaFormula.mk_eq_iff]
      exact searchValue_formula_iff S a b x φ ψ
        ((S.formulaRep_mk_iff _ _).mp hA) ((S.formulaRep_mk_iff _ _).mp hB)

/-- Totality holds for every numerical triple, including malformed syntax. -/
theorem searchTerm_apply (p : ℕ) : Relation.ReflTransGen Beta
    (app (searchTerm S) (numeral p)) (numeral (searchValue S p)) :=
  (searchTerm_computes S).2 p

def searchProgram : Program := ⟨searchTerm S, searchValue S, searchTerm_computes S⟩

end InstancePrograms
end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
