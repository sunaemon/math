module

public import PolishSpaceBook.FirstOrderEqualityMatcher
public import PolishSpaceBook.LambdaCompactCovers

@[expose] public section

/-! # Bounded variable-instance search for quantifier rules

In the membership language every term is a variable. A nonvacuous replacement
name is free in the observed instance, while a vacuous replacement may be zero.
Thus a numerical syntax bound gives a total finite lambda search.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm NamedFirstOrder
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false

/-- Even eager binder renaming leaves an absent-variable substitution alpha unchanged. -/
theorem absent_instance_alpha (φ : FOL) (x t : ℕ) (hx : x ∉ φ.fv) :
    (φ.subst x (.var t)).Alpha φ := by
  apply (encode_alpha_iff _ _).mp
  apply (Term.alpha_iff_bindingTree _ _).mpr
  rw [encode_instance_tree]
  exact BindingTree.subst_eq_self _ _ _ (by simpa using hx)

/-- A witness can be taken from zero and the observed instance's free names. -/
theorem instance_witness_bounded (φ ψ : FOL) (x : ℕ) :
    (∃ t, (φ.subst x (.var t)).Alpha ψ) ↔
      ∃ t < (encode ψ).code + 1, (φ.subst x (.var t)).Alpha ψ := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases hx : x ∈ φ.fv
    · have hfv : t ∈ ψ.fv := by
        rw [← ht.fv_eq, Formula.mem_fv_subst]
        exact Or.inr ⟨hx, by simp⟩
      have hb := EqualityMatcher.syntaxName_le_code (encode ψ)
        (EqualityMatcher.names_subset_syntaxNames ψ (fv_subset_names ψ hfv))
      exact ⟨t, by omega, ht⟩
    · exact ⟨0, by omega, (absent_instance_alpha φ x 0 hx).trans
        ((absent_instance_alpha φ x t hx).symm.trans ht)⟩
  · rintro ⟨t, _, ht⟩; exact ⟨t, ht⟩

theorem encoded_instance_alpha_iff (φ ψ : FOL) (x t : ℕ) :
    ((encode φ).subst x (.var t)).Alpha (encode ψ) ↔ (φ.subst x (.var t)).Alpha ψ := by
  rw [← encode_alpha_iff]
  exact ⟨fun h => (encode_subst_alpha φ x t).symm.trans h,
    fun h => (encode_subst_alpha φ x t).trans h⟩

namespace InstancePrograms
open TemplatePrograms

def input (a x b : ℕ) := Nat.pair a (Nat.pair x b)

def test (p t : ℕ) : Prop :=
  ((Term.decode p.unpair.1).subst p.unpair.2.unpair.1 (.var t)).Alpha
    (Term.decode p.unpair.2.unpair.2)
instance (p t : ℕ) : Decidable (test p t) := inferInstanceAs (Decidable (Term.Alpha _ _))

/-- Input is `(source,binder,target)` paired with the candidate replacement name. -/
def testProgram : Grammar.Program :=
  let p := Grammar.Program.ident.first
  let t := Grammar.Program.ident.second
  let a := p.first
  let x := p.second.first
  let b := p.second.second
  let substituted : Grammar.Program :=
    ⟨numericalApply3 substitutionTerm a.term x.term t.varCode.term,
      fun n => ((Term.decode (a.value n)).subst (x.value n) (.var (t.value n))).code, by
        have h := a.computes.apply3 x.computes t.varCode.computes substitutionTerm_closed
          (fun e i d => ((Term.decode e).subst i (Term.decode d)).code) substitutionTerm_apply
        simpa only [Grammar.Program.varCode, Term.decode_code] using h⟩
  substituted.alpha b

theorem testProgram_value (p t : ℕ) :
    testProgram.value (Nat.pair p t) = if test p t then 1 else 0 := by
  simp only [testProgram, Grammar.Program.alpha, Grammar.Program.first,
    Grammar.Program.second, Grammar.Program.ident, id_eq, Nat.unpair_pair,
    Term.decode_code, test]
  rfl

def boundProgram : Grammar.Program :=
  ⟨numericalCompose successorTerm Grammar.Program.ident.second.second.term,
    fun p => p.unpair.2.unpair.2 + 1,
    successor_computes.comp Grammar.Program.ident.second.second.computes⟩

def searchTerm : AlphaTerm := numericalAnyProgram testProgram.term boundProgram.term

def searchValue (p : ℕ) := boundedAnyBit testProgram.value p (p.unpair.2.unpair.2 + 1)

theorem searchTerm_computes : NumericalComputes searchTerm searchValue :=
  numericalAnyProgram_computes testProgram.computes boundProgram.computes

theorem searchValue_ne_zero (p : ℕ) : searchValue p ≠ 0 ↔ ∃ t < p.unpair.2.unpair.2 + 1, test p t := by
  rw [searchValue, boundedAnyBit_ne_zero]
  simp only [testProgram_value, ne_eq, ite_eq_right_iff, Nat.one_ne_zero, imp_false, not_not]

theorem searchValue_formula_iff (φ ψ : FOL) (x : ℕ) :
    searchValue (input (encode φ).code x (encode ψ).code) ≠ 0 ↔
      ∃ t, (φ.subst x (.var t)).Alpha ψ := by
  rw [searchValue_ne_zero]
  simp only [input, Nat.unpair_pair, test, Term.decode_code, encoded_instance_alpha_iff]
  exact (instance_witness_bounded φ ψ x).symm

/-- Totality is on arbitrary numerical input, not only on encoded formulas. -/
theorem searchTerm_apply (p : ℕ) : Relation.ReflTransGen Beta
    (app searchTerm (numeral p)) (numeral (searchValue p)) := searchTerm_computes.2 p

end InstancePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
