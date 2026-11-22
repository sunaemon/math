module

public import PolishSpaceBook.FirstOrderLambdaEncoding

@[expose] public section

/-! # Actual lambda tests for membership-formula data

These interfaces connect the binding-preserving encoding to the existing closed
alpha comparator, free-variable test and capture-avoiding substitution program.
They do not constitute a proof-tree checker or a grammar recognizer.
-/

namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm

/-- This decision procedure is transported from the implemented syntax comparator,
and the theorem below supplies its actual lambda realizer. -/
instance formulaAlphaDecidable (φ ψ : FOL) : Decidable (φ.Alpha ψ) :=
  decidable_of_iff ((encode φ).Alpha (encode ψ)) (encode_alpha_iff φ ψ)

theorem alphaDecisionTerm_formula (φ ψ : FOL) :
    Relation.ReflTransGen Beta
      (app (app alphaDecisionTerm (numeral (encode φ).code)) (numeral (encode ψ).code))
      (numeral (if φ.Alpha ψ then 1 else 0)) := by
  simpa only [encode_alpha_iff] using alphaDecisionTerm_code (encode φ) (encode ψ)

theorem freeVariableTerm_formula (φ : FOL) (x : ℕ) :
    Relation.ReflTransGen Beta
      (app (app freeVariableTerm (numeral (encode φ).code)) (numeral x))
      (numeral (if x ∈ φ.fv then 1 else 0)) := by
  simpa only [encode_fv] using freeVariableTerm_code (encode φ) x

/-- The total substitution program returns a representative alpha equivalent to
the correctly substituted formula, including capture and shadowing cases. -/
theorem substitutionTerm_formula (φ : FOL) (x y : ℕ) :
    ∃ c : ℕ,
      Relation.ReflTransGen Beta
        (app (app (app substitutionTerm (numeral (encode φ).code)) (numeral x))
          (numeral (Term.var y).code)) (numeral c) ∧
      (Term.decode c).Alpha (encode (φ.subst x (.var y))) := by
  refine ⟨((encode φ).subst x (.var y)).code, substitutionTerm_code _ _ _, ?_⟩
  simpa only [Term.decode_code] using encode_subst_alpha φ x y

/-- The three reused programs are closed lambda terms, not abstract test oracles. -/
theorem formula_programs_closed :
    alphaDecisionTerm.Closed ∧ freeVariableTerm.Closed ∧ substitutionTerm.Closed :=
  ⟨alphaDecisionTerm_closed, freeVariableTerm_closed, substitutionTerm_closed⟩

end PolishSpaceBook.FirstOrderLambdaEncoding
