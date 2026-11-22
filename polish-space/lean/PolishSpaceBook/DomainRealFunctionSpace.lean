module

public import PolishSpaceBook.DomainRealRepresentation
public import PolishSpaceBook.AdmissibleContinuousRealizers
public import PolishSpaceBook.LambdaFunctionSpaces

@[expose] public section

namespace PolishSpaceBook
open LambdaFunction

/-- For the actual real Cauchy representation, continuously realizable maps
are precisely the usual continuous real functions. -/
noncomputable def realFunctionMapEquiv (q : ℕ → ℝ) (hq : DenseRange q) :
    ContinuouslyRealizableMap (cauchyRepresentationObject q hq)
      (cauchyRepresentationObject q hq) ≃ C(ℝ, ℝ) where
  toFun f := ⟨f.val, (hasContinuousRealizer_iff_continuous _ _
    (cauchyRepresentationObject_isAdmissible q hq)
    (cauchyRepresentationObject_isAdmissible q hq) f.val).mp f.property⟩
  invFun f := ⟨f, (hasContinuousRealizer_iff_continuous _ _
    (cauchyRepresentationObject_isAdmissible q hq)
    (cauchyRepresentationObject_isAdmissible q hq) f).mpr f.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full continuous function space, named by the existing lambda interpreter
with an arbitrary retained infinite parameter. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The associated TTE
    function-space representation represents all continuous functions on $\R$, with its computable elements corresponding
    to the computable continuous functions.
-/
noncomputable def realContinuousFunctionRepresentation (q : ℕ → ℝ) (hq : DenseRange q) :
    Representation C(ℝ, ℝ) where
  domain := (typeTwoFunctionRepresentation
    (cauchyRepresentationObject q hq) (cauchyRepresentationObject q hq)).domain
  toFun := realFunctionMapEquiv q hq ∘
    (typeTwoFunctionRepresentation
      (cauchyRepresentationObject q hq) (cauchyRepresentationObject q hq)).toFun
  surjective := (realFunctionMapEquiv q hq).surjective.comp
    (typeTwoFunctionRepresentation
      (cauchyRepresentationObject q hq) (cauchyRepresentationObject q hq)).surjective

/-- Computable points of this full function space are exactly the real functions
having a Type-Two lambda realizer for the chosen Cauchy presentation. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    The associated TTE
    function-space representation represents all continuous functions on $\R$, with its computable elements corresponding
    to the computable continuous functions.
-/
theorem realContinuousFunctionRepresentation_computable_iff (q : ℕ → ℝ)
    (hq : DenseRange q) (f : C(ℝ, ℝ)) :
    (∃ a : (realContinuousFunctionRepresentation q hq).domain,
      ComputableName a.val ∧ (realContinuousFunctionRepresentation q hq).toFun a = f) ↔
      HasComputableRealizer (cauchyRepresentationObject q hq)
        (cauchyRepresentationObject q hq) f := by
  have h := representation_computable_name_iff
    (cauchyRepresentationObject q hq) (cauchyRepresentationObject q hq)
    ((realFunctionMapEquiv q hq).symm f)
  change (∃ a : (typeTwoFunctionRepresentation
      (cauchyRepresentationObject q hq) (cauchyRepresentationObject q hq)).domain,
    ComputableName a.val ∧ realFunctionMapEquiv q hq
      ((typeTwoFunctionRepresentation
        (cauchyRepresentationObject q hq) (cauchyRepresentationObject q hq)).toFun a) = f) ↔ _
  simp only [← Equiv.eq_symm_apply]
  exact h

end PolishSpaceBook
