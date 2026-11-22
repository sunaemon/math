module

public import PolishSpaceBook.FirstOrderEffectiveGrammarState

@[expose] public section

/-! # Exact recognition of arbitrary alpha-renamed rigid tags -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveGrammar
open NamedLambda
open FirstOrderLambdaEncoding (LTerm tag)
universe u v
variable {L : FirstOrder.Language.{u,v}}

theorem alpha_lam_tag_zero (x : ℕ) (A : LTerm) :
    (Term.lam x A).Alpha (tag 0) ↔ A = .var x := by
  rw [Term.alpha_iff_renameEq, Term.renameEq_iff_nameRel]
  change Term.NameRel Eq (.lam x A) (.lam 0 (.var 0)) ↔ _
  constructor
  · intro h
    cases h with
    | lam h =>
      cases h with
      | var h =>
        simp only [Term.bindNames, and_true, ne_eq, not_true_eq_false, false_and, and_false, or_false] at h
        subst h
        rfl
  · rintro rfl
    exact .lam (.var (Or.inl ⟨rfl, rfl⟩))

theorem alpha_lam_tag_succ (x : ℕ) (A : LTerm) (n : ℕ) :
    (Term.lam x A).Alpha (tag (n + 1)) ↔ A.Alpha (tag n) := by
  rw [Term.alpha_iff_renameEq, Term.renameEq_iff_nameRel]
  change Term.NameRel Eq (.lam x A) (.lam 0 (tag n)) ↔ _
  constructor
  · intro h
    cases h with
    | lam h => exact FirstOrderLambdaEncoding.source_tag_alpha h
  · intro h
    have hn := (Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp h)
    exact .lam (hn.congr (by simp))

theorem not_alpha_var_tag (x n : ℕ) : ¬(Term.var x).Alpha (tag n) := by
  intro h
  have h := (Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp h)
  cases n <;> cases h

theorem not_alpha_app_tag (A B : LTerm) (n : ℕ) : ¬(Term.app A B).Alpha (tag n) := by
  intro h
  have h := (Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp h)
  cases n <;> cases h

/-- The numerical tag field accepts precisely the closed tag's alpha class,
including arbitrary harmless renaming of all its binders. -/
theorem tagIndexPlus1_eq_succ_iff (S : EffectiveSignature L) (A : LTerm) (n : ℕ) :
    tagIndexPlus1 (state S A) = n + 1 ↔ A.Alpha (tag n) := by
  induction A generalizing n with
  | var x => simp [state, not_alpha_var_tag]
  | app A B => simp [state, not_alpha_app_tag]
  | lam x A ih =>
    simp only [state, tagIndexPlus1_pack, lambdaTag, code_state, Term.code_injective.eq_iff]
    cases n with
    | zero =>
      rw [alpha_lam_tag_zero]
      by_cases h : A = .var x
      · simp [h]
      · simp only [h, ite_false, Nat.zero_add]
        by_cases hz : tagIndexPlus1 (state S A) = 0
        · simp [hz]
        · simp [hz]
    | succ n =>
      rw [alpha_lam_tag_succ, ← ih n]
      by_cases h : A = .var x
      · subst A
        simp [state]
      · simp only [h, ite_false]
        by_cases hz : tagIndexPlus1 (state S A) = 0
        · simp [hz]
        · simp [hz]

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveGrammar
