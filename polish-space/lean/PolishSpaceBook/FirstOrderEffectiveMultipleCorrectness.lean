module

public import PolishSpaceBook.FirstOrderEffectiveRuleTests
public import PolishSpaceBook.FirstOrderLocalRuleCases

@[expose] public section

/-! # General-signature correctness of the two- and three-premise alternatives -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding
open LocalRulePrograms (P rawLeft rawRight HasTag)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem binary_represented (s p q : P) (n : ℕ) (Γ Δ Θ : Context L) (A B C : AlphaFormula L)
    (hsΓ : S.ContextRep (s.value n).unpair.1 Γ) (hpΔ : S.ContextRep (p.value n).unpair.1 Δ)
    (hqΘ : S.ContextRep (q.value n).unpair.1 Θ) (hsA : S.FormulaRep (s.value n).unpair.2 A)
    (hpB : S.FormulaRep (p.value n).unpair.2 B) (hqC : S.FormulaRep (q.value n).unpair.2 C) :
    (binary S s p q).value n ≠ 0 ↔ BinaryCases Γ A Δ B Θ C := by
  classical
  have hctxP := (S.contextRep_equal hsΓ hpΔ).trans eq_comm
  have hctxQ := (S.contextRep_equal hsΓ hqΘ).trans eq_comm
  have hand := S.binary_match hsA hpB hqC .conj
  have himp := S.binary_match hpB hqC hsA .imp
  have heq := S.equality_elim_match hsA hpB hqC
  have hex := S.existential_elim_match hsΓ hqΘ hpB hsA
  have hac := S.formulaRep_alpha_iff hsA hqC
  simp only [connectiveCode] at hand himp
  simp only [EigenvariablePrograms.exInput] at hex
  simp only [EqualityPrograms.input] at heq
  have hex' : (HasTag (p.value n).unpair.2 7 ∧
      (Term.decode (s.value n).unpair.2).Alpha (Term.decode (q.value n).unpair.2) ∧
      EigenvariablePrograms.exSearchValue (Nat.pair (s.value n).unpair.1
        (Nat.pair (q.value n).unpair.1 (Nat.pair (rawRight (p.value n).unpair.2)
          (Nat.pair (s.value n).unpair.2 (rawLeft (p.value n).unpair.2))))) ≠ 0) ↔
      A = C ∧ ∃ (φ : AlphaFormula L) (x y : ℕ), B = AlphaFormula.quant .ex x φ ∧
        Θ = insert (φ.subst x (.var y)) Γ ∧ y ∉ Γ.fv ∪ A.fv ∪ (AlphaFormula.quant .ex x φ).fv := by
    rw [and_left_comm, hac, hex]
    apply and_congr_right
    intro _
    constructor <;> rintro ⟨φ, x, y, hφ, hΘ, hy⟩ <;>
      exact ⟨φ, x, y, hφ, hΘ, by simpa only [hφ] using hy⟩
  simp only [binary, LocalRulePrograms.Program.any_cons_ne_zero, LocalRulePrograms.Program.any_nil_ne_zero,
    or_false, LocalRulePrograms.Program.all_cons_ne_zero, LocalRulePrograms.Program.alpha_ne_zero,
    LocalRulePrograms.Program.tagIs_ne_zero, LocalRulePrograms.Program.left_value,
    LocalRulePrograms.Program.right_value, LocalRulePrograms.Program.sameContext,
    LocalRulePrograms.Program.contextEqual_ne_zero, Grammar.Program.first, Grammar.Program.second,
    LocalRulePrograms.Program.exSearch, LocalRulePrograms.Program.call, Grammar.Program.pair,
    equalitySearch, run]
  simp only [LocalRulePrograms.Program.all, List.foldr_nil, Grammar.Program.const, ne_eq,
    Nat.one_ne_zero, not_false_eq_true, and_true]
  simp only [and_assoc, hctxP, hctxQ, hand, himp, hex', heq, BinaryCases]

theorem binary_iff (s p q : P) (n : ℕ) (T U V : Sequent L)
    (hs : S.SequentRep (s.value n) T) (hp : S.SequentRep (p.value n) U) (hq : S.SequentRep (q.value n) V) :
    (binary S s p q).value n ≠ 0 ↔ LocalRule [U,V] T := by
  rcases T with ⟨Γ,A⟩
  rcases U with ⟨Δ,B⟩
  rcases V with ⟨Θ,C⟩
  exact (binary_represented S s p q n Γ Δ Θ A B C hs.1 hp.1 hq.1 hs.2 hp.2 hq.2).trans
    (localRule_binary_iff _ _ _ _ _ _).symm

theorem ternary_represented (s p q r : P) (n : ℕ) (Γ Δ Θ Λ : Context L) (A B C D : AlphaFormula L)
    (hsΓ : S.ContextRep (s.value n).unpair.1 Γ) (hpΔ : S.ContextRep (p.value n).unpair.1 Δ)
    (hqΘ : S.ContextRep (q.value n).unpair.1 Θ) (hrΛ : S.ContextRep (r.value n).unpair.1 Λ)
    (hsA : S.FormulaRep (s.value n).unpair.2 A) (hpB : S.FormulaRep (p.value n).unpair.2 B)
    (hqC : S.FormulaRep (q.value n).unpair.2 C) (hrD : S.FormulaRep (r.value n).unpair.2 D) :
    (ternary s p q r).value n ≠ 0 ↔ TernaryCases Γ A Δ B Θ C Λ D := by
  have hctx := (S.contextRep_equal hsΓ hpΔ).trans eq_comm
  have hAC := (S.formulaRep_alpha_iff hsA hqC).trans eq_comm
  have hAD := (S.formulaRep_alpha_iff hsA hrD).trans eq_comm
  have hor := S.disjunction_context_match hsΓ hqΘ hrΛ hpB
  simp only [ternary, LocalRulePrograms.ternary, LocalRulePrograms.Program.all_cons_ne_zero,
    LocalRulePrograms.Program.alpha_ne_zero, LocalRulePrograms.Program.tagIs_ne_zero,
    LocalRulePrograms.Program.sameContext, LocalRulePrograms.Program.contextEqual_ne_zero,
    LocalRulePrograms.Program.conclusionEqual, Grammar.Program.first, Grammar.Program.second,
    LocalRulePrograms.Program.withHyp, TemplatePrograms.Program.cons, TemplatePrograms.Program.binary,
    LocalRulePrograms.Program.left_value, LocalRulePrograms.Program.right_value]
  simp only [LocalRulePrograms.Program.all, List.foldr_nil, Grammar.Program.const, ne_eq,
    Nat.one_ne_zero, not_false_eq_true, and_true]
  rw [hctx, hAC, hAD]
  unfold TernaryCases
  rw [← hor]
  tauto

theorem ternary_iff (s p q r : P) (n : ℕ) (T U V W : Sequent L)
    (hs : S.SequentRep (s.value n) T) (hp : S.SequentRep (p.value n) U)
    (hq : S.SequentRep (q.value n) V) (hr : S.SequentRep (r.value n) W) :
    (ternary s p q r).value n ≠ 0 ↔ LocalRule [U,V,W] T := by
  rcases T with ⟨Γ,A⟩
  rcases U with ⟨Δ,B⟩
  rcases V with ⟨Θ,C⟩
  rcases W with ⟨Λ,D⟩
  exact (ternary_represented S s p q r n Γ Δ Θ Λ A B C D hs.1 hp.1 hq.1 hr.1 hs.2 hp.2 hq.2 hr.2).trans
    (localRule_ternary_iff _ _ _ _ _ _ _ _).symm

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
