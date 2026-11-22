module

public import PolishSpaceBook.FirstOrderEffectiveContextTests
public import PolishSpaceBook.FirstOrderEffectiveGrammarTests
public import PolishSpaceBook.FirstOrderUnannotatedTrees

@[expose] public section

/-! # Actual lambda grammar checks for effective finite contexts and sequents -/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda NamedLambda.AlphaTerm
open FirstOrderLambdaEncoding
open Grammar (Program)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

namespace ContextGrammar

def invalidFormula : Program := (EffectiveGrammar.formulaRecognizer S).ifZero (Program.const 1) (Program.const 0)

def wellFormed (e : ℕ) : Bool := !(NatListCode.decode e).any
  (fun a => decide ((EffectiveGrammar.formulaRecognizer S).value a = 0))

def term : AlphaTerm := numericalCompose reverseZeroTerm (app listAnyTerm (invalidFormula S).term)

theorem computes : NumericalComputes (term S) (fun e => if wellFormed S e then 1 else 0) := by
  have hAny : NumericalComputes (app listAnyTerm (invalidFormula S).term)
      (fun e => if (NatListCode.decode e).any
        (fun a => decide ((EffectiveGrammar.formulaRecognizer S).value a = 0)) then 1 else 0) := by
    refine ⟨closed_app listAnyTerm_closed (invalidFormula S).computes.1,
      listAnyTerm_apply (invalidFormula S).computes.1 _ ?_⟩
    intro a
    simpa only [invalidFormula, Grammar.Program.ifZero, Grammar.Program.const, decide_eq_true_eq]
      using (invalidFormula S).computes.2 a
  have hh := reverseZero_computes.comp hAny
  refine ⟨hh.1, fun e => ?_⟩
  have flip (b : Bool) : (if !b then 1 else 0 : ℕ) =
      (if (if b then 1 else 0 : ℕ) = 0 then 1 else 0) := by cases b <;> rfl
  have hn := hh.2 e
  dsimp only at hn ⊢
  rw [← flip] at hn
  exact hn

def program : Program := ⟨term S, fun e => if wellFormed S e then 1 else 0, computes S⟩

theorem wellFormed_iff (e : ℕ) : wellFormed S e = true ↔
    ∀ a ∈ NatListCode.decode e, EffectiveGrammar.IsFormulaCode S a := by
  simp only [wellFormed, Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq,
    EffectiveGrammar.formulaRecognizer_reject, not_not]

theorem correct (e : ℕ) : (program S).value e ≠ 0 ↔ ∃ Γ : Context L, S.ContextRep e Γ := by
  change (if wellFormed S e then 1 else 0 : ℕ) ≠ 0 ↔ _
  have bit (b : Bool) : (if b then 1 else 0 : ℕ) ≠ 0 ↔ b = true := by cases b <;> decide
  rw [bit, wellFormed_iff, S.contextRep_exists_iff]
  simp only [S.formulaRep_exists_iff, EffectiveGrammar.IsFormulaCode]

theorem apply (e : ℕ) : Relation.ReflTransGen Beta
    (app (program S).term (numeral e)) (numeral (if wellFormed S e then 1 else 0)) :=
  (program S).computes.2 e

end ContextGrammar

def SequentRep (n : ℕ) (s : Sequent L) : Prop := S.ContextRep n.unpair.1 s.1 ∧ S.FormulaRep n.unpair.2 s.2

theorem sequentRep_unique {n : ℕ} {s t : Sequent L} (hs : S.SequentRep n s) (ht : S.SequentRep n t) : s = t := by
  apply Prod.ext
  · apply (S.contextRep_equal hs.1 ht.1).mp
    exact (ContextPrograms.equalBit_iff _ _).mpr rfl
  · exact S.formulaRep_unique hs.2 ht.2

theorem sequent_has_code (s : Sequent L) : ∃ n : ℕ, S.SequentRep n s := by
  obtain ⟨e, he⟩ := S.context_has_code s.1
  rcases s with ⟨Γ, A⟩
  induction A using Quotient.inductionOn with
  | _ φ =>
    refine ⟨Nat.pair e (S.encodeFormula φ).code, ?_⟩
    change S.ContextRep (Nat.pair e (S.encodeFormula φ).code).unpair.1 Γ ∧
      S.FormulaRep (Nat.pair e (S.encodeFormula φ).code).unpair.2 (AlphaFormula.mk φ)
    simpa only [Nat.unpair_pair] using And.intro he (S.formulaRep_encode φ)

namespace EffectiveRulePrograms

def run (f p : Program) : Program :=
  ⟨numericalCompose f.term p.term, fun n => f.value (p.value n), f.computes.comp p.computes⟩

def validSequent (p : Program) : Program :=
  (run (ContextGrammar.program S) p.first).mul (run (EffectiveGrammar.formulaRecognizer S) p.second)

theorem validSequent_correct (p : Program) (n : ℕ) :
    (validSequent S p).value n ≠ 0 ↔ ∃ s : Sequent L, S.SequentRep (p.value n) s := by
  change (ContextGrammar.program S).value (p.value n).unpair.1 *
    (EffectiveGrammar.formulaRecognizer S).value (p.value n).unpair.2 ≠ 0 ↔ _
  rw [Nat.mul_ne_zero_iff, ContextGrammar.correct]
  have hf : (EffectiveGrammar.formulaRecognizer S).value (p.value n).unpair.2 ≠ 0 ↔
      ∃ A : AlphaFormula L, S.FormulaRep (p.value n).unpair.2 A := by
    rw [ne_eq, EffectiveGrammar.formulaRecognizer_reject, not_not, S.formulaRep_exists_iff]
    rfl
  rw [hf]
  constructor
  · rintro ⟨⟨Γ, hΓ⟩, ⟨A, hA⟩⟩
    exact ⟨(Γ,A), hΓ, hA⟩
  · rintro ⟨⟨Γ,A⟩, hΓ, hA⟩
    exact ⟨⟨Γ,hΓ⟩, ⟨A,hA⟩⟩

end EffectiveRulePrograms
end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
