module

public import PolishSpaceBook.ArithmeticRosserProofs
public import Mathlib.ModelTheory.Encoding

@[expose] public section

/-! # Effective axioms and the external arithmetic proof-coding boundary

Formula codes below encode the actual finite syntax. Effective axiom presentations
are closed lambda enumerators of these codes. The standard proof-coding theorem
is an explicit external input, as in the book's cited arithmetization paragraph;
it supplies a total certified checker, not Rosser separation or incompleteness.
-/

namespace PolishSpaceBook.ArithmeticRosser
open FirstOrder Language NamedFirstOrder NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

def functionSymbolEquiv : (Σ n, ArithmeticFunction n) ≃ Fin 4 where
  toFun f := match f with
    | ⟨_, .zero⟩ => 0
    | ⟨_, .succ⟩ => 1
    | ⟨_, .add⟩ => 2
    | ⟨_, .mul⟩ => 3
  invFun := ![⟨0, .zero⟩, ⟨1, .succ⟩, ⟨2, .add⟩, ⟨2, .mul⟩]
  left_inv f := by obtain ⟨n, f⟩ := f; cases f <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Encodable (Σ n, arithmetic.Functions n) :=
  Encodable.ofEquiv (Fin 4) functionSymbolEquiv

instance : IsEmpty (Σ n, arithmetic.Relations n) :=
  ⟨fun f => Empty.elim f.2⟩

/-- A natural number encoding the finite list of symbols of the actual sentence. -/
def sentenceCode (φ : arithmetic.Sentence) : ℕ := Encodable.encode φ.listEncode

theorem sentenceCode_injective : Function.Injective sentenceCode := by
  intro φ ψ h
  have hl := Encodable.encode_injective h
  have hs : (⟨0, φ⟩ : Σ n, arithmetic.BoundedFormula Empty n) = ⟨0, ψ⟩ :=
    BoundedFormula.listEncode_sigma_injective hl
  exact (Sigma.mk.inj_iff.mp hs).2 |> eq_of_heq

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    A theory is \termdefineas{effectively axiomatized theory}{effectively axiomatized} here if its
    axioms form a computably enumerable set of finite formula codes.
-/
/-- A partial lambda enumerator with exactly the axiom codes as numerical outputs.
This allows empty and finite theories and does not decide axiom membership. -/
structure EffectiveAxiomPresentation (T : arithmetic.Theory) where
  program : AlphaTerm
  closed : program.Closed
  sound : ∀ n c, Runs program n c → ∃ φ ∈ T, sentenceCode φ = c
  complete : ∀ φ ∈ T, ∃ n, Runs program n (sentenceCode φ)

/-- Precise external proof-coding theorem used by the book: c.e. finite arithmetic
axioms give the total lambda proof-certificate checker for the explicitly formed
Rosser sentences. This is supplied by the cited arithmetization result, not proved
by the local diagonal argument. -/
def ProofCodingTheorem (B : arithmetic.Formula (Fin 3)) : Prop :=
  ∀ T : arithmetic.Theory, Nonempty (EffectiveAxiomPresentation T) →
    Nonempty (CertifiedRosserProofChecker T B)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: First incompleteness theorem (Gödel–Rosser)
-/
/-- With the two cited external arithmetic inputs, every ordinarily consistent
effectively axiomatized extension of the seven Q axioms has an independent
instance of the displayed Rosser family. -/
theorem ArithmeticInputs.incompleteness_of_effective_axioms (A : ArithmeticInputs)
    (proofCoding : ProofCodingTheorem A.B) (T : arithmetic.Theory)
    (effective : Nonempty (EffectiveAxiomPresentation T))
    (hQT : robinson ⊆ T) (hT : Consistent (namedTheory T)) :
    ∃ (E : CertifiedRosserProofChecker T A.B) (d : ℕ),
      NamedLambda.Term.closedProgram d = E.oppositeProgram ∧
      ¬ProvesFrom (namedTheory T) (namedSentence (sigma A.B d)) ∧
      ¬ProvesFrom (namedTheory T) (namedSentence (sigma A.B d).not) := by
  obtain ⟨E⟩ := proofCoding T effective
  obtain ⟨d, hd, hp, hn⟩ := A.exists_independent_sentence E hQT hT
  exact ⟨E, d, hd, hp, hn⟩

end PolishSpaceBook.ArithmeticRosser
