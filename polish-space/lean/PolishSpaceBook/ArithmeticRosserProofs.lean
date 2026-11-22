module

public import PolishSpaceBook.ArithmeticRosserSyntax

@[expose] public section

/-! # Arithmetic separation and the book's syntactic proof system

Only the cited numeralwise representation and finite-numeral facts are external
inputs. The Rosser implications, their derivations in the named natural-deduction
calculus, and the specialization of the lambda diagonal search are proved here.
-/

noncomputable section
namespace PolishSpaceBook.ArithmeticRosser
open FirstOrder Language Theory NamedFirstOrder
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- Translate an actual closed arithmetic formula into the book's alpha syntax. -/
def namedSentence (φ : arithmetic.Sentence) : AlphaFormula arithmetic :=
  AlphaFormula.mk (boundedToNamed φ)

def namedTheory (T : arithmetic.Theory) : Set (AlphaFormula arithmetic) := namedSentence '' T

theorem namedSentence_closed (φ : arithmetic.Sentence) : namedSentence φ ∈ Sentences arithmetic := by
  simpa only [namedSentence, Sentences, Set.mem_ofPred_eq, AlphaFormula.fv_mk] using
    boundedToNamed_sentence φ

theorem namedTheory_closed (T : arithmetic.Theory) : namedTheory T ⊆ Sentences arithmetic := by
  rintro _ ⟨φ, _, rfl⟩
  exact namedSentence_closed φ

theorem realize_namedSentence {M : Type*} [arithmetic.Structure M]
    (φ : arithmetic.Sentence) (s : ℕ → M) :
    (namedSentence φ).Realize s ↔ M ⊨ φ :=
  realize_boundedToNamed_sentence φ s

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The conclusions hold in every model of $\RobinsonArithmetic$; Gödel completeness gives the two derivability claims.
    This argument works equally in nonstandard models.
    \end{proof}
-/
/-- Semantic consequence is connected to actual finite derivations by the local
Henkin completeness theorem, rather than by a semantic theory-completeness API. -/
theorem proves_iff_models (T : arithmetic.Theory) (φ : arithmetic.Sentence) :
    ProvesFrom (namedTheory T) (namedSentence φ) ↔ T ⊨ᵇ φ := by
  rw [proves_iff_small_model_consequence (namedTheory_closed T) (namedSentence_closed φ)]
  constructor
  · intro h
    apply models_sentence_iff.mpr
    intro M
    let s : ℕ → M := fun _ => Classical.choice inferInstance
    apply (realize_namedSentence φ s).mp
    apply h M inferInstance inferInstance s
    rintro _ ⟨ψ, hψ, rfl⟩
    exact (realize_namedSentence ψ s).mpr (realize_sentence_of_mem T hψ)
  · intro h M inst hne s hT
    let := inst
    let := hne
    let : M ⊨ T := ⟨fun ψ hψ => (realize_namedSentence ψ s).mp (hT _ ⟨ψ, hψ, rfl⟩)⟩
    exact (realize_namedSentence φ s).mpr ((models_sentence_iff.mp h) (ModelType.of T M))

/-- Ordinary syntactic consistency suffices to produce the model needed by the
lambda diagonal theorem. No standard-model soundness is imposed. -/
theorem satisfiable_of_consistent (T : arithmetic.Theory) (hT : Consistent (namedTheory T)) :
    T.IsSatisfiable := by
  obtain ⟨M, inst, hne, hm⟩ := hT.exists_model (namedTheory_closed T)
  let := inst
  let := hne
  let s : ℕ → M := fun _ => Classical.choice hne
  let : M ⊨ T := ⟨fun ψ hψ => (realize_namedSentence ψ s).mp (hm s _ ⟨ψ, hψ, rfl⟩)⟩
  exact ⟨ModelType.of T M⟩

/-- The exact external arithmetic facts cited in the book. `B` is an arithmetic
formula representing the literal beta-certificate test. The model universe is
the syntax universe, which suffices by the local small-model completeness theorem. -/
structure ArithmeticInputs where
  B : arithmetic.Formula (Fin 3)
  numeralwise : ∀ (M : Type) [arithmetic.Structure M] [Nonempty M] [M ⊨ robinson]
    (e b s : ℕ), certificateRelation B e b (modelNumeral M s) ↔ accepts e b s = true
  finite : ∀ (M : Type) [arithmetic.Structure M] [Nonempty M] [M ⊨ robinson]
    (n : ℕ) (x : M), modelLe x (modelNumeral M n) → ∃ k ≤ n, x = modelNumeral M k
  compare : ∀ (M : Type) [arithmetic.Structure M] [Nonempty M] [M ⊨ robinson]
    (n : ℕ) (x : M), modelLe x (modelNumeral M n) ∨ modelLe (modelNumeral M n) x

namespace ArithmeticInputs
variable (A : ArithmeticInputs)

theorem certificate_iff (M : Type) [arithmetic.Structure M] [Nonempty M] [M ⊨ robinson]
    (e b : ℕ) : (∃ s, certificateRelation A.B e b (modelNumeral M s)) ↔ App e e b := by
  simp only [A.numeralwise M]
  exact exists_accepts_iff e b

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Work in an arbitrary model of $\RobinsonArithmetic$. If $\varphi_e(e)=0$, choose a standard certificate $s$ for this
    output. Numerical output uniqueness excludes every standard certificate for output $1$.
    Every model element below $\ArithmeticNumeral{s}$ is a standard numeral, so the numeralwise facts about $B$ prove
    that $\ArithmeticNumeral{s}$ witnesses $\sigma_e$ in this model.

    If $\varphi_e(e)=1$, choose a standard certificate $t$ for that output. Suppose an element $u$ witnessed
    $\sigma_e$. If $u\le\ArithmeticNumeral{t}$, then $u$ is a standard numeral, so
    $B(\ArithmeticNumeral{e},\ArithmeticNumeral{0},u)$ would give a standard computation with output $0$, contradicting
    output uniqueness. If $\ArithmeticNumeral{t}\le u$, the universal clause of $\sigma_e$ contradicts the accepted
    certificate $t$. Comparison with the fixed numeral covers both cases, so this model satisfies $\neg\sigma_e$.
-/
/-- The two conclusions are derived for the defined sentence by the Rosser
comparison; neither implication is a field of the arithmetic input. -/
theorem separation_in_model (M : Type) [arithmetic.Structure M] [Nonempty M] [M ⊨ robinson]
    (e : ℕ) : (App e e 0 → M ⊨ sigma A.B e) ∧ (App e e 1 → M ⊨ (sigma A.B e).not) := by
  simpa only [realize_sigma, Sentence.realize_not] using
    rosser_zero_one_separation (modelNumeral M) modelLe (certificateRelation A.B)
      (A.finite M) (A.compare M) (A.certificate_iff M) e

theorem rosser_zero (e : ℕ) (he : App e e 0) : robinson ⊨ᵇ sigma A.B e :=
  models_sentence_iff.mpr (fun M => (A.separation_in_model M e).1 he)

theorem rosser_one (e : ℕ) (he : App e e 1) : robinson ⊨ᵇ (sigma A.B e).not :=
  models_sentence_iff.mpr (fun M => (A.separation_in_model M e).2 he)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Rosser separation of computation outputs
-/
theorem proves_rosser_zero (e : ℕ) (he : App e e 0) :
    ProvesFrom (namedTheory robinson) (namedSentence (sigma A.B e)) :=
  (proves_iff_models _ _).mpr (A.rosser_zero e he)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Rosser separation of computation outputs
-/
theorem proves_rosser_one (e : ℕ) (he : App e e 1) :
    ProvesFrom (namedTheory robinson) (namedSentence (sigma A.B e).not) :=
  (proves_iff_models _ _).mpr (A.rosser_one e he)

end ArithmeticInputs

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    Let $T$ now be a consistent effectively axiomatized extension of $\RobinsonArithmetic$.
    For a candidate $k=\NatPair{b}{p}$, let $c_T(e,k)$ be $1$ if either $b=0$ and $p$ certifies $T\vdash\sigma_e$,
    or $b=1$ and $p$ certifies $T\vdash\neg\sigma_e$; let it be $0$ otherwise.
    Let $\LambdaTermName{certificateTest}_T$ be a closed lambda program computing this total test on the paired
    input $\NatPair{e}{k}$.
    Malformed certificates and other tags are rejected. Consistency ensures that, for a fixed $e$, all accepted candidates
    have the same tag.
-/
/-- The cited proof-coding input, specialized to the concrete arithmetic family.
Its certificates prove actual named-calculus derivations. The supplied closed
lambda program computes the total test on every numerical input, including
malformed certificates and tags other than zero and one. -/
structure CertifiedRosserProofChecker (T : arithmetic.Theory) (B : arithmetic.Formula (Fin 3)) where
  test : ℕ → ℕ → Bool
  program : AlphaTerm
  computes : NumericalComputes program (fun z => if test z.unpair.1 z.unpair.2 then 1 else 0)
  sound : ∀ e k, test e k = true →
    (k.unpair.1 = 0 ∧ ProvesFrom (namedTheory T) (namedSentence (sigma B e))) ∨
    (k.unpair.1 = 1 ∧ ProvesFrom (namedTheory T) (namedSentence (sigma B e).not))
  complete_pos : ∀ e, ProvesFrom (namedTheory T) (namedSentence (sigma B e)) →
    ∃ p, test e (Nat.pair 0 p) = true
  complete_neg : ∀ e, ProvesFrom (namedTheory T) (namedSentence (sigma B e).not) →
    ∃ p, test e (Nat.pair 1 p) = true

namespace CertifiedRosserProofChecker
variable {T : arithmetic.Theory} {B : arithmetic.Formula (Fin 3)}
  (E : CertifiedRosserProofChecker T B)

/-- The conversion uses the proved syntactic completeness bridge in both directions. -/
def toEffectiveSentenceFamily : EffectiveSentenceFamily T (sigma B) where
  test := E.test
  program := E.program
  computes := E.computes
  sound e k hk := (E.sound e k hk).imp
    (fun h => ⟨h.1, (proves_iff_models _ _).mp h.2⟩)
    (fun h => ⟨h.1, (proves_iff_models _ _).mp h.2⟩)
  complete_pos e h := E.complete_pos e ((proves_iff_models _ _).mpr h)
  complete_neg e h := E.complete_neg e ((proves_iff_models _ _).mpr h)

def oppositeProgram : AlphaTerm := E.toEffectiveSentenceFamily.oppositeProgram

theorem oppositeProgram_closed : E.oppositeProgram.Closed :=
  E.toEffectiveSentenceFamily.oppositeProgram_closed

end CertifiedRosserProofChecker

namespace ArithmeticInputs
variable (A : ArithmeticInputs) {T : arithmetic.Theory}

theorem extension_zero (hQT : robinson ⊆ T) (e : ℕ) (he : App e e 0) : T ⊨ᵇ sigma A.B e :=
  models_of_models_theory (fun _ hφ => models_sentence_of_mem (hQT hφ)) (A.rosser_zero e he)

theorem extension_one (hQT : robinson ⊆ T) (e : ℕ) (he : App e e 1) : T ⊨ᵇ (sigma A.B e).not :=
  models_of_models_theory (fun _ hφ => models_sentence_of_mem (hQT hφ)) (A.rosser_one e he)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Form the closed program
    $$\LambdaTermName{opposite}_T:= \lambdaab{z}{ \LambdaZeroTest\,( \LambdaTermName{proofSearch}_Tz)\,
    \ChurchNumeral{1}\, \ChurchNumeral{0}}.$$
    When the proof search returns $0$, it returns $1$; when the search returns $1$, it returns $0$.
    Choose a named representative of $\LambdaTermName{opposite}_T$ and let
    $d:=\LambdaSyntaxCode{\LambdaTermName{opposite}_T}$ be its index. Define $G:=\sigma_d$.
    If $T\vdash G$, then the proof search and the final zero test give
    $$\LambdaTermName{opposite}_T\ChurchNumeral{d}\to_\beta^*\ChurchNumeral{1},\qquad\varphi_d(d)=1.$$
    The Rosser separation lemma gives $\RobinsonArithmetic\vdash\neg\sigma_d$, hence $T\vdash\neg G$, contradicting
    consistency. If $T\vdash\neg G$, the same program instead gives
    $$\LambdaTermName{opposite}_T\ChurchNumeral{d}\to_\beta^*\ChurchNumeral{0},\qquad\varphi_d(d)=0.$$
    Now the lemma gives $\RobinsonArithmetic\vdash\sigma_d$, hence $T\vdash G$, again contradicting consistency.
    Thus neither sentence is provable. Every step uses a finite computation under the corresponding hypothetical proof;
    no decision of the entire theorem set, and no totality of $\LambdaTermName{proofSearch}_T$, was assumed.
    \end{proof}
-/
/-- Concrete arithmetic incompleteness from ordinary consistency and the cited
actual proof checker. The independent sentence is `sigma A.B d` at the index of
the constructed opposite-search lambda term. -/
theorem exists_independent_sentence (E : CertifiedRosserProofChecker T A.B)
    (hQT : robinson ⊆ T) (hT : Consistent (namedTheory T)) :
    ∃ d, NamedLambda.Term.closedProgram d = E.oppositeProgram ∧
      ¬ProvesFrom (namedTheory T) (namedSentence (sigma A.B d)) ∧
      ¬ProvesFrom (namedTheory T) (namedSentence (sigma A.B d).not) := by
  obtain ⟨d, hd, hp, hn⟩ := E.toEffectiveSentenceFamily.exists_independent_sentence
    (satisfiable_of_consistent T hT) (A.extension_zero hQT) (A.extension_one hQT)
  exact ⟨d, hd, fun h => hp ((proves_iff_models _ _).mp h),
    fun h => hn ((proves_iff_models _ _).mp h)⟩

end ArithmeticInputs

end PolishSpaceBook.ArithmeticRosser
