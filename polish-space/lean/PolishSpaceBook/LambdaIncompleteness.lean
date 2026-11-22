module

public import PolishSpaceBook.LambdaHaltingObstruction
public import Mathlib.ModelTheory.Satisfiability

@[expose] public section

/-! # Incompleteness by diagonal lambda proof search

The arithmetic input is an effective family of sentences that represents the
zero and one outputs of diagonal evaluation. We use mathlib's sentences,
semantic consequence and satisfiability. The local FirstOrderCompleteness module
proves the separate syntactic completeness bridge. An effective proof checker is supplied as an actual closed lambda term; the search and the
opposite-answer diagonal program are constructed here. For arithmetic theories,
the book states and cites the required arithmetization input separately.
The ArithmeticRosserSyntax, ArithmeticRosserProofs, ArithmeticRosserEffective,
and ArithmeticRosserCertificates modules specialize this interface to the actual
seven axioms of Robinson arithmetic and the displayed Rosser sentence. They
derive the separation hypotheses from the cited arithmetic inputs and connect
ordinary syntactic consistency through the local completeness theorem.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
open FirstOrder Language Theory
set_option maxRecDepth 4096

/-- Rosser comparison of finite computation certificates in an arithmetic model.
Only standard finite initial segments are used; the whole model need not be standard. -/
theorem rosser_zero_one_separation {M : Type*} (ν : ℕ → M) (R : M → M → Prop)
    (C : ℕ → ℕ → M → Prop)
    (hfinite : ∀ n x, R x (ν n) → ∃ k ≤ n, x = ν k)
    (hcompare : ∀ n x, R x (ν n) ∨ R (ν n) x)
    (hcertificate : ∀ e b, (∃ s, C e b (ν s)) ↔ App e e b) (e : ℕ) :
    (App e e 0 → ∃ u, C e 0 u ∧ ∀ v, R v u → ¬ C e 1 v) ∧
    (App e e 1 → ¬ ∃ u, C e 0 u ∧ ∀ v, R v u → ¬ C e 1 v) := by
  constructor
  · intro he
    obtain ⟨s,hs⟩ := (hcertificate e 0).mpr he
    refine ⟨ν s,hs,fun v hv hc => ?_⟩
    obtain ⟨k,_,rfl⟩ := hfinite s v hv
    have he' := (hcertificate e 1).mp ⟨k,hc⟩
    have := app_unique he he'
    omega
  · intro he
    obtain ⟨t,ht⟩ := (hcertificate e 1).mpr he
    rintro ⟨u,hu,hbefore⟩
    rcases hcompare t u with hsmall | hlarge
    · obtain ⟨k,_,rfl⟩ := hfinite t u hsmall
      have he' := (hcertificate e 0).mp ⟨k,hu⟩
      have := app_unique he' he
      omega
    · exact hbefore (ν t) hlarge ht

variable {L : FirstOrder.Language} {T : L.Theory} {σ : ℕ → L.Sentence}

/-- Tagged certificates: tag zero proves the sentence, tag one its negation.
The checker is total even on malformed certificates. -/
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
structure EffectiveSentenceFamily (T : L.Theory) (σ : ℕ → L.Sentence) where
  test : ℕ → ℕ → Bool
  program : AlphaTerm
  computes : NumericalComputes program (fun z => if test z.unpair.1 z.unpair.2 then 1 else 0)
  sound : ∀ e k, test e k = true →
    (k.unpair.1 = 0 ∧ T ⊨ᵇ σ e) ∨ (k.unpair.1 = 1 ∧ T ⊨ᵇ (σ e).not)
  complete_pos : ∀ e, T ⊨ᵇ σ e → ∃ p, test e (Nat.pair 0 p) = true
  complete_neg : ∀ e, T ⊨ᵇ (σ e).not → ∃ p, test e (Nat.pair 1 p) = true

/-- A nonempty model rules out simultaneous entailment of a sentence and its negation. -/
theorem models_not_both (hT : T.IsSatisfiable) (φ : L.Sentence)
    (hpos : T ⊨ᵇ φ) (hneg : T ⊨ᵇ φ.not) : False := by
  have hp := (models_sentence_iff.mp hpos) hT.some
  have hn := (models_sentence_iff.mp hneg) hT.some
  exact hn hp

namespace EffectiveSentenceFamily

variable (E : EffectiveSentenceFamily T σ)

def searchProgram : AlphaTerm := numericalResultSearch E.program (numericalProjectionTerm true)

theorem searchProgram_closed : E.searchProgram.Closed :=
  numericalResultSearch_closed E.computes (projection_computes true)

theorem accepted_tags_unique (hT : T.IsSatisfiable) (e i j : ℕ)
    (hi : E.test e i = true) (hj : E.test e j = true) : i.unpair.1 = j.unpair.1 := by
  rcases E.sound e i hi with ⟨hi,hpi⟩ | ⟨hi,hni⟩ <;>
    rcases E.sound e j hj with ⟨hj,hpj⟩ | ⟨hj,hnj⟩
  · exact hi.trans hj.symm
  · exact (models_not_both hT _ hpi hnj).elim
  · exact (models_not_both hT _ hpj hni).elim
  · exact hi.trans hj.symm

/-- Exact partial output: a search terminates precisely at the tag of a valid certificate. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    Use the parameterized result search from §{sec:lambda-rational-ball-programs}, replacing the identity result
    function by the first numerical projection. This gives a closed program $\LambdaTermName{proofSearch}_T$ that
    searches the candidates in numerical
    order and returns the tag of the first accepted one. Every individual test terminates. If a proof of either sentence
    exists, its certificate is eventually reached; consistency makes the returned tag independent of which certificate
    appears first. Consequently
    $$T\vdash\sigma_e\ \Longrightarrow\ \LambdaTermName{proofSearch}_T\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{0},\qquad
      T\vdash\neg\sigma_e\ \Longrightarrow\ \LambdaTermName{proofSearch}_T\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{1}.$$
    If neither sentence is provable, $\LambdaTermName{proofSearch}_T \ChurchNumeral{e}$ has no numeral output. We
    have not assumed that this search
    is total.
-/
theorem searchProgram_runs_iff (hT : T.IsSatisfiable) (e b : ℕ) :
    Runs E.searchProgram e b ↔ ∃ k, E.test e k = true ∧ k.unpair.1 = b := by
  have hu (i j : ℕ)
      (hi : (if E.test (Nat.pair e i).unpair.1 (Nat.pair e i).unpair.2 then 1 else 0) ≠ 0)
      (hj : (if E.test (Nat.pair e j).unpair.1 (Nat.pair e j).unpair.2 then 1 else 0) ≠ 0) :
      i.unpair.1 = j.unpair.1 := by
    apply E.accepted_tags_unique hT e i j
    · simpa using hi
    · simpa using hj
  simpa [searchProgram] using
    numericalResultSearch_runs_iff E.computes (projection_computes true) e b hu

theorem searchProgram_positive (hT : T.IsSatisfiable) (e : ℕ) (hp : T ⊨ᵇ σ e) :
    Runs E.searchProgram e 0 := by
  obtain ⟨p,hp⟩ := E.complete_pos e hp
  exact (E.searchProgram_runs_iff hT e 0).mpr ⟨Nat.pair 0 p,hp,by simp⟩

theorem searchProgram_negative (hT : T.IsSatisfiable) (e : ℕ) (hn : T ⊨ᵇ (σ e).not) :
    Runs E.searchProgram e 1 := by
  obtain ⟨p,hp⟩ := E.complete_neg e hn
  exact (E.searchProgram_runs_iff hT e 1).mpr ⟨Nat.pair 1 p,hp,by simp⟩

/-- Return one for a positive proof and zero for a negative proof. -/
def oppositeProgram : AlphaTerm := numericalCompose reverseZeroTerm E.searchProgram

theorem oppositeProgram_closed : E.oppositeProgram.Closed :=
  composeProgram_closed reverseZero_computes.1 E.searchProgram_closed

theorem oppositeProgram_positive (hT : T.IsSatisfiable) (e : ℕ) (hp : T ⊨ᵇ σ e) :
    Runs E.oppositeProgram e 1 := by
  exact composeProgram_runs reverseZero_computes.1 E.searchProgram_closed
    (E.searchProgram_positive hT e hp) (by simpa using reverseZero_computes.2 0)

theorem oppositeProgram_negative (hT : T.IsSatisfiable) (e : ℕ) (hn : T ⊨ᵇ (σ e).not) :
    Runs E.oppositeProgram e 0 := by
  exact composeProgram_runs reverseZero_computes.1 E.searchProgram_closed
    (E.searchProgram_negative hT e hn) (by simpa using reverseZero_computes.2 1)

/-- The exact independent sentence is the instance at the opposite-search program's index.
No soundness in the standard natural numbers is assumed. -/
theorem independent_at_opposite_index (hT : T.IsSatisfiable)
    (hzero : ∀ e, App e e 0 → T ⊨ᵇ σ e)
    (hone : ∀ e, App e e 1 → T ⊨ᵇ (σ e).not)
    (d : ℕ) (hd : Term.closedProgram d = E.oppositeProgram) :
    ¬ (T ⊨ᵇ σ d) ∧ ¬ (T ⊨ᵇ (σ d).not) := by
  constructor
  · intro hp
    have hr : App d d 1 := by
      unfold App
      rw [hd]
      exact E.oppositeProgram_positive hT d hp
    exact models_not_both hT _ hp (hone d hr)
  · intro hn
    have hr : App d d 0 := by
      unfold App
      rw [hd]
      exact E.oppositeProgram_negative hT d hn
    exact models_not_both hT _ (hzero d hr) hn

theorem exists_independent_sentence (hT : T.IsSatisfiable)
    (hzero : ∀ e, App e e 0 → T ⊨ᵇ σ e)
    (hone : ∀ e, App e e 1 → T ⊨ᵇ (σ e).not) :
    ∃ d, Term.closedProgram d = E.oppositeProgram ∧ ¬ (T ⊨ᵇ σ d) ∧ ¬ (T ⊨ᵇ (σ d).not) := by
  obtain ⟨d,hd⟩ := Term.closedProgram_surjective _ E.oppositeProgram_closed
  exact ⟨d,hd,E.independent_at_opposite_index hT hzero hone d hd⟩

include E in
theorem not_isComplete
    (hzero : ∀ e, App e e 0 → T ⊨ᵇ σ e)
    (hone : ∀ e, App e e 1 → T ⊨ᵇ (σ e).not) : ¬ T.IsComplete := by
  intro hT
  obtain ⟨d,_,hp,hn⟩ := E.exists_independent_sentence hT.1 hzero hone
  exact (hT.2 (σ d)).elim hp hn

end EffectiveSentenceFamily
end PolishSpaceBook.LambdaIndexPCA
