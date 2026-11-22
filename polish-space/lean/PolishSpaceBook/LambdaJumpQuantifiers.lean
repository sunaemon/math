module

public import PolishSpaceBook.LambdaJumpCompleteness
public import PolishSpaceBook.WellFoundedRankBounds

@[expose] public section

/-! # Numerical quantifiers and the local rank recursion

One fixed decision program lifts an existential or universal numerical
quantifier using one jump. Two lifts implement the actual bounded-rank
recursion when all lower-row answers share one input parameter and decider.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
set_option maxHeartbeats 800000

noncomputable def jumpName (ε : ℕ → ℕ) : ℕ → ℕ := characteristic (Jump ε)

theorem Decides.negate {ε : ℕ → ℕ} {P : AlphaTerm} {R : ℕ → Prop}
    (hP : Decides ε P R) : Decides ε (mapOutputProgram reverseZeroTerm P) (fun n => ¬ R n) := by
  refine ⟨mapOutputProgram_closed reverseZero_computes.1 hP.1,fun n => ⟨?_,?_⟩⟩
  · intro hn
    simpa using mapOutputProgram_runs reverseZero_computes.1 hP.1
      ((hP.2 n).2 hn) (reverseZero_computes.2 0)
  · intro hn
    simpa using mapOutputProgram_runs reverseZero_computes.1 hP.1
      ((hP.2 n).1 (not_not.mp hn)) (reverseZero_computes.2 1)

/-- The term is chosen before the input parameter and the decided relation. -/
theorem exists_existential_jump_program (P : AlphaTerm) (hP : P.Closed) :
    ∃ Q : AlphaTerm, Q.Closed ∧ ∀ (ε : ℕ → ℕ) (R : ℕ → ℕ → Prop),
      Decides ε P (fun z : ℕ => R z.unpair.1 z.unpair.2) →
      Decides (jumpName ε) Q (fun n => ∃ k, R n k) := by
  classical
  obtain ⟨e,he⟩ := Term.closedProgram_surjective (relativeSearchProgram P) (relativeSearchProgram_closed hP)
  let F := pairNumerical (numericalConstant e) numericalIdentity
  have hF : NumericalComputes F (fun n => Nat.pair e n) :=
    (numericalConstant_computes e).pair numericalIdentity_computes
  refine ⟨reindexProgram haltingDecisionProgram F,
    reindexProgram_closed (haltingDecisionProgram_decides (fun _ => 0)).1 hF.1,?_⟩
  intro ε R hd
  have ht : Computes ε P (fun z : ℕ => if R z.unpair.1 z.unpair.2 then 1 else 0) :=
    ⟨hd.1,fun z => hd.runs z⟩
  have hs (n : ℕ) : (∃ m, OracleRuns ε (relativeSearchProgram P) n m) ↔ ∃ k, R n k := by
    simp [relativeSearchProgram_runs_iff ht,Nat.unpair_pair]
  have h := (haltingDecisionProgram_decides ε).precompNumerical hF
    (g := fun n : ℕ => Nat.pair e n) (by simp)
  simpa only [Nat.unpair_pair,he,hs,jumpName] using h

theorem exists_universal_jump_program (P : AlphaTerm) (hP : P.Closed) :
    ∃ Q : AlphaTerm, Q.Closed ∧ ∀ (ε : ℕ → ℕ) (R : ℕ → ℕ → Prop),
      Decides ε P (fun z : ℕ => R z.unpair.1 z.unpair.2) →
      Decides (jumpName ε) Q (fun n => ∀ k, R n k) := by
  obtain ⟨Q,hQ,h⟩ := exists_existential_jump_program (mapOutputProgram reverseZeroTerm P)
    (mapOutputProgram_closed reverseZero_computes.1 hP)
  refine ⟨mapOutputProgram reverseZeroTerm Q,mapOutputProgram_closed reverseZero_computes.1 hQ,?_⟩
  intro ε R hd
  have hn := (h ε (fun n k => ¬ R n k) hd.negate).negate
  simpa only [not_exists,not_not] using hn

theorem exists_forall_exists_jump_program (P : AlphaTerm) (hP : P.Closed) :
    ∃ Q : AlphaTerm, Q.Closed ∧ ∀ (ε : ℕ → ℕ) (R : ℕ → ℕ → ℕ → Prop),
      Decides ε P (fun z : ℕ => R z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2) →
      Decides (jumpName (jumpName ε)) Q (fun n => ∀ t, ∃ b, R n t b) := by
  obtain ⟨Q,hQ,hx⟩ := exists_existential_jump_program P hP
  obtain ⟨U,hU,hu⟩ := exists_universal_jump_program Q hQ
  refine ⟨U,hU,fun ε R hd => ?_⟩
  exact hu (jumpName ε) (fun n t => ∃ b, R n t b)
    (hx ε (fun z b => R z.unpair.1 z.unpair.2 b) hd)

/-- The lower-row hypothesis is joint in both the stage and source-node indices. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: A rank step with two jumps
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The two deciders give a decider for
    $$M(s,t,b):=\neg\bigl(E_x(t,s)\mathbin{\wedge}\neg L_a(t,b)\bigr).$$
    The numerical-quantifier construction in §{sec:hyperarithmetic-hierarchy} decides
    $\forall t\,\exists b\,M(s,t,b)$ using two jumps. If $E_x(t,s)$ is false, every $b$ satisfies the matrix.
    If it is true, the matrix holds exactly for lower stages $b$ whose rank layer contains $x$ at $t$.
    Thus the quantified matrix is equivalent to the bounded-rank recursion formula.
    \end{proof}
-/
theorem rankLayer_decidable_twoJumps {ε : ℕ → ℕ} (R : ℕ → ℕ → Prop) (hR : WellFounded R)
    (E : ℕ → ℕ → Prop) (a : ℕ)
    (hE : DecidablePredicate ε (fun z : ℕ => E z.unpair.2 z.unpair.1))
    (hL : DecidablePredicate ε (fun z : ℕ => R z.unpair.2 a ∧ RankBound.Holds R hR E z.unpair.2 z.unpair.1)) :
    DecidablePredicate (jumpName (jumpName ε)) (fun s => RankBound.Holds R hR E a s) := by
  classical
  have he := hE.precompNumerical (projection_computes true)
    (g := fun z : ℕ => z.unpair.1) (by simp)
  have hl := hL.precompNumerical
    (((projection_computes false).comp (projection_computes true)).pair (projection_computes false))
    (g := fun z : ℕ => Nat.pair z.unpair.1.unpair.2 z.unpair.2) (by simp)
  have hm := (he.and hl.not).not
  obtain ⟨P,hP⟩ := hm
  obtain ⟨Q,_,hq⟩ := exists_forall_exists_jump_program P hP.1
  have h := hq ε (fun s t b => ¬ (E t s ∧ ¬ (R b a ∧ RankBound.Holds R hR E b t)))
    (by simpa only [Nat.unpair_pair] using hP)
  have hh : (fun s => ∀ t, ∃ b, ¬ (E t s ∧ ¬ (R b a ∧ RankBound.Holds R hR E b t))) =
      (fun s => RankBound.Holds R hR E a s) := by
    funext s
    apply propext
    rw [RankBound.iff_children]
    constructor
    · intro hs t ht
      obtain ⟨b,hb⟩ := hs t
      exact ⟨b,not_not.mp (fun hn => hb ⟨ht,hn⟩)⟩
    · intro hs t
      by_cases ht : E t s
      · obtain ⟨b,hb⟩ := hs t ht
        exact ⟨b,fun hn => hn.2 hb⟩
      · exact ⟨0,fun hn => ht hn.1⟩
  exact ⟨Q,hh ▸ h⟩

end LambdaRelative
end PolishSpaceBook
