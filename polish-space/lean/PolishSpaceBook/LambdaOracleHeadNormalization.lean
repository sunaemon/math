module

public import PolishSpaceBook.LambdaOracleHeadStandardization

@[expose] public section

/-! # Head stages and absence of numerical output with an input name -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

theorem OracleHeadSteps.then_step {p : ℕ → ℕ} {L M N : AlphaTerm}
    (h : OracleHeadSteps p L M) (hs : OracleHeadStep p M N) :
    ∃ P, OracleHeadStep p L P ∧ OracleHeadSteps p P N := by
  rcases h.cases_head with he | ⟨P,hp,ht⟩
  · subst M; exact ⟨N,hs,.refl⟩
  · exact ⟨P,hp,ht.tail hs⟩

theorem OracleStandard.pull_head {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadStep p M N)
    (L : AlphaTerm) (hs : OracleStandard p L M) :
    ∃ P, OracleHeadStep p L P ∧ Relation.ReflTransGen (OracleStep p) P N := by
  induction h generalizing L with
  | contract x A B =>
    obtain ⟨R,S,hp,hR,hS⟩ := hs.app_inv rfl
    obtain ⟨y,C,D,hy,hc,hCD,he⟩ := hR.lam_inv_any rfl
    obtain ⟨P,hP,ht⟩ := OracleHeadSteps.then_step (hp.trans (hc.app_left S))
      (OracleHeadStep.contract y C S)
    refine ⟨P,hP,ht.oracle_steps.trans ?_⟩
    have hb := (hCD.subst hS y hy).oracle_steps
    simpa only [contract_eq D A B y x he] using hb
  | query n hn =>
    obtain ⟨R,S,hp,hR,hS⟩ := hs.app_inv rfl
    obtain ⟨P,hP,ht⟩ := OracleHeadSteps.then_step
      (hp.trans ((hR.var_inv rfl).app_left S))
      (OracleHeadStep.query n (hS.oracle_steps.trans hn))
    exact ⟨P,hP,ht.oracle_steps⟩
  | app_left A h ih =>
    obtain ⟨R,S,hp,hR,hS⟩ := hs.app_inv rfl
    obtain ⟨R',hR',ht⟩ := ih R hR
    obtain ⟨P,hP,hrest⟩ := OracleHeadSteps.then_step hp (OracleHeadStep.app_left S hR')
    exact ⟨P,hP,hrest.oracle_steps.trans (oracle_steps_app ht hS.oracle_steps)⟩


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Moving an input head step to the front
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Replace the first reduction by a standard derivation and induct on the last head step. A root contraction is handled by the application and abstraction inversions, followed by substitution, as above. A grouped query is handled by the application inversion: expose the input variable in the operator, concatenate the argument's standard reduction with its given reduction to a numeral, and perform the grouped query. In either case this gives a nonempty head prefix from $L$; remove its first step and finish by finite beta/query reduction. For a head step inside the operator, apply the induction hypothesis there, lift the resulting step through application, and prepend the existing head prefix. Again remove its first step and finish both subterm reductions.
    \end{proof}
-/
theorem oracle_pull_head_step {p : ℕ → ℕ} {L M N : AlphaTerm}
    (hb : Relation.ReflTransGen (OracleStep p) L M) (hh : OracleHeadStep p M N) :
    ∃ P, OracleHeadStep p L P ∧ Relation.ReflTransGen (OracleStep p) P N :=
  OracleStandard.pull_head hh L (standard_of_oracle_steps hb)

/-- A grouped head step followed by an arbitrary finite beta/query reduction. -/
def OracleHeadStage (p : ℕ → ℕ) (M N : AlphaTerm) : Prop :=
  ∃ A, OracleHeadStep p M A ∧ Relation.ReflTransGen (OracleStep p) A N

theorem no_infinite_oracle_head_stages {p : ℕ → ℕ} {M A : AlphaTerm} {x : ℕ}
    (hn : OracleHeadSteps p M (lam x A)) (f : ℕ → AlphaTerm)
    (hf : Relation.ReflTransGen (OracleStep p) M (f 0))
    (hs : ∀ k, OracleHeadStage p (f k) (f (k + 1))) : False := by
  induction hn using Relation.ReflTransGen.head_induction_on generalizing f with
  | refl =>
    obtain ⟨B,hb,_⟩ := hs 0
    obtain ⟨P,hp,_⟩ := oracle_pull_head_step hf hb
    exact hp.not_lam rfl
  | @head M N hh ht ih =>
    obtain ⟨B,hb,htail⟩ := hs 0
    obtain ⟨P,hp,hP⟩ := oracle_pull_head_step hf hb
    have he := hh.deterministic hp
    subst P
    exact ih (fun k => f (k + 1)) (hP.trans htail) (fun k => hs (k + 1))


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Infinite input head stages exclude numerical output
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    A numeral output would give a finite head reduction to an abstraction. As in §{sec:lambda-head-exposure}, prove the stronger assertion allowing an initial finite reduction from a term $M$ to $S_0$, and induct on a head reduction from $M$ to an abstraction. At length zero, moving the first stage's head step to the front would produce a head step from an abstraction, which is impossible. Otherwise move that step to the front and use determinism to identify its target with the first target on the chosen head reduction. The shorter head reduction and the shifted sequence $S_1,S_2,\ldots$ contradict the induction hypothesis. This counts grouped head steps; the reductions inside queries need not have a common length bound.
    \end{proof}
-/
theorem no_numeral_of_oracle_head_stages {p : ℕ → ℕ} (f : ℕ → AlphaTerm)
    (hs : ∀ k, OracleHeadStage p (f k) (f (k + 1))) (n : ℕ) :
    ¬ Relation.ReflTransGen (OracleStep p) (f 0) (numeral n) := by
  intro hn
  obtain ⟨x,A,ha⟩ := oracle_head_exposes_abstraction hn
  exact no_infinite_oracle_head_stages ha f .refl hs

theorem oracle_numeral_after_reduction {p : ℕ → ℕ} {L M : AlphaTerm} {n : ℕ}
    (h : Relation.ReflTransGen (OracleStep p) L M)
    (hn : Relation.ReflTransGen (OracleStep p) L (numeral n)) :
    Relation.ReflTransGen (OracleStep p) M (numeral n) := by
  obtain ⟨P,hP,hnP⟩ := oracle_confluent h hn
  have he := numeral_eq_of_oracle_steps hnP
  simpa only [he] using hP

end PolishSpaceBook.NamedLambda.AlphaTerm
