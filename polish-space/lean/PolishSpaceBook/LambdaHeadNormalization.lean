module

public import PolishSpaceBook.LambdaHeadStandardization

@[expose] public section

/-! # Moving head steps forward and excluding infinite search stages -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

theorem HeadSteps.then_step {L M N : AlphaTerm} (h : HeadSteps L M) (hs : HeadStep M N) :
    ∃ P, HeadStep L P ∧ HeadSteps P N := by
  rcases h.cases_head with he | ⟨P, hp, ht⟩
  · subst M; exact ⟨N, hs, .refl⟩
  · exact ⟨P, hp, ht.tail hs⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Replace the first reduction by a standard derivation and induct on the final head step. For a root contraction, invert the application rule and then the abstraction rule. Their head prefixes, followed by the exposed root contraction, form a nonempty head reduction from $L$. Remove its first step. The remaining head steps followed by the substitution of the related argument into the related body reach $N$ by beta-reduction. For a head step in the operator, apply the induction hypothesis to the operator subderivation, lift the resulting head step through application, and prepend the application's head prefix. This is again a nonempty head reduction. After its first step, finish the operator and argument reductions. These two cases prove the assertion.
    \end{proof}
-/
theorem Standard.pull_head {M N : AlphaTerm} (h : HeadStep M N)
    (L : AlphaTerm) (hs : Standard L M) :
    ∃ P, HeadStep L P ∧ Relation.ReflTransGen Beta P N := by
  induction h generalizing L with
  | contract x A B =>
    obtain ⟨R, S, hp, hR, hS⟩ := hs.app_inv rfl
    obtain ⟨y, C, D, hc, hCD, he⟩ := hR.lam_inv_any rfl
    obtain ⟨P, hP, ht⟩ := HeadSteps.then_step (hp.trans (hc.app_left S)) (HeadStep.contract y C S)
    refine ⟨P, hP, ht.beta_steps.trans ?_⟩
    have hb := (hCD.subst hS y).beta_steps
    simpa only [contract_eq D A B y x he] using hb
  | app_left A h ih =>
    obtain ⟨R, S, hp, hR, hS⟩ := hs.app_inv rfl
    obtain ⟨R', hR', ht⟩ := ih R hR
    obtain ⟨P, hP, hrest⟩ := HeadSteps.then_step hp (HeadStep.app_left S hR')
    exact ⟨P, hP, hrest.beta_steps.trans (beta_steps_app ht hS.beta_steps)⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Moving a head step to the front
-/
theorem pull_head_step {L M N : AlphaTerm} (hb : Relation.ReflTransGen Beta L M)
    (hh : HeadStep M N) : ∃ P, HeadStep L P ∧ Relation.ReflTransGen Beta P N :=
  Standard.pull_head hh L (standard_of_beta_steps hb)

/-- A stage starts with a head step, followed by any finite beta reduction. -/
def HeadStage (M N : AlphaTerm) : Prop :=
  ∃ A, HeadStep M A ∧ Relation.ReflTransGen Beta A N

/-- A finite head-normalizing path bounds the number of these stages, even after an initial beta path. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    A numerical output would give a finite head reduction to an abstraction by head exposure. Prove the stronger assertion
    that, whenever $M$ has such a head reduction and $M\to_\beta^*S_0$, no infinite sequence as displayed can start at
    $S_0$. Induct on the length of the chosen head reduction from $M$. If the length is zero, $M$ is already an abstraction.
    Moving the first stage's head step to the front would give a head step from this abstraction, which is impossible.
    Otherwise write the first head step as $\LambdaHeadStep{M}{N}$. Moving the first stage's head step to the front gives
    another head step from $M$, followed by a beta-reduction to $S_1$. Head steps are deterministic: an abstraction cannot
    step, and an application either has a root redex or inherits the unique head step of its operator. Thus the new head
    step also ends at $N$. Apply the induction hypothesis to the shorter head reduction from $N$ and the shifted sequence
    $S_1,S_2,\ldots$.
    \end{proof}
-/
theorem no_infinite_head_stages {M A : AlphaTerm} {x : ℕ}
    (hn : HeadSteps M (lam x A)) (f : ℕ → AlphaTerm)
    (hf : Relation.ReflTransGen Beta M (f 0))
    (hs : ∀ k, HeadStage (f k) (f (k + 1))) : False := by
  induction hn using Relation.ReflTransGen.head_induction_on generalizing f with
  | refl =>
    obtain ⟨B, hb, _⟩ := hs 0
    obtain ⟨P, hp, _⟩ := pull_head_step hf hb
    exact hp.not_lam rfl
  | @head M N hh ht ih =>
    obtain ⟨B, hb, htail⟩ := hs 0
    obtain ⟨P, hp, hP⟩ := pull_head_step hf hb
    have he := hh.deterministic hp
    subst P
    exact ih (fun k => f (k + 1)) (hP.trans htail) (fun k => hs (k + 1))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Infinite head stages exclude numerical output
-/
theorem no_numeral_of_head_stages (f : ℕ → AlphaTerm)
    (hs : ∀ k, HeadStage (f k) (f (k + 1))) (n : ℕ) :
    ¬ Relation.ReflTransGen Beta (f 0) (numeral n) := by
  intro hn
  obtain ⟨x, A, ha⟩ := head_exposes_numeral hn
  exact no_infinite_head_stages ha f .refl hs

/-- A numerical normal form reached from a term is also reached from every finite reduct. -/
theorem numeral_after_reduction {L M : AlphaTerm} {n : ℕ}
    (h : Relation.ReflTransGen Beta L M) (hn : Relation.ReflTransGen Beta L (numeral n)) :
    Relation.ReflTransGen Beta M (numeral n) := by
  obtain ⟨P, hP, hnP⟩ := beta_confluent h hn
  have he := (numeral_normal n).eq_of_steps hnP
  simpa only [he] using hP

end PolishSpaceBook.NamedLambda.AlphaTerm
