module

public import PolishSpaceBook.LambdaReductionSubstitution

@[expose] public section

/-!
# Parallel beta-reduction on alpha-classes

Parallel contraction reduces a body and its argument before substituting.
All operations are those of the named calculus, descended to alpha-classes.
-/
namespace PolishSpaceBook.NamedLambda
namespace AlphaTerm

def namedConstructor : AlphaTerm → ℕ := Quotient.lift Term.constructorTag
  (fun M N h => ((Term.alpha_iff_renameEq M N).mp h).constructorTag_eq)

@[simp] theorem namedConstructor_var (x : ℕ) : (var x).namedConstructor = 0 := rfl
@[simp] theorem namedConstructor_app (M N : AlphaTerm) : (app M N).namedConstructor = 1 := by
  refine Quotient.inductionOn₂ M N ?_; intro M N; rfl
@[simp] theorem namedConstructor_lam (x : ℕ) (M : AlphaTerm) : (lam x M).namedConstructor = 2 := by
  refine Quotient.inductionOn M ?_; intro M; rfl

theorem app_inj {M N M' N' : AlphaTerm} (h : app M N = app M' N') : M = M' ∧ N = N' := by
  revert h
  refine Quotient.inductionOn₂ M N ?_
  intro A B
  refine Quotient.inductionOn₂ M' N' ?_
  intro C D h
  have hr : Term.RenameEq (Term.app A B) (Term.app C D) := Quotient.exact h
  cases hr.nameRel with
  | app hA hB => exact ⟨Quotient.sound hA.eq_renameEq, Quotient.sound hB.eq_renameEq⟩

theorem var_ne_app (x : ℕ) (M N : AlphaTerm) : var x ≠ app M N := by
  intro h; have ht := congrArg namedConstructor h; simp only [namedConstructor_var, namedConstructor_app] at ht; cases ht

theorem var_ne_lam (x y : ℕ) (M : AlphaTerm) : var x ≠ lam y M := by
  intro h; have ht := congrArg namedConstructor h; simp only [namedConstructor_var, namedConstructor_lam] at ht; cases ht

theorem app_ne_lam (M N : AlphaTerm) (x : ℕ) (P : AlphaTerm) : app M N ≠ lam x P := by
  intro h; have ht := congrArg namedConstructor h; simp only [namedConstructor_app, namedConstructor_lam] at ht; cases ht

theorem subst_self (M : AlphaTerm) (x : ℕ) : M.subst x (var x) = M := by
  refine Quotient.inductionOn M ?_
  intro M
  exact congrArg mk (Term.subst_self M x)

theorem lam_inj {M N : AlphaTerm} (x : ℕ) (h : lam x M = lam x N) : M = N := by
  have hh := contract_eq M N (var x) x x h
  simpa only [subst_self] using hh

@[simp] theorem fv_app (M N : AlphaTerm) : (app M N).fv = M.fv ∪ N.fv := by
  refine Quotient.inductionOn₂ M N ?_; intro M N; rfl
@[simp] theorem fv_lam (x : ℕ) (M : AlphaTerm) : (lam x M).fv = M.fv.erase x := by
  refine Quotient.inductionOn M ?_; intro M; rfl

theorem fv_subst_subset (M N : AlphaTerm) (x : ℕ) :
    (M.subst x N).fv ⊆ M.fv.erase x ∪ N.fv := by
  refine Quotient.inductionOn₂ M N ?_
  intro M N v hv
  change v ∈ (M.subst x N).fv at hv
  change v ∈ M.fv.erase x ∪ N.fv
  rcases (Term.mem_fv_subst M x N v).mp hv with h | h
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h.2, h.1⟩)
  · exact Finset.mem_union_right _ h.2

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    To prove that a computed value is unique, we introduce \termdefine{parallel beta-reduction}. This is the least relation $\ParallelBeta{M}{N}$ satisfying
    $$\begin{gathered}
    \dfrac{}{\ParallelBeta{x}{x}},\qquad
    \dfrac{\ParallelBeta{M}{M'}\quad\ParallelBeta{N}{N'}}{\ParallelBeta{MN}{M'N'}},\\[6pt]
    \dfrac{\ParallelBeta{M}{M'}}{\ParallelBeta{\lambdaab{x}{M}}{\lambdaab{x}{M'}}},\qquad
    \dfrac{\ParallelBeta{M}{M'}\quad\ParallelBeta{N}{N'}}{\ParallelBeta{(\lambdaab{x}{M})N}{\SubstLambda{M'}{x}{N'}}}.
    \end{gathered}$$
    All these rules act on alpha-classes. The application rule may retain a redex at the root, whereas the last rule contracts it after reducing the body and argument in parallel. Induction on a named representative gives $\ParallelBeta{M}{M}$ for every term.
-/
inductive Parallel : AlphaTerm → AlphaTerm → Prop where
  | var (x : ℕ) : Parallel (var x) (var x)
  | app {M M' N N' : AlphaTerm} : Parallel M M' → Parallel N N' → Parallel (app M N) (app M' N')
  | lam (x : ℕ) {M M' : AlphaTerm} : Parallel M M' → Parallel (lam x M) (lam x M')
  | contract (x : ℕ) {M M' N N' : AlphaTerm} : Parallel M M' → Parallel N N' →
      Parallel (app (lam x M) N) (M'.subst x N')

theorem Parallel.refl (M : AlphaTerm) : Parallel M M := by
  refine Quotient.inductionOn M ?_
  intro M
  induction M with
  | var x => exact .var x
  | app M N ihM ihN => exact .app ihM ihN
  | lam x M ih => exact .lam x ih

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Parallel reduction and substitution
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    First, induction on a parallel derivation proves inclusion of free-variable sets. In the contraction rule, use the free-variable formula for substitution and the inclusions for the body and argument. The other rules use unions and deletion of the binder variable.
-/
theorem Parallel.fv_subset {M N : AlphaTerm} (h : Parallel M N) : N.fv ⊆ M.fv := by
  induction h with
  | var x => exact Finset.Subset.refl _
  | app _ _ ihM ihN => simpa only [fv_app] using Finset.union_subset_union ihM ihN
  | lam x _ ih => simpa only [fv_lam] using Finset.erase_subset_erase x ih
  | @contract x M M' N N' _ _ ihM ihN =>
    exact Finset.Subset.trans (fv_subst_subset M' N' x)
      (by simpa only [fv_app, fv_lam] using (Finset.union_subset_union
        (Finset.erase_subset_erase x ihM) ihN))

theorem substs_subst_fresh (M N : AlphaTerm) (z : ℕ) (σ : List (ℕ × AlphaTerm))
    (hz : z ∉ forbidden σ) :
    substs (M.subst z N) σ = (substs M σ).subst z (substs N σ) := by
  induction σ generalizing M N with
  | nil => rfl
  | cons a σ ih =>
    rcases a with ⟨x, R⟩
    have hs : z ≠ x ∧ z ∉ R.fv ∧ z ∉ forbidden σ := by
      simpa only [forbidden, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc] using hz
    simp only [substs, subst_comp M N R z x hs.1 hs.2.1, ih _ _ hs.2.2]

/-- Related final images of variables suffice for two possibly different substitution lists. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For substitution, strengthen the assertion to two finite lists of substitutions. Apply each list from left to right, and assume that the final image of every variable under the first list reduces in parallel to its final image under the second. Induct on the parallel derivation. The variable case is the assumption, and application distributes over both lists.

    At an abstraction, choose one binder fresh for both bodies, every replacement in both lists, and every variable replaced by either list. Rename both bodies to this binder, and prepend that same variable renaming to both lists. The assumption on final variable images still holds: the old binder variable is sent to the final image of the new variable, and every other variable keeps its old image. The induction hypothesis therefore compares the renamed and substituted bodies. Move both lists under the fresh binder and apply the abstraction rule.

    At a contraction, use the same fresh renaming for the original and reduced bodies. The induction hypotheses compare the substituted bodies and the substituted arguments. Repeated use of the substitution composition law moves the fresh binder's substitution past the second list; freshness holds for each entry of that list. Thus the contraction rule produces exactly the second list applied to the original contractum. Singleton lists give the asserted substitution property.
-/
theorem Parallel.substs {M M' : AlphaTerm} (h : Parallel M M')
    (σ τ : List (ℕ × AlphaTerm))
    (hv : ∀ v, Parallel (AlphaTerm.substs (AlphaTerm.var v) σ) (AlphaTerm.substs (AlphaTerm.var v) τ)) :
    Parallel (substs M σ) (substs M' τ) := by
  induction h generalizing σ τ with
  | var x => exact hv x
  | app _ _ ihM ihN =>
    rw [substs_app, substs_app]
    exact .app (ihM σ τ hv) (ihN σ τ hv)
  | @lam y M M' h ih =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ)
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ ∧ z ∉ forbidden τ := by
      simpa only [z, Finset.mem_union, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ)
    have hv' : ∀ v, Parallel (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: σ))
        (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: τ)) := by
      intro v
      simp only [AlphaTerm.substs, subst_var]
      by_cases h : v = y
      · simpa only [ite_eq_left h] using hv z
      · simpa only [ite_eq_right h] using hv v
    rw [lam_rename M y z hz.1, lam_rename M' y z hz.2.1,
      substs_lam_fresh _ z σ hz.2.2.1, substs_lam_fresh _ z τ hz.2.2.2]
    exact .lam z (ih _ _ hv')
  | @contract y M M' N N' hM hN ihM ihN =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ)
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ ∧ z ∉ forbidden τ := by
      simpa only [z, Finset.mem_union, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ)
    have hv' : ∀ v, Parallel (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: σ))
        (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: τ)) := by
      intro v
      simp only [AlphaTerm.substs, subst_var]
      by_cases h : v = y
      · simpa only [ite_eq_left h] using hv z
      · simpa only [ite_eq_right h] using hv v
    have hl := lam_rename M' y z hz.2.1
    rw [substs_app, lam_rename M y z hz.1, substs_lam_fresh _ z σ hz.2.2.1,
      contract_eq M' (M'.subst y (AlphaTerm.var z)) N' y z hl,
      substs_subst_fresh _ _ z τ hz.2.2.2]
    exact .contract z (ihM _ _ hv') (ihN σ τ hv)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Parallel reduction and substitution
-/
theorem Parallel.subst {M M' N N' : AlphaTerm} (hM : Parallel M M')
    (hN : Parallel N N') (x : ℕ) : Parallel (M.subst x N) (M'.subst x N') := by
  apply Parallel.substs hM [(x, N)] [(x, N')]
  intro v
  simp only [AlphaTerm.substs, subst_var]
  by_cases h : v = x
  · simpa only [ite_eq_left h] using hN
  · simp only [ite_eq_right h]; exact .var v

theorem parallel_of_beta {M N : AlphaTerm} (h : Beta M N) : Parallel M N := by
  induction h with
  | contract x M N => exact .contract x (.refl M) (.refl N)
  | app_left N _ ih => exact .app ih (.refl N)
  | app_right M _ ih => exact .app (.refl M) ih
  | lam x _ ih => exact .lam x ih

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Every beta step is parallel: use reflexivity on the unchanged parts of a root contraction and then lift through contexts. Conversely, induct on a parallel derivation. Application and abstraction lift the finite beta-reductions supplied by the induction hypotheses. For a parallel contraction, first reduce the body under its binder and reduce the argument, then perform one root contraction. Concatenating these finite reductions proves the last assertion.
-/
theorem Parallel.beta_steps {M N : AlphaTerm} (h : Parallel M N) :
    Relation.ReflTransGen Beta M N := by
  induction h with
  | var x => exact .refl
  | app _ _ ihM ihN => exact beta_steps_app ihM ihN
  | lam x _ ih => exact beta_steps_lam x ih
  | contract x _ _ ihM ihN =>
    exact .tail (beta_steps_app (beta_steps_lam x ihM) ihN) (.contract x _ _)


theorem Parallel.var_inv {P Q : AlphaTerm} (h : Parallel P Q)
    {x : ℕ} (he : P = AlphaTerm.var x) : Q = AlphaTerm.var x := by
  cases h with
  | var y => exact he
  | app hM hN => exact False.elim (var_ne_app _ _ _ he.symm)
  | lam y hM => exact False.elim (var_ne_lam _ _ _ he.symm)
  | contract y hM hN => exact False.elim (var_ne_app _ _ _ he.symm)

theorem Parallel.app_inv {S Q : AlphaTerm} (h : Parallel S Q)
    {P A : AlphaTerm} (he : S = AlphaTerm.app P A) :
    (∃ P' A', Q = AlphaTerm.app P' A' ∧ Parallel P P' ∧ Parallel A A') ∨
    (∃ y B B' A', P = AlphaTerm.lam y B ∧ Parallel B B' ∧ Parallel A A' ∧
      Q = B'.subst y A') := by
  cases h with
  | var x => exact False.elim (var_ne_app _ _ _ he)
  | @app M M' N N' hM hN =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact Or.inl ⟨M', N', rfl, hM, hN⟩
  | lam y hM => exact False.elim (app_ne_lam _ _ _ _ he.symm)
  | @contract y M M' N N' hM hN =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact Or.inr ⟨y, M, M', N', rfl, hM, hN, rfl⟩

/-- Invert a parallel abstraction step using any prescribed source binder. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Parallel abstraction inversion
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Binder renaming preserves the outer constructor, so a variable, an application and an abstraction belong to distinct alpha-classes. Hence the last rule must be an abstraction rule. Write its source and target as $\lambdaab{y}{N}$ and $\lambdaab{y}{N'}$, where $\ParallelBeta{N}{N'}$. If $y=x$, equality of the source abstractions implies equality of their bodies: substitute the variable $x$ into both bodies, using independence of contraction from the binder name and the identity substitution. The assertion follows.

    Suppose $y\ne x$. Since $\lambdaab{y}{N}=\lambdaab{x}{M}$, their free-variable sets agree. The right-hand side has no free $x$, so $x\notin\FreeVarsLambda{N}$; otherwise $x$ would remain free on the left. Parallel reduction introduces no new free variables, hence also $x\notin\FreeVarsLambda{N'}$. Rename both binders from $y$ to $x$. Equality of abstractions with this fixed binder gives $\SubstLambda{N}{y}{x}=M$. The parallel substitution lemma gives
    $$
    \ParallelBeta{\SubstLambda{N}{y}{x}}{\SubstLambda{N'}{y}{x}}.
    $$
    Choose $M'=\SubstLambda{N'}{y}{x}$. The target renaming proves the required equality for $Q$.
-/
theorem Parallel.lam_inv {P Q : AlphaTerm} (h : Parallel P Q)
    {y : ℕ} {M : AlphaTerm} (he : P = AlphaTerm.lam y M) :
    ∃ M', Q = AlphaTerm.lam y M' ∧ Parallel M M' := by
  cases h with
  | var x => exact False.elim (var_ne_lam _ _ _ he)
  | app hM hN => exact False.elim (app_ne_lam _ _ _ _ he)
  | contract x hM hN => exact False.elim (app_ne_lam _ _ _ _ he)
  | @lam z N N' hN =>
    by_cases hzy : z = y
    · subst z
      have hm := lam_inj y he
      subst M
      exact ⟨N', rfl, hN⟩
    · have hyN : y ∉ N.fv := by
        intro hy
        have hf := congrArg AlphaTerm.fv he
        have hy' : y ∈ (AlphaTerm.lam z N).fv := by
          simpa only [fv_lam, Finset.mem_erase] using And.intro (Ne.symm hzy) hy
        rw [hf, fv_lam] at hy'
        exact (Finset.mem_erase.mp hy').1 rfl
      have hyN' : y ∉ N'.fv := fun hy => hyN (hN.fv_subset hy)
      have hs : N.subst z (AlphaTerm.var y) = M :=
        lam_inj y ((lam_rename N z y hyN).symm.trans he)
      refine ⟨N'.subst z (AlphaTerm.var y), lam_rename N' z y hyN', ?_⟩
      rw [← hs]
      exact hN.subst (.refl _) z


/-- Every pair of parallel steps has a common parallel successor. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Diamond property of parallel reduction
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Induct on the first parallel derivation. A variable only reduces to itself. For an abstraction, use parallel abstraction inversion to put the second derivation under the first derivation's binder. Apply the induction hypothesis to the bodies and lift the resulting two steps through that binder.

    Suppose the first derivation uses the application rule. The second derivation either also retains the root or contracts it. If both retain it, join the two operator reductions and the two argument reductions by their induction hypotheses, and combine the results by the application rule.

    If the second derivation contracts the root, the common operator is an abstraction. Write it with binder $x$, and use abstraction inversion to write the first operator result with the same binder. Apply the operator induction hypothesis to the first operator step and to the abstraction step formed from the second derivation's body step. Their common successor is again an abstraction. Inversion on both joining steps, followed by equality of bodies with a fixed binder, gives parallel steps from both resulting bodies to one body $R$. Independently join the argument steps at $S$. The application result contracts in parallel to $\SubstLambda{R}{x}{S}$, while the other result reaches that same term by the parallel substitution lemma.

    Finally, suppose the first derivation contracts the root. If the second retains it, invert its operator step using the first binder. The body and argument induction hypotheses give common successors $R$ and $S$. Parallel substitution joins the first contractum to $\SubstLambda{R}{x}{S}$, and parallel contraction joins the second result to it. If both derivations contract, their binders may differ. Lift the second body step to an abstraction step and invert it using the first binder. Independence of contraction from the binder name expresses the second contractum with this binder as well. Now apply the body and argument induction hypotheses and the parallel substitution lemma on both sides. These cases exhaust the four rules.
-/
theorem Parallel.diamond {M N : AlphaTerm} (h : Parallel M N) :
    ∀ {P}, Parallel M P → ∃ Q, Parallel N Q ∧ Parallel P Q := by
  induction h with
  | var x =>
    intro P hP
    have he := hP.var_inv rfl
    subst P
    exact ⟨_, .refl _, .refl _⟩
  | @lam y M M' hM ih =>
    intro P hP
    obtain ⟨M'', rfl, hM''⟩ := hP.lam_inv rfl
    obtain ⟨R, hR, hR'⟩ := ih hM''
    exact ⟨AlphaTerm.lam y R, .lam y hR, .lam y hR'⟩
  | @app M M' N N' hM hN ihM ihN =>
    intro P hP
    rcases hP.app_inv rfl with ⟨M'', N'', rfl, hM'', hN''⟩ |
        ⟨y, B, B', N'', he, hB, hN'' , rfl⟩
    · obtain ⟨R, hR, hR'⟩ := ihM hM''
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      exact ⟨AlphaTerm.app R S, .app hR hS, .app hR' hS'⟩
    · subst M
      obtain ⟨C, rfl, hC⟩ := hM.lam_inv rfl
      obtain ⟨L, hL, hL'⟩ := ihM (.lam y hB)
      obtain ⟨D, rfl, hD⟩ := hL.lam_inv rfl
      obtain ⟨D', heD, hD'⟩ := hL'.lam_inv rfl
      have hd := lam_inj y heD
      subst D'
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      exact ⟨D.subst y S, .contract y hD hS, hD'.subst hS' y⟩
  | @contract y M M' N N' hM hN ihM ihN =>
    intro P hP
    rcases hP.app_inv rfl with ⟨L, N'', rfl, hL, hN''⟩ |
        ⟨z, B, B', N'', he, hB, hN'', rfl⟩
    · obtain ⟨M'', rfl, hM''⟩ := hL.lam_inv rfl
      obtain ⟨R, hR, hR'⟩ := ihM hM''
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      exact ⟨R.subst y S, hR.subst hS y, .contract y hR' hS'⟩
    · obtain ⟨D, heD, hD⟩ := (Parallel.lam z hB).lam_inv he.symm
      obtain ⟨R, hR, hR'⟩ := ihM hD
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      refine ⟨R.subst y S, hR.subst hS y, ?_⟩
      rw [contract_eq B' D N'' z y heD]
      exact hR'.subst hS' y


/-- One parallel step can be moved across any finite parallel reduction. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    First move one parallel step across a finite sequence of parallel steps with the same source. For the empty sequence, its endpoint already takes the given step. To add one more step to the sequence, use the diamond property on that step and the joining step constructed so far, and append the new joining step on the opposite side. Induction gives a finite parallel reduction from the endpoint of the original single step and one parallel step from the endpoint of the original sequence, with a common target.
-/
theorem parallel_strip {M N P : AlphaTerm} (h : Parallel M N)
    (hs : Relation.ReflTransGen Parallel M P) :
    ∃ Q, Relation.ReflTransGen Parallel N Q ∧ Parallel P Q := by
  induction hs with
  | refl => exact ⟨N, .refl, h⟩
  | tail hs ht ih =>
    obtain ⟨R, hNR, hPR⟩ := ih
    obtain ⟨S, hRS, hPS⟩ := hPR.diamond ht
    exact ⟨S, .tail hNR hRS, hPS⟩

/-- Iterating the strip construction fills a finite rectangle of parallel steps. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Now induct on the length of one of two finite parallel reductions with the same source. The empty case is immediate. For the next step, use the construction just proved to move it across the joining sequence supplied by the induction hypothesis. This joins the new endpoint to the other reduction's endpoint. Finite parallel reduction and finite beta-reduction have the same endpoints, so beta-reduction is confluent as well.
-/
theorem parallel_steps_confluent {M N P : AlphaTerm}
    (h : Relation.ReflTransGen Parallel M N) (h' : Relation.ReflTransGen Parallel M P) :
    ∃ Q, Relation.ReflTransGen Parallel N Q ∧ Relation.ReflTransGen Parallel P Q := by
  induction h with
  | refl => exact ⟨P, h', .refl⟩
  | tail hs ht ih =>
    obtain ⟨R, hR, hR'⟩ := ih
    obtain ⟨S, hS, hS'⟩ := parallel_strip ht hR
    exact ⟨S, hS, .tail hR' hS'⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Parallel reduction and substitution
-/
theorem parallel_steps_iff_beta_steps {M N : AlphaTerm} :
    Relation.ReflTransGen Parallel M N ↔ Relation.ReflTransGen Beta M N := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail hs ht ih => exact ih.trans ht.beta_steps
  · intro h
    induction h with
    | refl => exact .refl
    | tail hs ht ih => exact .tail ih (parallel_of_beta ht)

/-- Confluence of finite beta-reduction on alpha-classes. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Church--Rosser theorem
-/
theorem beta_confluent {M N P : AlphaTerm}
    (h : Relation.ReflTransGen Beta M N) (h' : Relation.ReflTransGen Beta M P) :
    ∃ Q, Relation.ReflTransGen Beta N Q ∧ Relation.ReflTransGen Beta P Q := by
  obtain ⟨Q, hQ, hQ'⟩ := parallel_steps_confluent
    (parallel_steps_iff_beta_steps.mpr h) (parallel_steps_iff_beta_steps.mpr h')
  exact ⟨Q, parallel_steps_iff_beta_steps.mp hQ, parallel_steps_iff_beta_steps.mp hQ'⟩

/-- Church--Rosser: beta-convertibility is exactly the existence of a common reduct. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Church--Rosser theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    If two terms have a common reduct, they are beta-convertible by going forward to that reduct and backward to the other term. Conversely, induct on a derivation in the equivalence relation generated by beta-reduction. A single step and a reflexive step have an immediate common reduct, and symmetry exchanges the two reductions. For transitivity, suppose the first pair has common reduct $R$ and the second pair has common reduct $S$. The shared middle term reduces to both $R$ and $S$. Confluence supplies a common reduct of these two terms; concatenate the corresponding reductions from the two outer terms. This proves the equivalence.
-/
theorem church_rosser {M N : AlphaTerm} :
    Relation.EqvGen Beta M N ↔
      ∃ P, Relation.ReflTransGen Beta M P ∧ Relation.ReflTransGen Beta N P := by
  constructor
  · intro h
    induction h with
    | rel M N h => exact ⟨N, .single h, .refl⟩
    | refl M => exact ⟨M, .refl, .refl⟩
    | symm M N h ih =>
      obtain ⟨P, hMP, hNP⟩ := ih
      exact ⟨P, hNP, hMP⟩
    | trans M N P hMN hNP ihMN ihNP =>
      obtain ⟨R, hMR, hNR⟩ := ihMN
      obtain ⟨S, hNS, hPS⟩ := ihNP
      obtain ⟨T, hRT, hST⟩ := beta_confluent hNR hNS
      exact ⟨T, hMR.trans hRT, hPS.trans hST⟩
  · rintro ⟨P, hMP, hNP⟩
    have lift : ∀ {A B}, Relation.ReflTransGen Beta A B → Relation.EqvGen Beta A B := by
      intro A B h
      induction h with
      | refl => exact .refl _
      | tail hs ht ih => exact .trans _ _ _ ih (.rel _ _ ht)
    exact .trans _ _ _ (lift hMP) (.symm _ _ (lift hNP))

/-- A normal form admits no one-step beta-reduction. -/
def Normal (M : AlphaTerm) : Prop := ∀ N, ¬ Beta M N

theorem Normal.eq_of_steps {M N : AlphaTerm} (hM : Normal M)
    (h : Relation.ReflTransGen Beta M N) : N = M := by
  induction h with
  | refl => rfl
  | tail hs ht ih =>
    subst_vars
    exact False.elim (hM _ ht)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Uniqueness of normal forms
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    By confluence the two normal forms have a common reduct. A finite reduction starting at a normal form has length zero, since otherwise its first step would contradict normality. Hence each normal form equals the common reduct, and they equal each other.
-/
theorem normal_form_unique {M N P : AlphaTerm}
    (hN : Relation.ReflTransGen Beta M N) (hP : Relation.ReflTransGen Beta M P)
    (hn : Normal N) (hp : Normal P) : N = P := by
  obtain ⟨Q, hQ, hQ'⟩ := beta_confluent hN hP
  exact (hn.eq_of_steps hQ).symm.trans (hp.eq_of_steps hQ')

end AlphaTerm
end PolishSpaceBook.NamedLambda
