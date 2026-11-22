module

public import PolishSpaceBook.LambdaHeadStandardization
public import PolishSpaceBook.LambdaOracleReduction

@[expose] public section

/-! # Head exposure with an input name

A query at the operator spine may first reduce its argument to a numeral.
This groups an existing finite beta/query reduction into one head step; it
introduces neither a new computation language nor a new reduction rule.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Substitutions that preserve the input name preserve its finite reductions. -/
theorem oracle_steps_substs_preserving {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N) (σ : List (ℕ × AlphaTerm))
    (hσ : PreservesInput σ) :
    Relation.ReflTransGen (OracleStep p) (AlphaTerm.substs M σ) (AlphaTerm.substs N σ) := by
  induction h with
  | refl => exact .refl
  | tail _ ht ih =>
    apply ih.trans
    apply ht.substs_simulate σ
    intro n
    rw [substs_input σ hσ]
    exact .single (.query n)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To exclude numerical outputs from an endlessly unsuccessful search, we need the head-exposure argument also for input
    queries. Fix a name $p$. A \termdefine{head step with input queries}, written $\LambdaInputHeadStep{p}{M}{N}$, is a root
    beta contraction, such a head step in the operator of an application, or a grouped query step
    $$\frac{\LambdaInputSteps{p}{A}{\ChurchNumeral{n}}}
     {\LambdaInputHeadStep{p}{oA}{\ChurchNumeral{p(n)}}}.$$
    The last rule groups a finite reduction of the query argument and one actual query. It is an abbreviation for existing
    reductions. Write $\LambdaInputHeadSteps{p}{M}{N}$ for finitely many of these head steps. No head step enters an
    abstraction body.
-/
inductive OracleHeadStep (p : ℕ → ℕ) : AlphaTerm → AlphaTerm → Prop where
  | contract (x : ℕ) (M N : AlphaTerm) :
      OracleHeadStep p (app (lam x M) N) (M.subst x N)
  | query {A : AlphaTerm} (n : ℕ) : Relation.ReflTransGen (OracleStep p) A (numeral n) →
      OracleHeadStep p (app (var 0) A) (numeral (p n))
  | app_left {M M' : AlphaTerm} (N : AlphaTerm) : OracleHeadStep p M M' →
      OracleHeadStep p (app M N) (app M' N)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To exclude numerical outputs from an endlessly unsuccessful search, we need the head-exposure argument also for input
    queries. Fix a name $p$. A \termdefine{head step with input queries}, written $\LambdaInputHeadStep{p}{M}{N}$, is a root
    beta contraction, such a head step in the operator of an application, or a grouped query step
    $$\frac{\LambdaInputSteps{p}{A}{\ChurchNumeral{n}}}
     {\LambdaInputHeadStep{p}{oA}{\ChurchNumeral{p(n)}}}.$$
    The last rule groups a finite reduction of the query argument and one actual query. It is an abbreviation for existing
    reductions. Write $\LambdaInputHeadSteps{p}{M}{N}$ for finitely many of these head steps. No head step enters an
    abstraction body.
-/
abbrev OracleHeadSteps (p : ℕ → ℕ) := Relation.ReflTransGen (OracleHeadStep p)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To exclude numerical outputs from an endlessly unsuccessful search, we need the head-exposure argument also for input
    queries. Fix a name $p$. A \termdefine{head step with input queries}, written $\LambdaInputHeadStep{p}{M}{N}$, is a root
    beta contraction, such a head step in the operator of an application, or a grouped query step
    $$\frac{\LambdaInputSteps{p}{A}{\ChurchNumeral{n}}}
     {\LambdaInputHeadStep{p}{oA}{\ChurchNumeral{p(n)}}}.$$
    The last rule groups a finite reduction of the query argument and one actual query. It is an abbreviation for existing
    reductions. Write $\LambdaInputHeadSteps{p}{M}{N}$ for finitely many of these head steps. No head step enters an
    abstraction body.
-/
theorem OracleHeadStep.oracle_steps {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadStep p M N) :
    Relation.ReflTransGen (OracleStep p) M N := by
  induction h with
  | contract x A B => exact .single (.beta (.contract x A B))
  | query n h => exact (oracle_steps_app_right (var 0) h).tail (.query n)
  | app_left A _ ih => exact oracle_steps_app_left ih A

theorem OracleHeadSteps.oracle_steps {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadSteps p M N) :
    Relation.ReflTransGen (OracleStep p) M N := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.trans h.oracle_steps

theorem HeadStep.oracleHead {M N : AlphaTerm} (h : HeadStep M N) (p : ℕ → ℕ) :
    OracleHeadStep p M N := by
  induction h with
  | contract x A B => exact .contract x A B
  | app_left A _ ih => exact .app_left A ih

theorem OracleHeadStep.substs {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadStep p M N)
    (σ : List (ℕ × AlphaTerm)) (hσ : PreservesInput σ) :
    OracleHeadStep p (AlphaTerm.substs M σ) (AlphaTerm.substs N σ) := by
  induction h with
  | contract x A B =>
    obtain ⟨z, C, D, hs, ht⟩ := substs_redex A B x σ
    rw [hs, ht]
    exact .contract z C D
  | query n hn =>
    rw [substs_app, substs_input σ hσ, substs_closed _ (numeral_closed (p n))]
    apply OracleHeadStep.query n
    simpa only [substs_closed _ (numeral_closed n)] using oracle_steps_substs_preserving hn σ hσ
  | app_left A _ ih => rw [substs_app, substs_app]; exact .app_left _ ih

theorem OracleHeadSteps.substs {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadSteps p M N)
    (σ : List (ℕ × AlphaTerm)) (hσ : PreservesInput σ) :
    OracleHeadSteps p (AlphaTerm.substs M σ) (AlphaTerm.substs N σ) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (h.substs σ hσ)

theorem OracleHeadSteps.app_left {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadSteps p M N) (A : AlphaTerm) :
    OracleHeadSteps p (app M A) (app N A) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.app_left _ h)

theorem OracleHeadStep.not_lam {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadStep p M N)
    {x : ℕ} {A : AlphaTerm} (he : M = lam x A) : False := by
  cases h <;> exact app_ne_lam _ _ _ _ he

theorem OracleHeadStep.not_var {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadStep p M N)
    {x : ℕ} (he : M = var x) : False := by
  cases h <;> exact var_ne_app _ _ _ he.symm

theorem OracleHeadStep.app_inv {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleHeadStep p M N)
    {P A : AlphaTerm} (he : M = app P A) :
    (∃ x B, P = lam x B ∧ N = B.subst x A) ∨
    (P = var 0 ∧ ∃ n, Relation.ReflTransGen (OracleStep p) A (numeral n) ∧ N = numeral (p n)) ∨
    (∃ Q, OracleHeadStep p P Q ∧ N = app Q A) := by
  cases h with
  | contract x B C =>
    obtain ⟨heP, rfl⟩ := app_inj he
    exact Or.inl ⟨x, B, heP.symm, rfl⟩
  | query n hn =>
    obtain ⟨heP, rfl⟩ := app_inj he
    exact Or.inr (Or.inl ⟨heP.symm,n,hn,rfl⟩)
  | @app_left P Q B hp =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact Or.inr (Or.inr ⟨Q,hp,rfl⟩)


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Determinism of head steps with input queries
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Expand a grouped query into its argument reduction followed by the query; lift through the operator context when necessary. For determinism, inspect the operator. An abstraction permits the root contraction and has no head step of its own. The input variable permits a grouped query and has no head step of its own. If the query argument reduces to two numerals, confluence makes their values equal, so both queries give the same answer. In every other case, any head step comes from the operator, where induction gives uniqueness.
    \end{proof}
-/
theorem OracleHeadStep.deterministic {p : ℕ → ℕ} {M N P : AlphaTerm}
    (h : OracleHeadStep p M N) (h' : OracleHeadStep p M P) : N = P := by
  induction h generalizing P with
  | contract x A B =>
    rcases h'.app_inv rfl with ⟨y,C,he,rfl⟩ | ⟨he,hn⟩ | ⟨Q,hQ,rfl⟩
    · exact contract_eq A C B x y he
    · exact False.elim (var_ne_lam _ _ _ he.symm)
    · exact False.elim (hQ.not_lam rfl)
  | query n hn =>
    rcases h'.app_inv rfl with ⟨y,C,he,rfl⟩ | ⟨he,m,hm,rfl⟩ | ⟨Q,hQ,rfl⟩
    · exact False.elim (var_ne_lam _ _ _ he)
    · exact congrArg (fun i => numeral (p i)) (oracle_numeral_output_unique hn hm)
    · exact False.elim (hQ.not_var rfl)
  | app_left A h ih =>
    rcases h'.app_inv rfl with ⟨y,C,he,rfl⟩ | ⟨he,hn⟩ | ⟨Q,hQ,rfl⟩
    · exact False.elim (h.not_lam he)
    · exact False.elim (h.not_var he)
    · exact congrArg (fun X => app X A) (ih hQ)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use the inductive standard-reduction rules of §{sec:lambda-head-exposure}, replacing their head prefixes by the present
    head prefixes. More explicitly, define $\LambdaInputStandardSteps{p}{L}{M}$ by
    $$\frac{\LambdaInputHeadSteps{p}{L}{x}}{\LambdaInputStandardSteps{p}{L}{x}},$$
    $$\frac{\LambdaInputHeadSteps{p}{L}{AB}\quad
     \LambdaInputStandardSteps{p}{A}{C}\quad\LambdaInputStandardSteps{p}{B}{D}}
     {\LambdaInputStandardSteps{p}{L}{CD}},$$
    $$\frac{\LambdaInputHeadSteps{p}{L}{\lambdaab{x}{A}}\quad
     \LambdaInputStandardSteps{p}{A}{B}\quad x\ne o}
     {\LambdaInputStandardSteps{p}{L}{\lambdaab{x}{B}}}.$$
    The binder restriction keeps the input variable free during the body reduction; fresh alpha-renaming supplies such a
    binder for every abstraction.
-/
inductive OracleStandard (p : ℕ → ℕ) : AlphaTerm → AlphaTerm → Prop where
  | var {L : AlphaTerm} (x : ℕ) : OracleHeadSteps p L (AlphaTerm.var x) → OracleStandard p L (AlphaTerm.var x)
  | app {L A B C D : AlphaTerm} : OracleHeadSteps p L (AlphaTerm.app A B) →
      OracleStandard p A C → OracleStandard p B D → OracleStandard p L (AlphaTerm.app C D)
  | lam {L A B : AlphaTerm} (x : ℕ) (hx : x ≠ 0) : OracleHeadSteps p L (AlphaTerm.lam x A) →
      OracleStandard p A B → OracleStandard p L (AlphaTerm.lam x B)

theorem OracleStandard.refl (p : ℕ → ℕ) (M : AlphaTerm) : OracleStandard p M M := by
  apply induction_fresh {0} (fun x => .var x .refl)
    (fun _ _ hA hB => .app .refl hA hB) _ M
  intro x M hx hM
  exact .lam x (by simpa using hx) .refl hM

theorem OracleStandard.oracle_steps {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleStandard p M N) :
    Relation.ReflTransGen (OracleStep p) M N := by
  induction h with
  | var _ h => exact h.oracle_steps
  | app h _ _ ihA ihB => exact h.oracle_steps.trans (oracle_steps_app ihA ihB)
  | lam x hx h _ ih => exact h.oracle_steps.trans (oracle_steps_lam x hx ih)

theorem OracleStandard.head_prefix {p : ℕ → ℕ} {L M N : AlphaTerm} (h : OracleHeadSteps p L M) (hs : OracleStandard p M N) :
    OracleStandard p L N := by
  cases hs with
  | var x h' => exact .var x (h.trans h')
  | app h' hA hB => exact .app (h.trans h') hA hB
  | lam x hx h' hA => exact .lam x hx (h.trans h') hA

theorem oracle_steps_fv_subset {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N) : N.fv ⊆ M.fv := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ h ih => exact Finset.Subset.trans h.parallel.fv_subset ih

theorem OracleStandard.substs {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleStandard p M N)
    (σ τ : List (ℕ × AlphaTerm)) (hσ : PreservesInput σ) (hτ : PreservesInput τ)
    (hv : ∀ v, OracleStandard p (AlphaTerm.substs (AlphaTerm.var v) σ)
      (AlphaTerm.substs (AlphaTerm.var v) τ)) :
    OracleStandard p (AlphaTerm.substs M σ) (AlphaTerm.substs N τ) := by
  induction h generalizing σ τ with
  | var x hh => exact OracleStandard.head_prefix (hh.substs σ hσ) (hv x)
  | @app L A B C D hh hA hB ihA ihB =>
    have hp := hh.substs σ hσ
    rw [substs_app] at hp ⊢
    exact .app hp (ihA σ τ hσ hτ hv) (ihB σ τ hσ hτ hv)
  | @lam L A B y hy hh hb ih =>
    let z := Term.fresh (A.fv ∪ B.fv ∪ forbidden σ ∪ forbidden τ ∪ {0})
    have hz : z ∉ A.fv ∧ z ∉ B.fv ∧ z ∉ forbidden σ ∧ z ∉ forbidden τ ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (A.fv ∪ B.fv ∪ forbidden σ ∪ forbidden τ ∪ {0})
    have hs : PreservesInput ((y, AlphaTerm.var z) :: σ) := by
      intro a ha; rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact hσ a ha
    have ht : PreservesInput ((y, AlphaTerm.var z) :: τ) := by
      intro a ha; rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact hτ a ha
    have hv' : ∀ v, OracleStandard p (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: σ))
        (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: τ)) := by
      intro v
      simp only [AlphaTerm.substs, subst_var]
      by_cases h : v = y
      · simpa only [ite_eq_left h] using hv z
      · simpa only [ite_eq_right h] using hv v
    have hp := hh.substs σ hσ
    rw [lam_rename A y z hz.1, substs_lam_fresh _ z σ hz.2.2.1] at hp
    rw [lam_rename B y z hz.2.1, substs_lam_fresh _ z τ hz.2.2.2.1]
    exact .lam z hz.2.2.2.2 hp (ih _ _ hs ht hv')

theorem OracleStandard.subst {p : ℕ → ℕ} {M N A B : AlphaTerm}
    (h : OracleStandard p M N) (hab : OracleStandard p A B) (x : ℕ) (hx : x ≠ 0) :
    OracleStandard p (M.subst x A) (N.subst x B) := by
  apply h.substs [(x,A)] [(x,B)]
  · intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hx
  · intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hx
  · intro v
    simp only [AlphaTerm.substs, subst_var]
    by_cases hv : v = x
    · simpa only [ite_eq_left hv] using hab
    · simp only [ite_eq_right hv]; exact .refl _ _

theorem OracleStandard.var_inv {p : ℕ → ℕ} {L M : AlphaTerm} (h : OracleStandard p L M)
    {x : ℕ} (he : M = AlphaTerm.var x) : OracleHeadSteps p L (AlphaTerm.var x) := by
  cases h with
  | var y hh => simpa only [he] using hh
  | app hh hA hB => exact False.elim (var_ne_app _ _ _ he.symm)
  | lam y hy hh hA => exact False.elim (var_ne_lam _ _ _ he.symm)

theorem OracleStandard.app_inv {p : ℕ → ℕ} {L M : AlphaTerm} (h : OracleStandard p L M)
    {C D : AlphaTerm} (he : M = AlphaTerm.app C D) :
    ∃ A B, OracleHeadSteps p L (AlphaTerm.app A B) ∧ OracleStandard p A C ∧ OracleStandard p B D := by
  cases h with
  | var x hh => exact False.elim (var_ne_app _ _ _ he)
  | @app L A B C' D' hh hA hB =>
    obtain ⟨rfl,rfl⟩ := app_inj he
    exact ⟨A,B,hh,hA,hB⟩
  | lam x hx hh hA => exact False.elim (app_ne_lam _ _ _ _ he.symm)

theorem OracleStandard.lam_inv_any {p : ℕ → ℕ} {L M : AlphaTerm} (h : OracleStandard p L M)
    {x : ℕ} {B : AlphaTerm} (he : M = AlphaTerm.lam x B) :
    ∃ y A C, y ≠ 0 ∧ OracleHeadSteps p L (AlphaTerm.lam y A) ∧
      OracleStandard p A C ∧ AlphaTerm.lam y C = AlphaTerm.lam x B := by
  cases h with
  | var y hh => exact False.elim (var_ne_lam _ _ _ he)
  | app hh hA hB => exact False.elim (app_ne_lam _ _ _ _ he)
  | @lam L A C y hy hh hb => exact ⟨y,A,C,hy,hh,hb,he⟩

theorem OracleStandard.lam_inv {p : ℕ → ℕ} {L M : AlphaTerm} (h : OracleStandard p L M)
    {x : ℕ} {B : AlphaTerm} (he : M = AlphaTerm.lam x B) (hx : x ∉ L.fv) :
    ∃ A, OracleHeadSteps p L (AlphaTerm.lam x A) ∧ OracleStandard p A B := by
  obtain ⟨y,A,C,hy,hh,hb,he⟩ := h.lam_inv_any he
  by_cases hyx : y = x
  · subst y
    have he' := lam_inj x he
    subst C
    exact ⟨A,hh,hb⟩
  · have hxA : x ∉ A.fv := by
      intro hA
      have hf : x ∈ (AlphaTerm.lam y A).fv := by
        rw [fv_lam]
        exact Finset.mem_erase.mpr ⟨Ne.symm hyx,hA⟩
      exact hx (oracle_steps_fv_subset hh.oracle_steps hf)
    have hxC : x ∉ C.fv := fun hc => hxA (oracle_steps_fv_subset hb.oracle_steps hc)
    have hc : C.subst y (AlphaTerm.var x) = B :=
      lam_inj x ((lam_rename C y x hxC).symm.trans he)
    refine ⟨A.subst y (AlphaTerm.var x),?_,?_⟩
    · simpa only [← lam_rename A y x hxA] using hh
    · simpa only [hc] using hb.subst (.refl _ (AlphaTerm.var x)) y hy

theorem OracleStandard.contract {p : ℕ → ℕ} {L M N : AlphaTerm} (x : ℕ)
    (h : OracleStandard p L (AlphaTerm.app (AlphaTerm.lam x M) N)) :
    OracleStandard p L (M.subst x N) := by
  obtain ⟨P,A,hp,hP,hA⟩ := h.app_inv rfl
  obtain ⟨y,B,C,hy,hb,hBC,he⟩ := hP.lam_inv_any rfl
  have hh := (hp.trans (hb.app_left A)).tail (OracleHeadStep.contract y B A)
  have hs := OracleStandard.head_prefix hh (hBC.subst hA y hy)
  simpa only [contract_eq C M N y x he] using hs

theorem OracleStandard.query {p : ℕ → ℕ} {L : AlphaTerm} (n : ℕ)
    (h : OracleStandard p L (AlphaTerm.app (AlphaTerm.var 0) (numeral n))) :
    OracleStandard p L (numeral (p n)) := by
  obtain ⟨P,A,hp,hP,hA⟩ := h.app_inv rfl
  have hh := (hp.trans ((hP.var_inv rfl).app_left A)).tail
    (OracleHeadStep.query n hA.oracle_steps)
  exact OracleStandard.head_prefix hh (.refl _ _)

theorem OracleStandard.beta_substs_right {M N : AlphaTerm} (h : Beta M N)
    (p : ℕ → ℕ) (σ : List (ℕ × AlphaTerm)) (L : AlphaTerm)
    (hs : OracleStandard p L (AlphaTerm.substs M σ)) : OracleStandard p L (AlphaTerm.substs N σ) := by
  induction h generalizing σ L with
  | contract y M A =>
    obtain ⟨z,B,C,he,ht⟩ := substs_redex M A y σ
    rw [he] at hs
    rw [ht]
    exact hs.contract z
  | app_left A _ ih =>
    rw [substs_app] at hs ⊢
    obtain ⟨P,Q,hh,hP,hQ⟩ := hs.app_inv rfl
    exact .app hh (ih σ P hP) hQ
  | app_right A _ ih =>
    rw [substs_app] at hs ⊢
    obtain ⟨P,Q,hh,hP,hQ⟩ := hs.app_inv rfl
    exact .app hh hP (ih σ Q hQ)
  | @lam y M N h ih =>
    let z := Term.fresh (M.fv ∪ N.fv ∪ forbidden σ ∪ L.fv ∪ {0})
    have hz : z ∉ M.fv ∧ z ∉ N.fv ∧ z ∉ forbidden σ ∧ z ∉ L.fv ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ N.fv ∪ forbidden σ ∪ L.fv ∪ {0})
    rw [lam_rename M y z hz.1, substs_lam_fresh _ z σ hz.2.2.1] at hs
    rw [lam_rename N y z hz.2.1, substs_lam_fresh _ z σ hz.2.2.1]
    obtain ⟨A,hh,hA⟩ := hs.lam_inv rfl hz.2.2.2.1
    exact .lam z hz.2.2.2.2 hh (ih ((y,AlphaTerm.var z)::σ) A hA)

theorem OracleStandard.oracle_substs_right {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleStep p M N)
    (σ : List (ℕ × AlphaTerm)) (hσ : PreservesInput σ) (L : AlphaTerm)
    (hs : OracleStandard p L (AlphaTerm.substs M σ)) : OracleStandard p L (AlphaTerm.substs N σ) := by
  induction h generalizing σ L with
  | beta hb => exact OracleStandard.beta_substs_right hb p σ L hs
  | query n =>
    rw [substs_app, substs_input σ hσ, substs_closed _ (numeral_closed n)] at hs
    rw [substs_closed _ (numeral_closed (p n))]
    exact hs.query n
  | app_left A _ ih =>
    rw [substs_app] at hs ⊢
    obtain ⟨P,Q,hh,hP,hQ⟩ := hs.app_inv rfl
    exact .app hh (ih σ hσ P hP) hQ
  | app_right A _ ih =>
    rw [substs_app] at hs ⊢
    obtain ⟨P,Q,hh,hP,hQ⟩ := hs.app_inv rfl
    exact .app hh hP (ih σ hσ Q hQ)
  | @lam y hy M N h ih =>
    let z := Term.fresh (M.fv ∪ N.fv ∪ forbidden σ ∪ L.fv ∪ {0})
    have hz : z ∉ M.fv ∧ z ∉ N.fv ∧ z ∉ forbidden σ ∧ z ∉ L.fv ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ N.fv ∪ forbidden σ ∪ L.fv ∪ {0})
    have ht : PreservesInput ((y,AlphaTerm.var z)::σ) := by
      intro a ha; rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact hσ a ha
    rw [lam_rename M y z hz.1, substs_lam_fresh _ z σ hz.2.2.1] at hs
    rw [lam_rename N y z hz.2.1, substs_lam_fresh _ z σ hz.2.2.1]
    obtain ⟨A,hh,hA⟩ := hs.lam_inv rfl hz.2.2.2.1
    exact .lam z hz.2.2.2.2 hh (ih ((y,AlphaTerm.var z)::σ) ht A hA)

theorem OracleStandard.oracle_right {p : ℕ → ℕ} {L M N : AlphaTerm}
    (hs : OracleStandard p L M) (h : OracleStep p M N) : OracleStandard p L N :=
  OracleStandard.oracle_substs_right h [] (by simp [PreservesInput]) L hs

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Use the inductive standard-reduction rules of §{sec:lambda-head-exposure}, replacing their head prefixes by the present
    head prefixes. More explicitly, define $\LambdaInputStandardSteps{p}{L}{M}$ by
    $$\frac{\LambdaInputHeadSteps{p}{L}{x}}{\LambdaInputStandardSteps{p}{L}{x}},$$
    $$\frac{\LambdaInputHeadSteps{p}{L}{AB}\quad
     \LambdaInputStandardSteps{p}{A}{C}\quad\LambdaInputStandardSteps{p}{B}{D}}
     {\LambdaInputStandardSteps{p}{L}{CD}},$$
    $$\frac{\LambdaInputHeadSteps{p}{L}{\lambdaab{x}{A}}\quad
     \LambdaInputStandardSteps{p}{A}{B}\quad x\ne o}
     {\LambdaInputStandardSteps{p}{L}{\lambdaab{x}{B}}}.$$
    The binder restriction keeps the input variable free during the body reduction; fresh alpha-renaming supplies such a
    binder for every abstraction.
-/
theorem standard_of_oracle_steps {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N) : OracleStandard p M N := by
  induction h with
  | refl => exact .refl _ _
  | tail _ h ih => exact ih.oracle_right h


/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Inductive standard reduction with input queries
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fresh-binder induction proves reflexivity, and expanding head steps shows that every standard derivation is a finite beta/query reduction. A head prefix may be prepended to any standard derivation. For the substitution property, use two finite substitution lists that leave $o$ fixed and relate their images of each variable by standard reduction. Head prefixes are preserved by either list: root contractions use capture-avoiding substitution, and a grouped query uses the substitution property for its finite argument reduction, with $o$ and the closed numeral fixed. Induction on a standard derivation now proves compatibility with the two lists. At an abstraction, rename its binder outside both bodies, both lists' forbidden variables, and $\{o\}$; prepend this renaming to each list. The old binder differs from $o$, so both extended lists still preserve the input.

    Next show closure under appending one beta/query step. For a root beta contraction, invert the application and abstraction rules. Their head prefixes expose a root redex; contract it and apply the substitution property to the related bodies and arguments. For a query, invert the application and variable rules to expose $AB$ with a head reduction from $A$ to $o$ and a standard reduction from $B$ to the queried numeral. Reduce the operator to $o$ and use the grouped query rule on $B$. Application contexts use the corresponding subderivation. For an abstraction context, strengthen the argument to a substitution list and choose a common binder fresh also for the earlier source. This is possible because finite reductions introduce no free variables. The body induction then lifts through a binder different from $o$. The same argument handles beta steps originally written with binder $o$ by first renaming that binder. Induction on a finite reduction proves the forward implication. Finally, invert the last standard rule when the target is an abstraction: its head prefix gives the required exposure. Every Church numeral is an abstraction.
    \end{proof}
-/
theorem oracle_steps_iff_standard (p : ℕ → ℕ) (M N : AlphaTerm) :
    Relation.ReflTransGen (OracleStep p) M N ↔ OracleStandard p M N :=
  ⟨standard_of_oracle_steps,OracleStandard.oracle_steps⟩

theorem oracle_head_exposes_abstraction {p : ℕ → ℕ} {M A : AlphaTerm} {x : ℕ}
    (h : Relation.ReflTransGen (OracleStep p) M (lam x A)) :
    ∃ y B, OracleHeadSteps p M (lam y B) := by
  obtain ⟨y,B,C,hy,hh,_,_⟩ := (standard_of_oracle_steps h).lam_inv_any rfl
  exact ⟨y,B,hh⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
