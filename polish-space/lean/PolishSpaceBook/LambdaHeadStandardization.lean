module

public import PolishSpaceBook.LambdaNumerals

@[expose] public section

/-! # Head exposure by inductive standard reduction

Head steps contract the operator spine, without entering arguments or lambda
bodies. The structural proof follows Ryo Kashima, A Proof of the Standardization
Theorem in λ-Calculus (2000), https://www.is.c.titech.ac.jp/users/kashima/pub/C-145.pdf.
Finite substitution lists expose all alpha-renaming obligations.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    A \termdefine{head beta step} contracts a redex at the root or takes such a step in the operator of an application. It does not enter an argument or an abstraction body. Write $\LambdaHeadSteps{M}{N}$ for finitely many head steps, including none. Head steps are beta steps. They are preserved by substitution: a root redex remains a root redex after capture-avoiding substitution, and substitution preserves application contexts on the operator side.
-/
inductive HeadStep : AlphaTerm → AlphaTerm → Prop where
  | contract (x : ℕ) (M N : AlphaTerm) : HeadStep (AlphaTerm.app (AlphaTerm.lam x M) N) (M.subst x N)
  | app_left {M M' : AlphaTerm} (N : AlphaTerm) : HeadStep M M' → HeadStep (AlphaTerm.app M N) (AlphaTerm.app M' N)

abbrev HeadSteps := Relation.ReflTransGen HeadStep

theorem HeadStep.beta {M N : AlphaTerm} (h : HeadStep M N) : Beta M N := by
  induction h with
  | contract x A B => exact .contract x A B
  | app_left A _ ih => exact .app_left A ih

theorem HeadSteps.beta_steps {M N : AlphaTerm} (h : HeadSteps M N) :
    Relation.ReflTransGen Beta M N := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih h.beta

theorem HeadStep.substs {M N : AlphaTerm} (h : HeadStep M N) (σ : List (ℕ × AlphaTerm)) :
    HeadStep (AlphaTerm.substs M σ) (AlphaTerm.substs N σ) := by
  induction h with
  | contract x A B =>
    obtain ⟨z, C, D, hs, ht⟩ := substs_redex A B x σ
    rw [hs, ht]
    exact .contract z C D
  | app_left A _ ih => rw [substs_app, substs_app]; exact .app_left _ ih

theorem HeadSteps.substs {M N : AlphaTerm} (h : HeadSteps M N) (σ : List (ℕ × AlphaTerm)) :
    HeadSteps (AlphaTerm.substs M σ) (AlphaTerm.substs N σ) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (h.substs σ)

theorem HeadSteps.app_left {M N : AlphaTerm} (h : HeadSteps M N) (A : AlphaTerm) :
    HeadSteps (AlphaTerm.app M A) (AlphaTerm.app N A) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.app_left _ h)

theorem HeadStep.not_lam {M N : AlphaTerm} (h : HeadStep M N) {x : ℕ} {A : AlphaTerm}
    (he : M = AlphaTerm.lam x A) : False := by
  cases h with
  | contract y B C => exact app_ne_lam _ _ _ _ he
  | app_left B hA => exact app_ne_lam _ _ _ _ he

theorem HeadStep.app_inv {M N : AlphaTerm} (h : HeadStep M N) {P A : AlphaTerm}
    (he : M = AlphaTerm.app P A) :
    (∃ x B, P = AlphaTerm.lam x B ∧ N = B.subst x A) ∨
      (∃ Q, HeadStep P Q ∧ N = AlphaTerm.app Q A) := by
  cases h with
  | contract x B C =>
    obtain ⟨heP, rfl⟩ := app_inj he
    exact Or.inl ⟨x, B, heP.symm, rfl⟩
  | @app_left P Q B hp =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact Or.inr ⟨Q, hp, rfl⟩

theorem HeadStep.deterministic {M N P : AlphaTerm} (h : HeadStep M N) (h' : HeadStep M P) :
    N = P := by
  induction h generalizing P with
  | contract x A B =>
    rcases h'.app_inv rfl with ⟨y, C, he, rfl⟩ | ⟨Q, hQ, rfl⟩
    · exact contract_eq A C B x y he
    · exact False.elim (hQ.not_lam rfl)
  | app_left A h ih =>
    rcases h'.app_inv rfl with ⟨y, C, he, rfl⟩ | ⟨Q, hQ, rfl⟩
    · exact False.elim (h.not_lam he)
    · exact congrArg (fun X => AlphaTerm.app X A) (ih hQ)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    We use Kashima's inductive organization of standard reduction [@Kashima2000]. Define $\LambdaStandardSteps{M}{N}$ by the following three rules:
    $$\frac{\LambdaHeadSteps{L}{x}}{\LambdaStandardSteps{L}{x}},\qquad
    \frac{\LambdaHeadSteps{L}{AB}\quad\LambdaStandardSteps{A}{C}\quad\LambdaStandardSteps{B}{D}}
     {\LambdaStandardSteps{L}{CD}},$$
    $$\frac{\LambdaHeadSteps{L}{\lambdaab{x}{A}}\quad\LambdaStandardSteps{A}{B}}
     {\LambdaStandardSteps{L}{\lambdaab{x}{B}}}.$$
    Each rule first exposes the required outer constructor by head steps and then treats its immediate subterms.
-/
inductive Standard : AlphaTerm → AlphaTerm → Prop where
  | var {L : AlphaTerm} (x : ℕ) : HeadSteps L (AlphaTerm.var x) → Standard L (AlphaTerm.var x)
  | app {L A B C D : AlphaTerm} : HeadSteps L (AlphaTerm.app A B) →
      Standard A C → Standard B D → Standard L (AlphaTerm.app C D)
  | lam {L A B : AlphaTerm} (x : ℕ) : HeadSteps L (AlphaTerm.lam x A) →
      Standard A B → Standard L (AlphaTerm.lam x B)

theorem Standard.refl (M : AlphaTerm) : Standard M M := by
  refine Quotient.inductionOn M ?_
  intro M
  induction M with
  | var x => exact .var x .refl
  | app A B ihA ihB => exact .app .refl ihA ihB
  | lam x A ih => exact .lam x .refl ih

theorem Standard.beta_steps {M N : AlphaTerm} (h : Standard M N) :
    Relation.ReflTransGen Beta M N := by
  induction h with
  | var _ h => exact h.beta_steps
  | app h _ _ ihA ihB => exact h.beta_steps.trans (beta_steps_app ihA ihB)
  | lam x h _ ih => exact h.beta_steps.trans (beta_steps_lam x ih)

theorem Standard.head_prefix {L M N : AlphaTerm} (h : HeadSteps L M) (hs : Standard M N) :
    Standard L N := by
  cases hs with
  | var x h' => exact .var x (h.trans h')
  | app h' hA hB => exact .app (h.trans h') hA hB
  | lam x h' hA => exact .lam x (h.trans h') hA

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The rules give reflexivity by structural induction and imply finite beta-reduction. Prefixing a derivation by head steps also preserves the relation. Its substitution property follows by induction on the derivation, strengthened to two finite substitution lists whose final images of each variable are related. At an abstraction, choose a binder fresh for both bodies and both lists, rename both bodies, and prepend this renaming to each list. This gives
    $$\LambdaStandardSteps{M}{N},\quad\LambdaStandardSteps{A}{B}
    \quad\Longrightarrow\quad
    \LambdaStandardSteps{\SubstLambda{M}{x}{A}}{\SubstLambda{N}{x}{B}}.$$
-/
theorem Standard.substs {M N : AlphaTerm} (h : Standard M N)
    (σ τ : List (ℕ × AlphaTerm))
    (hv : ∀ v, Standard (AlphaTerm.substs (AlphaTerm.var v) σ) (AlphaTerm.substs (AlphaTerm.var v) τ)) :
    Standard (AlphaTerm.substs M σ) (AlphaTerm.substs N τ) := by
  induction h generalizing σ τ with
  | var x hh => exact Standard.head_prefix (hh.substs σ) (hv x)
  | @app L A B C D hh hA hB ihA ihB =>
    have hp := hh.substs σ
    rw [substs_app] at hp ⊢
    exact .app hp (ihA σ τ hv) (ihB σ τ hv)
  | @lam L A B y hh hb ih =>
    let z := Term.fresh (A.fv ∪ B.fv ∪ forbidden σ ∪ forbidden τ)
    have hz : z ∉ A.fv ∧ z ∉ B.fv ∧ z ∉ forbidden σ ∧ z ∉ forbidden τ := by
      simpa only [z, Finset.mem_union, not_or, and_assoc]
        using Term.fresh_not_mem (A.fv ∪ B.fv ∪ forbidden σ ∪ forbidden τ)
    have hv' : ∀ v, Standard (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: σ))
        (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: τ)) := by
      intro v
      simp only [AlphaTerm.substs, subst_var]
      by_cases h : v = y
      · simpa only [ite_eq_left h] using hv z
      · simpa only [ite_eq_right h] using hv v
    have hp := hh.substs σ
    rw [lam_rename A y z hz.1, substs_lam_fresh _ z σ hz.2.2.1] at hp
    rw [lam_rename B y z hz.2.1, substs_lam_fresh _ z τ hz.2.2.2]
    exact .lam z hp (ih _ _ hv')

theorem Standard.subst {M N A B : AlphaTerm} (h : Standard M N) (hab : Standard A B) (x : ℕ) :
    Standard (M.subst x A) (N.subst x B) := by
  apply h.substs [(x, A)] [(x, B)]
  intro v
  simp only [AlphaTerm.substs, subst_var]
  by_cases hv : v = x
  · simpa only [ite_eq_left hv] using hab
  · simp only [ite_eq_right hv]; exact .refl _

theorem Standard.app_inv {L M : AlphaTerm} (h : Standard L M) {C D : AlphaTerm}
    (he : M = AlphaTerm.app C D) :
    ∃ A B, HeadSteps L (AlphaTerm.app A B) ∧ Standard A C ∧ Standard B D := by
  cases h with
  | var x hh => exact False.elim (var_ne_app _ _ _ he)
  | @app L A B C' D' hh hA hB =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact ⟨A, B, hh, hA, hB⟩
  | lam x hh hA => exact False.elim (app_ne_lam _ _ _ _ he.symm)

theorem Standard.lam_inv_any {L M : AlphaTerm} (h : Standard L M) {x : ℕ} {B : AlphaTerm}
    (he : M = AlphaTerm.lam x B) :
    ∃ y A C, HeadSteps L (AlphaTerm.lam y A) ∧ Standard A C ∧ AlphaTerm.lam y C = AlphaTerm.lam x B := by
  cases h with
  | var y hh => exact False.elim (var_ne_lam _ _ _ he)
  | app hh hA hB => exact False.elim (app_ne_lam _ _ _ _ he)
  | @lam L A C y hh hb => exact ⟨y, A, C, hh, hb, he⟩

theorem Standard.lam_inv {L M : AlphaTerm} (h : Standard L M) {x : ℕ} {B : AlphaTerm}
    (he : M = AlphaTerm.lam x B) (hx : x ∉ L.fv) :
    ∃ A, HeadSteps L (AlphaTerm.lam x A) ∧ Standard A B := by
  obtain ⟨y, A, C, hh, hb, he⟩ := h.lam_inv_any he
  by_cases hyx : y = x
  · subst y
    have he' := lam_inj x he
    subst C
    exact ⟨A, hh, hb⟩
  · have hxA : x ∉ A.fv := by
      intro hA
      have hf : x ∈ (AlphaTerm.lam y A).fv := by
        rw [fv_lam]
        exact Finset.mem_erase.mpr ⟨Ne.symm hyx, hA⟩
      exact hx (beta_steps_fv_subset hh.beta_steps hf)
    have hxC : x ∉ C.fv := fun hc => hxA (beta_steps_fv_subset hb.beta_steps hc)
    have hc : C.subst y (AlphaTerm.var x) = B :=
      lam_inj x ((lam_rename C y x hxC).symm.trans he)
    refine ⟨A.subst y (AlphaTerm.var x), ?_, ?_⟩
    · simpa only [← lam_rename A y x hxA] using hh
    · simpa only [hc] using hb.subst (.refl (AlphaTerm.var x)) y

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Now append one beta step. For a root contraction, invert the application rule and then the abstraction rule. Their head prefixes expose a root redex in the source; contract it and apply the substitution property to its body and argument. Independence of contraction from the binder name identifies the resulting target. Application contexts use the corresponding subderivation.
-/
theorem Standard.contract {L M N : AlphaTerm} (x : ℕ)
    (h : Standard L (AlphaTerm.app (AlphaTerm.lam x M) N)) : Standard L (M.subst x N) := by
  obtain ⟨P, A, hp, hP, hA⟩ := h.app_inv rfl
  obtain ⟨y, B, C, hb, hBC, he⟩ := hP.lam_inv_any rfl
  have hh := (hp.trans (hb.app_left A)).tail (HeadStep.contract y B A)
  have hs := Standard.head_prefix hh (hBC.subst hA y)
  simpa only [contract_eq C M N y x he] using hs

/-- Lists permit renaming the binder away from the earlier source of the standard reduction. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For an abstraction context, strengthen this argument to an arbitrary finite substitution list. Choose a common binder fresh also for the earlier source of the standard derivation. Head steps introduce no free variables, so the exposed abstraction can be written with this binder; the substitution property renames its body derivation. Prepending the binder renaming to the substitution list makes the induction hypothesis applicable. Lift the resulting body derivation under the common binder. Thus the relation is closed under appending one beta step, and induction on a finite beta reduction proves the forward implication.
    \end{proof}
-/
theorem Standard.beta_substs_right {M N : AlphaTerm} (h : Beta M N)
    (σ : List (ℕ × AlphaTerm)) (L : AlphaTerm) (hs : Standard L (AlphaTerm.substs M σ)) :
    Standard L (AlphaTerm.substs N σ) := by
  induction h generalizing σ L with
  | contract y M A =>
    obtain ⟨z, B, C, he, ht⟩ := substs_redex M A y σ
    rw [he] at hs
    rw [ht]
    exact hs.contract z
  | app_left A _ ih =>
    rw [substs_app] at hs ⊢
    obtain ⟨P, Q, hh, hP, hQ⟩ := hs.app_inv rfl
    exact .app hh (ih σ P hP) hQ
  | app_right A _ ih =>
    rw [substs_app] at hs ⊢
    obtain ⟨P, Q, hh, hP, hQ⟩ := hs.app_inv rfl
    exact .app hh hP (ih σ Q hQ)
  | @lam y M N h ih =>
    let z := Term.fresh (M.fv ∪ N.fv ∪ forbidden σ ∪ L.fv)
    have hz : z ∉ M.fv ∧ z ∉ N.fv ∧ z ∉ forbidden σ ∧ z ∉ L.fv := by
      simpa only [z, Finset.mem_union, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ N.fv ∪ forbidden σ ∪ L.fv)
    rw [lam_rename M y z hz.1, substs_lam_fresh _ z σ hz.2.2.1] at hs
    rw [lam_rename N y z hz.2.1, substs_lam_fresh _ z σ hz.2.2.1]
    obtain ⟨A, hh, hA⟩ := hs.lam_inv rfl hz.2.2.2
    exact .lam z hh (ih ((y, AlphaTerm.var z) :: σ) A hA)

theorem Standard.beta_right {L M N : AlphaTerm} (hs : Standard L M) (h : Beta M N) :
    Standard L N := Standard.beta_substs_right h [] L hs

theorem standard_of_beta_steps {M N : AlphaTerm} (h : Relation.ReflTransGen Beta M N) :
    Standard M N := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact ih.beta_right h

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Inductive standard reduction
-/
theorem beta_steps_iff_standard (M N : AlphaTerm) :
    Relation.ReflTransGen Beta M N ↔ Standard M N :=
  ⟨standard_of_beta_steps, Standard.beta_steps⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Head exposure of an abstraction
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Apply the lemma. The last rule of a derivation with an abstraction as its target must be the abstraction rule, since the three outer constructors remain distinct on alpha-classes. Its head prefix gives the required reduction. Every Church numeral is an abstraction.
    \end{proof}
-/
theorem head_exposes_abstraction {M A : AlphaTerm} {x : ℕ}
    (h : Relation.ReflTransGen Beta M (AlphaTerm.lam x A)) :
    ∃ y B, HeadSteps M (AlphaTerm.lam y B) := by
  obtain ⟨y, B, C, hh, _, _⟩ := (standard_of_beta_steps h).lam_inv_any rfl
  exact ⟨y, B, hh⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Head exposure of an abstraction
-/
theorem head_exposes_numeral {M : AlphaTerm} {n : ℕ}
    (h : Relation.ReflTransGen Beta M (numeral n)) :
    ∃ y B, HeadSteps M (AlphaTerm.lam y B) :=
  head_exposes_abstraction h

theorem no_numeral_of_no_head_abstraction {M : AlphaTerm}
    (h : ∀ y B, ¬ HeadSteps M (AlphaTerm.lam y B)) (n : ℕ) :
    ¬ Relation.ReflTransGen Beta M (numeral n) := by
  intro hn
  obtain ⟨y, B, hb⟩ := head_exposes_numeral hn
  exact h y B hb

end PolishSpaceBook.NamedLambda.AlphaTerm
