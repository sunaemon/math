module

public import PolishSpaceBook.LambdaAlphaEquivalence

@[expose] public section

/-!
# Substitution laws and beta-reduction

All public reduction statements use the alpha-classes constructed in the
preceding module. Finite lists of substitutions supply the strengthened
induction hypothesis needed to rename binders during a reduction proof.
-/
namespace PolishSpaceBook.NamedLambda

namespace AlphaTerm

def var (x : ℕ) : AlphaTerm := mk (.var x)

theorem subst_var (v x : ℕ) (N : AlphaTerm) :
    (var v).subst x N = if v = x then N else var v := by
  refine Quotient.inductionOn N ?_
  intro N
  change (var v).subst x (mk N) = if v = x then mk N else var v
  by_cases h : v = x <;> simp [var, subst_mk, Term.subst_var, h]

theorem subst_app (M P N : AlphaTerm) (x : ℕ) :
    (app M P).subst x N = app (M.subst x N) (P.subst x N) := by
  refine Quotient.inductionOn₃ M P N ?_
  intro M P N
  change mk ((Term.app M P).subst x N) = mk (Term.app (M.subst x N) (P.subst x N))
  rw [Term.subst_app]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Substitution laws on alpha-classes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For the first identity, induct on the number of nodes of a named representative. Variables and applications follow from the substitution clauses. For an abstraction whose binder is the variable being replaced, substitution stops. For any other abstraction, the variable is absent from its body. If the binder must be renamed to avoid capture, the renamed body still lacks that variable and has the same number of nodes as the original body. Apply the induction hypothesis to that body and then undo the binder renaming up to alpha-equivalence. This gives the identity in every case. The abstraction formula follows directly from the substitution clause when the stated freshness conditions hold.
-/
theorem subst_not_free (M N : AlphaTerm) (x : ℕ) (hx : x ∉ M.fv) : M.subst x N = M := by
  revert hx
  refine Quotient.inductionOn₂ M N ?_
  intro M N hx
  exact Quotient.sound (Term.RenameEq.alpha (Term.renameEq_subst_not_free M N x hx))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Substitution laws on alpha-classes
-/
theorem subst_lam_fresh (M N : AlphaTerm) (y x : ℕ) (hyx : y ≠ x) (hy : y ∉ N.fv) :
    (lam y M).subst x N = lam y (M.subst x N) := by
  revert hy
  refine Quotient.inductionOn₂ M N ?_
  intro M N hy
  change y ∉ N.fv at hy
  change mk ((Term.lam y M).subst x N) = mk (Term.lam y (M.subst x N))
  rw [Term.subst_lam, ite_eq_right hyx, ite_eq_left hy]

theorem lam_rename (M : AlphaTerm) (y z : ℕ) (hz : z ∉ M.fv) :
    lam y M = lam z (M.subst y (var z)) := by
  revert hz
  refine Quotient.inductionOn M ?_
  intro M hz
  exact Quotient.sound (Term.alpha_rename M y z hz)

/-- Induction on alpha-classes, choosing binders outside any fixed finite set. -/
theorem induction_fresh {C : AlphaTerm → Prop} (s : Finset ℕ)
    (hv : ∀ x, C (var x))
    (ha : ∀ M N, C M → C N → C (app M N))
    (hl : ∀ x M, x ∉ s → C M → C (lam x M)) (M : AlphaTerm) : C M := by
  have bounded : ∀ k (M : Term), M.nodes ≤ k → C (mk M) := by
    intro k
    induction k with
    | zero => intro M hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M hk
      cases M with
      | var x => exact hv x
      | app M N =>
        change C (app (mk M) (mk N))
        apply ha
        · apply ih M; simp only [Term.nodes] at hk; omega
        · apply ih N; simp only [Term.nodes] at hk; omega
      | lam x M =>
        let z := Term.fresh (M.fv ∪ s)
        have hz : z ∉ M.fv ∧ z ∉ s := by
          simpa only [z, Finset.mem_union, not_or] using Term.fresh_not_mem (M.fv ∪ s)
        change C (lam x (mk M))
        rw [lam_rename (mk M) x z hz.1]
        apply hl z _ hz.2
        apply ih (M.subst x (.var z))
        rw [Term.nodes_subst_var]
        simp only [Term.nodes] at hk
        omega
  refine Quotient.inductionOn M ?_
  intro M
  exact bounded M.nodes M le_rfl

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Substitution laws on alpha-classes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For the composition identity, induct on a node-count bound for a named representative of $M$. At the variable $x$, both sides give $\SubstLambda{N}{y}{P}$. At the variable $y$, both sides give $P$, since $x$ does not occur freely in $P$. At any other variable, both sides leave it unchanged. The application case follows from the two induction hypotheses. For an abstraction, first rename its binder to a variable different from $x,y$ and absent from the free-variable sets of $N$, $P$ and $\SubstLambda{N}{y}{P}$. The renamed body has the original body's node count. Move each substitution under this common binder by the abstraction formula, apply the induction hypothesis to the body, and restore the abstraction. Thus the argument uses only named terms and capture-avoiding renaming.
-/
theorem subst_comp (M N P : AlphaTerm) (x y : ℕ) (hxy : x ≠ y) (hx : x ∉ P.fv) :
    (M.subst x N).subst y P = (M.subst y P).subst x (N.subst y P) := by
  apply induction_fresh (N.fv ∪ P.fv ∪ (N.subst y P).fv ∪ {x, y}) (M := M)
  · intro v
    by_cases hvx : v = x
    · subst v; simp only [subst_var, ite_true, ite_eq_right hxy]
    · by_cases hvy : v = y
      · subst v
        simp only [subst_var, ite_eq_right hvx, ite_true, subst_not_free P _ x hx]
      · simp only [subst_var, ite_eq_right hvx, ite_eq_right hvy]
  · intro A B ihA ihB
    simp only [subst_app, ihA, ihB]
  · intro z A hz ih
    have h : z ∉ N.fv ∧ z ∉ P.fv ∧ z ∉ (N.subst y P).fv ∧ z ≠ x ∧ z ≠ y := by
      simpa only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or, and_assoc] using hz
    rw [subst_lam_fresh _ N z x h.2.2.2.1 h.1,
      subst_lam_fresh _ P z y h.2.2.2.2 h.2.1,
      subst_lam_fresh _ P z y h.2.2.2.2 h.2.1,
      subst_lam_fresh _ (N.subst y P) z x h.2.2.2.1 h.2.2.1, ih]

theorem contract_eq (M M' A : AlphaTerm) (y z : ℕ) (h : lam y M = lam z M') :
    M.subst y A = M'.subst z A := by
  revert h
  refine Quotient.inductionOn₃ M M' A ?_
  intro M M' A h
  exact Quotient.sound (Term.alpha_contract (Quotient.exact h) (Term.Alpha.refl A))

/-- One substitution carries a root redex to a root redex with the corresponding contractum. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For the first assertion, strengthen the claim to any finite list of substitutions, applied from left to right, and induct on the derivation of the beta step. Consider a contraction at the root. For one substitution, rename the redex's binder to a variable absent from the body's and replacement's free-variable sets and different from the variable being replaced. The abstraction formula moves substitution under this binder. The composition formula then identifies the new contractum with the substituted old contractum. Thus one substitution takes a root redex to a root redex with the required contractum. Iterating this observation proves the root case for a finite list.
-/
theorem subst_redex (M A R : AlphaTerm) (y x : ℕ) :
    ∃ z B C, (app (lam y M) A).subst x R = app (lam z B) C ∧
      (M.subst y A).subst x R = B.subst z C := by
  let z := Term.fresh (M.fv ∪ R.fv ∪ {x})
  have hz : z ∉ M.fv ∧ z ∉ R.fv ∧ z ≠ x := by
    simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
      using Term.fresh_not_mem (M.fv ∪ R.fv ∪ {x})
  let B := M.subst y (var z)
  have hl : lam y M = lam z B := lam_rename M y z hz.1
  refine ⟨z, B.subst x R, A.subst x R, ?_, ?_⟩
  · rw [subst_app, hl, subst_lam_fresh _ _ z x hz.2.2 hz.2.1]
  · rw [contract_eq M B A y z hl, subst_comp B A R z x hz.2.2 hz.2.1]

/-- Apply a finite list from left to right. -/
def substs (M : AlphaTerm) : List (ℕ × AlphaTerm) → AlphaTerm
  | [] => M
  | (x, N) :: σ => substs (M.subst x N) σ

/-- Names that must be avoided when moving the whole list under a binder. -/
def forbidden : List (ℕ × AlphaTerm) → Finset ℕ
  | [] => ∅
  | (x, N) :: σ => {x} ∪ N.fv ∪ forbidden σ

theorem substs_app (M N : AlphaTerm) (σ : List (ℕ × AlphaTerm)) :
    substs (app M N) σ = app (substs M σ) (substs N σ) := by
  induction σ generalizing M N with
  | nil => rfl
  | cons a σ ih => rcases a with ⟨x, R⟩; simp only [substs, subst_app, ih]

theorem substs_lam_fresh (M : AlphaTerm) (z : ℕ) (σ : List (ℕ × AlphaTerm))
    (hz : z ∉ forbidden σ) : substs (lam z M) σ = lam z (substs M σ) := by
  induction σ generalizing M with
  | nil => rfl
  | cons a σ ih =>
    rcases a with ⟨x, R⟩
    have hs : z ≠ x ∧ z ∉ R.fv ∧ z ∉ forbidden σ := by
      simpa only [forbidden, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc] using hz
    simp only [substs, subst_lam_fresh M R z x hs.1 hs.2.1, ih _ hs.2.2]

theorem substs_redex (M A : AlphaTerm) (y : ℕ) (σ : List (ℕ × AlphaTerm)) :
    ∃ z B C, substs (app (lam y M) A) σ = app (lam z B) C ∧
      substs (M.subst y A) σ = B.subst z C := by
  induction σ generalizing M A y with
  | nil => exact ⟨y, M, A, rfl, rfl⟩
  | cons a σ ih =>
    rcases a with ⟨x, R⟩
    rcases subst_redex M A R y x with ⟨z, B, C, hs, ht⟩
    simp only [substs, hs, ht]
    exact ih B C z

/-- Strengthening to lists permits fresh renaming in the abstraction case. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Application contexts follow because the list distributes over both sides of an application. In an abstraction context, choose a common binder absent from both bodies' free-variable sets, from every replacement's free-variable set, and from every variable replaced by the list. Only finitely many names are excluded. Rename both bodies to this binder and move the whole list under it. The induction hypothesis applies to the list obtained by first performing this renaming and then performing the original list. Its conclusion lifts through the common abstraction. This is the reason for strengthening the induction hypothesis to lists: an arbitrary fresh renaming must be allowed before the intended substitution. The singleton list proves the first assertion, and induction on the length of a reduction proves its finite-step version with a fixed replacement.
-/
theorem Beta.substs {M M' : AlphaTerm} (h : Beta M M') (σ : List (ℕ × AlphaTerm)) :
    Beta (substs M σ) (substs M' σ) := by
  induction h generalizing σ with
  | contract y M A =>
    rcases substs_redex M A y σ with ⟨z, B, C, hs, ht⟩
    rw [hs, ht]
    exact .contract z B C
  | app_left N _ ih =>
    rw [substs_app, substs_app]
    exact .app_left _ (ih σ)
  | app_right M _ ih =>
    rw [substs_app, substs_app]
    exact .app_right _ (ih σ)
  | @lam y M M' h ih =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ)
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ := by
      simpa only [z, Finset.mem_union, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ)
    rw [lam_rename M y z hz.1, lam_rename M' y z hz.2.1,
      substs_lam_fresh _ z σ hz.2.2, substs_lam_fresh _ z σ hz.2.2]
    exact .lam z (ih ((y, var z) :: σ))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Substitution and finite beta-reduction
-/
theorem Beta.subst {M M' : AlphaTerm} (h : Beta M M') (x : ℕ) (N : AlphaTerm) :
    Beta (M.subst x N) (M'.subst x N) := h.substs [(x, N)]

theorem beta_steps_subst {M M' : AlphaTerm} (h : Relation.ReflTransGen Beta M M')
    (x : ℕ) (N : AlphaTerm) : Relation.ReflTransGen Beta (M.subst x N) (M'.subst x N) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (Beta.subst h x N)


theorem beta_steps_app_left {M M' : AlphaTerm} (h : Relation.ReflTransGen Beta M M')
    (N : AlphaTerm) : Relation.ReflTransGen Beta (app M N) (app M' N) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.app_left N h)

theorem beta_steps_app_right (M : AlphaTerm) {N N' : AlphaTerm}
    (h : Relation.ReflTransGen Beta N N') : Relation.ReflTransGen Beta (app M N) (app M N') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.app_right M h)

theorem beta_steps_app {M M' N N' : AlphaTerm} (hM : Relation.ReflTransGen Beta M M')
    (hN : Relation.ReflTransGen Beta N N') : Relation.ReflTransGen Beta (app M N) (app M' N') :=
  (beta_steps_app_left hM N).trans (beta_steps_app_right M' hN)

theorem beta_steps_lam (z : ℕ) {M M' : AlphaTerm} (h : Relation.ReflTransGen Beta M M') :
    Relation.ReflTransGen Beta (lam z M) (lam z M') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.lam z h)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    It remains to reduce the replacement itself. Fix $N\to_\beta^*N'$ and induct on a node-count bound for a named representative of $M$. At the variable $x$, use the given reduction; at any other variable, use zero steps. For an application, reduce the inserted copies in one branch and then in the other, using the two context rules. For an abstraction, choose one binder fresh for its body, both replacements, and $x$. Rename to this binder and move substitution under it on both sides. The renamed body has the original body's node count, so the induction hypothesis applies and its reduction lifts through the abstraction. This proves
    $$
    \SubstLambda{M}{x}{N}\to_\beta^*\SubstLambda{M}{x}{N'}.
    $$
    There may be several copies of the replacement, or none, so a finite reduction is required here.
-/
private theorem beta_steps_subst_arg_bounded (k : ℕ) (M : Term) (x : ℕ)
    {N N' : AlphaTerm} (h : Relation.ReflTransGen Beta N N') (hk : M.nodes ≤ k) :
    Relation.ReflTransGen Beta ((mk M).subst x N) ((mk M).subst x N') := by
  induction k generalizing M with
  | zero => have := M.nodes_pos; omega
  | succ k ih =>
    cases M with
    | var v =>
      change Relation.ReflTransGen Beta ((var v).subst x N) ((var v).subst x N')
      rw [subst_var, subst_var]
      by_cases hv : v = x
      · simpa only [ite_eq_left hv] using h
      · simp only [ite_eq_right hv]; exact .refl
    | app M P =>
      have hm : M.nodes ≤ k := by simp only [Term.nodes] at hk; omega
      have hp : P.nodes ≤ k := by simp only [Term.nodes] at hk; omega
      change Relation.ReflTransGen Beta ((app (mk M) (mk P)).subst x N)
        ((app (mk M) (mk P)).subst x N')
      rw [subst_app, subst_app]
      exact beta_steps_app (ih M hm) (ih P hp)
    | lam y M =>
      let z := Term.fresh (M.fv ∪ N.fv ∪ N'.fv ∪ {x})
      have hz : z ∉ M.fv ∧ z ∉ N.fv ∧ z ∉ N'.fv ∧ z ≠ x := by
        simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
          using Term.fresh_not_mem (M.fv ∪ N.fv ∪ N'.fv ∪ {x})
      have hm : (M.subst y (.var z)).nodes ≤ k := by
        rw [Term.nodes_subst_var]
        simp only [Term.nodes] at hk
        omega
      change Relation.ReflTransGen Beta ((lam y (mk M)).subst x N) ((lam y (mk M)).subst x N')
      rw [lam_rename (mk M) y z hz.1,
        subst_lam_fresh _ N z x hz.2.2.2 hz.2.1,
        subst_lam_fresh _ N' z x hz.2.2.2 hz.2.2.1]
      exact beta_steps_lam z (ih (M.subst y (.var z)) hm)

/-- Every inserted copy can be reduced; no copy means a zero-step reduction. -/
theorem beta_steps_subst_arg (M : AlphaTerm) (x : ℕ) {N N' : AlphaTerm}
    (h : Relation.ReflTransGen Beta N N') :
    Relation.ReflTransGen Beta (M.subst x N) (M.subst x N') := by
  refine Quotient.inductionOn M ?_
  intro M
  exact beta_steps_subst_arg_bounded M.nodes M x h le_rfl

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Substitution and finite beta-reduction
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Finally, first reduce $M$ to $M'$ while keeping $N$ fixed, then reduce the copies of $N$ to $N'$ in the resulting substitution. Transitivity gives the asserted joint reduction.
-/
theorem beta_steps_subst_both {M M' N N' : AlphaTerm}
    (hM : Relation.ReflTransGen Beta M M') (hN : Relation.ReflTransGen Beta N N') (x : ℕ) :
    Relation.ReflTransGen Beta (M.subst x N) (M'.subst x N') :=
  (beta_steps_subst hM x N).trans (beta_steps_subst_arg M' x hN)

end AlphaTerm
end PolishSpaceBook.NamedLambda
