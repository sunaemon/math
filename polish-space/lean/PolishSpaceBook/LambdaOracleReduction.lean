module

public import PolishSpaceBook.LambdaOraclePrograms

@[expose] public section

/-!
# Parallel reduction with an input-name parameter

Binders in the parallel rules avoid the distinguished free input variable.
Fresh renaming supplies such a binder for every abstraction. Substitution
preserves query steps only when it leaves that input variable fixed.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

theorem substs_closed (M : AlphaTerm) (hM : M.Closed) (σ : List (ℕ × AlphaTerm)) :
    substs M σ = M := by
  induction σ with
  | nil => rfl
  | cons a σ ih =>
    rcases a with ⟨x, N⟩
    rw [substs, subst_not_free M N x (by rw [hM]; simp), ih]

/-- The keys of these substitutions never replace the input-name parameter. -/
def PreservesInput (σ : List (ℕ × AlphaTerm)) : Prop := ∀ a ∈ σ, a.1 ≠ 0

theorem substs_input (σ : List (ℕ × AlphaTerm)) (hσ : PreservesInput σ) :
    substs (var 0) σ = var 0 := by
  induction σ with
  | nil => rfl
  | cons a σ ih =>
    rcases a with ⟨x, N⟩
    rw [substs, subst_var, ite_eq_right (Ne.symm (hσ (x, N) (by simp)))]
    exact ih (fun a ha => hσ a (by simp [ha]))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For a fixed name $p$, extend the parallel beta rules of §{sec:lambda-calculus} to a relation $\ParallelLambdaInput{p}{M}{N}$. Choose every binder in the abstraction and contraction rules different from $o$, and add the query rule
    $$\ParallelLambdaInput{p}{o\ChurchNumeral{i}}{\ChurchNumeral{p(i)}}.$$
    The variable and application rules are unchanged. Fresh alpha-renaming makes the binder requirement harmless: every abstraction has a representative with a binder different from $o$. Induction on the number of nodes, using that variable renaming preserves this number, proves reflexivity for all alpha-classes.
-/
inductive OracleParallel (p : ℕ → ℕ) : AlphaTerm → AlphaTerm → Prop where
  | var (x : ℕ) : OracleParallel p (var x) (var x)
  | app {M M' N N'} : OracleParallel p M M' → OracleParallel p N N' →
      OracleParallel p (app M N) (app M' N')
  | lam (x : ℕ) (hx : x ≠ 0) {M M'} : OracleParallel p M M' →
      OracleParallel p (lam x M) (lam x M')
  | contract (x : ℕ) (hx : x ≠ 0) {M M' N N'} :
      OracleParallel p M M' → OracleParallel p N N' →
      OracleParallel p (app (lam x M) N) (M'.subst x N')
  | query (n : ℕ) : OracleParallel p (app (var 0) (numeral n)) (numeral (p n))

theorem OracleParallel.refl (p : ℕ → ℕ) (M : AlphaTerm) : OracleParallel p M M := by
  apply induction_fresh {0} (fun x => .var x) (fun _ _ => .app) _ M
  intro x M hx hM
  exact .lam x (by simpa using hx) hM

theorem OracleParallel.fv_subset {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : OracleParallel p M N) : N.fv ⊆ M.fv := by
  induction h with
  | var x => exact Finset.Subset.refl _
  | app _ _ ihM ihN => simpa only [fv_app] using Finset.union_subset_union ihM ihN
  | lam x hx _ ih => simpa only [fv_lam] using Finset.erase_subset_erase x ih
  | @contract x hx M M' N N' _ _ ihM ihN =>
    exact Finset.Subset.trans (fv_subst_subset M' N' x)
      (by simpa only [fv_app, fv_lam] using (Finset.union_subset_union
        (Finset.erase_subset_erase x ihM) ihN))
  | query n => rw [numeral_closed]; exact Finset.empty_subset _

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Parallel reduction introduces no free variables. Its substitution lemma holds for substitution lists that never replace $o$: if the two lists send each variable to parallel-related terms, their images of parallel-related terms are again parallel-related. The proof follows the finite-list argument in §{sec:lambda-calculus}, choosing each fresh binder outside both bodies, both lists' forbidden variables, and $\{o\}$. Prepending a binder renaming still leaves $o$ fixed. In the new query case, substitution fixes $o$ and both closed numerals, so the same query rule applies. Thus the substitution lemma needed for beta contraction remains valid, since its binder differs from $o$.
-/
theorem OracleParallel.substs {p : ℕ → ℕ} {M M' : AlphaTerm} (h : OracleParallel p M M')
    (σ τ : List (ℕ × AlphaTerm)) (hσ : PreservesInput σ) (hτ : PreservesInput τ)
    (hv : ∀ v, OracleParallel p (AlphaTerm.substs (AlphaTerm.var v) σ)
      (AlphaTerm.substs (AlphaTerm.var v) τ)) :
    OracleParallel p (substs M σ) (substs M' τ) := by
  induction h generalizing σ τ with
  | var x => exact hv x
  | app _ _ ihM ihN =>
    rw [substs_app, substs_app]
    exact .app (ihM σ τ hσ hτ hv) (ihN σ τ hσ hτ hv)
  | query n =>
    rw [substs_app, substs_input σ hσ, substs_closed _ (numeral_closed n),
      substs_closed _ (numeral_closed (p n))]
    exact .query n
  | @lam y hy M M' h ih =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ ∪ {0})
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ ∧ z ∉ forbidden τ ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ ∪ {0})
    have hs : PreservesInput ((y, AlphaTerm.var z) :: σ) := by
      intro a ha; rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact hσ a ha
    have ht : PreservesInput ((y, AlphaTerm.var z) :: τ) := by
      intro a ha; rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact hτ a ha
    have hv' : ∀ v, OracleParallel p (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: σ))
        (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: τ)) := by
      intro v
      simp only [AlphaTerm.substs, subst_var]
      by_cases h : v = y
      · simpa only [ite_eq_left h] using hv z
      · simpa only [ite_eq_right h] using hv v
    rw [lam_rename M y z hz.1, lam_rename M' y z hz.2.1,
      substs_lam_fresh _ z σ hz.2.2.1, substs_lam_fresh _ z τ hz.2.2.2.1]
    exact .lam z hz.2.2.2.2 (ih _ _ hs ht hv')
  | @contract y hy M M' N N' hM hN ihM ihN =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ ∪ {0})
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ ∧ z ∉ forbidden τ ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ ∪ forbidden τ ∪ {0})
    have hs : PreservesInput ((y, AlphaTerm.var z) :: σ) := by
      intro a ha; rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact hσ a ha
    have ht : PreservesInput ((y, AlphaTerm.var z) :: τ) := by
      intro a ha; rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact hτ a ha
    have hv' : ∀ v, OracleParallel p (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: σ))
        (AlphaTerm.substs (AlphaTerm.var v) ((y, AlphaTerm.var z) :: τ)) := by
      intro v
      simp only [AlphaTerm.substs, subst_var]
      by_cases h : v = y
      · simpa only [ite_eq_left h] using hv z
      · simpa only [ite_eq_right h] using hv v
    have hl := lam_rename M' y z hz.2.1
    rw [substs_app, lam_rename M y z hz.1, substs_lam_fresh _ z σ hz.2.2.1,
      contract_eq M' (M'.subst y (AlphaTerm.var z)) N' y z hl,
      substs_subst_fresh _ _ z τ hz.2.2.2.1]
    exact .contract z hz.2.2.2.2 (ihM _ _ hs ht hv') (ihN σ τ hσ hτ hv)

theorem OracleParallel.subst {p : ℕ → ℕ} {M M' N N' : AlphaTerm}
    (hM : OracleParallel p M M') (hN : OracleParallel p N N') (x : ℕ) (hx : x ≠ 0) :
    OracleParallel p (M.subst x N) (M'.subst x N') := by
  apply OracleParallel.substs hM [(x, N)] [(x, N')]
  · intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hx
  · intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hx
  · intro v
    simp only [AlphaTerm.substs, subst_var]
    by_cases h : v = x
    · simpa only [ite_eq_left h] using hN
    · simp only [ite_eq_right h]; exact .var v

theorem oracle_steps_app_left {p : ℕ → ℕ} {M M' : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M M') (N : AlphaTerm) :
    Relation.ReflTransGen (OracleStep p) (app M N) (app M' N) := by
  induction h with
  | refl => exact .refl
  | tail hs ht ih => exact .tail ih (.app_left N ht)

theorem oracle_steps_app_right {p : ℕ → ℕ} (M : AlphaTerm) {N N' : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) N N') :
    Relation.ReflTransGen (OracleStep p) (app M N) (app M N') := by
  induction h with
  | refl => exact .refl
  | tail hs ht ih => exact .tail ih (.app_right M ht)

theorem oracle_steps_app {p : ℕ → ℕ} {M M' N N' : AlphaTerm}
    (hM : Relation.ReflTransGen (OracleStep p) M M')
    (hN : Relation.ReflTransGen (OracleStep p) N N') :
    Relation.ReflTransGen (OracleStep p) (app M N) (app M' N') :=
  (oracle_steps_app_left hM N).trans (oracle_steps_app_right M' hN)

theorem oracle_steps_lam {p : ℕ → ℕ} (x : ℕ) (hx : x ≠ 0) {M N : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N) :
    Relation.ReflTransGen (OracleStep p) (lam x M) (lam x N) := by
  induction h with
  | refl => exact .refl
  | tail hs ht ih => exact .tail ih (.lam x hx ht)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    A parallel step is a finite beta/query reduction: reduce the components and then contract the root when required. Conversely, each beta/query step is parallel. For a beta step under any binder, first choose a fresh binder different from $o$; the ordinary beta-substitution theorem justifies this renaming even when the original binder was $o$. Since numerals admit no beta/query steps, a parallel step from a numeral leaves it unchanged.
-/
theorem OracleParallel.steps {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleParallel p M N) :
    Relation.ReflTransGen (OracleStep p) M N := by
  induction h with
  | var x => exact .refl
  | app _ _ ihM ihN => exact oracle_steps_app ihM ihN
  | lam x hx _ ih => exact oracle_steps_lam x hx ih
  | contract x hx _ _ ihM ihN =>
    exact .tail (oracle_steps_app (oracle_steps_lam x hx ihM) ihN) (.beta (.contract x _ _))
  | query n => exact .single (.query n)

theorem numeral_eq_of_oracle_steps {p : ℕ → ℕ} {n : ℕ} {M : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) (numeral n) M) : M = numeral n := by
  induction h with
  | refl => rfl
  | tail hs ht ih =>
    subst_vars
    exact False.elim (numeral_no_oracle_step p n _ ht)

theorem OracleParallel.numeral_inv {p : ℕ → ℕ} {n : ℕ} {M : AlphaTerm}
    (h : OracleParallel p (numeral n) M) : M = numeral n :=
  numeral_eq_of_oracle_steps h.steps

/-- Ordinary beta steps remain available even beneath a binder named 0. -/
theorem Beta.oracleParallel_substs {M N : AlphaTerm} (h : Beta M N)
    (p : ℕ → ℕ) (σ : List (ℕ × AlphaTerm)) :
    OracleParallel p (AlphaTerm.substs M σ) (AlphaTerm.substs N σ) := by
  induction h generalizing σ with
  | contract y M A =>
    obtain ⟨x, B, C, hs, ht⟩ := substs_redex M A y σ
    let z := Term.fresh (B.fv ∪ {0})
    have hz : z ∉ B.fv ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or]
        using Term.fresh_not_mem (B.fv ∪ {0})
    rw [hs, ht, lam_rename B x z hz.1,
      contract_eq B (B.subst x (var z)) C x z (lam_rename B x z hz.1)]
    exact .contract z hz.2 (.refl _ _) (.refl _ _)
  | app_left N h ih =>
    rw [substs_app, substs_app]
    exact .app (ih σ) (.refl _ _)
  | app_right M h ih =>
    rw [substs_app, substs_app]
    exact .app (.refl _ _) (ih σ)
  | @lam y M M' h ih =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ ∪ {0})
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ ∪ {0})
    rw [lam_rename M y z hz.1, lam_rename M' y z hz.2.1,
      substs_lam_fresh _ z σ hz.2.2.1, substs_lam_fresh _ z σ hz.2.2.1]
    exact .lam z hz.2.2.2 (ih ((y, var z) :: σ))

theorem OracleStep.parallel {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleStep p M N) :
    OracleParallel p M N := by
  induction h with
  | beta h => exact h.oracleParallel_substs p []
  | query n => exact .query n
  | app_left N _ ih => exact .app ih (.refl _ _)
  | app_right M _ ih => exact .app (.refl _ _) ih
  | lam x hx _ ih => exact .lam x hx ih

theorem OracleParallel.var_inv {p : ℕ → ℕ} {P Q : AlphaTerm} (h : OracleParallel p P Q)
    {x : ℕ} (he : P = AlphaTerm.var x) : Q = AlphaTerm.var x := by
  cases h with
  | var y => exact he
  | app hM hN => exact False.elim (var_ne_app _ _ _ he.symm)
  | lam y hy hM => exact False.elim (var_ne_lam _ _ _ he.symm)
  | contract y hy hM hN => exact False.elim (var_ne_app _ _ _ he.symm)
  | query n => exact False.elim (var_ne_app _ _ _ he.symm)

theorem OracleParallel.app_inv {p : ℕ → ℕ} {S Q : AlphaTerm} (h : OracleParallel p S Q)
    {P A : AlphaTerm} (he : S = AlphaTerm.app P A) :
    (∃ P' A', Q = AlphaTerm.app P' A' ∧ OracleParallel p P P' ∧ OracleParallel p A A') ∨
    (∃ y B B' A', y ≠ 0 ∧ P = AlphaTerm.lam y B ∧ OracleParallel p B B' ∧
      OracleParallel p A A' ∧ Q = B'.subst y A') ∨
    (∃ n, P = AlphaTerm.var 0 ∧ A = numeral n ∧ Q = numeral (p n)) := by
  cases h with
  | var x => exact False.elim (var_ne_app _ _ _ he)
  | @app M M' N N' hM hN =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact Or.inl ⟨M', N', rfl, hM, hN⟩
  | lam y hy hM => exact False.elim (app_ne_lam _ _ _ _ he.symm)
  | @contract y hy M M' N N' hM hN =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact Or.inr (Or.inl ⟨y, M, M', N', hy, rfl, hM, hN, rfl⟩)
  | query n =>
    obtain ⟨rfl, rfl⟩ := app_inj he
    exact Or.inr (Or.inr ⟨n, rfl, rfl, rfl⟩)

theorem OracleParallel.lam_inv {p : ℕ → ℕ} {P Q : AlphaTerm} (h : OracleParallel p P Q)
    {y : ℕ} (_hy : y ≠ 0) {M : AlphaTerm} (he : P = AlphaTerm.lam y M) :
    ∃ M', Q = AlphaTerm.lam y M' ∧ OracleParallel p M M' := by
  cases h with
  | var x => exact False.elim (var_ne_lam _ _ _ he)
  | app hM hN => exact False.elim (app_ne_lam _ _ _ _ he)
  | contract x hx hM hN => exact False.elim (app_ne_lam _ _ _ _ he)
  | query n => exact False.elim (app_ne_lam _ _ _ _ he)
  | @lam z hz N N' hN =>
    by_cases hzy : z = y
    · subst z
      have hm := lam_inj y he
      subst M
      exact ⟨N', rfl, hN⟩
    · have hyN : y ∉ N.fv := by
        intro hy'
        have hf := congrArg AlphaTerm.fv he
        have hy'' : y ∈ (AlphaTerm.lam z N).fv := by
          simpa only [fv_lam, Finset.mem_erase] using And.intro (Ne.symm hzy) hy'
        rw [hf, fv_lam] at hy''
        exact (Finset.mem_erase.mp hy'').1 rfl
      have hyN' : y ∉ N'.fv := fun hy' => hyN (hN.fv_subset hy')
      have hs : N.subst z (AlphaTerm.var y) = M :=
        lam_inj y ((lam_rename N z y hyN).symm.trans he)
      refine ⟨N'.subst z (AlphaTerm.var y), lam_rename N' z y hyN', ?_⟩
      rw [← hs]
      exact hN.subst (.refl _ _) z hz

/-- Query and beta contraction have disjoint root shapes; numeral arguments
are already normal. These are the extra cases of the parallel diamond. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Now repeat the parallel diamond proof, using fresh binders and the restricted substitution lemma. Only the cases involving a root query are new. A beta contraction cannot compete with a root query: its operator is an abstraction, whereas a query's operator is the variable $o$. If the other step retains the application, its operator stays $o$ and its numeral argument stays unchanged, so that result takes the same query step. If both steps query, injectivity of Church numerals gives the same queried index and hence the same answer. All other cases join exactly as in the beta diamond proof. Moving a parallel step across a finite parallel reduction and then iterating this construction joins any two finite reductions. The equivalence with finite beta/query reduction proves confluence. Numerals are terminal, so any common reduct of two numeral outputs equals both of them; their injectivity proves equality of the output values.
-/
theorem OracleParallel.diamond {p : ℕ → ℕ} {M N : AlphaTerm} (h : OracleParallel p M N) :
    ∀ {P}, OracleParallel p M P → ∃ Q, OracleParallel p N Q ∧ OracleParallel p P Q := by
  induction h with
  | var x =>
    intro P hP
    have he := hP.var_inv rfl
    subst P
    exact ⟨_, .refl _ _, .refl _ _⟩
  | @lam y hy M M' hM ih =>
    intro P hP
    obtain ⟨M'', rfl, hM''⟩ := hP.lam_inv hy rfl
    obtain ⟨R, hR, hR'⟩ := ih hM''
    exact ⟨AlphaTerm.lam y R, .lam y hy hR, .lam y hy hR'⟩
  | @app M M' N N' hM hN ihM ihN =>
    intro P hP
    rcases hP.app_inv rfl with ⟨M'', N'', rfl, hM'', hN''⟩ |
        ⟨y, B, B', N'', hy, he, hB, hN'', rfl⟩ | ⟨n, heM, heN, rfl⟩
    · obtain ⟨R, hR, hR'⟩ := ihM hM''
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      exact ⟨AlphaTerm.app R S, .app hR hS, .app hR' hS'⟩
    · subst M
      obtain ⟨C, rfl, hC⟩ := hM.lam_inv hy rfl
      obtain ⟨L, hL, hL'⟩ := ihM (.lam y hy hB)
      obtain ⟨D, rfl, hD⟩ := hL.lam_inv hy rfl
      obtain ⟨D', heD, hD'⟩ := hL'.lam_inv hy rfl
      have hd := lam_inj y heD
      subst D'
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      exact ⟨D.subst y S, .contract y hy hD hS, hD'.subst hS' y hy⟩
    · subst M N
      have heM' := hM.var_inv rfl
      have heN' := hN.numeral_inv
      subst M' N'
      exact ⟨numeral (p n), .query n, .refl _ _⟩
  | @contract y hy M M' N N' hM hN ihM ihN =>
    intro P hP
    rcases hP.app_inv rfl with ⟨L, N'', rfl, hL, hN''⟩ |
        ⟨z, B, B', N'', hz, he, hB, hN'', rfl⟩ | ⟨n, he, _, _⟩
    · obtain ⟨M'', rfl, hM''⟩ := hL.lam_inv hy rfl
      obtain ⟨R, hR, hR'⟩ := ihM hM''
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      exact ⟨R.subst y S, hR.subst hS y hy, .contract y hy hR' hS'⟩
    · obtain ⟨D, heD, hD⟩ := (OracleParallel.lam z hz hB).lam_inv hy he.symm
      obtain ⟨R, hR, hR'⟩ := ihM hD
      obtain ⟨S, hS, hS'⟩ := ihN hN''
      refine ⟨R.subst y S, hR.subst hS y hy, ?_⟩
      rw [contract_eq B' D N'' z y heD]
      exact hR'.subst hS' y hy
    · exact False.elim (var_ne_lam _ _ _ he.symm)
  | query n =>
    intro P hP
    rcases hP.app_inv rfl with ⟨L, A, rfl, hL, hA⟩ |
        ⟨y, B, B', A, hy, he, _, _, _⟩ | ⟨m, _, he, rfl⟩
    · have heL := hL.var_inv rfl
      have heA := hA.numeral_inv
      subst L A
      exact ⟨numeral (p n), .refl _ _, .query n⟩
    · exact False.elim (var_ne_lam _ _ _ he)
    · have hnm := numeral_injective he
      subst m
      exact ⟨numeral (p n), .refl _ _, .refl _ _⟩

theorem oracle_parallel_strip {p : ℕ → ℕ} {M N P : AlphaTerm} (h : OracleParallel p M N)
    (hs : Relation.ReflTransGen (OracleParallel p) M P) :
    ∃ Q, Relation.ReflTransGen (OracleParallel p) N Q ∧ OracleParallel p P Q := by
  induction hs with
  | refl => exact ⟨N, .refl, h⟩
  | tail hs ht ih =>
    obtain ⟨R, hNR, hPR⟩ := ih
    obtain ⟨S, hRS, hPS⟩ := hPR.diamond ht
    exact ⟨S, .tail hNR hRS, hPS⟩

theorem oracle_parallel_steps_confluent {p : ℕ → ℕ} {M N P : AlphaTerm}
    (h : Relation.ReflTransGen (OracleParallel p) M N)
    (h' : Relation.ReflTransGen (OracleParallel p) M P) :
    ∃ Q, Relation.ReflTransGen (OracleParallel p) N Q ∧
      Relation.ReflTransGen (OracleParallel p) P Q := by
  induction h with
  | refl => exact ⟨P, h', .refl⟩
  | tail hs ht ih =>
    obtain ⟨R, hR, hR'⟩ := ih
    obtain ⟨S, hS, hS'⟩ := oracle_parallel_strip ht hR
    exact ⟨S, hS, .tail hR' hS'⟩

theorem oracle_parallel_steps_iff {p : ℕ → ℕ} {M N : AlphaTerm} :
    Relation.ReflTransGen (OracleParallel p) M N ↔ Relation.ReflTransGen (OracleStep p) M N := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail hs ht ih => exact ih.trans ht.steps
  · intro h
    induction h with
    | refl => exact .refl
    | tail hs ht ih => exact .tail ih ht.parallel

/-- The input-name extension is confluent for every supplied name. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Confluence with input queries
-/
theorem oracle_confluent {p : ℕ → ℕ} {M N P : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N)
    (h' : Relation.ReflTransGen (OracleStep p) M P) :
    ∃ Q, Relation.ReflTransGen (OracleStep p) N Q ∧ Relation.ReflTransGen (OracleStep p) P Q := by
  obtain ⟨Q, hQ, hQ'⟩ := oracle_parallel_steps_confluent
    (oracle_parallel_steps_iff.mpr h) (oracle_parallel_steps_iff.mpr h')
  exact ⟨Q, oracle_parallel_steps_iff.mp hQ, oracle_parallel_steps_iff.mp hQ'⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Confluence with input queries
-/
theorem oracle_numeral_output_unique {p : ℕ → ℕ} {M : AlphaTerm} {n m : ℕ}
    (hn : Relation.ReflTransGen (OracleStep p) M (numeral n))
    (hm : Relation.ReflTransGen (OracleStep p) M (numeral m)) : n = m := by
  obtain ⟨Q, hQ, hQ'⟩ := oracle_confluent hn hm
  exact numeral_injective ((numeral_eq_of_oracle_steps hQ).symm.trans
    (numeral_eq_of_oracle_steps hQ'))

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    This is the usual confluence property with the input function held fixed. It makes numerical output unambiguous. The
    complete reduction proof is given in §{sec:lambda-input-confluence}; the applications in this chapter use only the
    stated conclusion.
-/
theorem OracleRuns.output_unique {p : ℕ → ℕ} {P : AlphaTerm} {n a b : ℕ}
    (ha : OracleRuns p P n a) (hb : OracleRuns p P n b) : a = b :=
  oracle_numeral_output_unique ha hb

/-- Substituting an implementation for the input name simulates each query.
The implementation is itself a lambda term, not a second program language. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Fix a valid input name $p$ and let $q$ be its image under the inner map. Put $R=Q\,o$. For every $i$, the term $R\ChurchNumeral{i}$ reduces with input $p$ to $\ChurchNumeral{q(i)}$. In a finite reduction of the outer program with input $q$, replace the free variable $o$ by $R$. A beta step remains a beta step by capture-avoiding substitution. A query at $i$ is replaced by the finite reduction just described; closed numerals are unaffected by substitution. Application contexts lift these finite reductions. Under an abstraction, choose a binder fresh for both bodies, the replacement, and $o$, then lift the reduction through that binder.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    To justify fresh renaming within this induction, strengthen the claim to finite substitution lists: require that the substituted image of $o$, applied to each numeral, produces the corresponding digit of $q$. Prepending a renaming of a binder different from $o$ preserves that image. The induction therefore applies to the renamed bodies. Concatenating the resulting finite reductions proves the substitution assertion for the whole computation.
-/
theorem OracleStep.substs_simulate {p q : ℕ → ℕ} {M N : AlphaTerm}
    (h : OracleStep q M N) (σ : List (ℕ × AlphaTerm))
    (hq : ∀ n, Relation.ReflTransGen (OracleStep p)
      (app (AlphaTerm.substs (var 0) σ) (numeral n)) (numeral (q n))) :
    Relation.ReflTransGen (OracleStep p) (substs M σ) (substs N σ) := by
  induction h generalizing σ with
  | beta h => exact .single (.beta (h.substs σ))
  | query n =>
    rw [substs_app, substs_closed _ (numeral_closed n), substs_closed _ (numeral_closed (q n))]
    exact hq n
  | app_left N h ih =>
    rw [substs_app, substs_app]
    exact oracle_steps_app_left (ih σ hq) _
  | app_right M h ih =>
    rw [substs_app, substs_app]
    exact oracle_steps_app_right _ (ih σ hq)
  | @lam y hy M M' h ih =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ ∪ {0})
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ ∪ {0})
    have hq' : ∀ n, Relation.ReflTransGen (OracleStep p)
        (app (AlphaTerm.substs (var 0) ((y, var z) :: σ)) (numeral n)) (numeral (q n)) := by
      intro n
      simpa only [AlphaTerm.substs, subst_var, ite_eq_right (Ne.symm hy)] using hq n
    rw [lam_rename M y z hz.1, lam_rename M' y z hz.2.1,
      substs_lam_fresh _ z σ hz.2.2.1, substs_lam_fresh _ z σ hz.2.2.1]
    exact oracle_steps_lam z hz.2.2.2 (ih ((y, var z) :: σ) hq')

theorem oracle_steps_subst_input {p q : ℕ → ℕ} {M N R : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep q) M N)
    (hq : ∀ n, Relation.ReflTransGen (OracleStep p) (app R (numeral n)) (numeral (q n))) :
    Relation.ReflTransGen (OracleStep p) (M.subst 0 R) (N.subst 0 R) := by
  induction h with
  | refl => exact .refl
  | tail hs ht ih =>
    apply ih.trans
    apply ht.substs_simulate [(0, R)]
    intro n
    simpa [AlphaTerm.substs, subst_var] using hq n

end PolishSpaceBook.NamedLambda.AlphaTerm
