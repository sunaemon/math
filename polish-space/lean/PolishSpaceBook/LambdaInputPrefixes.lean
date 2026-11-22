module

public import PolishSpaceBook.LambdaOracleLists

@[expose] public section

/-! # Reading a finite prefix with a lambda program

The state is the numerical code of the prefix already read. Appending a
singleton preserves the original order, including when the input accessor
itself is a lambda computation relative to another name.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

def prefixStepBody (O K S : AlphaTerm) : AlphaTerm :=
  app (app listAppendTerm S) (app (app listConsTerm (app O K)) (numeral 0))

theorem prefixStepBody_fv (O K S : AlphaTerm) :
    (prefixStepBody O K S).fv = O.fv ∪ K.fv ∪ S.fv := by
  ext x
  simp only [prefixStepBody, fv_app, (show listAppendTerm.fv = ∅ from listAppendTerm_closed),
    (show listConsTerm.fv = ∅ from listConsTerm_closed),
    (show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem prefixStepBody_subst (O K S W : AlphaTerm) (x : ℕ) :
    (prefixStepBody O K S).subst x W =
      prefixStepBody (O.subst x W) (K.subst x W) (S.subst x W) := by
  simp only [prefixStepBody, subst_app, subst_closed _ _ _ listAppendTerm_closed,
    subst_closed _ _ _ listConsTerm_closed, subst_closed _ _ _ (numeral_closed 0)]

def prefixStep (O : AlphaTerm) : AlphaTerm :=
  lam 41 (lam 42 (prefixStepBody O (var 41) (var 42)))

theorem prefixStep_fv (O : AlphaTerm) :
    (prefixStep O).fv = (O.fv.erase 42).erase 41 := by
  ext x
  simp only [prefixStep, fv_lam, prefixStepBody_fv, fv_var, Finset.mem_erase,
    Finset.mem_union, Finset.mem_singleton]
  tauto

theorem prefixStep_input {O : AlphaTerm} (hO : O.fv ⊆ {0}) :
    (prefixStep O).fv ⊆ {0} := by
  rw [prefixStep_fv]
  intro x hx
  exact hO (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2

theorem prefixStep_start {O : AlphaTerm} (hO : O.fv ⊆ {0}) (k s : ℕ) :
    Relation.ReflTransGen Beta (app (app (prefixStep O) (numeral k)) (numeral s))
      (prefixStepBody O (numeral k) (numeral s)) := by
  have h₁ : Beta (app (prefixStep O) (numeral k))
      (lam 42 (prefixStepBody O (numeral k) (var 42))) := by
    have he : (lam 42 (prefixStepBody O (var 41) (var 42))).subst 41 (numeral k) =
        lam 42 (prefixStepBody O (numeral k) (var 42)) := by
      rw [subst_lam_fresh _ _ 42 41 (by decide) (by rw [numeral_closed]; simp),
        prefixStepBody_subst, subst_not_free _ _ _ (input_fresh hO (by decide : 41 ≠ 0))]
      simp [subst_var]
    unfold prefixStep
    rw [← he]
    exact Beta.contract _ _ _
  have h₂ : Beta (app (lam 42 (prefixStepBody O (numeral k) (var 42))) (numeral s))
      (prefixStepBody O (numeral k) (numeral s)) := by
    have he : (prefixStepBody O (numeral k) (var 42)).subst 42 (numeral s) =
        prefixStepBody O (numeral k) (numeral s) := by
      rw [prefixStepBody_subst,
        subst_not_free _ _ _ (input_fresh hO (by decide : 42 ≠ 0)),
        subst_closed _ _ _ (numeral_closed k)]
      simp [subst_var]
    rw [← he]
    exact Beta.contract _ _ _
  exact .tail (.single (.app_left _ h₁)) h₂

theorem prefixStep_apply {p : ℕ → ℕ} {O : AlphaTerm} (hO : O.fv ⊆ {0})
    (k v : ℕ) (xs : List ℕ)
    (hq : Relation.ReflTransGen (OracleStep p) (app O (numeral k)) (numeral v)) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (prefixStep O) (numeral k)) (numeral (NatListCode.encode xs)))
      (numeral (NatListCode.encode (xs ++ [v]))) := by
  apply (beta_steps_oracle (prefixStep_start hO k _)).trans
  have hc := (oracle_steps_app_left (oracle_steps_app_right listConsTerm hq) (numeral 0)).trans
    (beta_steps_oracle (listConsTerm_apply v 0))
  exact (oracle_steps_app_right (app listAppendTerm (numeral (NatListCode.encode xs))) hc).trans
    (beta_steps_oracle (listAppendTerm_code xs [v]))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    To read the first $n$ values of an input name, store the values already read as a numerical list code and append one new
    value at each stage. For a term $A$, put
    $$\begin{aligned}
    \LambdaPrefixStep{A}&:=\lambdaab{k}{\lambdaab{u}{
     \LambdaListAppend\,u\,(\LambdaListCons\,(Ak)\,\ChurchNumeral{0})}},\\
    \LambdaInputPrefix&:=\lambdaab{a}{\LambdaRecursor\,\LambdaPrefixStep{a}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    Expand the abbreviation $\LambdaPrefixStep{a}$ before abstracting over $a$. Choose its binders $k,u$ fresh for $A$ and
    distinct from the input variable $o$. The term $\LambdaInputPrefix$ is closed. Appending a singleton, rather than
    prepending it, preserves the order of the input values.
-/
def prefixProgram : AlphaTerm :=
  lam 40 (app (app recursorTerm (prefixStep (var 40))) (numeral 0))

@[simp] theorem prefixProgram_closed : prefixProgram.Closed := by
  unfold prefixProgram Closed
  simp only [fv_lam, fv_app, (show recursorTerm.fv = ∅ from recursorTerm_closed),
    prefixStep_fv, fv_var, (show (numeral 0).fv = ∅ from numeral_closed 0)]
  decide

theorem prefixProgram_start {O : AlphaTerm} (hO : O.fv ⊆ {0}) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app prefixProgram O) (numeral n))
      (app (app (app recursorTerm (prefixStep O)) (numeral 0)) (numeral n)) := by
  have he : (app (app recursorTerm (prefixStep (var 40))) (numeral 0)).subst 40 O =
      app (app recursorTerm (prefixStep O)) (numeral 0) := by
    simp only [subst_app, subst_closed _ _ _ recursorTerm_closed,
      subst_closed _ _ _ (numeral_closed 0)]
    unfold prefixStep
    rw [subst_lam_fresh _ _ 41 40 (by decide) (input_fresh hO (by decide)),
      subst_lam_fresh _ _ 42 40 (by decide) (input_fresh hO (by decide)), prefixStepBody_subst]
    simp [subst_var]
  apply Relation.ReflTransGen.single
  apply Beta.app_left
  unfold prefixProgram
  rw [← he]
  exact Beta.contract _ _ _

/-- Only the requested coordinates need to be computable. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    One beta step exposes the recursor with update $\LambdaPrefixStep{A}$ and initial value $\ChurchNumeral{0}$. Write
    $s_k:=\restrict{q}{k}$. At stage $k$, the state supplied for $u$ is
    $\ChurchNumeral{\LambdaListCode{s_k}}$. The empty prefix has list code zero.
    At stage $k<n$, two beta steps expose the update body; the
    assumed computation of $A\ChurchNumeral{k}$ and the list constructor produce the code of $[q(k)]$. The append program
    then produces the code of $s_k\concat[q(k)]=s_{k+1}$. All state values are closed numerals, while the update has no free
    variable other than possibly $o$. The finite-stage recursion argument in §{sec:lambda-input-recursion} therefore yields
    the code of $s_n$. For $n=0$ there is no update and no input query is needed.
-/
theorem prefixProgram_apply_upto {p q : ℕ → ℕ} {O : AlphaTerm}
    (hO : O.fv ⊆ {0}) (n : ℕ)
    (hq : ∀ k < n, Relation.ReflTransGen (OracleStep p) (app O (numeral k)) (numeral (q k))) :
    Relation.ReflTransGen (OracleStep p) (app (app prefixProgram O) (numeral n))
      (numeral (NatListCode.encode (seqPrefix q n))) := by
  apply (beta_steps_oracle (prefixProgram_start hO n)).trans
  apply recursorTerm_oracle_apply_upto (prefixStep_input hO)
    (fun k => numeral (NatListCode.encode (seqPrefix q k))) (fun _ => numeral_closed _) n
  intro k hk
  simpa only [seqPrefix_succ_eq_concat, concat] using
    prefixStep_apply hO k (q k) (seqPrefix q k) (hq k hk)

theorem prefixProgram_runs (p : ℕ → ℕ) (n : ℕ) :
    OracleRuns p prefixProgram n (NatListCode.encode (seqPrefix p n)) := by
  apply prefixProgram_apply_upto (by intro x hx; exact hx)
  intro k _
  exact .single (.query k)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Reading a finite input prefix
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    For $A=o$ and $q=p$, each required computation is one input-query step. This proves existence of the stated output; confluence and normality of numerals exclude every different numerical output. More generally, agreement of two names below $n$ gives the same prefix code, with no condition on their later values. Conversely, equal output codes imply equal prefixes because list encoding is injective.
    \end{proof}
-/
theorem prefixProgram_runs_iff (p : ℕ → ℕ) (n m : ℕ) :
    OracleRuns p prefixProgram n m ↔ m = NatListCode.encode (seqPrefix p n) := by
  constructor
  · intro h
    exact OracleRuns.output_unique h (prefixProgram_runs p n)
  · rintro rfl
    exact prefixProgram_runs p n

/-- The prefix reader is a total Type-Two realizer on every prescribed domain. -/
theorem prefixProgram_computes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes prefixProgram (fun p : D => fun n => NatListCode.encode (seqPrefix p.val n)) := by
  exact typeTwoComputes_iff_runs.mpr ⟨prefixProgram_closed, fun p n => prefixProgram_runs p.val n⟩

/-- Agreement on the requested prefix suffices; no later digit is needed. -/
theorem prefixProgram_agrees {p q : ℕ → ℕ} (n : ℕ) (hpq : ∀ k < n, q k = p k) :
    OracleRuns q prefixProgram n (NatListCode.encode (seqPrefix p n)) := by
  apply prefixProgram_apply_upto (by intro x hx; exact hx)
  intro k hk
  rw [← hpq k hk]
  exact .single (.query k)

/-- The numerical output retains the entire prefix, rather than just its length. -/
theorem prefixProgram_common_output_iff (p q : ℕ → ℕ) (n : ℕ) :
    (∃ m, OracleRuns p prefixProgram n m ∧ OracleRuns q prefixProgram n m) ↔
      seqPrefix p n = seqPrefix q n := by
  simp only [prefixProgram_runs_iff]
  constructor
  · rintro ⟨m, hp, hq⟩
    exact NatListCode.encode_injective (hp.symm.trans hq)
  · intro h
    exact ⟨_, rfl, congrArg NatListCode.encode h⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
