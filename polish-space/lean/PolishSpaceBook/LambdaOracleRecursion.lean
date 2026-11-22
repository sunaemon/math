module

public import PolishSpaceBook.LambdaPrimitiveRecursion
public import PolishSpaceBook.LambdaBasicRealizers

@[expose] public section

/-! # Primitive recursion with an input name in the same lambda calculus -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- A term whose only possible free variable is the input avoids every other binder. -/
theorem input_fresh {M : AlphaTerm} (hM : M.fv ⊆ {0}) {x : ℕ} (hx : x ≠ 0) : x ∉ M.fv := by
  intro h
  exact hx (Finset.mem_singleton.mp (hM h))

theorem beta_steps_oracle {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : Relation.ReflTransGen Beta M N) : Relation.ReflTransGen (OracleStep p) M N := by
  induction h with
  | refl => exact .refl
  | tail hs ht ih => exact .tail ih (.beta ht)

/-- The state values are closed, while the step term may query the free input. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Write
    $$S_k:=\LambdaPairValue{\ChurchNumeral{k}}{\ChurchNumeral{r_p(k)}}.$$
    Each state is closed. One application of $\LambdaRecUpdate{G}$ first selects its index and value. Successor produces the next index; the assumed reduction of $G$ on the old index and value produces the next value, using whatever queries that reduction requires. Pair formation therefore gives
    $$\LambdaInputSteps{p}{\LambdaRecUpdate{G}\,S_k}{S_{k+1}}.$$
    Induction on the iteration count now yields
    $$\LambdaInputSteps{p}{\LambdaIter{\LambdaRecUpdate{G}}{S_0}{n}}{S_n}.$$
    The zero case is the empty reduction. At a successor stage, reduce the preceding iterate and then perform the single update just described.
-/
theorem recursionUpdate_oracle_apply {p : ℕ → ℕ} {G A B : AlphaTerm}
    (hG : G.fv ⊆ {0}) (hA : A.Closed) (hB : B.Closed) (n : ℕ)
    (hg : Relation.ReflTransGen (OracleStep p) (app (app G (numeral n)) A) B) :
    Relation.ReflTransGen (OracleStep p) (app (recursionUpdate G) (pairValue (numeral n) A))
      (pairValue (numeral (n + 1)) B) := by
  let S := pairValue (numeral n) A
  have h₁ : Beta (app (recursionUpdate G) S)
      (app (app pairTerm (app successorTerm (app S trueTerm)))
        (app (app G (app S trueTerm)) (app S falseTerm))) := by
    convert Beta.contract 6
      (app (app pairTerm (app successorTerm (app (var 6) trueTerm)))
        (app (app G (app (var 6) trueTerm)) (app (var 6) falseTerm))) S using 1 <;> try rfl
    simp [subst_app, subst_var, subst_closed _ _ _ pairTerm_closed,
      subst_closed _ _ _ successorTerm_closed, subst_closed _ _ _ trueTerm_closed,
      subst_closed _ _ _ falseTerm_closed, subst_not_free _ _ _ (input_fresh hG (by decide : 6 ≠ 0))]
  have hs₁ : Relation.ReflTransGen (OracleStep p) (app S trueTerm) (numeral n) :=
    beta_steps_oracle (pairValue_first (numeral_closed n) hA)
  have hs₂ : Relation.ReflTransGen (OracleStep p) (app S falseTerm) A :=
    beta_steps_oracle (pairValue_second (numeral_closed n) hA)
  have hn := (oracle_steps_app_right successorTerm hs₁).trans (beta_steps_oracle (successorTerm_apply n))
  have hb := (oracle_steps_app (oracle_steps_app_right G hs₁) hs₂).trans hg
  exact (Relation.ReflTransGen.single (.beta h₁)).trans
    ((oracle_steps_app (oracle_steps_app_right pairTerm hn) hb).trans
      (beta_steps_oracle (pairTerm_apply (numeral_closed (n + 1)) hB)))

/-- Only the updates actually executed need to terminate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Use the states $\LambdaPairValue{\ChurchNumeral{k}}{\ChurchNumeral{v_k}}$ in the preceding argument and stop the induction at $n$. Each successor step uses only the assumed update for that stage. The base computation and final selection are unchanged. This also covers $n=0$, when no update is performed.
-/
theorem iterate_recursionUpdate_oracle_upto {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0})
    (V : ℕ → AlphaTerm) (hV : ∀ k, (V k).Closed) (n : ℕ)
    (hstep : ∀ k < n, Relation.ReflTransGen (OracleStep p)
      (app (app G (numeral k)) (V k)) (V (k + 1))) :
    Relation.ReflTransGen (OracleStep p)
      (iterateApp (recursionUpdate G) (pairValue (numeral 0) (V 0)) n)
      (pairValue (numeral n) (V n)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    have hs := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    exact (oracle_steps_app_right (recursionUpdate G) hs).trans
      (recursionUpdate_oracle_apply hG (hV n) (hV (n + 1)) n (hstep n (Nat.lt_succ_self n)))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Write
    $$S_k:=\LambdaPairValue{\ChurchNumeral{k}}{\ChurchNumeral{r_p(k)}}.$$
    Each state is closed. One application of $\LambdaRecUpdate{G}$ first selects its index and value. Successor produces the next index; the assumed reduction of $G$ on the old index and value produces the next value, using whatever queries that reduction requires. Pair formation therefore gives
    $$\LambdaInputSteps{p}{\LambdaRecUpdate{G}\,S_k}{S_{k+1}}.$$
    Induction on the iteration count now yields
    $$\LambdaInputSteps{p}{\LambdaIter{\LambdaRecUpdate{G}}{S_0}{n}}{S_n}.$$
    The zero case is the empty reduction. At a successor stage, reduce the preceding iterate and then perform the single update just described.
-/
theorem iterate_recursionUpdate_oracle {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0})
    (V : ℕ → AlphaTerm) (hV : ∀ n, (V n).Closed)
    (hstep : ∀ n, Relation.ReflTransGen (OracleStep p)
      (app (app G (numeral n)) (V n)) (V (n + 1))) (n : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (iterateApp (recursionUpdate G) (pairValue (numeral 0) (V 0)) n)
      (pairValue (numeral n) (V n)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    exact (oracle_steps_app_right (recursionUpdate G) ih).trans
      (recursionUpdate_oracle_apply hG (hV n) (hV (n + 1)) n (hstep n))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Fix $p\in D$ and put $G:=Ho$. Since $H$ is closed, the only possible free variable of $G$ is $o$. Unfold the parameterized recursor and reduce $Bo$ to $\ChurchNumeral{a(p)}$. The three outer beta steps of the recursor then expose its iteration body. The freshness of the internal binders preserves $G$ throughout these substitutions; it need not be closed.
-/
theorem recursorTerm_input_start {G A : AlphaTerm} (hG : G.fv ⊆ {0}) (hA : A.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (app recursorTerm G) A) (numeral n))
      (app (iterateApp (recursionUpdate G) (pairValue (numeral 0) A) n) falseTerm) := by
  have hGf (x : ℕ) (hx : x ≠ 0) : x ∉ G.fv := input_fresh hG hx
  have hUf (x : ℕ) (hx : x ≠ 0) : x ∉ (recursionUpdate G).fv := by
    rw [recursionUpdate_fv]
    exact fun h => hGf x hx (Finset.mem_erase.mp h).2
  have hAf (x : ℕ) : x ∉ A.fv := by rw [hA]; simp
  have h₁ : Beta (app recursorTerm G) (lam 8 (lam 3
      (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) (var 8))) falseTerm))) := by
    convert Beta.contract 7 (lam 8 (lam 3
      (app (app (app (var 3) (recursionUpdate (var 7)))
        (app (app pairTerm (numeral 0)) (var 8))) falseTerm))) G using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 8 7 (by decide) (hGf 8 (by decide)),
      subst_lam_fresh _ _ 3 7 (by decide) (hGf 3 (by decide))]
    simp [subst_app, subst_var, subst_recursionUpdate _ _ 7 (by decide) (hGf 6 (by decide)),
      subst_closed _ _ _ pairTerm_closed, subst_closed _ _ _ (numeral_closed 0),
      subst_closed _ _ _ falseTerm_closed]
  have h₂ : Beta (app (lam 8 (lam 3
      (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) (var 8))) falseTerm))) A)
      (lam 3 (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) A)) falseTerm)) := by
    convert Beta.contract 8 (lam 3
      (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) (var 8))) falseTerm)) A using 1
    rw [subst_lam_fresh _ _ 3 8 (by decide) (hAf 3)]
    simp [subst_app, subst_var, subst_not_free _ _ _ (hUf 8 (by decide)),
      subst_closed _ _ _ pairTerm_closed, subst_closed _ _ _ (numeral_closed 0),
      subst_closed _ _ _ falseTerm_closed]
  have h₃ : Beta (app (lam 3 (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) A)) falseTerm)) (numeral n))
      (app (app (app (numeral n) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) A)) falseTerm) := by
    convert Beta.contract 3 (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) A)) falseTerm) (numeral n) using 1
    simp [subst_app, subst_var, subst_not_free _ _ _ (hUf 3 (by decide)),
      subst_closed _ _ _ pairTerm_closed, subst_closed _ _ _ (numeral_closed 0),
      subst_closed _ _ _ falseTerm_closed, subst_closed _ _ _ hA]
  have hp := beta_steps_app_left (beta_steps_app_right (app (numeral n) (recursionUpdate G))
    (pairTerm_apply (numeral_closed 0) hA)) falseTerm
  have hf : 2 ∉ (recursionUpdate G).fv := hUf 2 (by decide)
  exact (Relation.ReflTransGen.tail (.tail (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂)) h₃).trans
    (hp.trans (beta_steps_app_left (numeral_apply n (recursionUpdate G) (pairValue (numeral 0) A) hf) falseTerm))

theorem recursorTerm_oracle_apply_upto {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0})
    (V : ℕ → AlphaTerm) (hV : ∀ k, (V k).Closed) (n : ℕ)
    (hstep : ∀ k < n, Relation.ReflTransGen (OracleStep p)
      (app (app G (numeral k)) (V k)) (V (k + 1))) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app recursorTerm G) (V 0)) (numeral n)) (V n) :=
  (beta_steps_oracle (recursorTerm_input_start hG (hV 0) n)).trans
    ((oracle_steps_app_left (iterate_recursionUpdate_oracle_upto hG V hV n hstep) falseTerm).trans
      (beta_steps_oracle (pairValue_second (numeral_closed n) (hV n))))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    The Church numeral unfolds to precisely this iteration: its binders also avoid $o$, so the iteration formula applies even though $\LambdaRecUpdate{G}$ may have that free variable. Selecting the value component of the final state returns $\ChurchNumeral{r_p(n)}$. All stages use finite reductions, hence so does their concatenation. Closedness of $B,H$ makes $\LambdaParamRec{B}{H}$ closed independently of $p$ and $n$. By confluence for beta/query reduction, no different numeral can be returned. This proves the exact-output condition for a realizer. No test for membership in $D$ is needed.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The recursor from §{sec:lambda-primitive-recursion} also permits queries to an input name during the update. Use the
    input variable $o$ and finite reductions $\LambdaInputSteps{p}{M}{N}$ just defined. Besides beta steps, these reductions
    allow $o\ChurchNumeral{i}$ to return $\ChurchNumeral{p(i)}$. Choose the recursor's internal binders distinct from $o$,
    so that they do not capture the input variable. The program is still an ordinary finite lambda term; only the behavior
    of the supplied argument is specified by the query rule.
-/
theorem recursorTerm_oracle_apply {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0})
    (V : ℕ → AlphaTerm) (hV : ∀ n, (V n).Closed)
    (hstep : ∀ n, Relation.ReflTransGen (OracleStep p)
      (app (app G (numeral n)) (V n)) (V (n + 1))) (n : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app recursorTerm G) (V 0)) (numeral n)) (V n) :=
  (beta_steps_oracle (recursorTerm_input_start hG (hV 0) n)).trans
    ((oracle_steps_app_left (iterate_recursionUpdate_oracle hG V hV hstep n) falseTerm).trans
      (beta_steps_oracle (pairValue_second (numeral_closed n) (hV n))))

theorem recursorTerm_oracle_numeral {p : ℕ → ℕ} {G : AlphaTerm} (hG : G.fv ⊆ {0})
    (a : ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ k r, Relation.ReflTransGen (OracleStep p)
      (app (app G (numeral k)) (numeral r)) (numeral (g k r))) (n : ℕ) :
    Relation.ReflTransGen (OracleStep p) (app (app (app recursorTerm G) (numeral a)) (numeral n))
      (numeral (primitiveRec a g n)) :=
  recursorTerm_oracle_apply hG (fun k => numeral (primitiveRec a g k))
    (fun _ => numeral_closed _) (fun k => hg k _) n

theorem parameterRecursor_input_start {B H X : AlphaTerm} (hB : B.Closed) (hH : H.Closed)
    (hX : X.fv ⊆ {0}) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (parameterRecursor B H) X) (numeral n))
      (app (app (app recursorTerm (app H X)) (app B X)) (numeral n)) := by
  have hf : 10 ∉ X.fv := input_fresh hX (by decide)
  have h₁ : Beta (app (parameterRecursor B H) X)
      (lam 10 (app (app (app recursorTerm (app H X)) (app B X)) (var 10))) := by
    convert Beta.contract 9 (lam 10
      (app (app (app recursorTerm (app H (var 9))) (app B (var 9))) (var 10))) X using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 10 9 (by decide) hf]
    simp [subst_app, subst_var, subst_closed _ _ _ recursorTerm_closed,
      subst_closed _ _ _ hB, subst_closed _ _ _ hH]
  have h₂ : Beta (app (lam 10
      (app (app (app recursorTerm (app H X)) (app B X)) (var 10))) (numeral n))
      (app (app (app recursorTerm (app H X)) (app B X)) (numeral n)) := by
    convert Beta.contract 10
      (app (app (app recursorTerm (app H X)) (app B X)) (var 10)) (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ recursorTerm_closed,
      subst_closed _ _ _ hB, subst_closed _ _ _ hH, subst_not_free _ _ _ hf]
  exact .tail (.single (.app_left _ h₁)) h₂

theorem parameterRecursor_oracle_apply_input {p : ℕ → ℕ} {B H X : AlphaTerm}
    (hB : B.Closed) (hH : H.Closed) (hX : X.fv ⊆ {0}) (a : ℕ) (g : ℕ → ℕ → ℕ)
    (hb : Relation.ReflTransGen (OracleStep p) (app B X) (numeral a))
    (hg : ∀ k r, Relation.ReflTransGen (OracleStep p)
      (app (app (app H X) (numeral k)) (numeral r)) (numeral (g k r))) (n : ℕ) :
    Relation.ReflTransGen (OracleStep p) (app (app (parameterRecursor B H) X) (numeral n))
      (numeral (primitiveRec a g n)) := by
  have hG : (app H X).fv ⊆ {0} := by
    rw [fv_app, hH, Finset.empty_union]
    exact hX
  exact (beta_steps_oracle (parameterRecursor_input_start hB hH hX n)).trans
    ((oracle_steps_app_left (oracle_steps_app_right (app recursorTerm (app H X)) hb) (numeral n)).trans
      (recursorTerm_oracle_numeral hG a g hg n))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: corollary
  title: Finite-stage recursion
-/
theorem parameterRecursor_oracle_apply_upto {p : ℕ → ℕ} {B H : AlphaTerm}
    (hB : B.Closed) (hH : H.Closed) (v : ℕ → ℕ) (n : ℕ)
    (hb : Relation.ReflTransGen (OracleStep p) (app B (var 0)) (numeral (v 0)))
    (hg : ∀ k < n, Relation.ReflTransGen (OracleStep p)
      (app (app (app H (var 0)) (numeral k)) (numeral (v k))) (numeral (v (k + 1)))) :
    OracleRuns p (parameterRecursor B H) n (v n) := by
  have hX : (var 0).fv ⊆ {0} := by rw [fv_var]
  have hG : (app H (var 0)).fv ⊆ {0} := by rw [fv_app, hH, fv_var]; simp
  exact (beta_steps_oracle (parameterRecursor_input_start hB hH hX n)).trans
    ((oracle_steps_app_left (oracle_steps_app_right (app recursorTerm (app H (var 0))) hb) (numeral n)).trans
      (recursorTerm_oracle_apply_upto hG (fun k => numeral (v k)) (fun _ => numeral_closed _) n hg))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Primitive recursion with an input name
-/
theorem parameterRecursor_oracle_apply {p : ℕ → ℕ} {B H : AlphaTerm}
    (hB : B.Closed) (hH : H.Closed) (a : ℕ) (g : ℕ → ℕ → ℕ)
    (hb : Relation.ReflTransGen (OracleStep p) (app B (var 0)) (numeral a))
    (hg : ∀ k r, Relation.ReflTransGen (OracleStep p)
      (app (app (app H (var 0)) (numeral k)) (numeral r)) (numeral (g k r))) (n : ℕ) :
    OracleRuns p (parameterRecursor B H) n (primitiveRec a g n) :=
  parameterRecursor_oracle_apply_input hB hH (by rw [fv_var]) a g hb hg n

/-- One closed term works uniformly over the whole name domain. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Primitive recursion with an input name
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    The Church numeral unfolds to precisely this iteration: its binders also avoid $o$, so the iteration formula applies even though $\LambdaRecUpdate{G}$ may have that free variable. Selecting the value component of the final state returns $\ChurchNumeral{r_p(n)}$. All stages use finite reductions, hence so does their concatenation. Closedness of $B,H$ makes $\LambdaParamRec{B}{H}$ closed independently of $p$ and $n$. By confluence for beta/query reduction, no different numeral can be returned. This proves the exact-output condition for a realizer. No test for membership in $D$ is needed.
-/
theorem parameterRecursor_typeTwoComputes {D : Set (ℕ → ℕ)} {B H : AlphaTerm}
    (hB : B.Closed) (hH : H.Closed) (a : D → ℕ) (g : D → ℕ → ℕ → ℕ)
    (hb : ∀ p : D, Relation.ReflTransGen (OracleStep p.val) (app B (var 0)) (numeral (a p)))
    (hg : ∀ (p : D) k r, Relation.ReflTransGen (OracleStep p.val)
      (app (app (app H (var 0)) (numeral k)) (numeral r)) (numeral (g p k r))) :
    TypeTwoComputes (parameterRecursor B H) (fun p n => primitiveRec (a p) (g p) n) := by
  rw [typeTwoComputes_iff_runs]
  exact ⟨parameterRecursor_closed hB hH,
    fun p n => parameterRecursor_oracle_apply hB hH (a p) (g p) (hb p) (hg p) n⟩

/-- The name argument is kept separate from the stage and the current state. -/
def inputIterationStep : AlphaTerm := lam 11 (lam 3 (lam 4 (app (var 11) (var 4))))

@[simp] theorem inputIterationStep_closed : inputIterationStep.Closed := by
  unfold inputIterationStep Closed
  simp [fv_lam, fv_app, fv_var]
  decide

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    The base term returns $\ChurchNumeral{0}$ by one beta step. For the update, three beta steps reduce $H\,o\,\ChurchNumeral{k}\,\ChurchNumeral{r}$ to $o\ChurchNumeral{r}$, and one query returns $\ChurchNumeral{p(r)}$. Both terms are closed. Apply the theorem with $a(p)=0$ and $g(p,k,r)=p(r)$.
-/
theorem inputIterationStep_apply (p : ℕ → ℕ) (k r : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app inputIterationStep (var 0)) (numeral k)) (numeral r)) (numeral (p r)) := by
  have h₁ : Beta (app inputIterationStep (var 0)) (lam 3 (lam 4 (app (var 0) (var 4)))) := by
    exact Beta.contract 11 (lam 3 (lam 4 (app (var 11) (var 4)))) (var 0)
  have h₂ : Beta (app (lam 3 (lam 4 (app (var 0) (var 4)))) (numeral k))
      (lam 4 (app (var 0) (var 4))) := by
    convert Beta.contract 3 (lam 4 (app (var 0) (var 4))) (numeral k) using 1
    rw [subst_lam_fresh _ _ 4 3 (by decide) (by rw [numeral_closed]; simp)]
    simp [subst_app, subst_var]
  have h₃ : Beta (app (lam 4 (app (var 0) (var 4))) (numeral r)) (app (var 0) (numeral r)) := by
    exact Beta.contract 4 (app (var 0) (var 4)) (numeral r)
  exact .tail (.tail (.tail (.single (.beta (.app_left _ (.app_left _ h₁))))
    (.beta (.app_left _ h₂))) (.beta h₃)) (.query r)

def inputIterationBase : AlphaTerm := lam 11 (numeral 0)

@[simp] theorem inputIterationBase_closed : inputIterationBase.Closed := by
  unfold inputIterationBase Closed
  rw [fv_lam, numeral_closed]
  simp

theorem inputIterationBase_apply (p : ℕ → ℕ) :
    Relation.ReflTransGen (OracleStep p) (app inputIterationBase (var 0)) (numeral 0) := by
  apply Relation.ReflTransGen.single
  apply OracleStep.beta
  simpa only [inputIterationBase, subst_closed _ _ _ (numeral_closed 0)] using
    Beta.contract 11 (numeral 0) (var 0)

/-- Iteration follows the previous answer as the address of the next query. -/
def inputIterationProgram : AlphaTerm := parameterRecursor inputIterationBase inputIterationStep

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: example
  title: Iteration of an input name
-/
theorem inputIteration_typeTwoComputes :
    TypeTwoComputes inputIterationProgram
      (fun p : (Set.univ : Set (ℕ → ℕ)) => primitiveRec 0 (fun _ r => p.val r)) :=
  parameterRecursor_typeTwoComputes inputIterationBase_closed inputIterationStep_closed
    (fun _ => 0) (fun p _ r => p.val r)
    (fun p => inputIterationBase_apply p.val) (fun p => inputIterationStep_apply p.val)

end PolishSpaceBook.NamedLambda.AlphaTerm
