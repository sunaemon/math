module

public import PolishSpaceBook.LambdaNumeralOperations

@[expose] public section

/-!
# Primitive recursion by lambda iteration of a counter and a value

The recursor is one closed finite lambda term. Its correctness theorem allows
arbitrary closed lambda values, so the step operation and initial value are
runtime arguments rather than an externally assumed recursion primitive.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

def recursionUpdate (G : AlphaTerm) : AlphaTerm := lam 6
  (app (app pairTerm (app successorTerm (app (var 6) trueTerm)))
    (app (app G (app (var 6) trueTerm)) (app (var 6) falseTerm)))

theorem recursionUpdate_fv (G : AlphaTerm) : (recursionUpdate G).fv = G.fv.erase 6 := by
  unfold recursionUpdate
  simp only [fv_lam, fv_app]
  rw [pairTerm_closed, successorTerm_closed, trueTerm_closed, falseTerm_closed]
  ext x
  simp only [fv_var, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, or_false, false_or]
  aesop

theorem recursionUpdate_closed {G : AlphaTerm} (hG : G.Closed) : (recursionUpdate G).Closed := by
  unfold Closed
  rw [recursionUpdate_fv, hG]
  simp

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For closed $A,B$ with $G\ChurchNumeral{k}A\to_\beta^*B$, one update satisfies
    $$\LambdaRecUpdate{G}\,\LambdaPairValue{\ChurchNumeral{k}}{A}
    \to_\beta^*\LambdaPairValue{\ChurchNumeral{k+1}}{B}.$$
    After the root beta step, reduce the true selectors to the index and the false selector to the value. Apply successor to the first copy of the index and use the given reduction of $G$ on the second copy and the value. Finally reduce the pair constructor. Closedness prevents capture in these substitutions.
-/
theorem recursionUpdate_apply {G A B : AlphaTerm} (hG : G.Closed) (hA : A.Closed) (hB : B.Closed)
    (n : ℕ) (hg : Relation.ReflTransGen Beta (app (app G (numeral n)) A) B) :
    Relation.ReflTransGen Beta (app (recursionUpdate G) (pairValue (numeral n) A))
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
      subst_closed _ _ _ falseTerm_closed, subst_closed _ _ _ hG]
  have hs₁ : Relation.ReflTransGen Beta (app S trueTerm) (numeral n) :=
    pairValue_first (numeral_closed n) hA
  have hs₂ : Relation.ReflTransGen Beta (app S falseTerm) A :=
    pairValue_second (numeral_closed n) hA
  have hn := (beta_steps_app_right successorTerm hs₁).trans (successorTerm_apply n)
  have hb := (beta_steps_app (beta_steps_app_right G hs₁) hs₂).trans hg
  exact (Relation.ReflTransGen.single h₁).trans
    ((beta_steps_app (beta_steps_app_right pairTerm hn) hb).trans
      (pairTerm_apply (numeral_closed (n + 1)) hB))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Induction on $n$ now gives the state invariant
    $$\LambdaIter{\LambdaRecUpdate{G}}{\LambdaPairValue{\ChurchNumeral{0}}{V_0}}{n}
    \to_\beta^*\LambdaPairValue{\ChurchNumeral{n}}{V_n}.$$
    The zero case is the initial state. For the successor case, first reduce the preceding iterate using the induction hypothesis, then use the single-update calculation. No numerical encoding of the value component is needed.
-/
theorem iterate_recursionUpdate {G : AlphaTerm} (hG : G.Closed) (V : ℕ → AlphaTerm)
    (hV : ∀ n, (V n).Closed)
    (hstep : ∀ n, Relation.ReflTransGen Beta (app (app G (numeral n)) (V n)) (V (n + 1)))
    (n : ℕ) :
    Relation.ReflTransGen Beta (iterateApp (recursionUpdate G) (pairValue (numeral 0) (V 0)) n)
      (pairValue (numeral n) (V n)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    exact (beta_steps_app_right (recursionUpdate G) ih).trans
      (recursionUpdate_apply hG (hV n) (hV (n + 1)) n (hstep n))

/-- The same closed term accepts the step, the initial value, and the counter. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The pair state can carry an arbitrary closed value, not just the previous counter. Given a closed step term $G$, define
    $$\LambdaRecUpdate{G}:=\lambdaab{s}{\LambdaPair\,(\LambdaSucc(s\LambdaTrue))\,(G(s\LambdaTrue)(s\LambdaFalse))}.$$
    It reads the current index and value, increments the index, and applies $G$ to the old index and value. Define one
    closed \termdefine{lambda recursor} by
    $$\LambdaRecursor:=\lambdaab{g}{\lambdaab{a}{\lambdaab{n}{\bigl(n\LambdaRecUpdate{g}(\LambdaPair\,\ChurchNumeral{0}
    \,a)\bigr)\LambdaFalse}}}.$$
    In this expression, expand the definition of $\LambdaRecUpdate{g}$ using a binder $s$ distinct from $g,a,n$. The step
    term and initial value are arguments of this single finite lambda term.
-/
def recursorTerm : AlphaTerm := lam 7 (lam 8 (lam 3
  (app (app (app (var 3) (recursionUpdate (var 7)))
    (app (app pairTerm (numeral 0)) (var 8))) falseTerm)))

@[simp] theorem recursorTerm_closed : recursorTerm.Closed := by
  unfold recursorTerm Closed
  simp only [fv_lam, fv_app, recursionUpdate_fv]
  rw [pairTerm_closed, numeral_closed, falseTerm_closed]
  simp [fv_var] ; decide

theorem subst_recursionUpdate (G R : AlphaTerm) (x : ℕ) (hx : 6 ≠ x) (hR : 6 ∉ R.fv) :
    (recursionUpdate G).subst x R = recursionUpdate (G.subst x R) := by
  unfold recursionUpdate
  rw [subst_lam_fresh _ _ 6 x hx hR]
  simp [subst_app, subst_var, hx,
    subst_closed _ _ _ pairTerm_closed, subst_closed _ _ _ successorTerm_closed,
    subst_closed _ _ _ trueTerm_closed, subst_closed _ _ _ falseTerm_closed]

theorem recursorTerm_start {G A : AlphaTerm} (hG : G.Closed) (hA : A.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (app recursorTerm G) A) (numeral n))
      (app (iterateApp (recursionUpdate G) (pairValue (numeral 0) A) n) falseTerm) := by
  have hGf (x : ℕ) : x ∉ G.fv := by rw [hG]; simp
  have hAf (x : ℕ) : x ∉ A.fv := by rw [hA]; simp
  have h₁ : Beta (app recursorTerm G) (lam 8 (lam 3
      (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) (var 8))) falseTerm))) := by
    convert Beta.contract 7 (lam 8 (lam 3
      (app (app (app (var 3) (recursionUpdate (var 7)))
        (app (app pairTerm (numeral 0)) (var 8))) falseTerm))) G using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 8 7 (by decide) (hGf 8),
      subst_lam_fresh _ _ 3 7 (by decide) (hGf 3)]
    simp [subst_app, subst_var, subst_recursionUpdate _ _ 7 (by decide) (hGf 6),
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
    simp [subst_app, subst_var, subst_closed _ _ _ (recursionUpdate_closed hG),
      subst_closed _ _ _ pairTerm_closed, subst_closed _ _ _ (numeral_closed 0),
      subst_closed _ _ _ falseTerm_closed]
  have h₃ : Beta (app (lam 3 (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) A)) falseTerm)) (numeral n))
      (app (app (app (numeral n) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) A)) falseTerm) := by
    convert Beta.contract 3 (app (app (app (var 3) (recursionUpdate G))
        (app (app pairTerm (numeral 0)) A)) falseTerm) (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ (recursionUpdate_closed hG),
      subst_closed _ _ _ pairTerm_closed, subst_closed _ _ _ (numeral_closed 0),
      subst_closed _ _ _ falseTerm_closed, subst_closed _ _ _ hA]
  have hp := beta_steps_app_left (beta_steps_app_right (app (numeral n) (recursionUpdate G))
    (pairTerm_apply (numeral_closed 0) hA)) falseTerm
  have hf : 2 ∉ (recursionUpdate G).fv := by rw [recursionUpdate_closed hG]; simp
  exact (Relation.ReflTransGen.tail (.tail (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂)) h₃).trans
    (hp.trans (beta_steps_app_left (numeral_apply n (recursionUpdate G) (pairValue (numeral 0) A) hf) falseTerm))

/-- Primitive recursion on any sequence of closed lambda values. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Primitive recursion by a closed lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Three outer beta steps expose the body of the recursor. Construct the initial pair and apply the Church-numeral iteration formula to the closed term $\LambdaRecUpdate{G}$. The state invariant yields the final pair, and false selection returns $V_n$. The displayed bindings and the closed constants show that $\LambdaRecursor$ and $\LambdaRecUpdate{G}$ are closed. Taking $V_k=\ChurchNumeral{f(k)}$ gives numerical primitive recursion; uniqueness of numeral outputs rules out any different answer.
-/
theorem recursorTerm_apply {G : AlphaTerm} (hG : G.Closed) (V : ℕ → AlphaTerm)
    (hV : ∀ n, (V n).Closed)
    (hstep : ∀ n, Relation.ReflTransGen Beta (app (app G (numeral n)) (V n)) (V (n + 1)))
    (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (app recursorTerm G) (V 0)) (numeral n)) (V n) :=
  (recursorTerm_start hG (hV 0) n).trans
    ((beta_steps_app_left (iterate_recursionUpdate hG V hV hstep n) falseTerm).trans
      (pairValue_second (numeral_closed n) (hV n)))

/-- The mathematical recurrence whose numeral is produced by the recursor. -/
def primitiveRec (a : ℕ) (g : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => a
  | n + 1 => g n (primitiveRec a g n)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Primitive recursion by a closed lambda term
-/
theorem recursorTerm_numeral {G : AlphaTerm} (hG : G.Closed) (a : ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ n r, Relation.ReflTransGen Beta (app (app G (numeral n)) (numeral r)) (numeral (g n r)))
    (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (app recursorTerm G) (numeral a)) (numeral n))
      (numeral (primitiveRec a g n)) :=
  recursorTerm_apply hG (fun n => numeral (primitiveRec a g n))
    (fun _ => numeral_closed _) (fun n => hg n _) n

theorem closed_app {M N : AlphaTerm} (hM : M.Closed) (hN : N.Closed) : (app M N).Closed := by
  unfold Closed
  rw [fv_app, hM, hN]
  simp

/-- An initial-value program and a step program may depend on one closed
parameter value, including a functional tuple of parameters. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Parameters can be supplied uniformly. For closed terms $B,H$, put
    $$\LambdaParamRec{B}{H}:=\lambdaab{x}{\lambdaab{n}{\LambdaRecursor\,(Hx)\,(Bx)\,n}}.$$
    This term is closed and contains neither the supplied parameter nor the iteration count.
-/
def parameterRecursor (B H : AlphaTerm) : AlphaTerm := lam 9 (lam 10
  (app (app (app recursorTerm (app H (var 9))) (app B (var 9))) (var 10)))

theorem parameterRecursor_closed {B H : AlphaTerm} (hB : B.Closed) (hH : H.Closed) :
    (parameterRecursor B H).Closed := by
  unfold parameterRecursor Closed
  simp only [fv_lam, fv_app]
  rw [recursorTerm_closed, hB, hH]
  simp [fv_var] ; decide

theorem parameterRecursor_start {B H X : AlphaTerm} (hB : B.Closed) (hH : H.Closed)
    (hX : X.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (parameterRecursor B H) X) (numeral n))
      (app (app (app recursorTerm (app H X)) (app B X)) (numeral n)) := by
  have hf : 10 ∉ X.fv := by rw [hX]; simp
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
      subst_closed _ _ _ hB, subst_closed _ _ _ hH, subst_closed _ _ _ hX]
  exact .tail (.single (.app_left _ h₁)) h₂

/-- Correctness is uniform in the supplied parameter X; the constructed term
contains B and H but contains neither X nor the iteration count. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Parameterized lambda recursion
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Two beta steps give $\LambdaRecursor\,(HX)\,(BX)\,\ChurchNumeral{n}$. Reduce the initial-value argument to $\ChurchNumeral{a}$. The step term $HX$ is closed and has the required numerical behavior, so apply the theorem. The same constructed term works for every valid $X$. In particular, several closed parameters may be supplied together as nested functional pairs.
-/
theorem parameterRecursor_apply {B H X : AlphaTerm} (hB : B.Closed) (hH : H.Closed)
    (hX : X.Closed) (a : ℕ) (g : ℕ → ℕ → ℕ)
    (hb : Relation.ReflTransGen Beta (app B X) (numeral a))
    (hg : ∀ k r, Relation.ReflTransGen Beta
      (app (app (app H X) (numeral k)) (numeral r)) (numeral (g k r))) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (parameterRecursor B H) X) (numeral n))
      (numeral (primitiveRec a g n)) :=
  (parameterRecursor_start hB hH hX n).trans
    ((beta_steps_app_left (beta_steps_app_right (app recursorTerm (app H X)) hb) (numeral n)).trans
      (recursorTerm_numeral (closed_app hH hX) a g hg n))

/-- Only the finitely many updates visited by this call must reduce. -/
theorem recursorTerm_apply_bounded {G : AlphaTerm} (hG : G.Closed) (V : ℕ → AlphaTerm)
    (n : ℕ) (hV : ∀ k ≤ n, (V k).Closed)
    (hstep : ∀ k < n, Relation.ReflTransGen Beta
      (app (app G (numeral k)) (V k)) (V (k + 1))) :
    Relation.ReflTransGen Beta (app (app (app recursorTerm G) (V 0)) (numeral n)) (V n) := by
  have hi : ∀ k, k ≤ n → Relation.ReflTransGen Beta
      (iterateApp (recursionUpdate G) (pairValue (numeral 0) (V 0)) k)
      (pairValue (numeral k) (V k)) := by
    intro k
    induction k with
    | zero => intro _; exact .refl
    | succ k ih =>
      intro hk
      exact (beta_steps_app_right (recursionUpdate G) (ih (by omega))).trans
        (recursionUpdate_apply hG (hV k (by omega)) (hV (k + 1) hk) k (hstep k (by omega)))
  exact (recursorTerm_start hG (hV 0 (Nat.zero_le _)) n).trans
    ((beta_steps_app_left (hi n le_rfl) falseTerm).trans
      (pairValue_second (numeral_closed n) (hV n le_rfl)))

/-- The initial value and every visited update receive the same retained parameter.
Values may themselves be functions; no termination is required past n. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Every natural number decodes to a finite list. The empty-list code is zero, and list access returns entry $j$ when
    $j<|s|$, and zero otherwise. List recursion may return a numeral, a pair, or a function. Indexed recursion retains its
    parameters in both the initial value and the update; only the updates actually visited must terminate.
-/
theorem parameterRecursor_apply_bounded {B H X : AlphaTerm} (hB : B.Closed) (hH : H.Closed)
    (hX : X.Closed) (V : ℕ → AlphaTerm) (n : ℕ) (hV : ∀ k ≤ n, (V k).Closed)
    (hb : Relation.ReflTransGen Beta (app B X) (V 0))
    (hstep : ∀ k < n, Relation.ReflTransGen Beta
      (app (app (app H X) (numeral k)) (V k)) (V (k + 1))) :
    Relation.ReflTransGen Beta (app (app (parameterRecursor B H) X) (numeral n)) (V n) :=
  (parameterRecursor_start hB hH hX n).trans
    ((beta_steps_app_left (beta_steps_app_right (app recursorTerm (app H X)) hb) (numeral n)).trans
      (recursorTerm_apply_bounded (closed_app hH hX) V n hV hstep))

end PolishSpaceBook.NamedLambda.AlphaTerm
