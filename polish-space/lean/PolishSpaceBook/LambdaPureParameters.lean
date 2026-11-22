module

public import PolishSpaceBook.LambdaRelativePredicates

@[expose] public section

/-! # Eliminating a parameter implemented by an ordinary lambda term

Each query becomes the supplied finite beta computation. The proof uses
capture-avoiding substitution throughout, including abstraction contexts.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Strengthen the substitution claim to finite substitution lists and induct on one beta/query step.
    A beta contraction remains a beta contraction under capture-avoiding substitution. A query at $n$ is
    replaced by the assumed finite reduction of $E\ChurchNumeral{n}$ to $\ChurchNumeral{\varepsilon(n)}$.
    Application contexts preserve these reductions. Under an abstraction, first rename its binder to a
    variable fresh for the substitution list, both bodies, and the input variable; the induction hypothesis
    then applies to the renamed body. Concatenating the finite reductions handles an entire computation.
    Closed numerals are unchanged by substitution. For $P$, closedness also leaves the program unchanged,
    so substitution in $Po\ChurchNumeral{n}$ gives $PE\ChurchNumeral{n}$. This proves the decision assertion.
    \end{proof}
-/
theorem OracleStep.substs_simulate_beta {q : ℕ → ℕ} {M N : AlphaTerm}
    (h : OracleStep q M N) (σ : List (ℕ × AlphaTerm))
    (hq : ∀ n, Relation.ReflTransGen Beta
      (app (AlphaTerm.substs (var 0) σ) (numeral n)) (numeral (q n))) :
    Relation.ReflTransGen Beta (substs M σ) (substs N σ) := by
  induction h generalizing σ with
  | beta h => exact .single (h.substs σ)
  | query n =>
    rw [substs_app, substs_closed _ (numeral_closed n), substs_closed _ (numeral_closed (q n))]
    exact hq n
  | app_left N h ih =>
    rw [substs_app, substs_app]
    exact beta_steps_app_left (ih σ hq) _
  | app_right M h ih =>
    rw [substs_app, substs_app]
    exact beta_steps_app_right _ (ih σ hq)
  | @lam y hy M M' h ih =>
    let z := Term.fresh (M.fv ∪ M'.fv ∪ forbidden σ ∪ {0})
    have hz : z ∉ M.fv ∧ z ∉ M'.fv ∧ z ∉ forbidden σ ∧ z ≠ 0 := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using Term.fresh_not_mem (M.fv ∪ M'.fv ∪ forbidden σ ∪ {0})
    have hq' : ∀ n, Relation.ReflTransGen Beta
        (app (AlphaTerm.substs (var 0) ((y, var z) :: σ)) (numeral n)) (numeral (q n)) := by
      intro n
      simpa only [AlphaTerm.substs, subst_var, ite_eq_right (Ne.symm hy)] using hq n
    rw [lam_rename M y z hz.1, lam_rename M' y z hz.2.1,
      substs_lam_fresh _ z σ hz.2.2.1, substs_lam_fresh _ z σ hz.2.2.1]
    exact beta_steps_lam z (ih ((y, var z) :: σ) hq')

theorem oracle_steps_subst_input_beta {q : ℕ → ℕ} {M N R : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep q) M N)
    (hq : ∀ n, Relation.ReflTransGen Beta (app R (numeral n)) (numeral (q n))) :
    Relation.ReflTransGen Beta (M.subst 0 R) (N.subst 0 R) := by
  induction h with
  | refl => exact .refl
  | tail hs ht ih =>
    apply ih.trans
    apply ht.substs_simulate_beta [(0, R)]
    intro n
    simpa [AlphaTerm.substs, subst_var] using hq n

end PolishSpaceBook.NamedLambda.AlphaTerm
namespace PolishSpaceBook.LambdaRelative
open NamedLambda NamedLambda.AlphaTerm

theorem Computes.toNumerical {ε f : ℕ → ℕ} {P E : AlphaTerm}
    (hP : Computes ε P f) (hE : NumericalComputes E ε) :
    NumericalComputes (app P E) f := by
  refine ⟨closed_app hP.1 hE.1,fun n => ?_⟩
  have h := oracle_steps_subst_input_beta (hP.2 n) hE.2
  simpa only [Encodable.encode_nat,subst_app,subst_var,ite_true,
    subst_closed _ _ _ hP.1,subst_closed _ _ _ (numeral_closed n),
    subst_closed _ _ _ (numeral_closed (f n))] using h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Eliminating a computable input parameter
  excerpt: |
    Suppose a closed numerical term $E$ computes $\varepsilon$. Substituting $E$ for the input variable in
    any finite beta/query computation at $\varepsilon$ gives a finite beta computation with the same output.
    In particular, if $P$ is a decision program at $\varepsilon$, the closed term $PE$ is an ordinary
    numerical decision program for the same predicate. Taking $E=\lambdaab{k}{\ChurchNumeral{0}}$ removes
    the constant-zero parameter.
-/
theorem Decides.toPure {α : Type} [Encodable α] {ε : ℕ → ℕ} {P E : AlphaTerm} {R : α → Prop}
    (hP : Decides ε P R) (hE : NumericalComputes E ε) :
    (app P E).Closed ∧ ∀ n,
      (R n → Relation.ReflTransGen Beta (app (app P E) (numeral (Encodable.encode n))) (numeral 1)) ∧
      (¬ R n → Relation.ReflTransGen Beta (app (app P E) (numeral (Encodable.encode n))) (numeral 0)) := by
  refine ⟨closed_app hP.1 hE.1,fun n => ⟨?_,?_⟩⟩ <;> intro hn
  · have h := oracle_steps_subst_input_beta ((hP.2 n).1 hn) hE.2
    simpa only [Encodable.encode_nat,subst_app,subst_var,ite_true,
      subst_closed _ _ _ hP.1,subst_closed _ _ _ (numeral_closed (Encodable.encode n)),
      subst_closed _ _ _ (numeral_closed 1)] using h
  · have h := oracle_steps_subst_input_beta ((hP.2 n).2 hn) hE.2
    simpa only [Encodable.encode_nat,subst_app,subst_var,ite_true,
      subst_closed _ _ _ hP.1,subst_closed _ _ _ (numeral_closed (Encodable.encode n)),
      subst_closed _ _ _ (numeral_closed 0)] using h

end PolishSpaceBook.LambdaRelative
