module

public import PolishSpaceBook.TriposToposForcingRealizability

@[expose] public section

/-! # Concrete lambda indices for the realizability quantifiers

Both code transformations are total numerical lambda programs. In particular,
dummy abstraction builds syntax before evaluating the represented application.
-/
namespace PolishSpaceBook.LambdaIndexPCA

open NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

/-- Evaluate the returned index at zero. -/
def lowerProgram (u : ℕ) : AlphaTerm := lam 90
  (app (app outputSearchTerm (app (app outputSearchTerm (numeral u)) (var 90))) (numeral 0))

theorem lowerProgram_closed (u : ℕ) : (lowerProgram u).Closed := by
  unfold lowerProgram Closed
  simp only [fv_lam, fv_app, fv_var,
    (show outputSearchTerm.fv = ∅ from outputSearchTerm_closed),
    (show (numeral u).fv = ∅ from numeral_closed u),
    (show (numeral 0).fv = ∅ from numeral_closed 0)]
  decide

theorem lowerProgram_apply {u a e b : ℕ} (hu : App u a e) (he : App e 0 b) :
    Relation.ReflTransGen Beta (app (lowerProgram u) (numeral a)) (numeral b) := by
  have hs : Beta (app (lowerProgram u) (numeral a))
      (app (app outputSearchTerm (app (app outputSearchTerm (numeral u)) (numeral a))) (numeral 0)) := by
    simpa only [lowerProgram, subst_app, subst_var, ite_true,
      subst_closed _ _ _ outputSearchTerm_closed, subst_closed _ _ _ (numeral_closed u),
      subst_closed _ _ _ (numeral_closed 0)] using
      Beta.contract 90 (app (app outputSearchTerm (app (app outputSearchTerm (numeral u)) (var 90))) (numeral 0)) (numeral a)
  exact (Relation.ReflTransGen.single hs).trans
    ((beta_steps_app_left (beta_steps_app_right outputSearchTerm
      ((outputSearchTerm_runs_iff u a e).mpr hu)) (numeral 0)).trans
        ((outputSearchTerm_runs_iff e 0 b).mpr he))

/-- An unused argument delays evaluation of the represented application. -/
def dummyProgram (v a : ℕ) : AlphaTerm := lam 91
  (app (app outputSearchTerm (numeral v)) (numeral a))

theorem dummyProgram_closed (v a : ℕ) : (dummyProgram v a).Closed := by
  unfold dummyProgram Closed
  simp only [fv_lam, fv_app,
    (show outputSearchTerm.fv = ∅ from outputSearchTerm_closed),
    (show (numeral v).fv = ∅ from numeral_closed v),
    (show (numeral a).fv = ∅ from numeral_closed a)]
  decide

theorem dummyProgram_runs_iff (v a n b : ℕ) :
    Relation.ReflTransGen Beta (app (dummyProgram v a) (numeral n)) (numeral b) ↔ App v a b := by
  have hs : Beta (app (dummyProgram v a) (numeral n))
      (app (app outputSearchTerm (numeral v)) (numeral a)) := by
    simpa only [dummyProgram, subst_app, subst_closed _ _ _ outputSearchTerm_closed,
      subst_closed _ _ _ (numeral_closed v), subst_closed _ _ _ (numeral_closed a)] using
      Beta.contract 91 (app (app outputSearchTerm (numeral v)) (numeral a)) (numeral n)
  unfold App
  rw [← outputSearchTerm_runs_iff v a b]
  exact ⟨numeral_after_reduction (.single hs), fun h => (Relation.ReflTransGen.single hs).trans h⟩

def lowerSyntax (U : Term) (u : ℕ) : Term := .lam 90
  (.app (.app U (.app (.app U (Term.churchNumeral u)) (.var 90))) (Term.churchNumeral 0))

def dummySyntax (U : Term) (v a : ℕ) : Term := .lam 91
  (.app (.app U (Term.churchNumeral v)) (Term.churchNumeral a))

theorem lowerSyntax_mk (U : Term) (hU : mk U = outputSearchTerm) (u : ℕ) :
    mk (lowerSyntax U u) = lowerProgram u := by
  change lam 90 (app (app (mk U) (app (app (mk U) (mk (Term.churchNumeral u))) (var 90)))
    (mk (Term.churchNumeral 0))) = _
  rw [hU, Term.mk_churchNumeral, Term.mk_churchNumeral]
  rfl

theorem dummySyntax_mk (U : Term) (hU : mk U = outputSearchTerm) (v a : ℕ) :
    mk (dummySyntax U v a) = dummyProgram v a := by
  change lam 91 (app (app (mk U) (mk (Term.churchNumeral v))) (mk (Term.churchNumeral a))) = _
  rw [hU, Term.mk_churchNumeral, Term.mk_churchNumeral]
  rfl

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $U=\LambdaOutputSearch$, the closed universal evaluation term constructed in
    §{sec:lambda-input-universal-evaluation}. Thus
    $$U\ChurchNumeral{e}\ChurchNumeral{a}\to_\beta^*\ChurchNumeral{b}
    \quad\Longleftrightarrow\quad e\cdot a=b.$$
    Fix a named representative of $U$ and use it in the syntax codes
    $$
    \begin{aligned}
    \ell(u)&=\LambdaSyntaxCode{\lambda x.\,U(U\ChurchNumeral{u}x)\ChurchNumeral{0}},\\
    d(v,a)&=\LambdaSyntaxCode{\lambda n.\,U\ChurchNumeral{v}\ChurchNumeral{a}}.
    \end{aligned}
    $$
    The numeral-code, application-code, and abstraction-code programs compute these two maps without evaluating the
    coded applications. One beta contraction and two uses of the evaluator give the first implication. For the last
    identity, applying the program with code $d(v,a)$ to any numeral removes the unused binder. The evaluator theorem
    and confluence give exactly the same numeral outputs as $P_v\ChurchNumeral{a}$, including absence of output.
-/
theorem lowerCode_computes (U : Term) :
    ∃ L, NumericalComputes L (fun u => (lowerSyntax U u).code) := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed, numeralCodeTerm_apply⟩
  have hu := numericalConstant_computes U.code
  have hi := (hu.applicationCode hn).applicationCode (numericalConstant_computes (Term.var 90).code)
  exact ⟨_, ((hu.applicationCode hi).applicationCode
    (numericalConstant_computes (Term.churchNumeral 0).code)).abstractionCode 90⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Choose a closed term $B$ computing $d$ on paired inputs and set
    $$H=\lambda v.\lambda a.\,B(\LambdaNumericPair\,v\,a),\qquad
    r(v)=\LambdaSyntaxCode{H\ChurchNumeral{v}}.$$
    Here too, fix a named representative of $H$ before taking syntax codes. The map $r$ is computed by the
    numeral-code and application-code programs. Since $B$ is total,
    $$P_{r(v)}\ChurchNumeral{a}\to_\beta^*B\ChurchNumeral{\NatPair{v}{a}}
    \to_\beta^*\ChurchNumeral{d(v,a)}$$
    for every $v,a$. This computation returns a code and never evaluates $v\cdot a$.
    \end{proof}
-/
theorem dummyCode_computes (U : Term) :
    ∃ B, NumericalComputes B (fun z => (dummySyntax U z.unpair.1 z.unpair.2).code) := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed, numeralCodeTerm_apply⟩
  exact ⟨_, (((numericalConstant_computes U.code).applicationCode
    (hn.comp (projection_computes true))).applicationCode
      (hn.comp (projection_computes false))).abstractionCode 91⟩

/-- All three index maps are computed by closed numerical lambda programs. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: lemma
  title: uniform indices for realizability quantifiers
-/
theorem exists_computable_realizerAbstraction :
    ∃ K : RealizerAbstraction ℕ, K.app = App ∧ K.zero = 0 ∧
      (∃ L, NumericalComputes L K.lower) ∧
      (∃ R, NumericalComputes R K.raise) ∧
      (∃ B, NumericalComputes B (fun z => K.body z.unpair.1 z.unpair.2)) ∧
      ∀ v a n b, App (K.body v a) n b ↔ App v a b := by
  obtain ⟨U, hU⟩ := Quotient.exists_rep outputSearchTerm
  have hU' : mk U = outputSearchTerm := hU
  obtain ⟨L, hL⟩ := lowerCode_computes U
  obtain ⟨B, hB⟩ := dummyCode_computes U
  obtain ⟨H, hH⟩ := Quotient.exists_rep (curryNumerical B)
  have hH' : mk H = curryNumerical B := hH
  let lower (u : ℕ) := (lowerSyntax U u).code
  let body (v a : ℕ) := (dummySyntax U v a).code
  let raise (v : ℕ) := (Term.app H (Term.churchNumeral v)).code
  have hlower (u : ℕ) : Term.closedProgram (lower u) = lowerProgram u := by
    have hm := lowerSyntax_mk U hU' u
    exact (closedProgram_code_of_closed _ (hm.symm ▸ lowerProgram_closed u)).trans hm
  have hbody (v a : ℕ) : Term.closedProgram (body v a) = dummyProgram v a := by
    have hm := dummySyntax_mk U hU' v a
    exact (closedProgram_code_of_closed _ (hm.symm ▸ dummyProgram_closed v a)).trans hm
  have hraise (v : ℕ) : Term.closedProgram (raise v) = app (curryNumerical B) (numeral v) := by
    have hm : mk (Term.app H (Term.churchNumeral v)) = app (curryNumerical B) (numeral v) := by
      change app (mk H) (mk (Term.churchNumeral v)) = _
      rw [hH', Term.mk_churchNumeral]
    exact (closedProgram_code_of_closed _ (hm.symm ▸ closed_app
      (curryNumerical_closed hB.1) (numeral_closed v))).trans hm
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed, numeralCodeTerm_apply⟩
  have hr := (numericalConstant_computes H.code).applicationCode hn
  refine ⟨{
    app := App
    zero := 0
    lower := lower
    raise := raise
    body := body
    lower_app := ?_
    raise_outer := ?_
    raise_inner := ?_ }, rfl, rfl, ⟨L, hL⟩, ⟨_, hr⟩, ⟨B, hB⟩, ?_⟩
  · intro u a e b hu he
    unfold App
    rw [hlower]
    exact lowerProgram_apply hu he
  · intro v a
    unfold App
    rw [hraise]
    exact (curryNumerical_apply hB.1 v a).trans
      (by simpa only [Nat.unpair_pair] using hB.2 (Nat.pair v a))
  · intro v a b hv n
    unfold App
    rw [hbody]
    exact (dummyProgram_runs_iff v a n b).mpr hv

  · intro v a n b
    unfold App
    rw [hbody]
    exact dummyProgram_runs_iff v a n b

noncomputable def realizerAbstraction : RealizerAbstraction ℕ :=
  exists_computable_realizerAbstraction.choose

theorem realizerAbstraction_app : realizerAbstraction.app = App :=
  exists_computable_realizerAbstraction.choose_spec.1

/-- The quantifier trackers use the application of the previously constructed PCA. -/
theorem realizerAbstraction_app_iff_mem (e n m : ℕ) :
    realizerAbstraction.app e n m ↔ m ∈ indexPCA.application e n := by
  rw [realizerAbstraction_app]
  exact (mem_indexPCA_iff e n m).symm

theorem realizerAbstraction_zero : realizerAbstraction.zero = 0 :=
  exists_computable_realizerAbstraction.choose_spec.2.1

theorem realizerAbstraction_computable :
    (∃ L, NumericalComputes L realizerAbstraction.lower) ∧
    (∃ R, NumericalComputes R realizerAbstraction.raise) ∧
    (∃ B, NumericalComputes B (fun z => realizerAbstraction.body z.unpair.1 z.unpair.2)) :=
  ⟨exists_computable_realizerAbstraction.choose_spec.2.2.1,
    exists_computable_realizerAbstraction.choose_spec.2.2.2.1,
    exists_computable_realizerAbstraction.choose_spec.2.2.2.2.1⟩

theorem realizerAbstraction_body_iff (v a n b : ℕ) :
    App (realizerAbstraction.body v a) n b ↔ App v a b :=
  exists_computable_realizerAbstraction.choose_spec.2.2.2.2.2 v a n b

/-- The quantifier adjunctions now hold for the actual numerical lambda graph. -/
theorem lambda_realizability_quantifier_adjunctions {I J : Type*} (f : I → J)
    (φ : RealizabilityPredicate ℕ I) (ψ : RealizabilityPredicate ℕ J) :
    (RealizabilityReducible realizerAbstraction (realizabilityExists f φ) ψ ↔
      RealizabilityReducible realizerAbstraction φ (realizabilityReindex f ψ)) ∧
    (RealizabilityReducible realizerAbstraction (realizabilityReindex f ψ) φ ↔
      RealizabilityReducible realizerAbstraction ψ (realizabilityForall realizerAbstraction f φ)) :=
  realizability_quantifier_adjunctions realizerAbstraction f φ ψ

end PolishSpaceBook.LambdaIndexPCA
