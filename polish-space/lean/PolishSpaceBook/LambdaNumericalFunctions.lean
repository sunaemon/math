module

public import PolishSpaceBook.LambdaNumericalProjections

@[expose] public section

/-! # Uniform composition of numerical lambda programs

The executable objects are closed lambda terms. The predicate records their
ordinary beta reductions on Church numerals, with no input-name oracle.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def NumericalComputes (P : AlphaTerm) (f : ℕ → ℕ) : Prop :=
  P.Closed ∧ ∀ n, Relation.ReflTransGen Beta (app P (numeral n)) (numeral (f n))

def numericalCompose (F G : AlphaTerm) : AlphaTerm := lam 40 (app F (app G (var 40)))
def numericalCombine (B F G : AlphaTerm) : AlphaTerm :=
  lam 40 (app (app B (app F (var 40))) (app G (var 40)))
def numericalConstant (m : ℕ) : AlphaTerm := lam 40 (numeral m)
def numericalIdentity : AlphaTerm := lam 40 (var 40)

theorem numericalConstant_computes (m : ℕ) : NumericalComputes (numericalConstant m) (fun _ => m) := by
  refine ⟨?_,fun n => ?_⟩
  · unfold numericalConstant Closed; rw [fv_lam,numeral_closed]; rfl
  · exact .single (by simpa only [numericalConstant, subst_closed _ _ _ (numeral_closed m)] using
      (Beta.contract 40 (numeral m) (numeral n)))

theorem numericalIdentity_computes : NumericalComputes numericalIdentity id := by
  refine ⟨?_,fun n => ?_⟩
  · unfold numericalIdentity Closed; rw [fv_lam,fv_var]; simp
  · exact .single (by simpa only [numericalIdentity,subst_var,ite_true,id_eq] using Beta.contract 40 (var 40) (numeral n))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For composition, if closed terms $G,H$ compute numerical functions $g,h$, then $\lambdaab{x}{G(Hx)}$ computes $g\circ h$: contract the outer abstraction, reduce the inner application, and then reduce the outer application. The same argument works for a closed binary operation applied to two computed arguments. This constructs every component above.
-/
theorem NumericalComputes.comp {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) :
    NumericalComputes (numericalCompose F G) (fun n => f (g n)) := by
  refine ⟨?_,fun n => ?_⟩
  · unfold numericalCompose Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [hf.1,hg.1]; simp
  · have he : (app F (app G (var 40))).subst 40 (numeral n) = app F (app G (numeral n)) := by
      simp only [subst_app,subst_var,ite_true,subst_closed _ _ _ hf.1,subst_closed _ _ _ hg.1]
    have hs : Beta (app (numericalCompose F G) (numeral n)) (app F (app G (numeral n))) := by
      rw [← he]; exact Beta.contract 40 _ _
    exact (Relation.ReflTransGen.single hs).trans ((beta_steps_app_right F (hg.2 n)).trans (hf.2 _))

theorem NumericalComputes.combine {F G B : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) (hB : B.Closed)
    (b : ℕ → ℕ → ℕ)
    (hb : ∀ i j, Relation.ReflTransGen Beta (app (app B (numeral i)) (numeral j)) (numeral (b i j))) :
    NumericalComputes (numericalCombine B F G) (fun n => b (f n) (g n)) := by
  refine ⟨?_,fun n => ?_⟩
  · unfold numericalCombine Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [hB,hf.1,hg.1]; simp
  · have he : (app (app B (app F (var 40))) (app G (var 40))).subst 40 (numeral n) =
        app (app B (app F (numeral n))) (app G (numeral n)) := by
      simp only [subst_app,subst_var,ite_true,subst_closed _ _ _ hB,
        subst_closed _ _ _ hf.1,subst_closed _ _ _ hg.1]
    have hs : Beta (app (numericalCombine B F G) (numeral n))
        (app (app B (app F (numeral n))) (app G (numeral n))) := by
      rw [← he]; exact Beta.contract 40 _ _
    exact (Relation.ReflTransGen.single hs).trans
      ((beta_steps_app (beta_steps_app_right B (hf.2 n)) (hg.2 n)).trans (hb _ _))

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Natural numbers are supplied as Church numerals. Numerical predicates return the numeral one for true and zero for
    false; the selectors $\LambdaTrue,\LambdaFalse$ instead select the first and second branch. An unselected branch need
    not terminate. Functional pairs store terms; numerical pairs encode two natural numbers as a single numerical input.
    The arithmetic operations and numerical projections terminate on every numerical input.
-/
theorem projection_computes (first : Bool) :
    NumericalComputes (numericalProjectionTerm first)
      (fun n => if first then n.unpair.1 else n.unpair.2) :=
  ⟨numericalProjectionTerm_closed first,numericalProjectionTerm_apply first⟩

theorem successor_computes : NumericalComputes successorTerm Nat.succ :=
  ⟨successorTerm_closed,successorTerm_apply⟩

theorem predecessor_computes : NumericalComputes predecessorTerm (fun n => n-1) :=
  ⟨predecessorTerm_closed,predecessorTerm_apply⟩

def addNumerical (F G : AlphaTerm) : AlphaTerm := numericalCombine additionTerm F G
def mulNumerical (F G : AlphaTerm) : AlphaTerm := numericalCombine multiplicationTerm F G
def pairNumerical (F G : AlphaTerm) : AlphaTerm := numericalCombine numericalPairTerm F G

theorem NumericalComputes.add {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) :
    NumericalComputes (addNumerical F G) (fun n => f n + g n) :=
  hf.combine hg additionTerm_closed (· + ·) additionTerm_apply

theorem NumericalComputes.mul {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) :
    NumericalComputes (mulNumerical F G) (fun n => f n * g n) :=
  hf.combine hg multiplicationTerm_closed (· * ·) multiplicationTerm_apply

theorem NumericalComputes.pair {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) :
    NumericalComputes (pairNumerical F G) (fun n => Nat.pair (f n) (g n)) :=
  hf.combine hg numericalPairTerm_closed Nat.pair numericalPairTerm_apply

/-- Turn a closed binary numerical operation into a unary operation on paired input. -/
def uncurryNumerical (B : AlphaTerm) : AlphaTerm :=
  numericalCombine B (numericalProjectionTerm true) (numericalProjectionTerm false)

theorem uncurryNumerical_computes {B : AlphaTerm} (hB : B.Closed) (b : ℕ → ℕ → ℕ)
    (hb : ∀ i j, Relation.ReflTransGen Beta (app (app B (numeral i)) (numeral j)) (numeral (b i j))) :
    NumericalComputes (uncurryNumerical B) (fun z => b z.unpair.1 z.unpair.2) := by
  simpa [uncurryNumerical] using (projection_computes true).combine (projection_computes false) hB b hb

def lessOrEqualTerm : AlphaTerm := lam 40 (lam 41
  (chooseLeBody (var 40) (var 41) (numeral 1) (numeral 0)))

theorem lessOrEqualTerm_closed : lessOrEqualTerm.Closed := by
  unfold lessOrEqualTerm Closed
  rw [fv_lam,fv_lam,chooseLeBody_fv,numeral_closed,numeral_closed]
  simp [fv_var]; decide

theorem lessOrEqualTerm_apply (a b : ℕ) :
    Relation.ReflTransGen Beta (app (app lessOrEqualTerm (numeral a)) (numeral b))
      (numeral (if a ≤ b then 1 else 0)) := by
  have h₁ : Beta (app lessOrEqualTerm (numeral a))
      (lam 41 (chooseLeBody (numeral a) (var 41) (numeral 1) (numeral 0))) := by
    have he : (lam 41 (chooseLeBody (var 40) (var 41) (numeral 1) (numeral 0))).subst 40 (numeral a) =
        lam 41 (chooseLeBody (numeral a) (var 41) (numeral 1) (numeral 0)) := by
      rw [subst_lam_fresh _ _ 41 40 (by decide) (by rw [numeral_closed]; simp)]
      simp [chooseLeBody_subst,subst_var,subst_closed _ _ _ (numeral_closed 1),
        subst_closed _ _ _ (numeral_closed 0)]
    rw [← he]; exact Beta.contract 40 _ _
  have h₂ : Beta (app (lam 41 (chooseLeBody (numeral a) (var 41) (numeral 1) (numeral 0))) (numeral b))
      (chooseLeBody (numeral a) (numeral b) (numeral 1) (numeral 0)) := by
    simpa only [chooseLeBody_subst,subst_var,ite_true,subst_closed _ _ _ (numeral_closed _)] using
      Beta.contract 41 (chooseLeBody (numeral a) (var 41) (numeral 1) (numeral 0)) (numeral b)
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans (chooseLeBody_apply a b 1 0)

/-- Return one for strict inequality and zero otherwise. -/
def strictLessTerm : AlphaTerm := lam 40 (lam 41
  (chooseLeBody (app successorTerm (var 40)) (var 41) (numeral 1) (numeral 0)))

theorem strictLessTerm_closed : strictLessTerm.Closed := by
  unfold strictLessTerm Closed
  rw [fv_lam,fv_lam,chooseLeBody_fv,fv_app,successorTerm_closed,numeral_closed,numeral_closed]
  simp [fv_var]; decide

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Natural numbers are supplied as Church numerals. Numerical predicates return the numeral one for true and zero for
    false; the selectors $\LambdaTrue,\LambdaFalse$ instead select the first and second branch. An unselected branch need
    not terminate. Functional pairs store terms; numerical pairs encode two natural numbers as a single numerical input.
    The arithmetic operations and numerical projections terminate on every numerical input.
-/
theorem strictLessTerm_apply (a b : ℕ) :
    Relation.ReflTransGen Beta (app (app strictLessTerm (numeral a)) (numeral b))
      (numeral (if a < b then 1 else 0)) := by
  let body := chooseLeBody (app successorTerm (var 40)) (var 41) (numeral 1) (numeral 0)
  have h₁ : Beta (app strictLessTerm (numeral a))
      (lam 41 (chooseLeBody (app successorTerm (numeral a)) (var 41) (numeral 1) (numeral 0))) := by
    have he : (lam 41 body).subst 40 (numeral a) =
        lam 41 (chooseLeBody (app successorTerm (numeral a)) (var 41) (numeral 1) (numeral 0)) := by
      rw [subst_lam_fresh _ _ 41 40 (by decide) (by rw [numeral_closed]; simp)]
      simp [body,chooseLeBody_subst,subst_app,subst_var,subst_closed _ _ _ successorTerm_closed,
        subst_closed _ _ _ (numeral_closed 1),subst_closed _ _ _ (numeral_closed 0)]
    rw [← he]; exact Beta.contract 40 _ _
  have h₂ : Beta (app (lam 41 (chooseLeBody (app successorTerm (numeral a)) (var 41) (numeral 1) (numeral 0))) (numeral b))
      (chooseLeBody (app successorTerm (numeral a)) (numeral b) (numeral 1) (numeral 0)) := by
    simpa only [chooseLeBody_subst,subst_app,subst_var,ite_true,
      subst_closed _ _ _ successorTerm_closed,subst_closed _ _ _ (numeral_closed _)] using
      Beta.contract 41 (chooseLeBody (app successorTerm (numeral a)) (var 41) (numeral 1) (numeral 0)) (numeral b)
  apply (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
  have h := (chooseLeBody_steps (successorTerm_apply a) .refl .refl .refl).trans
    (chooseLeBody_apply (a+1) b 1 0)
  simpa only [Nat.succ_le_iff] using h

/-- Church iteration computes powers of two without a numerical recursion backend. -/
def powerTwoTerm : AlphaTerm := lam 40
  (app (app (var 40) (app multiplicationTerm (numeral 2))) (numeral 1))

theorem powerTwo_computes : NumericalComputes powerTwoTerm (fun n => 2^n) := by
  let D := app multiplicationTerm (numeral 2)
  have hD : D.Closed := by unfold D Closed; rw [fv_app,multiplicationTerm_closed,numeral_closed]; simp
  have hi (n : ℕ) : Relation.ReflTransGen Beta (iterateApp D (numeral 1) n) (numeral (2^n)) := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
      exact (beta_steps_app_right D ih).trans (by simpa [pow_succ,Nat.mul_comm] using multiplicationTerm_apply 2 (2^n))
  refine ⟨?_,fun n => ?_⟩
  · unfold powerTwoTerm Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [multiplicationTerm_closed,numeral_closed,numeral_closed]; simp
  · have hb : Beta (app powerTwoTerm (numeral n)) (app (app (numeral n) D) (numeral 1)) := by
      simpa only [powerTwoTerm, subst_app,subst_var,ite_true,subst_closed _ _ _ hD,
        subst_closed _ _ _ (numeral_closed 1)] using
        Beta.contract 40 (app (app (var 40) D) (numeral 1)) (numeral n)
    exact (Relation.ReflTransGen.single hb).trans
      ((numeral_apply n D (numeral 1) (by rw [hD]; simp)).trans (hi n))

end PolishSpaceBook.NamedLambda.AlphaTerm
