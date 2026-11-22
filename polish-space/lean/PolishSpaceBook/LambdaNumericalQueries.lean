module

public import PolishSpaceBook.LambdaNumericalFunctions
public import PolishSpaceBook.LambdaProducts

@[expose] public section

/-! # Uniform numerical programs with input queries

These constructors keep one closed lambda term for every input name and every
numerical argument. They use only application, beta-reduction and name queries.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def UniformNumericalComputes (P : AlphaTerm) (f : (ℕ → ℕ) → ℕ → ℕ) : Prop :=
  P.Closed ∧ ∀ p n, OracleRuns p P n (f p n)

def liftNumericalProgram (F : AlphaTerm) : AlphaTerm := lam 40 F

theorem NumericalComputes.uniform {F : AlphaTerm} {f : ℕ → ℕ} (h : NumericalComputes F f) :
    UniformNumericalComputes (liftNumericalProgram F) (fun _ n => f n) := by
  refine ⟨?_,fun p n => ?_⟩
  · unfold liftNumericalProgram Closed; rw [fv_lam,h.1]; simp
  · have hb : Beta (app (liftNumericalProgram F) (var 0)) F := by
      simpa only [liftNumericalProgram,subst_closed _ _ _ h.1] using Beta.contract 40 F (var 0)
    exact (Relation.ReflTransGen.single (.beta (.app_left _ hb))).trans (beta_steps_oracle (h.2 n))

theorem uniform_constant (m : ℕ) : UniformNumericalComputes (constantProgram m) (fun _ _ => m) :=
  ⟨constantProgram_closed m,constantProgram_runs m⟩

theorem UniformNumericalComputes.map {P F : AlphaTerm} {g : (ℕ → ℕ) → ℕ → ℕ} {f : ℕ → ℕ}
    (hP : UniformNumericalComputes P g) (hF : NumericalComputes F f) :
    UniformNumericalComputes (mapOutputProgram F P) (fun p n => f (g p n)) :=
  ⟨mapOutputProgram_closed hF.1 hP.1,fun p n => mapOutputProgram_runs hF.1 hP.1 (hP.2 p n) (hF.2 _)⟩

theorem UniformNumericalComputes.pair {P Q : AlphaTerm} {f g : (ℕ → ℕ) → ℕ → ℕ}
    (hf : UniformNumericalComputes P f) (hg : UniformNumericalComputes Q g) :
    UniformNumericalComputes (pairOutputProgram P Q) (fun p n => Nat.pair (f p n) (g p n)) :=
  ⟨pairOutputProgram_closed hf.1 hg.1,fun p n => pairOutputProgram_runs hf.1 hg.1 (hf.2 p n) (hg.2 p n)⟩

def combineOutputProgram (B P Q : AlphaTerm) : AlphaTerm :=
  mapOutputProgram (uncurryNumerical B) (pairOutputProgram P Q)

theorem UniformNumericalComputes.combine {P Q B : AlphaTerm} {f g : (ℕ → ℕ) → ℕ → ℕ}
    (hf : UniformNumericalComputes P f) (hg : UniformNumericalComputes Q g)
    (hB : B.Closed) (b : ℕ → ℕ → ℕ)
    (hb : ∀ i j, Relation.ReflTransGen Beta (app (app B (numeral i)) (numeral j)) (numeral (b i j))) :
    UniformNumericalComputes (combineOutputProgram B P Q) (fun p n => b (f p n) (g p n)) := by
  simpa [combineOutputProgram,Nat.unpair_pair] using (hf.pair hg).map (uncurryNumerical_computes hB b hb)

def queryOutputProgram (P : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app (var 1) (app (app P (var 1)) (var 2))))

theorem UniformNumericalComputes.query {P : AlphaTerm} {f : (ℕ → ℕ) → ℕ → ℕ}
    (h : UniformNumericalComputes P f) :
    UniformNumericalComputes (queryOutputProgram P) (fun p n => p (f p n)) := by
  refine ⟨?_,fun p n => ?_⟩
  · unfold queryOutputProgram Closed
    simp only [fv_lam,fv_app,fv_var]; rw [h.1]; decide
  · have h₁ : Beta (app (queryOutputProgram P) (var 0))
        (lam 2 (app (var 0) (app (app P (var 0)) (var 2)))) := by
      have he : (lam 2 (app (var 1) (app (app P (var 1)) (var 2)))).subst 1 (var 0) =
          lam 2 (app (var 0) (app (app P (var 0)) (var 2))) := by
        rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
        simp [subst_app,subst_var,subst_closed _ _ _ h.1]
      rw [← he]; exact Beta.contract 1 _ _
    have h₂ : Beta (app (lam 2 (app (var 0) (app (app P (var 0)) (var 2)))) (numeral n))
        (app (var 0) (app (app P (var 0)) (numeral n))) := by
      simpa only [subst_app,subst_var,ite_true,ite_false,show (0 : ℕ) ≠ 2 from by decide,
        subst_closed _ _ _ h.1] using
        Beta.contract 2 (app (var 0) (app (app P (var 0)) (var 2))) (numeral n)
    exact ((Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
      (oracle_steps_app_right (var 0) (h.2 p n))).tail (.query _)

/-- Change the numerical input without changing the supplied name. -/
def reindexProgram (P F : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app (app P (var 1)) (app F (var 2))))

theorem reindexProgram_closed {P F : AlphaTerm} (hP : P.Closed) (hF : F.Closed) :
    (reindexProgram P F).Closed := by
  unfold reindexProgram Closed
  simp only [fv_lam,fv_app,fv_var]; rw [hP,hF]; decide

theorem reindexProgram_runs {P F : AlphaTerm} (hP : P.Closed) (hF : F.Closed)
    (p : ℕ → ℕ) (n m r : ℕ)
    (hf : Relation.ReflTransGen Beta (app F (numeral n)) (numeral m))
    (hp : OracleRuns p P m r) : OracleRuns p (reindexProgram P F) n r := by
  have h₁ : Beta (app (reindexProgram P F) (var 0))
      (lam 2 (app (app P (var 0)) (app F (var 2)))) := by
    have he : (lam 2 (app (app P (var 1)) (app F (var 2)))).subst 1 (var 0) =
        lam 2 (app (app P (var 0)) (app F (var 2))) := by
      rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
      simp [subst_app,subst_var,subst_closed _ _ _ hP,subst_closed _ _ _ hF]
    rw [← he]; exact Beta.contract 1 _ _
  have h₂ : Beta (app (lam 2 (app (app P (var 0)) (app F (var 2)))) (numeral n))
      (app (app P (var 0)) (app F (numeral n))) := by
    simpa only [subst_app,subst_var,ite_true,ite_false,show (0 : ℕ) ≠ 2 from by decide,
      subst_closed _ _ _ hP,subst_closed _ _ _ hF] using
      Beta.contract 2 (app (app P (var 0)) (app F (var 2))) (numeral n)
  exact (Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
    ((oracle_steps_app_right _ (beta_steps_oracle hf)).trans hp)

theorem UniformNumericalComputes.reindex {P F : AlphaTerm} {f : (ℕ → ℕ) → ℕ → ℕ} {g : ℕ → ℕ}
    (hP : UniformNumericalComputes P f) (hF : NumericalComputes F g) :
    UniformNumericalComputes (reindexProgram P F) (fun p n => f p (g n)) :=
  ⟨reindexProgram_closed hP.1 hF.1,fun p n => reindexProgram_runs hP.1 hF.1 p n _ _ (hF.2 n) (hP.2 p _)⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
