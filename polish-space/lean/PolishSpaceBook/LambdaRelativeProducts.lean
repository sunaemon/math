module

public import PolishSpaceBook.LambdaRelativePredicates
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

/-! # Bounded products relative to one fixed input parameter

The same input variable is passed to every trial. Totality is required only
for that parameter, not for all possible functions supplied as input.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let $T$ be a closed lambda program whose numerical input codes a pair. To multiply its answers while keeping
    one parameter fixed, expand the following abbreviations inside their enclosing abstractions:
    $$\begin{aligned}
    G_T(o,x)&:=\lambdaab{k}{\lambdaab{r}{
     \LambdaMul\,r\,\bigl(To(\LambdaNumericPair\,x\,k)\bigr)}},\\
    x(z)&:=\LambdaNumericProjection{1}z,\qquad
    N(z):=\LambdaNumericProjection{2}z,\\
    \LambdaRelativeProduct{T}&:=\lambdaab{o}{\lambdaab{z}{
     \LambdaRecursor\,G_T(o,x(z))\,\ChurchNumeral{1}\,N(z)}}.
    \end{aligned}$$
    Choose all displayed binders distinct, and choose the recursor's internal binders fresh for the input variable.
    The resulting term is closed. The same $o$ occurs in every call to $T$; it is never replaced by a new parameter.
-/
def relativeProductBody (T O X K R : AlphaTerm) : AlphaTerm :=
  app (app multiplicationTerm R) (app (app T O) (app (app numericalPairTerm X) K))

theorem relativeProductBody_fv {T : AlphaTerm} (hT : T.Closed) (O X K R : AlphaTerm) :
    (relativeProductBody T O X K R).fv = O.fv ∪ X.fv ∪ K.fv ∪ R.fv := by
  ext z
  simp only [relativeProductBody,fv_app,(show T.fv = ∅ from hT),
    (show multiplicationTerm.fv = ∅ from multiplicationTerm_closed),
    (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed),
    Finset.mem_union,Finset.notMem_empty]
  tauto

theorem relativeProductBody_subst {T : AlphaTerm} (hT : T.Closed)
    (O X K R W : AlphaTerm) (z : ℕ) :
    (relativeProductBody T O X K R).subst z W =
      relativeProductBody T (O.subst z W) (X.subst z W) (K.subst z W) (R.subst z W) := by
  simp only [relativeProductBody,subst_app,subst_closed _ _ _ hT,
    subst_closed _ _ _ multiplicationTerm_closed,subst_closed _ _ _ numericalPairTerm_closed]

def relativeProductStep (T O X : AlphaTerm) : AlphaTerm :=
  lam 70 (lam 71 (relativeProductBody T O X (var 70) (var 71)))

theorem relativeProductStep_fv {T : AlphaTerm} (hT : T.Closed) (O X : AlphaTerm) :
    (relativeProductStep T O X).fv = ((O.fv ∪ X.fv).erase 71).erase 70 := by
  ext z
  simp only [relativeProductStep,fv_lam,relativeProductBody_fv hT,fv_var,
    Finset.mem_erase,Finset.mem_union,Finset.mem_singleton]
  tauto

theorem relativeProductStep_subst {T : AlphaTerm} (hT : T.Closed) (O X W : AlphaTerm)
    (z : ℕ) (h70 : 70 ≠ z) (h71 : 71 ≠ z) (hw70 : 70 ∉ W.fv) (hw71 : 71 ∉ W.fv) :
    (relativeProductStep T O X).subst z W =
      relativeProductStep T (O.subst z W) (X.subst z W) := by
  unfold relativeProductStep
  rw [subst_lam_fresh _ _ 70 z h70 hw70,subst_lam_fresh _ _ 71 z h71 hw71,
    relativeProductBody_subst hT]
  simp only [subst_var,ite_eq_right h70,ite_eq_right h71]

theorem relativeProductStep_apply {ε : ℕ → ℕ} {T : AlphaTerm} (hT : T.Closed)
    (x k r v : ℕ) (ht : OracleRuns ε T (Nat.pair x k) v) :
    Relation.ReflTransGen (OracleStep ε)
      (app (app (relativeProductStep T (var 0) (numeral x)) (numeral k)) (numeral r))
      (numeral (r * v)) := by
  have h₁ : Beta (app (relativeProductStep T (var 0) (numeral x)) (numeral k))
      (lam 71 (relativeProductBody T (var 0) (numeral x) (numeral k) (var 71))) := by
    convert Beta.contract 70 (lam 71 (relativeProductBody T (var 0) (numeral x) (var 70) (var 71))) (numeral k) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 71 70 (by decide) (by rw [numeral_closed]; simp),relativeProductBody_subst hT]
    simp [subst_var,subst_closed _ _ _ (numeral_closed x)]
  have h₂ : Beta
      (app (lam 71 (relativeProductBody T (var 0) (numeral x) (numeral k) (var 71))) (numeral r))
      (relativeProductBody T (var 0) (numeral x) (numeral k) (numeral r)) := by
    convert Beta.contract 71 (relativeProductBody T (var 0) (numeral x) (numeral k) (var 71)) (numeral r) using 1
    rw [relativeProductBody_subst hT]
    simp [subst_var,subst_closed _ _ _ (numeral_closed x),subst_closed _ _ _ (numeral_closed k)]
  have hp := (oracle_steps_app_right (app T (var 0)) (beta_steps_oracle (numericalPairTerm_apply x k))).trans ht
  exact (Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
    ((oracle_steps_app_right (app multiplicationTerm (numeral r)) hp).trans
      (beta_steps_oracle (multiplicationTerm_apply r v)))

def relativeProductRun (T O X N : AlphaTerm) : AlphaTerm :=
  app (app (app recursorTerm (relativeProductStep T O X)) (numeral 1)) N

def relativeProductProgram (T : AlphaTerm) : AlphaTerm :=
  lam 72 (lam 73 (relativeProductRun T (var 72)
    (app (numericalProjectionTerm true) (var 73)) (app (numericalProjectionTerm false) (var 73))))

theorem relativeProductProgram_closed {T : AlphaTerm} (hT : T.Closed) :
    (relativeProductProgram T).Closed := by
  unfold relativeProductProgram relativeProductRun Closed
  simp only [fv_lam,fv_app,relativeProductStep_fv hT,fv_var,(show recursorTerm.fv = ∅ from recursorTerm_closed),
    (show (numeral 1).fv = ∅ from numeral_closed 1),
    (show (numericalProjectionTerm true).fv = ∅ from (projection_computes true).1),
    (show (numericalProjectionTerm false).fv = ∅ from (projection_computes false).1)]
  decide

theorem relativeProductProgram_start {T : AlphaTerm} (hT : T.Closed) (z : ℕ) :
    Relation.ReflTransGen Beta (app (app (relativeProductProgram T) (var 0)) (numeral z))
      (relativeProductRun T (var 0) (numeral z.unpair.1) (numeral z.unpair.2)) := by
  have h₁ : Beta (app (relativeProductProgram T) (var 0))
      (lam 73 (relativeProductRun T (var 0)
        (app (numericalProjectionTerm true) (var 73)) (app (numericalProjectionTerm false) (var 73)))) := by
    convert Beta.contract 72 (lam 73 (relativeProductRun T (var 72)
      (app (numericalProjectionTerm true) (var 73)) (app (numericalProjectionTerm false) (var 73)))) (var 0) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 73 72 (by decide) (by simp [fv_var])]
    simp only [relativeProductRun,subst_app,subst_closed _ _ _ recursorTerm_closed,
      subst_closed _ _ _ (numeral_closed 1),relativeProductStep_subst hT _ _ (var 0) 72 (by decide) (by decide)
        (by simp [fv_var]) (by simp [fv_var]),
      subst_closed _ _ _ (projection_computes true).1,subst_closed _ _ _ (projection_computes false).1,subst_var]
    simp
  have h₂ : Beta
      (app (lam 73 (relativeProductRun T (var 0)
        (app (numericalProjectionTerm true) (var 73)) (app (numericalProjectionTerm false) (var 73)))) (numeral z))
      (relativeProductRun T (var 0)
        (app (numericalProjectionTerm true) (numeral z)) (app (numericalProjectionTerm false) (numeral z))) := by
    convert Beta.contract 73 (relativeProductRun T (var 0)
      (app (numericalProjectionTerm true) (var 73)) (app (numericalProjectionTerm false) (var 73))) (numeral z) using 1
    simp only [relativeProductRun,subst_app,subst_closed _ _ _ recursorTerm_closed,
      subst_closed _ _ _ (numeral_closed 1),relativeProductStep_subst hT _ _ (numeral z) 73 (by decide) (by decide)
        (by rw [numeral_closed]; simp) (by rw [numeral_closed]; simp),
      subst_closed _ _ _ (projection_computes true).1,subst_closed _ _ _ (projection_computes false).1,subst_var]
    simp
  have hx := (projection_computes true).2 z
  have hn := (projection_computes false).2 z
  have hs : Relation.ReflTransGen Beta
      (relativeProductStep T (var 0) (app (numericalProjectionTerm true) (numeral z)))
      (relativeProductStep T (var 0) (numeral z.unpair.1)) := by
    apply beta_steps_lam
    apply beta_steps_lam
    exact beta_steps_app_right _ (beta_steps_app_right _
      (beta_steps_app_left (beta_steps_app_right numericalPairTerm hx) _))
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    (beta_steps_app (beta_steps_app_left (beta_steps_app_right recursorTerm hs) _) hn)

/-- Zero stages need beta reduction only, with no input queries or trial evaluation. -/
theorem relativeProductProgram_zero {T : AlphaTerm} (hT : T.Closed) (x : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (relativeProductProgram T) (var 0)) (numeral (Nat.pair x 0))) (numeral 1) := by
  have hG : (relativeProductStep T (var 0) (numeral x)).fv ⊆ {0} := by
    rw [relativeProductStep_fv hT,fv_var,numeral_closed]; simp
  have hs := relativeProductProgram_start hT (Nat.pair x 0)
  simp only [Nat.unpair_pair] at hs
  exact hs.trans ((recursorTerm_input_start hG (numeral_closed 1) 0).trans
    (pairValue_second (numeral_closed 0) (numeral_closed 1)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Bounded products relative to a fixed parameter
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Two outer beta steps expose the recursor. The numerical projections give $x$ and $N$. Set $b_0=1$ and
    $b_{k+1}=b_k a_k$ for $k<N$. At stage $k$, two beta steps expose the body of $G_T$; numerical pairing produces
    $\ChurchNumeral{\NatPair{x}{k}}$, the assumed computation of $T$ gives $\ChurchNumeral{a_k}$, and multiplication
    returns $\ChurchNumeral{b_{k+1}}$. The update has only the input variable free, and every state is a closed numeral.
    The finite-stage recursion theorem of §{sec:lambda-input-recursion} therefore gives $\ChurchNumeral{b_N}$.
    Induction identifies $b_N$ with the displayed product. For zero stages, the Church numeral selects the initial
    value without evaluating the update. For zero-or-one factors, multiplication preserves this range and returns one
    exactly when every factor is one. All reductions use the same parameter, and output uniqueness excludes a
    different numerical answer.
-/
theorem relativeProductProgram_runs {ε : ℕ → ℕ} {T : AlphaTerm} (hT : T.Closed)
    (t : ℕ → ℕ) (x N : ℕ)
    (ht : ∀ k < N, OracleRuns ε T (Nat.pair x k) (t (Nat.pair x k))) :
    OracleRuns ε (relativeProductProgram T) (Nat.pair x N) (boundedProduct t x N) := by
  have hG : (relativeProductStep T (var 0) (numeral x)).fv ⊆ {0} := by
    rw [relativeProductStep_fv hT,fv_var,numeral_closed]; simp
  have hs := relativeProductProgram_start hT (Nat.pair x N)
  simp only [Nat.unpair_pair] at hs
  apply (beta_steps_oracle hs).trans
  apply recursorTerm_oracle_apply_upto hG (fun k => numeral (boundedProduct t x k))
    (fun _ => numeral_closed _) N
  intro k hk
  exact relativeProductStep_apply hT x k _ _ (ht k hk)

end PolishSpaceBook.NamedLambda.AlphaTerm

namespace PolishSpaceBook.LambdaRelative
open NamedLambda NamedLambda.AlphaTerm

theorem Computes.map {ε : ℕ → ℕ} {P F : AlphaTerm} {g f : ℕ → ℕ}
    (hg : Computes ε P g) (hf : NumericalComputes F f) :
    Computes ε (mapOutputProgram F P) (fun n => f (g n)) :=
  ⟨mapOutputProgram_closed hf.1 hg.1,fun n => mapOutputProgram_runs hf.1 hg.1 (hg.2 n) (hf.2 _)⟩

theorem Computes.pair {ε : ℕ → ℕ} {P Q : AlphaTerm} {f g : ℕ → ℕ}
    (hf : Computes ε P f) (hg : Computes ε Q g) :
    Computes ε (pairOutputProgram P Q) (fun n => Nat.pair (f n) (g n)) :=
  ⟨pairOutputProgram_closed hf.1 hg.1,fun n => pairOutputProgram_runs hf.1 hg.1 (hf.2 n) (hg.2 n)⟩

theorem Computes.reindex {ε : ℕ → ℕ} {P F : AlphaTerm} {f g : ℕ → ℕ}
    (hf : Computes ε P f) (hg : NumericalComputes F g) :
    Computes ε (reindexProgram P F) (fun n => f (g n)) :=
  ⟨reindexProgram_closed hf.1 hg.1,fun n => reindexProgram_runs hf.1 hg.1 ε n _ _ (hg.2 n) (hf.2 _)⟩

theorem ofNumerical {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) (ε : ℕ → ℕ) :
    Computes ε (liftNumericalProgram F) f := ⟨hf.uniform.1,hf.uniform.2 ε⟩

theorem Computes.boundedProduct {ε : ℕ → ℕ} {T : AlphaTerm} {t : ℕ → ℕ}
    (ht : Computes ε T t) :
    Computes ε (relativeProductProgram T) (fun z : ℕ => boundedProduct t z.unpair.1 z.unpair.2) := by
  refine ⟨relativeProductProgram_closed ht.1,fun z => ?_⟩
  simpa only [Nat.pair_unpair,Encodable.encode_nat] using
    relativeProductProgram_runs ht.1 t z.unpair.1 z.unpair.2 (fun k _ => ht.2 _)

end PolishSpaceBook.LambdaRelative
