module

public import PolishSpaceBook.LambdaComputablePointAssemblies
public import PolishSpaceBook.LambdaAssemblyTrackedRelations
public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.InsideEffectiveTopos

@[expose] public section

/-! # Doubling computable reals with explicit lambda programs -/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
open Filter Topology

/-- Double both numerator parts, retaining the positive denominator. -/
def rationalDoubleIndex (n : ℕ) : ℕ :=
  Nat.pair (Nat.pair (2 * n.unpair.1.unpair.1) (2 * n.unpair.1.unpair.2)) n.unpair.2

def rationalDoubleTerm : AlphaTerm :=
  pairNumerical
    (pairNumerical (mulNumerical (numericalConstant 2) (rationalNumeratorTerm true))
      (mulNumerical (numericalConstant 2) (rationalNumeratorTerm false)))
    (numericalProjectionTerm false)

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: construction
  title: Doubling computable reals
-/
theorem rationalDouble_computes : NumericalComputes rationalDoubleTerm rationalDoubleIndex := by
  exact (((numericalConstant_computes 2).mul (rationalNumerator_computes true)).pair
    ((numericalConstant_computes 2).mul (rationalNumerator_computes false))).pair
      (projection_computes false)

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: construction
  title: Doubling computable reals
-/
theorem rationalDouble_value (i : ℕ) : rationalPoint (rationalDoubleIndex i) = 2 * rationalPoint i := by
  simp only [rationalPoint,rationalDoubleIndex,RationalCode.ofNat,Nat.unpair_pair,RationalCode.value]
  push_cast
  ring

/-- The literal name transformer: lambda p n, dbl (p (succ n)). -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: construction
  title: Doubling computable reals
-/
def shiftDoubleProgram : AlphaTerm := lam 1 (lam 2
  (app rationalDoubleTerm (app (var 1) (app successorTerm (var 2)))))

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: construction
  title: Doubling computable reals
-/
theorem shiftDoubleProgram_closed : shiftDoubleProgram.Closed := by
  unfold shiftDoubleProgram Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [rationalDouble_computes.1,successor_computes.1]
  decide

/-- Two contractions expose the numerical query, for arbitrary supplied terms. -/
theorem shiftDoubleProgram_start (A : AlphaTerm) (hA : 2 ∉ A.fv) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app shiftDoubleProgram A) (numeral n))
      (app rationalDoubleTerm (app A (app successorTerm (numeral n)))) := by
  have h₁ : Beta (app shiftDoubleProgram A)
      (lam 2 (app rationalDoubleTerm (app A (app successorTerm (var 2))))) := by
    simpa only [shiftDoubleProgram,subst_lam_fresh _ _ 2 1 (by decide) hA, subst_app,subst_var,
      ite_true,ite_false,show (2 : ℕ) ≠ 1 from by decide,
      subst_closed _ _ _ rationalDouble_computes.1,subst_closed _ _ _ successor_computes.1]
      using Beta.contract 1 (lam 2 (app rationalDoubleTerm (app (var 1) (app successorTerm (var 2))))) A
  have h₂ : Beta (app (lam 2 (app rationalDoubleTerm (app A (app successorTerm (var 2))))) (numeral n))
      (app rationalDoubleTerm (app A (app successorTerm (numeral n)))) := by
    simpa only [subst_app,subst_var,ite_true,subst_closed _ _ _ rationalDouble_computes.1,
      subst_closed _ _ _ successor_computes.1,subst_not_free _ _ _ hA] using
      Beta.contract 2 (app rationalDoubleTerm (app A (app successorTerm (var 2)))) (numeral n)
  exact (Relation.ReflTransGen.single (.app_left _ h₁)).tail h₂

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: construction
  title: Doubling computable reals
-/
theorem shiftDoubleProgram_runs (p : ℕ → ℕ) (n : ℕ) :
    OracleRuns p shiftDoubleProgram n (rationalDoubleIndex (p (n+1))) := by
  apply (beta_steps_oracle (shiftDoubleProgram_start (var 0) (by simp [fv_var]) n)).trans
  apply (oracle_steps_app_right rationalDoubleTerm
    (oracle_steps_app_right (var 0) (beta_steps_oracle (successor_computes.2 n)))).trans
  exact (Relation.ReflTransGen.single (.app_right _ (.query (n+1)))).trans
    (beta_steps_oracle (rationalDouble_computes.2 (p (n+1))))

/-- Only the queried coordinate is required; the indexed input may be partial elsewhere. -/
theorem shiftDoubleProgram_partial {e n m : ℕ} (he : App e (n+1) m) :
    Relation.ReflTransGen Beta (app (app shiftDoubleProgram (evalProgram e)) (numeral n))
      (numeral (rationalDoubleIndex m)) := by
  apply (shiftDoubleProgram_start (evalProgram e) (by rw [evalProgram_closed]; simp) n).trans
  apply (beta_steps_app_right rationalDoubleTerm
    ((beta_steps_app_right (evalProgram e) (successor_computes.2 n)).trans
      ((evalProgram_runs_iff e (n+1) m).mpr he))).trans
  exact rationalDouble_computes.2 m


def doubleName (p : realRepresentation.domain) : realRepresentation.domain :=
  ⟨shiftedDoubleName rationalDoubleIndex p.val,
    shiftedDoubleName_isCauchyName rationalPoint rationalDoubleIndex rationalDouble_value p.property⟩

theorem doubleName_computes : TypeTwoComputes shiftDoubleProgram (fun p => (doubleName p).val) :=
  typeTwoComputes_iff_runs.mpr ⟨shiftDoubleProgram_closed,fun p n => shiftDoubleProgram_runs p.val n⟩

theorem doubleName_realizes : Realizes realRepresentation realRepresentation doubleName (fun x => 2*x) := by
  intro p
  exact tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint (doubleName p))
    (tendsto_shiftedDoubleName rationalPoint rationalDoubleIndex rationalDouble_value
      (tendsto_cauchyRepresentation rationalPoint p))

theorem doubling_hasComputableRealizer :
    HasComputableRealizer realRepresentation realRepresentation (fun x => 2*x) :=
  ⟨doubleName,⟨shiftDoubleProgram,doubleName_computes⟩,doubleName_realizes⟩

noncomputable def realDoublingMap : Assembly.Hom (computablePointAssembly realRepresentation)
    (computablePointAssembly realRepresentation) := computablePointMap doubling_hasComputableRealizer

/-- One total code transformer handles all indices and preserves each defined queried value. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $U=\LambdaOutputSearch$. The code construction used for the name-to-index transformation above gives
    $$t(e):=\LambdaSyntaxCode{P(U\ChurchNumeral{e})}.$$
    This function is computed by a closed numerical program on every $e$, without executing $\varphi_e$.
    If $\varphi_e(n+1)=m$, two outer beta contractions, the successor reduction, universal evaluation, and the rational
    program give
    $$\begin{aligned}
    P(U\ChurchNumeral{e})\ChurchNumeral{n}
    &\to_\beta^*\LambdaRationalDouble\,
      ((U\ChurchNumeral{e})(\LambdaSucc\ChurchNumeral{n}))\\
    &\to_\beta^*\LambdaRationalDouble\ChurchNumeral{m}
     \to_\beta^*\ChurchNumeral{\mathrm{dbl}(m)}.
    \end{aligned}$$
    Only this one input value is needed; the indexed program may be partial elsewhere.
    For a valid Cauchy name, the preceding lemma proves that the transformed name represents $2x$.
    Thus $t$ tracks $d$ on computable points.
-/
theorem doubling_indices : ∃ t : ℕ → ℕ, (∃ k, ∀ e, App k e (t e)) ∧
    (∀ e n m, App e (n+1) m → App (t e) n (rationalDoubleIndex m)) ∧
    ∀ (x : (computablePointAssembly realRepresentation).Carrier) e,
      e ∈ (computablePointAssembly realRepresentation).realizes x →
      t e ∈ (computablePointAssembly realRepresentation).realizes (realDoublingMap.toFun x) := by
  obtain ⟨t,ht,hprogram⟩ := application_indices shiftDoubleProgram shiftDoubleProgram_closed
  have hp (e n m : ℕ) (he : App e (n+1) m) : App (t e) n (rationalDoubleIndex m) := by
    unfold App
    rw [hprogram]
    exact shiftDoubleProgram_partial he
  refine ⟨t,ht,hp,?_⟩
  rintro x e ⟨p,hp',he⟩
  refine ⟨doubleName p,(doubleName_realizes p).trans (congrArg (fun x : ℝ => 2*x) hp'),?_⟩
  intro n
  exact hp e n _ (he (n+1))

/-- The displayed doubling relation has all four trackers and represents the embedded map. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: Tracked doubling
-/
theorem doubling_functional_relation :
    ∃ t : ℕ → ℕ, (∃ k, ∀ e, App k e (t e)) ∧
      (∀ e n m, App e (n+1) m → App (t e) n (rationalDoubleIndex m)) ∧
      ∃ D : FunctionalRelation (computablePointAssembly realRepresentation).toPER
          (computablePointAssembly realRepresentation).toPER,
        D.val = Assembly.trackedRelationValue realDoublingMap t ∧
        D.Equivalent realDoublingMap.toRelation := by
  obtain ⟨t,ht,hp,htrack⟩ := doubling_indices
  exact ⟨t,ht,hp,Assembly.trackedRelation realDoublingMap t ht htrack,rfl,
    Assembly.trackedRelation_equiv_graph realDoublingMap t ht htrack⟩

end PolishSpaceBook.LambdaIndexPCA
