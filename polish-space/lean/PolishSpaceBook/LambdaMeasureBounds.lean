module

public import PolishSpaceBook.LambdaCantorMeasure
public import PolishSpaceBook.LambdaNumericalComparison
public import PolishSpaceBook.EffectiveDensePresentations

@[expose] public section

/-! # Cauchy names from complementary lower approximations

The search retains the numerical family parameter by checking it in every
candidate. Its output is a lower-bound code at a successful stage.
-/
namespace PolishSpaceBook
open Set Filter Topology MeasureTheory Metric NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Two lower approximations with complementary limiting masses. -/
structure ComplementaryLowerBounds (a b : ℕ → ℕ) (i : ℕ) (x : ℝ) : Prop where
  lower_left : ∀ s, rationalPoint (a (Nat.pair i s)) ≤ x
  lower_right : ∀ s, rationalPoint (b (Nat.pair i s)) ≤ 1-x
  limit_left : Tendsto (fun s => rationalPoint (a (Nat.pair i s))) atTop (𝓝 x)
  limit_right : Tendsto (fun s => rationalPoint (b (Nat.pair i s))) atTop (𝓝 (1-x))

def measureGapCode (a b : ℕ → ℕ) (c : ℕ) : ℕ :=
  rationalDifferenceCode (Nat.pair (RationalCode.dyadic 0).natCode
    ((RationalCode.ofNat (a c)).add (RationalCode.ofNat (b c))).natCode)

@[simp] theorem measureGapCode_value (a b : ℕ → ℕ) (c : ℕ) :
    rationalPoint (measureGapCode a b c) = 1-rationalPoint (a c)-rationalPoint (b c) := by
  rw [measureGapCode,rationalPoint_difference,rationalPoint_dyadic]
  simp [rationalPoint,sub_eq_add_neg,RationalCode.value_add]
  ring

def measureGapProgram (A B : AlphaTerm) : AlphaTerm := numericalCompose rationalDifferenceProgram
  (pairNumerical (numericalConstant (RationalCode.dyadic 0).natCode)
    (numericalCompose rationalAddTerm (pairNumerical A B)))

theorem measureGapProgram_computes {A B : AlphaTerm} {a b : ℕ → ℕ}
    (ha : NumericalComputes A a) (hb : NumericalComputes B b) :
    NumericalComputes (measureGapProgram A B) (measureGapCode a b) := by
  have h := rationalDifferenceProgram_computes.comp
    ((numericalConstant_computes (RationalCode.dyadic 0).natCode).pair
      (rationalAdd_computes.comp (ha.pair hb)))
  refine ⟨h.1,fun c => ?_⟩
  simpa only [measureGapProgram,measureGapCode,Nat.unpair_pair] using h.2 c

/-- Input is ((family parameter,precision),(candidate parameter,stage)). -/
def measureBoundBit (a b : ℕ → ℕ) (z : ℕ) : ℕ :=
  (if z.unpair.1.unpair.1 = z.unpair.2.unpair.1 then 1 else 0) *
  (if (RationalCode.ofNat (measureGapCode a b z.unpair.2)).value <
      (RationalCode.dyadic (z.unpair.1.unpair.2+1)).value then 1 else 0)

def measureBoundTest (A B : AlphaTerm) : AlphaTerm :=
  let input := numericalProjectionTerm true
  let candidate := numericalProjectionTerm false
  let i := numericalCompose (numericalProjectionTerm true) input
  let j := numericalCompose (numericalProjectionTerm true) candidate
  let n := numericalCompose (numericalProjectionTerm false) input
  let eps := numericalCompose rationalDyadicTerm (numericalCompose successorTerm n)
  mulNumerical (numericalCombine equalityTerm i j)
    (numericalCompose rationalLessTerm (pairNumerical
      (numericalCompose (measureGapProgram A B) candidate) eps))

theorem measureBoundTest_computes {A B : AlphaTerm} {a b : ℕ → ℕ}
    (ha : NumericalComputes A a) (hb : NumericalComputes B b) :
    NumericalComputes (measureBoundTest A B) (measureBoundBit a b) := by
  have hi := (projection_computes true).comp (projection_computes true)
  have hj := (projection_computes true).comp (projection_computes false)
  have hn := (projection_computes false).comp (projection_computes true)
  have heq := hi.combine hj equalityTerm_closed (fun i j => if i = j then 1 else 0) equalityTerm_apply
  have hg := (measureGapProgram_computes ha hb).comp (projection_computes false)
  have he := rationalDyadic_computes.comp (successor_computes.comp hn)
  have hc := rationalLess_computes.comp (hg.pair he)
  have h := heq.mul hc
  refine ⟨h.1,fun z => ?_⟩
  simpa only [measureBoundTest,measureBoundBit,Nat.unpair_pair,Bool.true_eq,ite_true,
    Bool.false_eq_true,ite_false,Nat.succ_eq_add_one,RationalCode.ofNat_natCode] using h.2 z

theorem measureBoundBit_success (a b : ℕ → ℕ) (i n c : ℕ) :
    measureBoundBit a b (Nat.pair (Nat.pair i n) c) ≠ 0 ↔
    c.unpair.1 = i ∧ rationalPoint (measureGapCode a b c) < (1/2:ℝ)^(n+1) := by
  have hr : (RationalCode.ofNat (measureGapCode a b c)).value <
      (RationalCode.dyadic (n+1)).value ↔
      rationalPoint (measureGapCode a b c) < (1/2:ℝ)^(n+1) := by
    rw [← rationalPoint_dyadic]
    simp only [rationalPoint,RationalCode.ofNat_natCode,Rat.cast_lt]
  have hbit (P : Prop) [Decidable P] : (if P then 1 else 0 : ℕ) ≠ 0 ↔ P := by
    split_ifs <;> simp_all
  simp only [measureBoundBit,Nat.unpair_pair,mul_ne_zero_iff,hbit,hr,eq_comm]

theorem ComplementaryLowerBounds.gap_tendsto {a b : ℕ → ℕ} {i : ℕ} {x : ℝ}
    (h : ComplementaryLowerBounds a b i x) :
    Tendsto (fun s => rationalPoint (measureGapCode a b (Nat.pair i s))) atTop (𝓝 0) := by
  simp_rw [measureGapCode_value]
  have ht := ((tendsto_const_nhds (x := (1:ℝ))).sub h.limit_left).sub h.limit_right
  simpa only [sub_self] using ht

theorem ComplementaryLowerBounds.exists_candidate {a b : ℕ → ℕ} {i : ℕ} {x : ℝ}
    (h : ComplementaryLowerBounds a b i x) (n : ℕ) :
    ∃ c, measureBoundBit a b (Nat.pair (Nat.pair i n) c) ≠ 0 := by
  obtain ⟨s,hs⟩ := (h.gap_tendsto.eventually
    (eventually_lt_nhds (by positivity : (0:ℝ)<(1/2:ℝ)^(n+1)))).exists
  exact ⟨Nat.pair i s,(measureBoundBit_success a b i n _).mpr ⟨by simp,hs⟩⟩

theorem ComplementaryLowerBounds.candidate_error {a b : ℕ → ℕ} {i : ℕ} {x : ℝ}
    (h : ComplementaryLowerBounds a b i x) (n c : ℕ)
    (hc : measureBoundBit a b (Nat.pair (Nat.pair i n) c) ≠ 0) :
    dist (rationalPoint (a c)) x ≤ (1/2:ℝ)^(n+1) := by
  obtain ⟨hi,hgap⟩ := (measureBoundBit_success a b i n c).mp hc
  have he : c = Nat.pair i c.unpair.2 := by rw [← hi,Nat.pair_unpair]
  have ha := h.lower_left c.unpair.2
  have hb := h.lower_right c.unpair.2
  rw [← he] at ha hb
  rw [measureGapCode_value] at hgap
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr ha)]
  linarith

def measureFromBoundsProgram (A B : AlphaTerm) : AlphaTerm := numericalResultSearch (measureBoundTest A B) A

theorem measureFromBoundsProgram_closed {A B : AlphaTerm} {a b : ℕ → ℕ}
    (ha : NumericalComputes A a) (hb : NumericalComputes B b) :
    (measureFromBoundsProgram A B).Closed := numericalResultSearch_closed (measureBoundTest_computes ha hb) ha

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Complementary lower bounds
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For input $\NatPair{i}{n}$, search through candidate codes $c=\NatPair{j}{s}$ and accept exactly when
    $$j=i\quad\text{and}\quad 1-u_{j,s}-v_{j,s}<2^{-(n+1)}.$$
    Let $\LambdaTermName{candidateTest}$ be the total numerical term returning one on acceptance and zero otherwise.
    Numerical projections,
    equality, rational arithmetic, the dyadic term, and rational comparison construct
    $\LambdaTermName{candidateTest}$ from $\LambdaTermName{lowerBound}, \LambdaTermName{complementBound}$. With
    $\LambdaTermName{reverseBit}:=\lambdaab{\tau}{\LambdaZeroTest\,\tau\,\ChurchNumeral{1}\,\ChurchNumeral{0}}$, put
    $$\LambdaTermName{fromBounds}:=\lambdaab{z}{\LambdaResultSearch\,
     ( \lambdaab{c}{ \LambdaTermName{reverseBit}( \LambdaTermName{candidateTest}( \LambdaNumericPair\,z\,c))})\,
    \LambdaTermName{lowerBound}}.$$
    The test includes $j=i$, so evaluating $\LambdaTermName{lowerBound}$ on a successful candidate returns a lower
    bound for the correct
    family member. Since $1-u_{i,s}-v_{i,s}\to0$, an accepted candidate exists for every requested precision.
    The result-search theorem gives the beta reduction to its output code.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For the returned lower bound $u_{i,s}$,
    $$0\le x_i-u_{i,s}\le 1-v_{i,s}-u_{i,s}<2^{-(n+1)}.$$
    If $p_i(n)$ is its code, the triangle inequality gives
    $$\Abs{\RationalValue{p_i(n)}-\RationalValue{p_i(m)}}
     \le 2^{-(n+1)}+2^{-(m+1)}\le 2^{-n}\qquad(n\le m).$$
    The outputs converge to $x_i$, so they form the required name. Neither monotonicity of the lower bounds nor a
    modulus for their convergence was used.
-/
theorem measureFromBoundsProgram_computes_name {A B : AlphaTerm} {a b : ℕ → ℕ}
    (ha : NumericalComputes A a) (hb : NumericalComputes B b) {i : ℕ} {x : ℝ}
    (h : ComplementaryLowerBounds a b i x) :
    ∃ p : realRepresentation.domain, realRepresentation.toFun p = x ∧
      ∀ n, Relation.ReflTransGen Beta
        (app (measureFromBoundsProgram A B) (numeral (Nat.pair i n))) (numeral (p.val n)) := by
  classical
  let p : ℕ → ℕ := fun n => a (Nat.find (h.exists_candidate n))
  have hp (n : ℕ) : dist (rationalPoint (p n)) x ≤ (1/2:ℝ)^(n+1) :=
    h.candidate_error n _ (Nat.find_spec (h.exists_candidate n))
  refine ⟨⟨p,isCauchyName_of_halfError_le hp⟩,cauchyRepresentation_eq_of_halfError_le p x hp,fun n => ?_⟩
  exact numericalResultSearch_hit (measureBoundTest_computes ha hb) ha (Nat.pair i n)
    (Nat.find (h.exists_candidate n)) (Nat.find_spec (h.exists_candidate n))
    (fun c hc => not_ne_iff.mp (Nat.find_min (h.exists_candidate n) hc))

/-- Specialize only the family index; precision remains the program's input. -/
def measureAtParameter (A B : AlphaTerm) (i : ℕ) : AlphaTerm :=
  numericalCompose (measureFromBoundsProgram A B) (insertBallCode i)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Complementary lower bounds
-/
theorem measureAtParameter_computes_name {A B : AlphaTerm} {a b : ℕ → ℕ}
    (ha : NumericalComputes A a) (hb : NumericalComputes B b) {i : ℕ} {x : ℝ}
    (h : ComplementaryLowerBounds a b i x) :
    ∃ p : realRepresentation.domain, realRepresentation.toFun p = x ∧
      NumericalComputes (measureAtParameter A B i) p.val := by
  obtain ⟨p,hp,hr⟩ := measureFromBoundsProgram_computes_name ha hb h
  have hP := measureFromBoundsProgram_closed ha hb
  have hI := (insertBallCode_computes i).1
  refine ⟨p,hp,?_,fun n => ?_⟩
  · unfold measureAtParameter numericalCompose Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [hP,hI]; simp
  · have hs : Beta (app (measureAtParameter A B i) (numeral n))
        (app (measureFromBoundsProgram A B) (app (insertBallCode i) (numeral n))) := by
      simpa only [measureAtParameter,numericalCompose,subst_app,subst_var,ite_true,
        subst_closed _ _ _ hP,subst_closed _ _ _ hI] using
        Beta.contract 40 (app (measureFromBoundsProgram A B) (app (insertBallCode i) (var 40))) (numeral n)
    exact (Relation.ReflTransGen.single hs).trans
      ((beta_steps_app_right _ ((insertBallCode_computes i).2 n)).trans (hr n))

end PolishSpaceBook
