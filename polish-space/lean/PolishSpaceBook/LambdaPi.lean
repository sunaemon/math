module

public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.LambdaBoundedProducts
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! # Machin's formula and numerical lambda programs for pi -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open Filter Topology
set_option maxRecDepth 4096

noncomputable def arctanMagnitude (t : ℝ) (j : ℕ) := t^(2*j+1)/(2*j+1)
noncomputable def arctanPartial (t : ℝ) (N : ℕ) :=
  ∑ j ∈ Finset.range N, (-1:ℝ)^j * arctanMagnitude t j

theorem arctanMagnitude_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    0 ≤ arctanMagnitude t j := by unfold arctanMagnitude; positivity

theorem arctanMagnitude_le_power {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    arctanMagnitude t j ≤ t^(2*j+1) := by
  unfold arctanMagnitude
  apply div_le_self (by positivity)
  norm_num

theorem arctanMagnitude_antitone {t : ℝ} (ht : 0 ≤ t) (h1 : t ≤ 1) :
    Antitone (arctanMagnitude t) := by
  intro i j hij
  unfold arctanMagnitude
  apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one ht h1 (by omega))
    (by positivity) (by exact_mod_cast (show 2*i+1 ≤ 2*j+1 by omega))

theorem arctanMagnitude_summable {t : ℝ} (ht : 0 ≤ t) (h1 : t < 1) :
    Summable (arctanMagnitude t) := by
  apply Summable.of_nonneg_of_le (arctanMagnitude_nonneg ht)
    (fun j => (arctanMagnitude_le_power ht j).trans
      (pow_le_pow_of_le_one ht h1.le (by omega : j ≤ 2*j+1)))
    (summable_geometric_of_lt_one ht h1)

theorem arctanPartial_error {t : ℝ} (ht : 0 ≤ t) (h1 : t < 1) (N : ℕ) :
    |arctanPartial t N - Real.arctan t| ≤ t^(2*N+1)/(2*N+1) := by
  have hs : HasSum (fun j => (-1:ℝ)^j * arctanMagnitude t j) (Real.arctan t) := by
    simpa [arctanMagnitude,mul_div_assoc] using
      Real.hasSum_arctan (by simpa [Real.norm_eq_abs,abs_of_nonneg ht] using h1)
  rw [abs_sub_comm,← hs.tsum_eq]
  exact alternating_series_error_bound _ (arctanMagnitude_antitone ht h1.le)
    (arctanMagnitude_summable ht h1) N

/-- Derive the identity by two doublings and the addition formula, keeping the branches explicit. -/
theorem machin_formula : Real.pi = 16*Real.arctan (1/5) - 4*Real.arctan (1/239) := by
  have h : 4 * Real.arctan (1/5) - Real.arctan (1/239) = Real.pi/4 := by
    rw [show 4 * Real.arctan (1/5) = 2 * (2 * Real.arctan (1/5)) by ring,
      Real.two_mul_arctan,Real.two_mul_arctan,← Real.arctan_one,sub_eq_iff_eq_add,Real.arctan_add]
    <;> norm_num
  linarith

noncomputable def machinPartial (N : ℕ) := 16*arctanPartial (1/5) N - 4*arctanPartial (1/239) N

theorem arctanPartial_dyadic_error {t : ℝ} (ht : 0 ≤ t) (hhalf : t ≤ 1/2) (n : ℕ) :
    |arctanPartial t (n+4) - Real.arctan t| ≤ (1/2:ℝ)^(n+8) := by
  have h := arctanPartial_error ht (by linarith : t<1) (n+4)
  refine h.trans ((arctanMagnitude_le_power ht (n+4)).trans ?_)
  calc
    t^(2*(n+4)+1) ≤ (1/2:ℝ)^(2*(n+4)+1) := pow_le_pow_left₀ ht hhalf _
    _ ≤ (1/2:ℝ)^(n+8) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem machinPartial_error (n : ℕ) :
    |machinPartial (n+4) - Real.pi| ≤ (1/2:ℝ)^(n+3) := by
  have h5 := arctanPartial_dyadic_error (by norm_num : (0:ℝ)≤1/5) (by norm_num) n
  have h239 := arctanPartial_dyadic_error (by norm_num : (0:ℝ)≤1/239) (by norm_num) n
  rw [machinPartial,machin_formula]
  calc
    |16*arctanPartial (1/5) (n+4) - 4*arctanPartial (1/239) (n+4) -
        (16*Real.arctan (1/5)-4*Real.arctan (1/239))|
        = |16*(arctanPartial (1/5) (n+4)-Real.arctan (1/5)) -
          4*(arctanPartial (1/239) (n+4)-Real.arctan (1/239))| := by congr 1; ring
    _ ≤ 16*|arctanPartial (1/5) (n+4)-Real.arctan (1/5)| +
        4*|arctanPartial (1/239) (n+4)-Real.arctan (1/239)| := by
      simpa [abs_mul] using abs_sub_le
        (16*(arctanPartial (1/5) (n+4)-Real.arctan (1/5))) 0
        (4*(arctanPartial (1/239) (n+4)-Real.arctan (1/239)))
    _ ≤ 20*(1/2:ℝ)^(n+8) := by nlinarith
    _ ≤ (1/2:ℝ)^(n+3) := by
      rw [show n+8 = (n+3)+5 by omega,pow_add]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) (n+3)]

/-- Specialize numerical recursion to an unused parameter zero. -/
def piRecursionProgram (a : ℕ) (H : AlphaTerm) : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant a) H)
  (pairNumerical (numericalConstant 0) numericalIdentity)

theorem piRecursion_computes {H : AlphaTerm} {h : ℕ → ℕ → ℕ}
    (hh : NumericalComputes H (fun z => h z.unpair.2.unpair.1 z.unpair.2.unpair.2)) (a : ℕ) :
    NumericalComputes (piRecursionProgram a H) (primitiveRec a h) := by
  simpa [piRecursionProgram,Nat.unpair_pair] using
    (numericalRecursion_computes (numericalConstant_computes a) hh).comp
      ((numericalConstant_computes 0).pair numericalIdentity_computes)

def piCounter : AlphaTerm := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
def piState : AlphaTerm := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)

theorem piCounter_computes : NumericalComputes piCounter (fun z => z.unpair.2.unpair.1) :=
  (projection_computes true).comp (projection_computes false)
theorem piState_computes : NumericalComputes piState (fun z => z.unpair.2.unpair.2) :=
  (projection_computes false).comp (projection_computes false)

def piPowerProgram (b : ℕ) : AlphaTerm :=
  piRecursionProgram 1 (mulNumerical (numericalConstant b) piState)

theorem piPower_computes (b : ℕ) : NumericalComputes (piPowerProgram b) (fun j => b^j) := by
  have h := piRecursion_computes (h := fun _ r => b*r) ((numericalConstant_computes b).mul piState_computes) 1
  have he : primitiveRec 1 (fun _ r => b*r) = (fun j => b^j) := by
    funext j
    induction j with
    | zero => rfl
    | succ j ih => simpa only [primitiveRec,pow_succ'] using congrArg (b*·) ih
  simpa [piPowerProgram,he] using h

/-- The positive and negative numerator parts alternate by swapping. -/
def piSignState : ℕ → ℕ := primitiveRec (Nat.pair 1 0) (fun _ s => Nat.pair s.unpair.2 s.unpair.1)

theorem piSignState_value (j : ℕ) :
    ((piSignState j).unpair.1:ℝ) - (piSignState j).unpair.2 = (-1:ℝ)^j := by
  induction j with
  | zero => norm_num [piSignState,primitiveRec]
  | succ j ih =>
    change ((Nat.pair (piSignState j).unpair.2 (piSignState j).unpair.1).unpair.1:ℝ) -
      (Nat.pair (piSignState j).unpair.2 (piSignState j).unpair.1).unpair.2 = _
    rw [Nat.unpair_pair,pow_succ,← ih]
    ring

def piSignProgram : AlphaTerm := piRecursionProgram (Nat.pair 1 0)
  (pairNumerical (numericalCompose (numericalProjectionTerm false) piState)
    (numericalCompose (numericalProjectionTerm true) piState))

theorem piSign_computes : NumericalComputes piSignProgram piSignState :=
  piRecursion_computes (h := fun _ s => Nat.pair s.unpair.2 s.unpair.1) (((projection_computes false).comp piState_computes).pair
    ((projection_computes true).comp piState_computes)) (Nat.pair 1 0)

def arctanTermCode (b j : ℕ) : RationalCode :=
  ((piSignState j).unpair,(2*j+1)*b^(2*j+1)-1)

theorem arctanTermCode_value (b j : ℕ) (hb : 0<b) :
    ((arctanTermCode b j).value:ℝ) = (-1:ℝ)^j * arctanMagnitude (1/(b:ℝ)) j := by
  have hd : 1 ≤ (2*j+1)*b^(2*j+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [arctanTermCode,RationalCode.value,Nat.sub_add_cancel hd]
  push_cast
  rw [piSignState_value]
  simp only [arctanMagnitude,div_eq_mul_inv,mul_inv_rev]
  ring

def arctanTermProgram (b : ℕ) : AlphaTerm :=
  let J := addNumerical (mulNumerical (numericalConstant 2) numericalIdentity) (numericalConstant 1)
  pairNumerical piSignProgram (numericalCompose predecessorTerm
    (mulNumerical J (numericalCompose (piPowerProgram b) J)))

theorem arctanTerm_computes (b : ℕ) :
    NumericalComputes (arctanTermProgram b) (fun j => (arctanTermCode b j).natCode) := by
  have hj := ((numericalConstant_computes 2).mul numericalIdentity_computes).add (numericalConstant_computes 1)
  have h := piSign_computes.pair (predecessor_computes.comp (hj.mul ((piPower_computes b).comp hj)))
  simpa [arctanTermProgram,arctanTermCode,RationalCode.natCode,Nat.pair_unpair] using h

/-- Keep finite sums symbolic instead of expanding their large natural-number codes during elaboration. -/
@[irreducible] def arctanSumCode (b : ℕ) : ℕ → ℕ := primitiveRec 0 (fun j s =>
  (RationalCode.add (RationalCode.ofNat s) (arctanTermCode b j)).natCode)

theorem arctanSumCode_succ (b N : ℕ) : arctanSumCode b (N+1) =
    (RationalCode.add (RationalCode.ofNat (arctanSumCode b N)) (arctanTermCode b N)).natCode := by
  rw [arctanSumCode,primitiveRec]

theorem arctanSumCode_value (b N : ℕ) (hb : 0<b) :
    rationalPoint (arctanSumCode b N) = arctanPartial (1/(b:ℝ)) N := by
  induction N with
  | zero => norm_num [arctanSumCode,primitiveRec,rationalPoint,RationalCode.ofNat,RationalCode.value,arctanPartial]
  | succ N ih =>
    rw [arctanSumCode_succ]
    simp only [rationalPoint,RationalCode.ofNat_natCode,RationalCode.value_add,Rat.cast_add]
    rw [show ((RationalCode.ofNat (arctanSumCode b N)).value:ℝ) =
      arctanPartial (1/(b:ℝ)) N from ih,arctanTermCode_value b N hb]
    simp [arctanPartial,Finset.sum_range_succ]

def arctanSumProgram (b : ℕ) : AlphaTerm := piRecursionProgram 0
  (numericalCompose rationalAddTerm (pairNumerical piState
    (numericalCompose (arctanTermProgram b) piCounter)))

theorem arctanSum_computes (b : ℕ) : NumericalComputes (arctanSumProgram b) (arctanSumCode b) := by
  have h := rationalAdd_computes.comp
    (piState_computes.pair ((arctanTerm_computes b).comp piCounter_computes))
  unfold arctanSumCode
  apply piRecursion_computes
  simpa [Nat.unpair_pair] using h

def piScaleCode (k s : ℕ) : ℕ :=
  RationalCode.natCode ((k*s.unpair.1.unpair.1,k*s.unpair.1.unpair.2),s.unpair.2)

def piScaleProgram (k : ℕ) : AlphaTerm := pairNumerical
  (pairNumerical (mulNumerical (numericalConstant k) (rationalNumeratorTerm true))
    (mulNumerical (numericalConstant k) (rationalNumeratorTerm false))) (numericalProjectionTerm false)

theorem piScale_computes (k : ℕ) : NumericalComputes (piScaleProgram k) (piScaleCode k) := by
  exact (((numericalConstant_computes k).mul (rationalNumerator_computes true)).pair
    ((numericalConstant_computes k).mul (rationalNumerator_computes false))).pair (projection_computes false)

theorem piScale_value (k s : ℕ) : rationalPoint (piScaleCode k s) = k*rationalPoint s := by
  simp [piScaleCode,rationalPoint,RationalCode.ofNat,RationalCode.natCode,RationalCode.value]
  ring

def piNegateCode (s : ℕ) : ℕ :=
  RationalCode.natCode ((s.unpair.1.unpair.2,s.unpair.1.unpair.1),s.unpair.2)

def piNegateProgram : AlphaTerm := pairNumerical
  (pairNumerical (rationalNumeratorTerm false) (rationalNumeratorTerm true)) (numericalProjectionTerm false)

theorem piNegate_computes : NumericalComputes piNegateProgram piNegateCode :=
  ((rationalNumerator_computes false).pair (rationalNumerator_computes true)).pair (projection_computes false)

theorem piNegate_value (s : ℕ) : rationalPoint (piNegateCode s) = -rationalPoint s := by
  simp [piNegateCode,rationalPoint,RationalCode.ofNat,RationalCode.natCode,RationalCode.value]
  ring

def piName (n : ℕ) : ℕ := (RationalCode.add
  (RationalCode.ofNat (piScaleCode 16 (arctanSumCode 5 (n+4))))
  (RationalCode.ofNat (piNegateCode (piScaleCode 4 (arctanSumCode 239 (n+4)))))).natCode

theorem piName_value (n : ℕ) : rationalPoint (piName n) = machinPartial (n+4) := by
  have hadd (s t : ℕ) : rationalPoint ((RationalCode.add (RationalCode.ofNat s)
      (RationalCode.ofNat t)).natCode) = rationalPoint s + rationalPoint t := by simp [rationalPoint]
  unfold piName
  rw [hadd,piNegate_value,piScale_value,piScale_value,
    arctanSumCode_value 5 (n+4) (by decide),arctanSumCode_value 239 (n+4) (by decide)]
  simp [machinPartial,sub_eq_add_neg]

def piNameProgram : AlphaTerm :=
  let N := addNumerical numericalIdentity (numericalConstant 4)
  let A := numericalCompose (piScaleProgram 16) (numericalCompose (arctanSumProgram 5) N)
  let B := numericalCompose piNegateProgram
    (numericalCompose (piScaleProgram 4) (numericalCompose (arctanSumProgram 239) N))
  numericalCompose rationalAddTerm (pairNumerical A B)

theorem piName_computes : NumericalComputes piNameProgram piName := by
  have hn := numericalIdentity_computes.add (numericalConstant_computes 4)
  have ha := (piScale_computes 16).comp ((arctanSum_computes 5).comp hn)
  have hb := piNegate_computes.comp ((piScale_computes 4).comp ((arctanSum_computes 239).comp hn))
  have h := rationalAdd_computes.comp (ha.pair hb)
  refine ⟨h.1,fun n => ?_⟩
  simpa only [piNameProgram,piName,Nat.unpair_pair,id_eq] using h.2 n

theorem piName_error (n : ℕ) : |rationalPoint (piName n) - Real.pi| ≤ (1/2:ℝ)^(n+3) := by
  rw [piName_value]
  exact machinPartial_error n

theorem piName_isCauchy : IsCauchyName rationalPoint piName := by
  intro n m hnm
  calc
    dist (rationalPoint (piName n)) (rationalPoint (piName m))
        ≤ dist (rationalPoint (piName n)) (Real.pi) +
          dist (Real.pi) (rationalPoint (piName m)) := dist_triangle _ _ _
    _ ≤ (1/2:ℝ)^(n+3) + (1/2:ℝ)^(m+3) := by
      rw [dist_comm (Real.pi)]
      exact add_le_add (piName_error n) (piName_error m)
    _ ≤ (1/2:ℝ)^(n+3) + (1/2:ℝ)^(n+3) := add_le_add_right
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        (Nat.add_le_add_right hnm 3)) _
    _ ≤ (1/2:ℝ)^n := by
      rw [pow_add]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

theorem piName_tendsto :
    Tendsto (fun n => rationalPoint (piName n)) atTop (𝓝 (Real.pi)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ)<1)
  refine ⟨N,fun n hn => ?_⟩
  exact lt_of_le_of_lt ((piName_error n).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))) hN

def piNamePoint : realRepresentation.domain := ⟨piName,piName_isCauchy⟩

theorem piName_represents : realRepresentation.toFun piNamePoint = Real.pi :=
  tendsto_nhds_unique (f := fun n => rationalPoint (piName n))
    (tendsto_cauchyRepresentation rationalPoint piNamePoint) piName_tendsto

/-- The standard real pi has a Cauchy name computed by one closed lambda term. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: example
  title: Computing $\pi$ by Machin's formula
  excerpt: |
    \begin{example*}[Computing $\pi$ by Machin's formula]
    The real number $\pi$ is computable.
    \end{example*}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The arctangent addition and doubling formulas give
    $$\begin{aligned}
    2\arctan(1/5)&=\arctan(5/12),\\
    2\arctan(5/12)&=\arctan(120/119),\\
    \arctan(1)+\arctan(1/239)&=\arctan(120/119).
    \end{aligned}$$
    In each use of the addition formula the product of the two arguments is less than $1$, so no correction by $\pi$ is
    needed. Since $\arctan(1)=\pi/4$, these identities prove Machin's formula
    $$\pi=16\arctan(1/5)-4\arctan(1/239).$$

    For $0\le t<1$, write the first $N$ terms of the arctangent series as
    $$T_N(t):=\sum_{j<N}(-1)^j\frac{t^{2j+1}}{2j+1}.$$
    The nonnegative magnitudes $t^{2j+1}/(2j+1)$ decrease and are bounded by $t^j$, so they form a summable sequence.
    The series sums to $\arctan t$, and the alternating-series estimate bounds the error by the next term:
    $$|T_N(t)-\arctan t|\le\frac{t^{2N+1}}{2N+1}.$$
    Both arguments in Machin's formula are at most $1/2$. For $N=n+4$, we have $2N+1\ge n+8$, so each arctangent error
    is at most $2^{-(n+8)}$. Consequently the rational
    $$q_n:=16T_{n+4}(1/5)-4T_{n+4}(1/239)$$
    satisfies
    $$|q_n-\pi|\le(16+4)2^{-(n+8)}\le2^{-(n+3)}.$$
    As in the preceding examples, this proves convergence to $\pi$ and the pairwise bounds for a fast Cauchy name.

    We next implement these rational partial sums. Represent the alternating sign by two natural numbers:
    $$(u_0,v_0)=(1,0),\qquad (u_{j+1},v_{j+1})=(v_j,u_j).$$
    Taking the difference in the integers, induction gives $u_j-v_j=(-1)^j$. For a fixed positive integer $b$, set
    $$c_{b,j}:=\RationalCode{u_j}{v_j}{(2j+1)b^{2j+1}-1}.$$
    Its denominator is positive, and its rational value is
    $$\RationalValue{c_{b,j}}=\frac{(-1)^j}{(2j+1)b^{2j+1}}.$$
    The two sign components are computed by swapping numerical projections in a recursion starting at the code of $(1,0)$.
    A second recursion, starting at $1$ and multiplying by $b$ at each step, computes $k\mapsto b^k$.
    Compose these recursions with addition, multiplication, predecessor, and pairing. This constructs a closed term $B_b$
    with
    $$B_b\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{c_{b,j}}.$$
    The subtraction in the denominator code is ordinary subtraction because $(2j+1)b^{2j+1}>0$.

    The rational-zero code is $\RationalCode{0}{0}{0}=0$. Define the closed step term and recursor
    $$\begin{aligned}
    H_b&:=\lambdaab{u}{\lambdaab{v}{\LambdaRationalAdd\,(\LambdaNumericPair\,v\,(B_bu))}},\\
    Q_b&:=\LambdaRecursor\,H_b\,\ChurchNumeral{0}.
    \end{aligned}$$
    At step $j$, the accumulator code is added to $c_{b,j}$ by the rational-addition program. Induction on $N$ gives
    $$Q_b\ChurchNumeral{N}\to_\beta^*\ChurchNumeral{s_{b,N}},\qquad
    \RationalValue{s_{b,N}}=T_N(1/b).$$
    Every step terminates and preserves this value identity, including the initial empty sum.

    Finally, multiplication of a rational code by a natural number $k$ and negation are the operations
    $$\RationalCode{u}{v}{d}\longmapsto\RationalCode{ku}{kv}{d},\qquad
    \RationalCode{u}{v}{d}\longmapsto\RationalCode{v}{u}{d}.$$
    They use only multiplication, projection, and pairing, and hence have closed lambda implementations.
    On input $n$, run $Q_5$ and $Q_{239}$ at $n+4$, multiply their rational outputs by $16$ and $4$, negate the second,
    and add them. The resulting closed term $P$ satisfies
    $$P\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{p(n)},\qquad \RationalValue{p(n)}=q_n.$$
    The error estimate above shows that $p$ is a computable fast Cauchy name of $\pi$.
    \end{proof}
-/
theorem pi_computable :
    ∃ p : realRepresentation.domain, realRepresentation.toFun p = Real.pi ∧
      ∃ P : AlphaTerm, NumericalComputes P p.val := by
  refine ⟨piNamePoint,piName_represents,piNameProgram,?_⟩
  change NumericalComputes piNameProgram piName
  exact piName_computes

end PolishSpaceBook
