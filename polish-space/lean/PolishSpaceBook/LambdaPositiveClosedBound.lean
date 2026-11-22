module

public import PolishSpaceBook.LambdaOpenPointCylinder

@[expose] public section

/-! # Finding a test row small enough for a positive closed set
A fast name of the open complement supplies a terminating rational search.
-/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA CantorMeasure
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def complementMarginBit (q : ℕ → ℕ) (s : ℕ) : ℕ :=
  if (RationalCode.ofNat (massUpperCode (massUpperCode q) s)).value <
    (RationalCode.dyadic 0).value then 1 else 0

def complementMarginProgram (Q : AlphaTerm) : AlphaTerm := numericalCompose rationalLessTerm
  (pairNumerical (massUpperProgram (massUpperProgram Q)) (numericalConstant (RationalCode.dyadic 0).natCode))

theorem complementMarginProgram_computes {Q : AlphaTerm} {q : ℕ → ℕ} (hq : NumericalComputes Q q) :
    NumericalComputes (complementMarginProgram Q) (complementMarginBit q) := by
  have h := rationalLess_computes.comp ((massUpperProgram_computes (massUpperProgram_computes hq)).pair
    (numericalConstant_computes (RationalCode.dyadic 0).natCode))
  change NumericalComputes _ (fun s => if (RationalCode.ofNat (massUpperCode (massUpperCode q) s)).value <
    (RationalCode.dyadic 0).value then 1 else 0)
  simpa only [complementMarginProgram,Nat.unpair_pair,RationalCode.ofNat_natCode] using h

theorem complementMarginBit_iff (q : ℕ → ℕ) (s : ℕ) : complementMarginBit q s ≠ 0 ↔
    rationalPoint (q s) + 2*(1/2:ℝ)^s < 1 := by
  have hc : (RationalCode.ofNat (massUpperCode (massUpperCode q) s)).value <
      (RationalCode.dyadic 0).value ↔ rationalPoint (q s) + 2*(1/2:ℝ)^s < 1 := by
    rw [← Rat.cast_lt (K := ℝ)]
    change rationalPoint (massUpperCode (massUpperCode q) s) < ((RationalCode.dyadic 0).value : ℝ) ↔ _
    rw [massUpperCode_value,massUpperCode_value,RationalCode.value_dyadic]
    norm_num
    ring_nf
  unfold complementMarginBit
  split_ifs with h <;> simp_all

def positiveComplementRowProgram (Q : AlphaTerm) : AlphaTerm :=
  numericalResultSearch (numericalCompose (complementMarginProgram Q) (numericalProjectionTerm false)) successorTerm

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: lemma
  title: Refining a positive closed set
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    First compute an integer $n$ with $2^{-n}<\mu(K)/2$.
    Let $Q$ compute a fast Cauchy name $a$ of the measure of the open complement, and write
    $r_s:=q_{a(s)}$. Search for the first $s$ with
    $$r_s+2\cdot2^{-s}<1,$$
    and put $n:=s+1$. The search terminates because $r_s\to1-\mu(K)<1$.
    The Cauchy error bound gives $1-\mu(K)\le r_s+2^{-s}$, hence
    $$2^{-s}<\mu(K),\qquad 2^{-n}<\mu(K)/2.$$
    To write the search as a lambda term, put $c_1:=\RationalCode{1}{0}{0}$ and use
    $$\begin{aligned}
    A&:=\lambdaab{s}{\LambdaRationalAdd(\LambdaNumericPair\,(Qs)\,(\LambdaDyadic\,s))},\\
    B&:=\lambdaab{s}{\LambdaRationalAdd(\LambdaNumericPair\,(As)\,(\LambdaDyadic\,s))},\\
    T&:=\lambdaab{s}{\LambdaRationalLess(\LambdaNumericPair\,(Bs)\,\ChurchNumeral{c_1})},\\
    J&:=\LambdaResultSearch\,
     (\lambdaab{s}{\LambdaZeroTest\,(Ts)\,\ChurchNumeral{1}\,\ChurchNumeral{0}})\,\LambdaSucc.
    \end{aligned}$$
    The rational comparison succeeds at the stated stage and $J\to_\beta^*\ChurchNumeral{n}$.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Set $C:=\SetDifference{K}{U_n}$. Then
    $$\mu(C)\ge\mu(K)-\mu(U_n)\ge\mu(K)-2^{-n}>\mu(K)/2>0.$$
    Its complement is the union of the open complement of $K$ and $U_n$.
    Both have computable open and measure names, so the finite-union proposition makes $C$ effectively closed
    with computable measure. The row programs for $U_n$ are obtained by substituting the computed numeral for
    the row argument of the two uniform Schnorr-test programs.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Apply the computable-support-point theorem to $C$. It gives a computable point $y\in C$ with
    $$\mu(C\cap\cyl{\restrict{y}{k}})>0\qquad(k\in\NN).$$
    Every computable point fails Schnorr randomness, hence also Martin-Löf randomness.
    By universality, $y\in V_e$. The cylinder-search lemma computes a binary word $w$ with
    $y\in\cyl{w}\IncludedIn V_e$. Since $w=\restrict{y}{|w|}$, the set
    $$L:=C\cap\cyl{w}$$
    has positive measure. It is effectively closed with computable measure by the cylinder-complement lemma.
    It is contained in $K\cap V_e$ and disjoint from $U_n$, as required.
-/
theorem positiveComplementRowProgram_finds {Q : AlphaTerm} (q : realRepresentation.domain)
    (hq : NumericalComputes Q q.val) (hq1 : realRepresentation.toFun q < 1) :
    (positiveComplementRowProgram Q).Closed ∧ ∃ n : ℕ,
      Relation.ReflTransGen Beta (app (positiveComplementRowProgram Q) (numeral 0)) (numeral n) ∧
      (1/2:ℝ)^n < (1-realRepresentation.toFun q)/2 := by
  have hq' := tendsto_cauchyRepresentation rationalPoint q
  change Tendsto (fun s => rationalPoint (q.val s)) atTop (𝓝 (realRepresentation.toFun q)) at hq'
  have he : Tendsto (fun s => (1/2:ℝ)^s) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun s => rationalPoint (q.val s) + 2*(1/2:ℝ)^s) atTop
      (𝓝 (realRepresentation.toFun q)) := by simpa using hq'.add (he.const_mul 2)
  have hex : ∃ s, complementMarginBit q.val s ≠ 0 := by
    obtain ⟨s,hs⟩ := (ht.eventually (eventually_lt_nhds hq1)).exists
    exact ⟨s,(complementMarginBit_iff q.val s).mpr hs⟩
  let s := Nat.find hex
  have hhit := Nat.find_spec hex
  have hb := (complementMarginBit_iff q.val s).mp hhit
  have hu := massUpperCode_bound q s
  rw [massUpperCode_value] at hu
  have hf := (complementMarginProgram_computes hq).comp (projection_computes false)
  refine ⟨numericalResultSearch_closed hf successor_computes,s+1,?_,?_⟩
  · exact numericalResultSearch_hit hf successor_computes 0 s (by simpa using hhit)
      (fun k hk => by simpa using not_ne_iff.mp (Nat.find_min hex hk))
  · rw [pow_succ]
    linarith

end PolishSpaceBook.LambdaRandomness
