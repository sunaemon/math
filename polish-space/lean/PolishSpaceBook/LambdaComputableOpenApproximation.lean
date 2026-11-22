module

public import PolishSpaceBook.LambdaRandomLimitApproximation

@[expose] public section

/-! # Finite approximations to an open set of computable measure
A fast name of the total mass supplies a computable stage with a small
unseen tail. The same stage controls the error in every binary cylinder.
-/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory Metric NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open CantorMeasure CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def massUpperCode (q : ℕ → ℕ) (s : ℕ) : ℕ :=
  ((RationalCode.ofNat (q s)).add (RationalCode.dyadic s)).natCode

def tailGapCode (p q : ℕ → ℕ) (s : ℕ) : ℕ :=
  rationalDifferenceCode (Nat.pair (massUpperCode q s) (lowerMeasureCode p s))

@[simp] theorem massUpperCode_value (q : ℕ → ℕ) (s : ℕ) :
    rationalPoint (massUpperCode q s) = rationalPoint (q s) + (1/2:ℝ)^s := by
  simp [massUpperCode,rationalPoint,RationalCode.value_add,RationalCode.value_dyadic]

@[simp] theorem tailGapCode_value (p q : ℕ → ℕ) (s : ℕ) :
    rationalPoint (tailGapCode p q s) =
      rationalPoint (q s) + (1/2:ℝ)^s-rationalPoint (lowerMeasureCode p s) := by
  rw [tailGapCode,rationalPoint_difference,massUpperCode_value]

theorem massUpperCode_bound (q : realRepresentation.domain) (s : ℕ) :
    realRepresentation.toFun q ≤ rationalPoint (massUpperCode q.val s) := by
  have h := cauchyRepresentation_dist_le rationalPoint q s
  change dist (rationalPoint (q.val s)) (realRepresentation.toFun q) ≤ (1/2:ℝ)^s at h
  rw [Real.dist_eq,abs_le] at h
  rw [massUpperCode_value]
  linarith [h.1]

theorem tailGapCode_tendsto {p : ℕ → ℕ} (hp : ValidOpenName p) (q : realRepresentation.domain)
    (hq : realRepresentation.toFun q = fairCoinProduct.real (namedOpen p)) :
    Tendsto (fun s => rationalPoint (tailGapCode p q.val s)) atTop (𝓝 0) := by
  have hq' := tendsto_cauchyRepresentation rationalPoint q
  change Tendsto (fun s => rationalPoint (q.val s)) atTop (𝓝 (realRepresentation.toFun q)) at hq'
  rw [hq] at hq'
  have he : Tendsto (fun s => (1/2:ℝ)^s) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [tailGapCode_value,add_zero,sub_self] using (hq'.add he).sub (lowerMeasureCode_tendsto hp)

def tailSmallBit (p q : ℕ → ℕ) (z : ℕ) : ℕ :=
  if (RationalCode.ofNat (tailGapCode p q z.unpair.2)).value <
    (RationalCode.dyadic (z.unpair.1+1)).value then 1 else 0

theorem tailSmallBit_iff (p q : ℕ → ℕ) (k s : ℕ) :
    tailSmallBit p q (Nat.pair k s) ≠ 0 ↔
      rationalPoint (tailGapCode p q s) < (1/2:ℝ)^(k+1) := by
  have hh : (RationalCode.ofNat (tailGapCode p q s)).value < (RationalCode.dyadic (k+1)).value ↔
      rationalPoint (tailGapCode p q s) < (1/2:ℝ)^(k+1) := by
    rw [← rationalPoint_dyadic]
    simp only [rationalPoint,RationalCode.ofNat_natCode,Rat.cast_lt]
  simp only [tailSmallBit,Nat.unpair_pair]
  split_ifs with h <;> simp_all

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Let $P$ compute $p$, and let $Q$ compute a fast Cauchy name $r$ of $\mu(U_p)$.
    Write $q_{r(s)}$ for its rational approximation at stage $s$, so
    $|q_{r(s)}-\mu(U_p)|\le 2^{-s}$. Set
    $$u_s:=q_{r(s)}+2^{-s},\qquad d_s:=u_s-\mu(U_{L_s}).$$
    Then $u_s\ge\mu(U_p)$ and
    $$0\le\mu\bigl(\SetDifference{U_p}{U_{L_s}}\bigr)
    =\mu(U_p)-\mu(U_{L_s})\le d_s.$$
    Both $u_s$ and $\mu(U_{L_s})$ tend to $\mu(U_p)$, hence $d_s\to0$.
    The rational $d_s$ is exactly computable from the two programs and the finite-union measure algorithm.
    Search for the first $s$ with $d_s<2^{-(k+1)}$ and return that stage. The convergence proves termination.
-/
theorem tailSmallBit_exists {p : ℕ → ℕ} (hp : ValidOpenName p) (q : realRepresentation.domain)
    (hq : realRepresentation.toFun q = fairCoinProduct.real (namedOpen p)) (k : ℕ) :
    ∃ s, tailSmallBit p q.val (Nat.pair k s) ≠ 0 := by
  obtain ⟨s,hs⟩ := ((tailGapCode_tendsto hp q hq).eventually
    (eventually_lt_nhds (by positivity : (0:ℝ)<(1/2:ℝ)^(k+1)))).exists
  exact ⟨s,(tailSmallBit_iff p q.val k s).mpr hs⟩

theorem stageOpen_subset (p : ℕ → ℕ) (s : ℕ) : stageOpen p s ⊆ namedOpen p := by
  rw [← iUnion_stageOpen]
  exact subset_iUnion (stageOpen p) s

theorem tailSmallBit_error {p : ℕ → ℕ} (hp : ValidOpenName p) (q : realRepresentation.domain)
    (hq : realRepresentation.toFun q = fairCoinProduct.real (namedOpen p)) (k s : ℕ)
    (hs : tailSmallBit p q.val (Nat.pair k s) ≠ 0) :
    fairCoinProduct.real (namedOpen p \ stageOpen p s) < (1/2:ℝ)^(k+1) := by
  have h := (tailSmallBit_iff p q.val k s).mp hs
  have hu := massUpperCode_bound q s
  rw [hq,massUpperCode_value] at hu
  rw [tailGapCode_value,lowerMeasureCode_value hp] at h
  rw [measureReal_sdiff (stageOpen_subset p s)
    (by rw [← finiteOpen_prefix]; exact (isOpen_finiteOpen _).measurableSet)]
  linarith

/-- Computation uses the supplied total-mass name and finite-union enumeration. -/
def massUpperProgram (Q : AlphaTerm) : AlphaTerm :=
  numericalCompose rationalAddTerm (pairNumerical Q rationalDyadicTerm)

def tailGapProgram (P Q : AlphaTerm) : AlphaTerm := numericalCompose rationalDifferenceProgram
  (pairNumerical (massUpperProgram Q) (app lowerMeasureProgram P))

def tailSmallProgram (P Q : AlphaTerm) : AlphaTerm := numericalCompose rationalLessTerm
  (pairNumerical (numericalCompose (tailGapProgram P Q) (numericalProjectionTerm false))
    (numericalCompose rationalDyadicTerm
      (numericalCompose successorTerm (numericalProjectionTerm true))))

def tailStageProgram (P Q : AlphaTerm) : AlphaTerm :=
  numericalResultSearch (tailSmallProgram P Q) numericalIdentity

theorem massUpperProgram_computes {Q : AlphaTerm} {q : ℕ → ℕ} (hq : NumericalComputes Q q) :
    NumericalComputes (massUpperProgram Q) (massUpperCode q) := by
  have h := rationalAdd_computes.comp (hq.pair rationalDyadic_computes)
  change NumericalComputes _ (fun s => ((RationalCode.ofNat (q s)).add (RationalCode.dyadic s)).natCode)
  simpa only [massUpperProgram,massUpperCode,Nat.unpair_pair,RationalCode.ofNat_natCode] using h

theorem tailGapProgram_computes {P Q : AlphaTerm} {p q : ℕ → ℕ}
    (hp : NumericalComputes P p) (hq : NumericalComputes Q q) :
    NumericalComputes (tailGapProgram P Q) (tailGapCode p q) := by
  have h := rationalDifferenceProgram_computes.comp
    ((massUpperProgram_computes hq).pair (lowerMeasureProgram_on_computable hp))
  change NumericalComputes _ (fun s => rationalDifferenceCode (Nat.pair (massUpperCode q s) (lowerMeasureCode p s)))
  simpa only [tailGapProgram,tailGapCode,Nat.unpair_pair] using h

theorem tailSmallProgram_computes {P Q : AlphaTerm} {p q : ℕ → ℕ}
    (hp : NumericalComputes P p) (hq : NumericalComputes Q q) :
    NumericalComputes (tailSmallProgram P Q) (tailSmallBit p q) := by
  have h := rationalLess_computes.comp
    (((tailGapProgram_computes hp hq).comp (projection_computes false)).pair
      (rationalDyadic_computes.comp (successor_computes.comp (projection_computes true))))
  change NumericalComputes _ (fun z => if (RationalCode.ofNat (tailGapCode p q z.unpair.2)).value <
    (RationalCode.dyadic (z.unpair.1+1)).value then 1 else 0)
  simpa only [tailSmallProgram,tailSmallBit,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,
    Nat.succ_eq_add_one,RationalCode.ofNat_natCode] using h

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Finite approximation from computable measure
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    To give the lambda term, let $M$ be the finite-union measure program and $D$ the rational-subtraction program
    used above. Expand the abbreviations inside the abstractions:
    $$\begin{aligned}
    E&:=\lambdaab{m}{\LambdaRationalAdd(\LambdaNumericPair\,(Qm)\,(\LambdaDyadic\,m))},\\
    F&:=\lambdaab{m}{D(\LambdaNumericPair\,(Em)\,(M(\LambdaInputPrefix\,P\,m)))},\\
    T(k,m)&:=\LambdaRationalLess(\LambdaNumericPair\,(Fm)\,(\LambdaDyadic(\LambdaSucc\,k))),\\
    A&:=\lambdaab{k}{\LambdaResultSearch\,
     (\lambdaab{m}{\LambdaZeroTest\,T(k,m)\,\ChurchNumeral{1}\,\ChurchNumeral{0}})\,
     (\lambdaab{m}{m})}.
    \end{aligned}$$
    All tests terminate. The test supplied to $\LambdaResultSearch$ returns zero precisely at a successful stage,
    and its result function returns that stage itself. The finite-prefix, rational-arithmetic, and search reductions
    therefore give $A\ChurchNumeral{k}\to_\beta^*\ChurchNumeral{a(k)}$.
-/
theorem tailStageProgram_computes {P Q : AlphaTerm} {p : ℕ → ℕ}
    (hp : NumericalComputes P p) (hv : ValidOpenName p) (q : realRepresentation.domain)
    (hq : NumericalComputes Q q.val) (he : realRepresentation.toFun q = fairCoinProduct.real (namedOpen p)) :
    ∃ a : ℕ → ℕ, NumericalComputes (tailStageProgram P Q) a ∧
      ∀ k, fairCoinProduct.real (namedOpen p \ stageOpen p (a k)) < (1/2:ℝ)^(k+1) := by
  let a := fun k => Nat.find (tailSmallBit_exists hv q he k)
  refine ⟨a,⟨numericalResultSearch_closed (tailSmallProgram_computes hp hq) numericalIdentity_computes,
    fun k => ?_⟩,fun k => tailSmallBit_error hv q he k (a k) (Nat.find_spec (tailSmallBit_exists hv q he k))⟩
  exact numericalResultSearch_hit (tailSmallProgram_computes hp hq) numericalIdentity_computes
    k (a k) (Nat.find_spec (tailSmallBit_exists hv q he k))
    (fun s hs => not_ne_iff.mp (Nat.find_min (tailSmallBit_exists hv q he k) hs))

/-- Removing a finite approximation changes every local mass by at most the unseen tail. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: corollary
  title: Computable local measures of the complement
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    The same tail estimate controls every cylinder:
    $$0\le G_{L_m}(w)-\mu\bigl(\SetDifference{\cyl{w}}{U_p}\bigr)
    \le\mu\bigl(\SetDifference{U_p}{U_{L_m}}\bigr).$$
    For the first inequality, use inclusion of the remaining sets. For the second, use
    $$\SetDifference{\cyl{w}}{U_{L_m}}\IncludedIn
    \bigl(\SetDifference{\cyl{w}}{U_p}\bigr)\cup
    \bigl(\SetDifference{U_p}{U_{L_m}}\bigr)$$
    and subadditivity. Thus $G_{L_{a(k)}}(w)$ has error less than $2^{-(k+1)}$.
    For $k\le l$, two such rational approximations differ by at most
    $2^{-(k+1)}+2^{-(l+1)}\le2^{-k}$. Hence they form a fast Cauchy name of the asserted measure.
    With $Z,H$ the previously defined fold for $G_L$ and $\pi_i:=\LambdaNumericProjection{i}$, use
    $$C:=\lambdaab{z}{
     ((\LambdaListFold{Z}{H})(\LambdaInputPrefix\,P\,(A(\pi_2z))))(\pi_1z)}.$$
    On input $\NatPair{\LambdaListCode{w}}{k}$, this term returns the required rational code.
    The word and precision both remain inputs, and the stage search is independent of the word.
-/
theorem localMass_tail_bound (p : ℕ → ℕ) (s : ℕ) (C : Set (ℕ → Bool)) :
    dist (fairCoinProduct.real (C \ stageOpen p s)) (fairCoinProduct.real (C \ namedOpen p)) ≤
      fairCoinProduct.real (namedOpen p \ stageOpen p s) := by
  have hl := measureReal_mono (μ := fairCoinProduct) (Set.sdiff_subset_sdiff_right (stageOpen_subset p s))
  have hsub : C \ stageOpen p s ⊆ (C \ namedOpen p) ∪ (namedOpen p \ stageOpen p s) := by
    intro x hx
    by_cases h : x ∈ namedOpen p
    · exact Or.inr ⟨h,hx.2⟩
    · exact Or.inl ⟨hx.1,h⟩
  have hu := (measureReal_mono (μ := fairCoinProduct) hsub).trans (measureReal_union_le _ _)
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith

def localMassCode (p a : ℕ → ℕ) (z : ℕ) : ℕ :=
  avoidCode (seqPrefix p (a z.unpair.2)) z.unpair.1

def localMassProgram (P A : AlphaTerm) : AlphaTerm := numericalCompose remainingProgram
  (pairNumerical (numericalCompose (app prefixProgram P)
    (numericalCompose A (numericalProjectionTerm false))) (numericalProjectionTerm true))

theorem localMassProgram_computes {P A : AlphaTerm} {p a : ℕ → ℕ}
    (hp : NumericalComputes P p) (ha : NumericalComputes A a) :
    NumericalComputes (localMassProgram P A) (localMassCode p a) := by
  have hpre : NumericalComputes (app prefixProgram P) (fun s => NatListCode.encode (seqPrefix p s)) :=
    ⟨closed_app prefixProgram_closed hp.1,
      fun s => (prefixProgram_runs p s).apply_numerical prefixProgram_closed hp⟩
  have h := remainingProgram_computes.comp ((hpre.comp (ha.comp (projection_computes false))).pair
    (projection_computes true))
  change NumericalComputes _ (fun z => avoidCode (seqPrefix p (a z.unpair.2)) z.unpair.1)
  simpa only [localMassProgram,localMassCode,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,
    NatListCode.decode_encode] using h

theorem localMassCode_error {p a : ℕ → ℕ} (hp : ValidOpenName p)
    (ha : ∀ k, fairCoinProduct.real (namedOpen p \ stageOpen p (a k)) < (1/2:ℝ)^(k+1))
    (w : List Bool) (k : ℕ) :
    dist (rationalPoint (localMassCode p a (Nat.pair (encodeWord w) k)))
      (fairCoinProduct.real (cyl w \ namedOpen p)) ≤ (1/2:ℝ)^(k+1) := by
  rw [localMassCode,Nat.unpair_pair,avoidCode_value _ (prefixEntries_valid hp _) _ (binary_encodeWord w),
    decodeWord_encodeWord,finiteOpen_prefix]
  exact (localMass_tail_bound p (a k) (cyl w)).trans (ha k).le

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: corollary
  title: Computable local measures of the complement
-/
theorem computable_local_complement_mass {P Q : AlphaTerm} {p : ℕ → ℕ}
    (hp : NumericalComputes P p) (hv : ValidOpenName p) (q : realRepresentation.domain)
    (hq : NumericalComputes Q q.val) (he : realRepresentation.toFun q = fairCoinProduct.real (namedOpen p)) :
    ∃ A : AlphaTerm, A.Closed ∧ ∀ w : List Bool, ∃ r : realRepresentation.domain,
      realRepresentation.toFun r = fairCoinProduct.real (cyl w \ namedOpen p) ∧
      ∀ k, Relation.ReflTransGen Beta (app A (numeral (Nat.pair (encodeWord w) k))) (numeral (r.val k)) := by
  obtain ⟨a,ha,hb⟩ := tailStageProgram_computes hp hv q hq he
  have hc := localMassProgram_computes hp ha
  refine ⟨localMassProgram P (tailStageProgram P Q),hc.1,fun w => ?_⟩
  let r := fun k => localMassCode p a (Nat.pair (encodeWord w) k)
  have hr := localMassCode_error hv hb w
  exact ⟨⟨r,isCauchyName_of_halfError_le hr⟩,cauchyRepresentation_eq_of_halfError_le r _ hr,
    fun k => hc.2 _⟩

end PolishSpaceBook.LambdaRandomness
