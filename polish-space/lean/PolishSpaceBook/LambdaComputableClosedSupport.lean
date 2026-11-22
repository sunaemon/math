module

public import PolishSpaceBook.LambdaComputableOpenApproximation

@[expose] public section

/-! # A computable support point in a closed set of positive computable measure
At depth k preserve mass at least 2^(-m-2k). An approximation with error
at most one eighth of that threshold decides which child to retain.
-/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory Metric NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open CantorMeasure CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def closedMass (p : ℕ → ℕ) (w : List Bool) : ℝ :=
  fairCoinProduct.real (cyl w \ namedOpen p)

def supportBit (p a : ℕ → ℕ) (m k : ℕ) (w : List Bool) : Bool :=
  decide ((RationalCode.ofNat (localMassCode p a
    (Nat.pair (encodeWord (w ++ [false])) (m+2*k+2)))).value < (RationalCode.dyadic (m+2*k+1)).value)

def supportWord (p a : ℕ → ℕ) (m : ℕ) : ℕ → List Bool
  | 0 => []
  | k+1 => let w := supportWord p a m k; w ++ [supportBit p a m k w]

def supportPoint (p a : ℕ → ℕ) (m k : ℕ) : Bool :=
  supportBit p a m k (supportWord p a m k)

theorem supportPoint_prefix (p a : ℕ → ℕ) (m k : ℕ) :
    seqPrefix (supportPoint p a m) k = supportWord p a m k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [seqPrefix_succ_eq_concat,ih]; rfl

theorem closedMass_children (p : ℕ → ℕ) (w : List Bool) :
    closedMass p w ≤ closedMass p (w ++ [false]) + closedMass p (w ++ [true]) := by
  dsimp only [closedMass]
  rw [binary_cylinder_split w,union_sdiff_distrib]
  exact measureReal_union_le _ _

theorem supportBit_eq (p a : ℕ → ℕ) (m k : ℕ) (w : List Bool) :
    supportBit p a m k w = decide (rationalPoint (localMassCode p a
      (Nat.pair (encodeWord (w ++ [false])) (m+2*k+2))) < (1/2:ℝ)^(m+2*k+1)) := by
  unfold supportBit
  congr 1
  rw [← rationalPoint_dyadic]
  simp only [rationalPoint,RationalCode.ofNat_natCode,Rat.cast_lt]

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Write $U_p:=\SetDifference{\CantorSpace}{K}$. Its measure is computable by subtraction from one.
    Choose $m$ as in the statement and set $t_k:=2^{-(m+2k)}$.
    We construct words $w_k$ of length $k$, starting with $w_0:=\emptySeq$, and maintain
    $$\mu(K\cap\cyl{w_k})\ge t_k.$$
    Use the local-measure program of §{sec:tte-cantor-open-measure} at the word $w_k\concat0$ and precision
    $m+2k+2$. Its rational output value $r_k$ satisfies
    $$|r_k-\mu(K\cap\cyl{w_k\concat0})|\le t_k/8.$$
    Choose
    $$b_k:=\begin{cases}0,&r_k\ge t_k/2,\\1,&r_k<t_k/2,\end{cases}
    \qquad w_{k+1}:=w_k\concat b_k.$$
    In the first case the chosen child's mass is at least $3t_k/8$.
    In the second, the zero-child's mass is less than $5t_k/8$, so the other child's mass is greater than
    $3t_k/8$. Both bounds imply the next invariant because $t_{k+1}=t_k/4$.
    The initial invariant follows from $\mu(K)\ge2^{-m}$.
-/
theorem support_step_mass {p a : ℕ → ℕ} (hv : ValidOpenName p)
    (ha : ∀ k, fairCoinProduct.real (namedOpen p \ stageOpen p (a k)) < (1/2:ℝ)^(k+1))
    (m k : ℕ) (w : List Bool) (hw : (1/2:ℝ)^(m+2*k) ≤ closedMass p w) :
    (1/2:ℝ)^(m+2*(k+1)) ≤ closedMass p (w ++ [supportBit p a m k w]) := by
  have he := localMassCode_error hv ha (w ++ [false]) (m+2*k+2)
  change dist _ (closedMass p (w ++ [false])) ≤ _ at he
  rw [Real.dist_eq,abs_le] at he
  have h0 : (1/2:ℝ)^(m+2*k+1) = (1/2:ℝ)^(m+2*k)/2 := by rw [pow_add]; norm_num; ring
  have h1 : (1/2:ℝ)^(m+2*k+2+1) = (1/2:ℝ)^(m+2*k)/8 := by
    rw [show m+2*k+2+1 = m+2*k+3 by omega,pow_add]; norm_num; ring
  have h2 : (1/2:ℝ)^(m+2*(k+1)) = (1/2:ℝ)^(m+2*k)/4 := by
    rw [show m+2*(k+1) = m+2*k+2 by omega,pow_add]; norm_num; ring
  rw [h1] at he
  rw [supportBit_eq,h2]
  by_cases hh : rationalPoint (localMassCode p a
      (Nat.pair (encodeWord (w ++ [false])) (m+2*k+2))) < (1/2:ℝ)^(m+2*k+1)
  · rw [decide_eq_true hh]
    rw [h0] at hh
    have hc := closedMass_children p w
    have ht : 0 < (1/2:ℝ)^(m+2*k) := by positivity
    linarith [he.1]
  · rw [decide_eq_false hh]
    rw [h0] at hh
    have ht : 0 < (1/2:ℝ)^(m+2*k) := by positivity
    linarith [he.2]

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: A computable point with positive local mass
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Define $x(k):=b_k$, so $\restrict{x}{k}=w_k$. Every such cylinder meets $K$ in positive measure.
    If $x\notin K$, openness of $U_p$ supplies a prefix cylinder of $x$ contained in $U_p$, contradicting
    that positive measure. Thus $x\in K$. The construction computes each bit after finitely many exact rational
    operations and terminating stage searches; it never waits for equality of an unknown real to zero.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Here are the terms. Let $C$ compute the local mass names, with input consisting of a word code and a
    precision. In the following abbreviations, $m,k,w,b$ denote numerals for the lower-bound exponent, depth,
    word code, and bit:
    $$\begin{aligned}
    E(w,b)&:=\LambdaListAppend\,w\,(\LambdaListCons\,b\,\ChurchNumeral{0}),\\
    N(m,k)&:=\LambdaSucc(\LambdaAdd\,m\,(\LambdaAdd\,k\,k)),\\
    T(m,k,w)&:=\LambdaRationalLess\bigl(\LambdaNumericPair\,
     (C(\LambdaNumericPair\,E(w,\ChurchNumeral{0})\,(\LambdaSucc\,N(m,k))))\,
     (\LambdaDyadic\,N(m,k))\bigr).
    \end{aligned}$$
    The strict comparison directly returns the bit $b_k$: one selects the one-child, and zero the zero-child.
    To iterate while keeping $m$ as a parameter, set
    $$\begin{aligned}
    B_0&:=\lambdaab{m}{\ChurchNumeral{0}},\\
    J&:=\lambdaab{m}{\lambdaab{k}{\lambdaab{w}{E(w,T(m,k,w))}}},\\
    S&:=\lambdaab{z}{\LambdaParamRec{B_0}{J}\,(\pi_1z)\,(\pi_2z)},\\
    X_m&:=\lambdaab{k}{T(\ChurchNumeral{m},k,S(\LambdaNumericPair\,\ChurchNumeral{m}\,k))}.
    \end{aligned}$$
    Here $\pi_i:=\LambdaNumericProjection{i}$, and all abbreviations are expanded inside the abstractions.
    Induction on $k$ using the parameterized-recursion reductions shows that $S$ returns the code of $w_k$.
    Therefore $X_m\ChurchNumeral{k}\to_\beta^*\ChurchNumeral{x(k)}$. Positivity of $\mu(K)$ guarantees that some
    integer $m$ satisfies the initial bound; once it is fixed, every subsequent step is computed by these terms.
-/
theorem supportWord_mass {p a : ℕ → ℕ} (hv : ValidOpenName p)
    (ha : ∀ k, fairCoinProduct.real (namedOpen p \ stageOpen p (a k)) < (1/2:ℝ)^(k+1))
    (m : ℕ) (hm : (1/2:ℝ)^m ≤ closedMass p []) (k : ℕ) :
    (1/2:ℝ)^(m+2*k) ≤ closedMass p (supportWord p a m k) := by
  induction k with
  | zero => simpa [supportWord] using hm
  | succ k ih => exact support_step_mass hv ha m k _ ih

theorem supportPoint_positive {p a : ℕ → ℕ} (hv : ValidOpenName p)
    (ha : ∀ k, fairCoinProduct.real (namedOpen p \ stageOpen p (a k)) < (1/2:ℝ)^(k+1))
    (m : ℕ) (hm : (1/2:ℝ)^m ≤ closedMass p []) (k : ℕ) :
    0 < closedMass p (seqPrefix (supportPoint p a m) k) := by
  rw [supportPoint_prefix]
  exact lt_of_lt_of_le (by positivity) (supportWord_mass hv ha m hm k)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: A computable point with positive local mass
-/
theorem supportPoint_outside {p a : ℕ → ℕ} (hv : ValidOpenName p)
    (ha : ∀ k, fairCoinProduct.real (namedOpen p \ stageOpen p (a k)) < (1/2:ℝ)^(k+1))
    (m : ℕ) (hm : (1/2:ℝ)^m ≤ closedMass p []) : supportPoint p a m ∉ namedOpen p := by
  intro hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp hx
  by_cases hz : p j = 0
  · simp [entrySet,hz] at hj
  let w := decodeWord (p j-1)
  have hxw : supportPoint p a m ∈ cyl w := by simpa only [entrySet,ite_eq_right hz] using hj
  have hsub : cyl w ⊆ namedOpen p := by
    intro y hy
    exact mem_iUnion.mpr ⟨j,by simpa only [entrySet,ite_eq_right hz] using hy⟩
  have hpos := supportPoint_positive hv ha m hm w.length
  rw [seqPrefix_eq_of_mem_cyl hxw,closedMass,Set.sdiff_eq_empty.mpr hsub,measureReal_empty] at hpos
  linarith

def supportBitCode (f : ℕ → ℕ) (z : ℕ) : ℕ :=
  if (RationalCode.ofNat (f (Nat.pair (snocCode false z.unpair.2.unpair.2)
    (z.unpair.1+2*z.unpair.2.unpair.1+2)))).value <
    (RationalCode.dyadic (z.unpair.1+2*z.unpair.2.unpair.1+1)).value then 1 else 0

def supportBitProgram (F : AlphaTerm) : AlphaTerm :=
  let M := numericalProjectionTerm true
  let K := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let W := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  let N := numericalCompose successorTerm (addNumerical M (addNumerical K K))
  numericalCompose rationalLessTerm (pairNumerical
    (numericalCompose F (pairNumerical (numericalCompose (snocProgram false) W)
      (numericalCompose successorTerm N))) (numericalCompose rationalDyadicTerm N))

theorem supportBitProgram_computes {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) :
    NumericalComputes (supportBitProgram F) (supportBitCode f) := by
  have hm := projection_computes true
  have hk := (projection_computes true).comp (projection_computes false)
  have hw := (projection_computes false).comp (projection_computes false)
  have hn := successor_computes.comp (hm.add (hk.add hk))
  have hq := hf.comp (((snocProgram_computes false).comp hw).pair (successor_computes.comp hn))
  have h := rationalLess_computes.comp (hq.pair (rationalDyadic_computes.comp hn))
  change NumericalComputes _ (fun z => if (RationalCode.ofNat (f
    (Nat.pair (snocCode false z.unpair.2.unpair.2) (z.unpair.1+2*z.unpair.2.unpair.1+2)))).value <
      (RationalCode.dyadic (z.unpair.1+2*z.unpair.2.unpair.1+1)).value then 1 else 0)
  simpa only [supportBitProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,
    RationalCode.ofNat_natCode,Nat.succ_eq_add_one,two_mul,Nat.add_assoc] using h

theorem supportBitCode_word (p a : ℕ → ℕ) (m k : ℕ) (w : List Bool) :
    supportBitCode (localMassCode p a) (Nat.pair m (Nat.pair k (encodeWord w))) =
      (supportBit p a m k w).toNat := by
  simp only [supportBitCode,Nat.unpair_pair,snocCode_word,supportBit]
  split_ifs with h <;> simp only [h,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false]

def supportStepCode (f : ℕ → ℕ) (z : ℕ) : ℕ :=
  NatListCode.encode (NatListCode.decode z.unpair.2.unpair.2 ++ [supportBitCode f z])

def supportStepProgram (F : AlphaTerm) : AlphaTerm :=
  numericalCombine listAppendTerm
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
    (numericalCombine listConsTerm (supportBitProgram F) (numericalConstant 0))

theorem supportStepProgram_computes {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) :
    NumericalComputes (supportStepProgram F) (supportStepCode f) := by
  have hw := (projection_computes false).comp (projection_computes false)
  have hb := (supportBitProgram_computes hf).combine (numericalConstant_computes 0)
    listConsTerm_closed (fun a d => Nat.pair a d+1) listConsTerm_apply
  have h := hw.combine hb listAppendTerm_closed
    (fun a d => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode d)) listAppendTerm_apply
  change NumericalComputes _ (fun z => NatListCode.encode
    (NatListCode.decode z.unpair.2.unpair.2 ++ [supportBitCode f z]))
  simpa only [supportStepProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,
    NatListCode.decode,Nat.add_sub_cancel,Nat.unpair_zero] using h

def supportStateProgram (F : AlphaTerm) : AlphaTerm :=
  numericalRecursion (numericalConstant 0) (supportStepProgram F)

theorem supportRecursion_eq (p a : ℕ → ℕ) (m n : ℕ) :
    primitiveRec 0 (fun k r => supportStepCode (localMassCode p a) (Nat.pair m (Nat.pair k r))) n =
      encodeWord (supportWord p a m n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [primitiveRec,ih]
    simp only [supportStepCode,Nat.unpair_pair]
    rw [supportBitCode_word]
    simp only [encodeWord,NatListCode.decode_encode,supportWord,List.map_append,List.map_cons,List.map_nil]

theorem supportStateProgram_computes {F : AlphaTerm} {p a : ℕ → ℕ}
    (hf : NumericalComputes F (localMassCode p a)) :
    NumericalComputes (supportStateProgram F)
      (fun z => encodeWord (supportWord p a z.unpair.1 z.unpair.2)) := by
  simpa only [supportStateProgram,supportRecursion_eq] using
    numericalRecursion_computes (numericalConstant_computes 0) (supportStepProgram_computes hf)

def supportPointProgram (F : AlphaTerm) (m : ℕ) : AlphaTerm := numericalCompose (supportBitProgram F)
  (pairNumerical (numericalConstant m) (pairNumerical numericalIdentity
    (numericalCompose (supportStateProgram F) (pairNumerical (numericalConstant m) numericalIdentity))))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: A computable point with positive local mass
-/
theorem supportPointProgram_computes {F : AlphaTerm} {p a : ℕ → ℕ}
    (hf : NumericalComputes F (localMassCode p a)) (m : ℕ) :
    NumericalComputes (supportPointProgram F m) (fun k => (supportPoint p a m k).toNat) := by
  have hw := (supportStateProgram_computes hf).comp ((numericalConstant_computes m).pair numericalIdentity_computes)
  have h := (supportBitProgram_computes hf).comp
    ((numericalConstant_computes m).pair (numericalIdentity_computes.pair hw))
  simpa only [supportPointProgram,Nat.unpair_pair,id_eq,supportBitCode_word,supportPoint] using h

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: A computable point with positive local mass
-/
theorem exists_computable_closed_support {P Q : AlphaTerm} {p : ℕ → ℕ}
    (hp : NumericalComputes P p) (hv : ValidOpenName p) (q : realRepresentation.domain)
    (hq : NumericalComputes Q q.val) (he : realRepresentation.toFun q = fairCoinProduct.real (namedOpen p))
    (hpos : 0 < fairCoinProduct.real (namedOpen p)ᶜ) :
    ∃ X : AlphaTerm, ∃ x : ℕ → Bool, NumericalComputes X (fun k => (x k).toNat) ∧
      x ∉ namedOpen p ∧ ∀ k, 0 < fairCoinProduct.real (cyl (seqPrefix x k) \ namedOpen p) := by
  obtain ⟨a,ha,hb⟩ := tailStageProgram_computes hp hv q hq he
  have hc := localMassProgram_computes hp ha
  have ht : Tendsto (fun m => (1/2:ℝ)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨m,hm⟩ := (ht.eventually (eventually_lt_nhds hpos)).exists
  have hm' : (1/2:ℝ)^m ≤ closedMass p [] := by
    simpa only [closedMass,cyl_nil,← Set.compl_eq_univ_sdiff] using hm.le
  exact ⟨supportPointProgram (localMassProgram P (tailStageProgram P Q)) m,supportPoint p a m,
    supportPointProgram_computes hc m,supportPoint_outside hv hb m hm',supportPoint_positive hv hb m hm'⟩

/-- Every particular Schnorr test is passed by a computable point. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: No universal Schnorr test
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Let $\Sequence{U_n}{n\in\omega}$ be a Schnorr test. Then $K:=\SetDifference{\CantorSpace}{U_1}$ is effectively closed
    with
    computable measure at least $1/2$. If $P,Q$ compute the uniform open table and the uniform measure names,
    respectively, specialize them by
    $$P_1:=\lambdaab{s}{P(\LambdaNumericPair\,\ChurchNumeral{1}\,s)},\qquad
    Q_1:=\lambdaab{k}{Q(\LambdaNumericPair\,\ChurchNumeral{1}\,k)}.$$
    Apply the theorem with these programs and $m=1$. The resulting computable point is outside $U_1$,
    so it passes this test. It is not Schnorr random, by the earlier corollary about computable points.
    Thus this particular test cannot cover all points failing some Schnorr test.
-/
theorem SchnorrTest.computable_point_passes {U : ℕ → Set (ℕ → Bool)} (hU : SchnorrTest U) :
    ∃ X : AlphaTerm, ∃ x : ℕ → Bool, NumericalComputes X (fun k => (x k).toNat) ∧ AvoidsTest x U := by
  obtain ⟨P,p,hp,hv,hn⟩ := hU.1.1
  obtain ⟨Q,q,hq,hm⟩ := hU.2
  let p1 := fun s => p (Nat.pair 1 s)
  have hp1 : NumericalComputes
      (numericalCompose P (pairNumerical (numericalConstant 1) numericalIdentity)) p1 :=
    hp.comp ((numericalConstant_computes 1).pair numericalIdentity_computes)
  have hq1 : NumericalComputes
      (numericalCompose Q (pairNumerical (numericalConstant 1) numericalIdentity)) (q 1).val := by
    simpa only [Nat.unpair_pair,id_eq] using
      hq.comp ((numericalConstant_computes 1).pair numericalIdentity_computes)
  have he : realRepresentation.toFun (q 1) = fairCoinProduct.real (namedOpen p1) := by rw [hm,hn 1]
  have hb : fairCoinProduct.real (namedOpen p1) ≤ (1/2:ℝ) := by
    simpa only [hn 1,pow_one] using hU.1.2 1
  have hroot : (1/2:ℝ)^1 ≤ closedMass p1 [] := by
    rw [closedMass,cyl_nil,← Set.compl_eq_univ_sdiff,
      measureReal_compl (isOpen_namedOpen p1).measurableSet,probReal_univ,pow_one]
    linarith
  obtain ⟨a,ha,ht⟩ := tailStageProgram_computes hp1 (hv 1) (q 1) hq1 he
  have hc := localMassProgram_computes hp1 ha
  refine ⟨_,supportPoint p1 a 1,supportPointProgram_computes hc 1,fun hi => ?_⟩
  apply supportPoint_outside (hv 1) ht 1 hroot
  rw [← hn 1]
  exact mem_iInter.mp hi 1

/-- No Schnorr test covers all points that fail some Schnorr test. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: No universal Schnorr test
-/
theorem no_universal_schnorr_test (U : ℕ → Set (ℕ → Bool)) (hU : SchnorrTest U) :
    ∃ x : ℕ → Bool, ¬ SchnorrRandom x ∧ AvoidsTest x U := by
  obtain ⟨_,x,hx,hpass⟩ := hU.computable_point_passes
  exact ⟨x,not_schnorrRandom_of_computable hx,hpass⟩

end PolishSpaceBook.LambdaRandomness
