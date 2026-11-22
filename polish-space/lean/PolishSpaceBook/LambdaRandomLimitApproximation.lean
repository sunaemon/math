module

public import PolishSpaceBook.LambdaUniversalRandomnessTest

@[expose] public section

/-! # A computable limit approximation outside a small effectively open set

At each finite stage, greedily retain a child with positive uncovered mass.
Nested finite unions make every fixed prefix eventually stable.
-/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open CantorMeasure CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def remainingMass (L : List ℕ) (w : List Bool) : ℝ :=
  fairCoinProduct.real (cyl w \ finiteOpen L)

def greedyBit (L : List ℕ) (w : List Bool) : Bool :=
  if 0 < (RationalCode.ofNat (avoidCode L (encodeWord (w ++ [false])))).value then false else true

def greedyWord (L : List ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => let w := greedyWord L n; w ++ [greedyBit L w]

def greedyApprox (p : ℕ → ℕ) (s k : ℕ) : Bool :=
  greedyBit (seqPrefix p s) (greedyWord (seqPrefix p s) k)

theorem prefixEntries_valid {p : ℕ → ℕ} (hp : ValidOpenName p) (s : ℕ) :
    ∀ a ∈ seqPrefix p s, ValidEntry a := by
  intro a ha
  simp only [seqPrefix,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  exact hp i

theorem greedyBit_eq {L : List ℕ} (hL : ∀ a ∈ L, ValidEntry a) (w : List Bool) :
    greedyBit L w = if 0 < remainingMass L (w ++ [false]) then false else true := by
  have hv := avoidCode_value L hL (encodeWord (w ++ [false])) (binary_encodeWord _)
  simp only [decodeWord_encodeWord] at hv
  unfold greedyBit remainingMass
  rw [← hv]
  simp only [rationalPoint,Rat.cast_pos]

theorem binary_cylinder_split (w : List Bool) :
    cyl w = cyl (w ++ [false]) ∪ cyl (w ++ [true]) := by
  ext x
  have h (b : Bool) : x ∈ cyl (w ++ [b]) ↔ x ∈ cyl w ∧ x w.length = b := by
    change x ∈ cyl (concat w [b]) ↔ _
    rw [mem_cyl_concat_iff]
    simp [cyl,prefixOfSeq]
  rw [mem_union,h false,h true]
  cases x w.length <;> simp

theorem remainingMass_children (L : List ℕ) (w : List Bool) :
    remainingMass L w ≤ remainingMass L (w ++ [false]) + remainingMass L (w ++ [true]) := by
  dsimp only [remainingMass]
  rw [binary_cylinder_split w,union_sdiff_distrib]
  exact measureReal_union_le _ _

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Computable approximation outside a small open set
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Every chosen prefix has positive uncovered mass. Indeed,
    $G_{L_s}(\emptySeq)=1-\mu(U_{L_s})\ge 1/2$.
    The cylinders $\cyl{w\concat0}$ and $\cyl{w\concat1}$ partition $\cyl{w}$, so
    $$G_{L_s}(w)\le G_{L_s}(w\concat0)+G_{L_s}(w\concat1).$$
    If the parent has positive uncovered mass and the zero-child has none, the one-child has positive mass.
    Induction on $k$ therefore gives $G_{L_s}(w_{s,k})>0$.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    For each fixed $k$, the word $w_{s,k}$ eventually stops changing. This is immediate for $k=0$.
    Suppose the length-$k$ prefix has stabilized to $w$ after stage $N$.
    The finite unions $U_{L_s}$ increase, so $G_{L_s}(w\concat0)$ is nonincreasing in $s$.
    Either it stays positive at all stages $s\ge N$, or it becomes zero and remains zero thereafter.
    Accordingly, the next bit is always zero or eventually always one. This proves stabilization at length $k+1$.
    Let $x(k)$ be the eventual value of $a_s(k)$. No bound on the stabilization stage is claimed.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    If $x\in U_p$, some enumerated cylinder $\cyl{u}$ contains $x$.
    Choose $s$ after that cylinder has been enumerated and after the first $|u|$ bits have stabilized.
    Then $w_{s,|u|}=u$ and $\cyl{u}\IncludedIn U_{L_s}$, contradicting
    $G_{L_s}(w_{s,|u|})>0$. Hence $x\notin U_p$.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Retain the finite-list code as a parameter of the recursion:
    $$\begin{aligned}
    B_0&:=\lambdaab{v}{\ChurchNumeral{0}},\\
    J&:=\lambdaab{v}{\lambdaab{k}{\lambdaab{w}{E(w,B(\LambdaNumericPair\,v\,w))}}},\\
    S&:=\lambdaab{z}{\LambdaParamRec{B_0}{J}\,(\pi_1z)\,(\pi_2z)},\\
    L(z)&:=\LambdaInputPrefix\,P\,(\pi_1z),\\
    A&:=\lambdaab{z}{B\bigl(\LambdaNumericPair\,L(z)\,
     (S(\LambdaNumericPair\,L(z)\,(\pi_2z)))\bigr)}.
    \end{aligned}$$
    Expand the abbreviations inside the abstractions. The list-fold reductions show that $R$ computes $G_L$;
    induction on the recursion depth shows that $S$ returns the code of $w_{s,k}$ when supplied with the code of
    $L_s$ and $k$. Consequently, $A\,\ChurchNumeral{\NatPair{s}{k}}\to_\beta^*\ChurchNumeral{a_s(k)}$.
    All finite-list and rational operations terminate. Neither the approximation nor its program uses a
    stabilization bound or an oracle for the limiting point.
-/
theorem greedyWord_positive {L : List ℕ} (hL : ∀ a ∈ L, ValidEntry a)
    (hroot : 0 < remainingMass L []) (n : ℕ) : 0 < remainingMass L (greedyWord L n) := by
  induction n with
  | zero => exact hroot
  | succ n ih =>
    simp only [greedyWord,greedyBit_eq hL]
    split_ifs with h
    · exact h
    · have hc := remainingMass_children L (greedyWord L n)
      linarith

theorem remainingMass_stage_antitone (p : ℕ → ℕ) (w : List Bool) :
    Antitone (fun s => remainingMass (seqPrefix p s) w) := by
  intro s t hst
  dsimp only [remainingMass]
  rw [finiteOpen_prefix,finiteOpen_prefix]
  exact measureReal_mono (μ := fairCoinProduct) (Set.sdiff_subset_sdiff_right (stageOpen_mono p hst))

theorem greedyWord_length (L : List ℕ) (n : ℕ) : (greedyWord L n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [greedyWord,List.length_append,List.length_singleton] using congrArg (·+1) ih

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Put $L_s:=(p(0),\ldots,p(s-1))$, with $L_0=[]$, and use the uncovered mass $G_L(w)$ from
    §{sec:tte-cantor-open-measure}. Define binary words by
    $$\begin{gathered}
    w_{s,0}:=\emptySeq,\qquad w_{s,k+1}:=w_{s,k}\concat b_s(w_{s,k}),\\
    b_s(w):=\begin{cases}
    0,&G_{L_s}(w\concat0)>0,\\
    1,&G_{L_s}(w\concat0)=0.
    \end{cases}
    \end{gathered}$$
    Here $G_{L_s}$ takes nonnegative rational values, so the two cases are exhaustive and decidable.
    Set $a_s(k):=b_s(w_{s,k})$. Then $\restrict{a_s}{k}=w_{s,k}$.
-/
theorem greedyApprox_prefix (p : ℕ → ℕ) (s n : ℕ) :
    seqPrefix (greedyApprox p s) n = greedyWord (seqPrefix p s) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [seqPrefix_succ_eq_concat,ih]; rfl

/-- Once a prefix has settled, its zero-child can lose all remaining mass at most once. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Computable approximation outside a small open set
-/
theorem greedyWord_eventually {p : ℕ → ℕ} (hp : ValidOpenName p) (n : ℕ) :
    ∃ w : List Bool, ∃ N, ∀ s ≥ N, greedyWord (seqPrefix p s) n = w := by
  classical
  induction n with
  | zero => exact ⟨[],0,fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨w,N,hN⟩ := ih
    by_cases hpos : ∀ s ≥ N, 0 < remainingMass (seqPrefix p s) (w ++ [false])
    · refine ⟨w ++ [false],N,fun s hs => ?_⟩
      simp only [greedyWord,hN s hs,greedyBit_eq (prefixEntries_valid hp s),ite_eq_left (hpos s hs)]
    · push Not at hpos
      obtain ⟨M,hMN,hM⟩ := hpos
      refine ⟨w ++ [true],M,fun s hs => ?_⟩
      have hh := (remainingMass_stage_antitone p (w ++ [false]) hs).trans hM
      simp only [greedyWord,hN s (hMN.trans hs),greedyBit_eq (prefixEntries_valid hp s),
        ite_eq_right (not_lt_of_ge hh)]

theorem greedyApprox_eventually {p : ℕ → ℕ} (hp : ValidOpenName p) (k : ℕ) :
    ∃ b : Bool, ∃ N, ∀ s ≥ N, greedyApprox p s k = b := by
  obtain ⟨w,N,hN⟩ := greedyWord_eventually hp (k+1)
  refine ⟨w.getD k false,N,fun s hs => ?_⟩
  have he := congrArg (fun v : List Bool => v.getD k false) (hN s hs)
  rw [← greedyApprox_prefix] at he
  have hk : k < (seqPrefix (greedyApprox p s) (k+1)).length := by simp
  change ((seqPrefix (greedyApprox p s) (k+1))[k]?).getD false = w.getD k false at he
  rw [List.getElem?_eq_getElem hk] at he
  simpa only [Option.getD_some,seqPrefix,List.getElem_ofFn] using he

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Computable approximation outside a small open set
-/
theorem exists_greedy_limit {p : ℕ → ℕ} (hp : ValidOpenName p) :
    ∃ x, Approximates (greedyApprox p) x := by
  classical
  let x := fun k => Classical.choose (greedyApprox_eventually hp k)
  exact ⟨x,fun k => Classical.choose_spec (greedyApprox_eventually hp k)⟩

theorem remainingMass_root_positive {p : ℕ → ℕ}
    (hb : fairCoinProduct.real (namedOpen p) ≤ (1/2:ℝ)) (s : ℕ) :
    0 < remainingMass (seqPrefix p s) [] := by
  have hsub : stageOpen p s ⊆ namedOpen p := by
    rw [← iUnion_stageOpen]
    exact subset_iUnion (stageOpen p) s
  have hm := (measureReal_mono (μ := fairCoinProduct) hsub).trans hb
  dsimp only [remainingMass]
  rw [cyl_nil,← Set.compl_eq_univ_sdiff,measureReal_compl (isOpen_finiteOpen _).measurableSet,probReal_univ,
    finiteOpen_prefix]
  linarith

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Computable approximation outside a small open set
-/
theorem greedy_limit_outside {p : ℕ → ℕ} {x : ℕ → Bool} (hp : ValidOpenName p)
    (hb : fairCoinProduct.real (namedOpen p) ≤ (1/2:ℝ))
    (hx : Approximates (greedyApprox p) x) : x ∉ namedOpen p := by
  intro h
  obtain ⟨j,hj⟩ := mem_iUnion.mp h
  by_cases hz : p j = 0
  · simp [entrySet,hz] at hj
  let w := decodeWord (p j-1)
  have hxw : x ∈ cyl w := by simpa only [entrySet,ite_eq_right hz] using hj
  obtain ⟨N,hN⟩ := hx.prefix_stable w.length
  let s := max N (j+1)
  have hNs : N ≤ s := le_max_left _ _
  have hjs : j < s := lt_of_lt_of_le (by omega) (le_max_right _ _)
  have he : seqPrefix (greedyApprox p s) w.length = seqPrefix x w.length := by
    unfold seqPrefix
    congr 1
    funext i
    exact hN s hNs i.val i.isLt
  rw [greedyApprox_prefix,seqPrefix_eq_of_mem_cyl hxw] at he
  have hsub : cyl w ⊆ finiteOpen (seqPrefix p s) := by
    rw [finiteOpen_prefix]
    intro y hy
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hjs,by simpa only [entrySet,ite_eq_right hz] using hy⟩⟩
  have hpos := greedyWord_positive (prefixEntries_valid hp s) (remainingMass_root_positive hb s) w.length
  rw [he] at hpos
  have he0 : remainingMass (seqPrefix p s) w = 0 := by
    rw [remainingMass,Set.sdiff_eq_empty.mpr hsub,measureReal_empty]
  linarith

/-- The finite-list fold computes an uncovered mass at any supplied word code. -/
def remainingProgram : AlphaTerm := uncurryNumerical finiteAvoidFold

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Computable approximation outside a small open set
-/
theorem remainingProgram_computes : NumericalComputes remainingProgram
    (fun z => avoidCode (NatListCode.decode z.unpair.1) z.unpair.2) := by
  have hc : finiteAvoidFold.Closed := listFold_closed (avoidProgram_computes []).1 avoidHandler_closed
  unfold remainingProgram
  apply uncurryNumerical_computes hc (fun l w => avoidCode (NatListCode.decode l) w)
  intro l w
  have hs := finiteAvoidFold_apply (NatListCode.decode l)
  simp only [NatListCode.encode_decode] at hs
  exact (beta_steps_app_left hs (numeral w)).trans ((avoidProgram_computes _).2 w)

def snocCode (b : Bool) (e : ℕ) : ℕ := NatListCode.encode (NatListCode.decode e ++ [b.toNat])

def snocProgram (b : Bool) : AlphaTerm := numericalCombine listAppendTerm numericalIdentity
  (numericalConstant (NatListCode.encode [b.toNat]))

theorem snocProgram_computes (b : Bool) : NumericalComputes (snocProgram b) (snocCode b) := by
  have h := numericalIdentity_computes.combine (numericalConstant_computes (NatListCode.encode [b.toNat]))
    listAppendTerm_closed (fun a d => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode d))
    listAppendTerm_apply
  change NumericalComputes _ (fun e => NatListCode.encode (NatListCode.decode e ++ [b.toNat]))
  simpa only [snocProgram,id_eq,NatListCode.decode_encode] using h

theorem snocCode_word (b : Bool) (w : List Bool) : snocCode b (encodeWord w) = encodeWord (w ++ [b]) := by
  simp [snocCode,encodeWord]

def greedyTestProgram : AlphaTerm := numericalCompose rationalLessTerm
  (pairNumerical (numericalConstant 0) (numericalCompose remainingProgram
    (pairNumerical (numericalProjectionTerm true)
      (numericalCompose (snocProgram false) (numericalProjectionTerm false)))))

def greedyBitCode (z : ℕ) : ℕ :=
  if 0 < (RationalCode.ofNat (avoidCode (NatListCode.decode z.unpair.1) (snocCode false z.unpair.2))).value
    then 0 else 1

def greedyBitProgram : AlphaTerm := numericalIfZero greedyTestProgram (numericalConstant 1) (numericalConstant 0)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    For completeness, the bit calculation can be written as a closed lambda term. Let $P$ compute $p$,
    and let $Z,H$ be the list-fold seed and handler for $G_L$ in §{sec:tte-cantor-open-measure}.
    Write $\pi_i:=\LambdaNumericProjection{i}$. In the following abbreviations, $v,w$ are list and word codes,
    and $b$ is a bit numeral:
    $$\begin{aligned}
    R&:=\lambdaab{z}{((\LambdaListFold{Z}{H})(\pi_1z))(\pi_2z)},\\
    E(w,b)&:=\LambdaListAppend\,w\,(\LambdaListCons\,b\,\ChurchNumeral{0}),\\
    T(v,w)&:=\LambdaRationalLess\bigl(\LambdaNumericPair\,\ChurchNumeral{0}\,
     (R(\LambdaNumericPair\,v\,E(w,\ChurchNumeral{0})))\bigr),\\
    B&:=\lambdaab{z}{\LambdaZeroTest\,T(\pi_1z,\pi_2z)\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    The rational code zero denotes zero, and the strict comparison returns one for a positive mass.
    Thus $B$ returns precisely the selected bit.
-/
theorem greedyBitProgram_computes : NumericalComputes greedyBitProgram greedyBitCode := by
  have hm := remainingProgram_computes.comp ((projection_computes true).pair
    ((snocProgram_computes false).comp (projection_computes false)))
  have ht := rationalLess_computes.comp ((numericalConstant_computes 0).pair hm)
  have h := numericalIfZero_computes ht (numericalConstant_computes 1) (numericalConstant_computes 0)
  unfold greedyBitProgram greedyTestProgram
  convert h using 1
  funext z
  simp only [Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false]
  have hz : (RationalCode.ofNat 0).value = 0 := by norm_num [RationalCode.ofNat,RationalCode.value]
  simp only [greedyBitCode,hz]
  split_ifs <;> simp_all

theorem greedyBitCode_word (l : ℕ) (w : List Bool) :
    greedyBitCode (Nat.pair l (encodeWord w)) = (greedyBit (NatListCode.decode l) w).toNat := by
  simp only [greedyBitCode,Nat.unpair_pair,snocCode_word,greedyBit]
  split_ifs <;> rfl

/-- Input (list,(depth,word)); retain the list throughout the recursion. -/
def greedyStepProgram : AlphaTerm :=
  let L := numericalProjectionTerm true
  let R := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  numericalCombine listAppendTerm R (numericalCombine listConsTerm
    (numericalCompose greedyBitProgram (pairNumerical L R)) (numericalConstant 0))

def greedyStepCode (z : ℕ) : ℕ := NatListCode.encode (NatListCode.decode z.unpair.2.unpair.2 ++
  [greedyBitCode (Nat.pair z.unpair.1 z.unpair.2.unpair.2)])

theorem greedyStepProgram_computes : NumericalComputes greedyStepProgram greedyStepCode := by
  have hl := projection_computes true
  have hr := (projection_computes false).comp (projection_computes false)
  have hb := greedyBitProgram_computes.comp (hl.pair hr)
  have hs := hb.combine (numericalConstant_computes 0) listConsTerm_closed
    (fun a d => Nat.pair a d+1) listConsTerm_apply
  have h := hr.combine hs listAppendTerm_closed
    (fun a d => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode d)) listAppendTerm_apply
  unfold greedyStepProgram
  convert h using 1
  funext z
  simp [greedyStepCode,NatListCode.decode]

def greedyStateProgram : AlphaTerm := numericalRecursion (numericalConstant 0) greedyStepProgram

theorem greedyRecursion_eq (l n : ℕ) :
    primitiveRec 0 (fun k r => greedyStepCode (Nat.pair l (Nat.pair k r))) n =
      encodeWord (greedyWord (NatListCode.decode l) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [primitiveRec,ih]
    simp only [greedyStepCode,Nat.unpair_pair]
    rw [greedyBitCode_word]
    simp only [encodeWord,NatListCode.decode_encode,greedyWord,List.map_append,List.map_cons,List.map_nil]

theorem greedyStateProgram_computes : NumericalComputes greedyStateProgram
    (fun z => encodeWord (greedyWord (NatListCode.decode z.unpair.1) z.unpair.2)) := by
  simpa only [greedyStateProgram,greedyRecursion_eq] using
    numericalRecursion_computes (numericalConstant_computes 0) greedyStepProgram_computes

/-- Stage and requested bit remain inputs; no stabilization bound is used. -/
def greedyApproxProgram (P : AlphaTerm) : AlphaTerm :=
  let L := numericalCompose (app prefixProgram P) (numericalProjectionTerm true)
  numericalCompose greedyBitProgram (pairNumerical L (numericalCompose greedyStateProgram
    (pairNumerical L (numericalProjectionTerm false))))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: proposition
  title: Computable approximation outside a small open set
-/
theorem greedyApproxProgram_computes {P : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes P p) :
    NumericalComputes (greedyApproxProgram P) (fun z => (greedyApprox p z.unpair.1 z.unpair.2).toNat) := by
  have hpre : NumericalComputes (app prefixProgram P) (fun s => NatListCode.encode (seqPrefix p s)) :=
    ⟨closed_app prefixProgram_closed hp.1,
      fun s => (prefixProgram_runs p s).apply_numerical prefixProgram_closed hp⟩
  have hl := hpre.comp (projection_computes true)
  have hw := greedyStateProgram_computes.comp (hl.pair (projection_computes false))
  have h := greedyBitProgram_computes.comp (hl.pair hw)
  simpa only [greedyApproxProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,
    greedyBitCode_word,NatListCode.decode_encode,greedyApprox] using h

/-- An actual computable approximation supplies a non-weakly-2-random random point. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Martin-Löf versus weak 2-randomness
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Apply the preceding proposition to $U_p=V_1$ from the universal test, whose measure is at most $1/2$.
    If $V$ is the universal enumeration program, a program for $p$ is
    $$P:=\lambdaab{s}{V(\LambdaNumericPair\,\ChurchNumeral{1}\,s)}.$$
    It gives a point $x\notin V_1$ and a uniformly computable approximation to its bits. The point is Martin-Löf
    random by the positive-closed-class corollary. The null test for a computable limit approximation constructed
    above covers $x$, so $x$ is not weakly 2-random.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Start with Cantor space and the fair-coin measure $\mu$. A
    \termdefineas{Martin-Lof test}{Martin-Löf test} [@MartinLof1966] is a uniformly effectively open sequence
    $\Sequence{U_n}{n\in\omega}$ such that
    $$\mu(U_n)\le 2^{-n}.$$
    A real $x\in\CantorSpace$ is \termdefineas{Martin-Lof randomness}{Martin-Löf random} if
    $$x\notin\bigcap_n U_n$$
    for every Martin-Löf test $\Sequence{U_n}{n\in\omega}$. Equivalently, $x$ lies outside the intersection of every
    uniformly effectively open
    sequence whose measures shrink at the prescribed computable rate $\mu(U_n)\le 2^{-n}$. Dropping that rate and requiring
    avoidance of every effectively presented null $G_\delta$ set instead gives the strictly stronger notion of
    \termdefine{weak 2-randomness}. Thus Martin-Löf randomness is the rate-bounded effective analogue of the forcing
    slogan "the random real avoids every old null set"; it does not quantify over all effective null $G_\delta$ codes.
-/
theorem exists_mlRandom_not_weakTwoRandom : ∃ x : ℕ → Bool, MLRandom x ∧ ¬ W2Random x := by
  let p := fun s => universalEntry (Nat.pair 1 s)
  let P := numericalCompose universalProgram (pairNumerical (numericalConstant 1) numericalIdentity)
  have hp : NumericalComputes P p :=
    universalProgram_computes.comp ((numericalConstant_computes 1).pair numericalIdentity_computes)
  have hv : ValidOpenName p := universalEntry_valid 1
  have hb : fairCoinProduct.real (namedOpen p) ≤ (1/2:ℝ) := by
    have h := universalOpen_bound 1
    rw [universalEntry_names 1] at h
    simpa only [pow_one] using h
  obtain ⟨x,hx⟩ := exists_greedy_limit hv
  have hout := greedy_limit_outside hv hb hx
  have hml : MLRandom x := outside_universal_one_random (by rw [universalEntry_names 1]; exact hout)
  exact ⟨x,hml,not_weakTwoRandom_of_approximation (greedyApproxProgram_computes hp) hx⟩

end PolishSpaceBook.LambdaRandomness
