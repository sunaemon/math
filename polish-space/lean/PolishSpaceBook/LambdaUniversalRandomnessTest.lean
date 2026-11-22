module

public import PolishSpaceBook.LambdaBoundedOpenTests

@[expose] public section

/-! # A universal Martin-Löf test from lambda evaluation certificates -/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open CantorMeasure CantorDerivative
open scoped ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def bitCheck (z : ℕ) : ℕ := if (NatListCode.decode z.unpair.1).getD z.unpair.2 0 ≤ 1 then 1 else 0

def binaryCheck (e : ℕ) : ℕ := boundedProduct bitCheck e (NatListCode.decode e).length

def binaryCheckProgram : AlphaTerm := numericalCompose
  (boundedProductTerm (numericalCombine lessOrEqualTerm listGetTerm (numericalConstant 1)))
  (pairNumerical numericalIdentity listLengthTerm)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Universal Martin-Löf test
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Enumerate all closed numerical lambda programs by their syntax codes, replacing an invalid code by a fixed
    closed term as in §{sec:lambda-program-input-codes}. The program with index $e$ need not terminate or enumerate
    valid entries. Instead of waiting for it, use the total finite-certificate test $\LambdaOutputCandidate$.
    At stage $t=\NatPair{s}{k}$ of row $(e,n)$, unpair $k$ into an output $a$ and a certificate bound. Emit $a$ if
    the certificate verifies output $a$ on input $\NatPair{n}{s}$ and $a$ is a valid cylinder entry; otherwise emit zero.
    Call this total table $c(\NatPair{\NatPair{e}{n}}{t})$.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Validity is a finite binary-digit test. For a word code $w$, take
    $$\begin{aligned}
    Q&:=\lambdaab{z}{\LambdaLeCase{\LambdaListGet\,z}{\ChurchNumeral{1}}{\ChurchNumeral{1}}{\ChurchNumeral{0}}},\\
    D&:=\lambdaab{w}{\LambdaBoundedProduct{Q}(\LambdaNumericPair\,w\,(\LambdaListLength\,w))}.
    \end{aligned}$$
    The output of $D$ is nonzero exactly when every decoded digit is at most one. The padding entry is valid;
    for $a>0$, apply this test to the word code $a-1$. To display the full candidate program, abbreviate the
    numerical projections as $\pi_i:=\LambdaNumericProjection{i}$ and set
    $$\begin{gathered}
    \begin{aligned}
    E(z)&:=\pi_1(\pi_1z),&N(z)&:=\pi_2(\pi_1z),\\
    J(z)&:=\pi_1(\pi_2z),&K(z)&:=\pi_2(\pi_2z),\\
    O(z)&:=\pi_1(K(z)).
    \end{aligned}\\
    \begin{aligned}
    T(z)&:=\LambdaOutputCandidate\,E(z)\,(\LambdaNumericPair\,N(z)\,J(z))\,K(z),\\
    A(z)&:=\LambdaZeroTest\,(D(\LambdaPred\,O(z)))\,\ChurchNumeral{0}\,O(z),\\
    C&:=\lambdaab{z}{\LambdaZeroTest\,T(z)\,\ChurchNumeral{0}\,A(z)}.
    \end{aligned}
    \end{gathered}$$
    For output zero the same formula returns zero. Thus all stages terminate, all nonzero entries are valid,
    and both the program index and the test row remain numerical inputs.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Apply the preceding lemma to each row with bound $2^{-n}$. Write $\widehat c_{e,n}$ for the resulting name
    and $G_{e,n}:=U_{\widehat c_{e,n}}$. One closed program $R$ computes all these names on input
    $\NatPair{\NatPair{e}{n}}{t}$: use $C$ above as its candidate program and
    $B:=\lambdaab{h}{\LambdaDyadic(\LambdaNumericProjection{2}h)}$ as its bound program.
    Then $\mu(G_{e,n})\le 2^{-n}$ for every $e,n$, regardless of the original program's behavior.
    If index $e$ computes a genuine test $\Sequence{U_n}{n\in\omega}$, every accepted certificate for row $n$ has the same
    output as
    that test's enumeration, by uniqueness of numerical outputs. Conversely, each actual output has a finite
    certificate. Hence the unmodified certificate row names exactly $U_n$. Its measure is already within the
    bound, so the lemma leaves it unchanged and $G_{e,n}=U_n$.
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Now put
    $$V_n:=\bigcup_e G_{e,n+e+1}.$$
    The row and stage pairing gives one enumeration program. More explicitly, with
    $E(z):=\pi_1(\pi_2z)$ and $L(z):=\LambdaSucc(\LambdaAdd\,(\pi_1z)\,E(z))$, it is
    $$V:=\lambdaab{z}{R\bigl(\LambdaNumericPair\,
     (\LambdaNumericPair\,E(z)\,L(z))\,(\pi_2(\pi_2z))\bigr)}.$$
    Countable subadditivity gives
    $$\mu(V_n)\le\sum_{e=0}^{\infty}2^{-(n+e+1)}=2^{-n}.$$
    Thus $\Sequence{V_n}{n\in\omega}$ is a Martin-Löf test. Every genuine test has a closed-program index $e$, and the
    equality
    $G_{e,m}=U_m$ proved above gives $U_{n+e+1}\IncludedIn V_n$. A point failing any test therefore lies in
    $\bigcap_n V_n$. Conversely, a point in that intersection fails this particular Martin-Löf test.
-/
theorem binaryCheck_computes : NumericalComputes binaryCheckProgram binaryCheck := by
  have hb : NumericalComputes (numericalCombine lessOrEqualTerm listGetTerm (numericalConstant 1)) bitCheck :=
    listGet_computes.combine (numericalConstant_computes 1)
      lessOrEqualTerm_closed (fun a b => if a ≤ b then 1 else 0) lessOrEqualTerm_apply
  change NumericalComputes _ (fun e => boundedProduct bitCheck e (NatListCode.decode e).length)
  simpa only [binaryCheckProgram,Nat.unpair_pair,id_eq] using
    (boundedProduct_computes hb).comp (numericalIdentity_computes.pair listLength_computes)

theorem binaryCheck_ne_zero (e : ℕ) : binaryCheck e ≠ 0 ↔ Binary e := by
  rw [binaryCheck,boundedProduct_ne_zero]
  simp only [bitCheck,Nat.unpair_pair,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not]
  constructor
  · intro h a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
    simpa [List.getD,hi] using h i hi
  · intro h i hi
    have ha := h _ (List.getElem_mem hi)
    simpa [List.getD,hi] using ha

theorem entryCheck_ne_zero (a : ℕ) : binaryCheck (a-1) ≠ 0 ↔ ValidEntry a := by
  rw [binaryCheck_ne_zero]
  constructor
  · exact Or.inr
  · rintro (rfl | h)
    · simp [Binary,NatListCode.decode]
    · exact h

/-- Parameters (program,row), stage (input-stage,output-certificate). -/
def certificateEntry (z : ℕ) : ℕ :=
  let e := z.unpair.1.unpair.1
  let n := z.unpair.1.unpair.2
  let s := z.unpair.2.unpair.1
  let k := z.unpair.2.unpair.2
  if Term.outputCandidate e (Nat.pair n s) k then
    if binaryCheck (k.unpair.1-1) = 0 then 0 else k.unpair.1
  else 0

def certificateEntryProgram : AlphaTerm :=
  let X := numericalProjectionTerm true
  let S := numericalProjectionTerm false
  let E := numericalCompose (numericalProjectionTerm true) X
  let N := numericalCompose (numericalProjectionTerm false) X
  let J := numericalCompose (numericalProjectionTerm true) S
  let K := numericalCompose (numericalProjectionTerm false) S
  let O := numericalCompose (numericalProjectionTerm true) K
  let T := numericalApply3 outputCandidateTerm E (pairNumerical N J) K
  numericalIfZero T (numericalConstant 0)
    (numericalIfZero (numericalCompose binaryCheckProgram (numericalCompose predecessorTerm O))
      (numericalConstant 0) O)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Universal Martin-Löf test
-/
theorem certificateEntry_computes : NumericalComputes certificateEntryProgram certificateEntry := by
  have hx := projection_computes true
  have hs := projection_computes false
  have he := (projection_computes true).comp hx
  have hn := (projection_computes false).comp hx
  have hj := (projection_computes true).comp hs
  have hk := (projection_computes false).comp hs
  have ho := (projection_computes true).comp hk
  have ht := he.apply3 (hn.pair hj) hk outputCandidateTerm_closed
    (fun e n k => if Term.outputCandidate e n k then 1 else 0) outputCandidateTerm_apply
  have hv := numericalIfZero_computes (binaryCheck_computes.comp (predecessor_computes.comp ho))
    (numericalConstant_computes 0) ho
  have h := numericalIfZero_computes ht (numericalConstant_computes 0) hv
  unfold certificateEntryProgram
  convert h using 1
  funext z
  simp only [ite_true,Bool.false_eq_true,ite_false]
  unfold certificateEntry
  split <;> simp_all

theorem certificateEntry_valid (z : ℕ) : ValidEntry (certificateEntry z) := by
  dsimp only [certificateEntry]
  split_ifs with h hv
  · exact Or.inl rfl
  · exact (entryCheck_ne_zero _).mp hv
  · exact Or.inl rfl

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Universal Martin-Löf test
-/
theorem certificateEntry_names {e : ℕ} {p : ℕ → ℕ}
    (hp : NumericalComputes (Term.closedProgram e) p)
    (hv : ∀ n, ValidOpenName (fun s => p (Nat.pair n s))) (n : ℕ) :
    namedOpen (fun t => certificateEntry (Nat.pair (Nat.pair e n) t)) =
      namedOpen (fun s => p (Nat.pair n s)) := by
  ext x
  simp only [namedOpen,mem_iUnion]
  constructor
  · rintro ⟨t,ht⟩
    simp only [certificateEntry,Nat.unpair_pair] at ht
    split_ifs at ht with hc hb
    · simp [entrySet] at ht
    · have ho := (program_output_iff_candidate e (Nat.pair n t.unpair.1) t.unpair.2.unpair.1).mpr
        ⟨t.unpair.2,rfl,(outputCandidate_accept_iff _ _ _).mpr hc⟩
      have he := numeral_output_unique (hp.2 (Nat.pair n t.unpair.1)) ho
      exact ⟨t.unpair.1,he ▸ ht⟩
    · simp [entrySet] at ht
  · rintro ⟨s,hs⟩
    obtain ⟨k,hk,hc⟩ := (program_output_iff_candidate e (Nat.pair n s) (p (Nat.pair n s))).mp (hp.2 _)
    have ha := (outputCandidate_accept_iff _ _ _).mp hc
    have hb := (entryCheck_ne_zero _).mpr (hv n s)
    refine ⟨Nat.pair s k,?_⟩
    simpa only [certificateEntry,Nat.unpair_pair,ha,ite_true,hk,ite_eq_right hb] using hs

/-- The same budget compiler handles every program index and test row. -/
def trimmedEntry (z : ℕ) : ℕ := budgetName ((1/2:ℚ)^z.unpair.1.unpair.2)
  (fun t => certificateEntry (Nat.pair z.unpair.1 t)) z.unpair.2

def trimmedProgram : AlphaTerm := budgetProgram
  (numericalCompose rationalDyadicTerm (numericalProjectionTerm false)) certificateEntryProgram

theorem trimmedProgram_computes : NumericalComputes trimmedProgram trimmedEntry := by
  have h := budgetProgram_computes (rationalDyadic_computes.comp (projection_computes false))
    certificateEntry_computes
  unfold trimmedProgram
  convert h using 1
  funext z
  simp [trimmedEntry]

def trimmedRow (e n : ℕ) : Set (ℕ → Bool) :=
  namedOpen (fun t => trimmedEntry (Nat.pair (Nat.pair e n) t))

theorem trimmedEntry_valid (z : ℕ) : ValidEntry (trimmedEntry z) :=
  budgetName_valid (fun t => certificateEntry_valid (Nat.pair z.unpair.1 t)) z.unpair.2

theorem trimmedRow_bound (e n : ℕ) : fairCoinProduct.real (trimmedRow e n) ≤ (1/2:ℝ)^n := by
  have h := budgetName_bound (b := (1/2:ℚ)^n) (by positivity)
    (fun t => certificateEntry_valid (Nat.pair (Nat.pair e n) t))
  simpa [trimmedRow,trimmedEntry] using h

theorem trimmedRow_eq {e : ℕ} {p : ℕ → ℕ}
    (hp : NumericalComputes (Term.closedProgram e) p)
    (hv : ∀ n, ValidOpenName (fun s => p (Nat.pair n s))) (n : ℕ)
    (hb : fairCoinProduct.real (namedOpen (fun s => p (Nat.pair n s))) ≤ (1/2:ℝ)^n) :
    trimmedRow e n = namedOpen (fun s => p (Nat.pair n s)) := by
  have he := certificateEntry_names hp hv n
  have hb' : fairCoinProduct.real (namedOpen (fun t => certificateEntry (Nat.pair (Nat.pair e n) t))) ≤
      (((1/2:ℚ)^n : ℚ) : ℝ) := by simpa only [he,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hb
  have hn := budgetName_unchanged (fun t => certificateEntry_valid (Nat.pair (Nat.pair e n) t)) hb'
  simpa only [trimmedRow,trimmedEntry,Nat.unpair_pair,hn] using he

def universalOpen (n : ℕ) : Set (ℕ → Bool) := ⋃ e, trimmedRow e (n+e+1)

def universalEntry (z : ℕ) : ℕ := trimmedEntry
  (Nat.pair (Nat.pair z.unpair.2.unpair.1 (z.unpair.1+z.unpair.2.unpair.1+1)) z.unpair.2.unpair.2)

def universalProgram : AlphaTerm :=
  let N := numericalProjectionTerm true
  let E := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let T := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  numericalCompose trimmedProgram (pairNumerical
    (pairNumerical E (numericalCompose successorTerm (addNumerical N E))) T)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Universal Martin-Löf test
-/
theorem universalProgram_computes : NumericalComputes universalProgram universalEntry := by
  have hn := projection_computes true
  have he := (projection_computes true).comp (projection_computes false)
  have ht := (projection_computes false).comp (projection_computes false)
  have h := trimmedProgram_computes.comp (he.pair (successor_computes.comp (hn.add he)) |>.pair ht)
  unfold universalProgram
  convert h using 1
  funext z
  simp [universalEntry]

theorem universalEntry_valid (n : ℕ) : ValidOpenName (fun t => universalEntry (Nat.pair n t)) :=
  fun _ => trimmedEntry_valid _

theorem universalEntry_names (n : ℕ) : universalOpen n = namedOpen (fun t => universalEntry (Nat.pair n t)) := by
  ext x
  simp only [universalOpen,trimmedRow,namedOpen,mem_iUnion,universalEntry,Nat.unpair_pair]
  constructor
  · rintro ⟨e,t,ht⟩
    exact ⟨Nat.pair e t,by simpa only [Nat.unpair_pair] using ht⟩
  · rintro ⟨t,ht⟩
    exact ⟨t.unpair.1,t.unpair.2,ht⟩

theorem universalOpen_uniform : UniformlyOpen universalOpen :=
  ⟨universalProgram,universalEntry,universalProgram_computes,universalEntry_valid,universalEntry_names⟩

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Universal Martin-Löf test
-/
theorem universalOpen_bound (n : ℕ) : fairCoinProduct.real (universalOpen n) ≤ (1/2:ℝ)^n := by
  have hb (e m : ℕ) : fairCoinProduct (trimmedRow e m) ≤ (1/2:ℝ≥0∞)^m := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simpa only [universalOpen,Measure.real,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
      using trimmedRow_bound e m
  have h := (measure_iUnion_le (fun e => trimmedRow e (n+e+1))).trans
    (ENNReal.tsum_le_tsum (fun e => hb e (n+e+1)))
  have hs : (∑' e, (1/2:ℝ≥0∞)^(n+e+1)) = (1/2:ℝ≥0∞)^n := by
    simp_rw [Nat.add_assoc,pow_add]
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
    norm_num
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]
  rw [hs] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simpa only [universalOpen,Measure.real,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hr

theorem universalOpen_MLTest : MLTest universalOpen := ⟨universalOpen_uniform,universalOpen_bound⟩

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Universal Martin-Löf test
-/
theorem universalOpen_covers {U : ℕ → Set (ℕ → Bool)} (hU : MLTest U) :
    ∃ e, ∀ n, U (n+e+1) ⊆ universalOpen n := by
  obtain ⟨P,p,hp,hv,hu⟩ := hU.1
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hp.1
  have hp' : NumericalComputes (Term.closedProgram e) p := he ▸ hp
  refine ⟨e,fun n => ?_⟩
  have hb := hU.2 (n+e+1)
  rw [hu (n+e+1)] at hb ⊢
  rw [← trimmedRow_eq hp' hv (n+e+1) hb]
  exact subset_iUnion (fun e => trimmedRow e (n+e+1)) e

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: theorem
  title: Universal Martin-Löf test
-/
theorem mlRandom_iff_avoids_universal (x : ℕ → Bool) : MLRandom x ↔ AvoidsTest x universalOpen := by
  constructor
  · intro hx
    exact hx _ universalOpen_MLTest
  · intro hx U hU hmem
    apply hx
    obtain ⟨e,he⟩ := universalOpen_covers hU
    exact mem_iInter.mpr (fun n => he n (mem_iInter.mp hmem (n+e+1)))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: A positive closed class of random points
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    The set $V_1$ is effectively open and has measure at most $1/2$, so its complement is closed with measure
    at least $1/2$. A point outside $V_1$ is outside $\bigcap_n V_n$, and is therefore Martin-Löf random by the theorem.
-/
theorem outside_universal_one_random {x : ℕ → Bool} (hx : x ∉ universalOpen 1) : MLRandom x := by
  apply (mlRandom_iff_avoids_universal x).mpr
  intro h
  exact hx (mem_iInter.mp h 1)


/-- A positive effectively closed class all of whose points are Martin-Löf random. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: A positive closed class of random points
-/
theorem universalComplement_closed : IsClosed (universalOpen 1)ᶜ :=
  (universalOpen_uniform.isOpen 1).isClosed_compl

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: A positive closed class of random points
-/
theorem universalComplement_mass : (1/2:ℝ) ≤ fairCoinProduct.real (universalOpen 1)ᶜ := by
  rw [measureReal_compl (universalOpen_uniform.isOpen 1).measurableSet,probReal_univ]
  have h := universalOpen_bound 1
  norm_num at h ⊢
  linarith

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: corollary
  title: A positive closed class of random points
-/
theorem universalComplement_nonempty : ((universalOpen 1)ᶜ).Nonempty := by
  by_contra h
  have he := Set.not_nonempty_iff_eq_empty.mp h
  have hm := universalComplement_mass
  rw [he,measureReal_empty] at hm
  norm_num at hm

end PolishSpaceBook.LambdaRandomness
