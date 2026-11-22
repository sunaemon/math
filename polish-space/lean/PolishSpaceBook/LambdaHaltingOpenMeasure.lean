module

public import PolishSpaceBook.LambdaCantorMeasure
public import PolishSpaceBook.LambdaHaltingReal

@[expose] public section
/-! # An effectively open set with noncomputable fair-coin measure

A total numerical lambda term enumerates disjoint cylinders when finite
certificates of diagonal halting are accepted. Their measure is the previously
constructed noncomputable base-four real.
-/
namespace PolishSpaceBook.CantorMeasure
open Set MeasureTheory NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA CantorDerivative
set_option maxRecDepth 4096

def haltingWord (e : ℕ) : List Bool := List.replicate (2*e) false ++ [true,false]

@[simp] theorem haltingWord_length (e : ℕ) : (haltingWord e).length = 2*e+2 := by
  simp [haltingWord]

theorem haltingWord_disjoint_lt {e f : ℕ} (h : e < f) :
    Disjoint (cyl (haltingWord e)) (cyl (haltingWord f)) := by
  rw [Set.disjoint_left]
  intro x he hf
  have hae : 2*e < (haltingWord e).length := by simp
  have haf : 2*e < (haltingWord f).length := by simp; omega
  have hx := he (2*e) hae
  have hy := hf (2*e) haf
  have hlt : 2*e < 2*f := by omega
  simp [haltingWord,List.get_eq_getElem,hlt] at hx hy
  simp [hx] at hy

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Let $K$ be the diagonal halting set used there. For each $e\in\NN$, take the binary word
    $$s_e:=\wordRepeat{0}{2e}\concat(1,0),\qquad U:=\bigcup_{e\in K}\cyl{s_e}.$$
    These cylinders are pairwise disjoint. Indeed, if $e<f$, their members have different bits at coordinate $2e$:
    a member of $\cyl{s_e}$ has bit $1$, whereas a member of $\cyl{s_f}$ has bit $0$.
    Their lengths and measures are
    $$|s_e|=2e+2,\qquad \mu(\cyl{s_e})=2^{-(2e+2)}=4^{-(e+1)}.$$
-/
theorem haltingWord_disjoint : Pairwise (fun e f => Disjoint (cyl (haltingWord e)) (cyl (haltingWord f))) := by
  intro e f h
  rcases lt_or_gt_of_ne h with h | h
  · exact haltingWord_disjoint_lt h
  · exact (haltingWord_disjoint_lt h).symm

theorem haltingWord_measure (e : ℕ) : fairCoinProduct.real (cyl (haltingWord e)) = haltingWeight e := by
  rw [Measure.real,fairCoinProduct_cyl,haltingWord_length,ENNReal.toReal_pow]
  have he : 2*e+2=2*(e+1) := by omega
  rw [he,pow_mul]
  norm_num [haltingWeight]



@[simp] theorem haltingWord_succ (e : ℕ) : haltingWord (e+1) = false :: false :: haltingWord e := by
  unfold haltingWord
  rw [show 2*(e+1) = (2*e+1)+1 by omega,List.replicate_succ,List.replicate_succ]
  rfl

def haltingWordCode : ℕ → ℕ := primitiveRec (encodeWord [true,false])
  (fun _ r => Nat.pair 0 (Nat.pair 0 r + 1) + 1)

theorem haltingWordCode_eq (e : ℕ) : haltingWordCode e = encodeWord (haltingWord e) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    change Nat.pair 0 (Nat.pair 0 (haltingWordCode e) + 1) + 1 = _
    rw [ih,haltingWord_succ]
    rfl

def prependZeroProgram : AlphaTerm := numericalCombine listConsTerm
  (numericalConstant 0) numericalIdentity

theorem prependZeroProgram_computes : NumericalComputes prependZeroProgram (fun r => Nat.pair 0 r + 1) :=
  (numericalConstant_computes 0).combine numericalIdentity_computes listConsTerm_closed
    (fun a d => Nat.pair a d + 1) listConsTerm_apply

def haltingWordProgram : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant (encodeWord [true,false]))
    (numericalCompose (numericalCompose prependZeroProgram prependZeroProgram)
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))))
  (pairNumerical (numericalConstant 0) numericalIdentity)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    We give a closed numerical lambda program for an open name of $U$. Generate the codes
    $\LambdaListCode{s_e}$ directly by the following terms:
    $$\begin{aligned}
    A&:=\lambdaab{x}{\ChurchNumeral{\LambdaListCode{[1,0]}}},\\
    H&:=\lambdaab{x}{\lambdaab{j}{\lambdaab{r}{
     \LambdaListCons\,\ChurchNumeral{0}\,(\LambdaListCons\,\ChurchNumeral{0}\,r)}}},\\
    W&:=\lambdaab{e}{\LambdaParamRec{A}{H}\,\ChurchNumeral{0}\,e}.
    \end{aligned}$$
    The parameter $x$ and counter $j$ are unused. The step prepends two zeros, so induction gives
    $$W\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{\LambdaListCode{s_e}}.$$
    This calculation terminates for every $e$ and uses only numerical list construction and recursion.
-/
theorem haltingWordProgram_computes : NumericalComputes haltingWordProgram haltingWordCode := by
  have hn := prependZeroProgram_computes.comp prependZeroProgram_computes
  have hh := hn.comp ((projection_computes false).comp (projection_computes false))
  have hr := (numericalRecursion_computes (numericalConstant_computes (encodeWord [true,false])) hh).comp
    ((numericalConstant_computes 0).pair numericalIdentity_computes)
  simpa only [haltingWordProgram,haltingWordCode,Nat.unpair_pair,Bool.false_eq_true,ite_false,id_eq] using hr

def haltingOpenName (z : ℕ) : ℕ :=
  if Term.outputCandidate z.unpair.1 z.unpair.1 z.unpair.2 then haltingWordCode z.unpair.1 + 1 else 0

def haltingOpenProgram : AlphaTerm :=
  let E := numericalProjectionTerm true
  let K := numericalProjectionTerm false
  numericalIfZero (numericalApply3 outputCandidateTerm E E K) (numericalConstant 0)
    (numericalCompose successorTerm (numericalCompose haltingWordProgram E))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Let $c_e(k)\in\{0,1\}$ be the finite certificate test for the numerical halting of $\varphi_e(e)$ at candidate $k$.
    The certificate theorem says that $e\in K$ exactly when some $k$ satisfies $c_e(k)=1$. Define an enumeration by
    $$p(\NatPair{e}{k}):=\begin{cases}
    \LambdaListCode{s_e}+1,&c_e(k)=1,\\
    0,&c_e(k)=0.
    \end{cases}$$
    A closed term computing this total function is
    $$\begin{aligned}
    T&:=\lambdaab{e}{\lambdaab{k}{\LambdaOutputCandidate\,e\,e\,k}},\\
    Q&:=\lambdaab{z}{T\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)},\\
    P&:=\lambdaab{z}{\LambdaZeroTest\,(Qz)\,\ChurchNumeral{0}\,
     (\LambdaSucc(W(\LambdaNumericProjection{1}z)))}.
    \end{aligned}$$
    Thus $P\ChurchNumeral{z}\to_\beta^*\ChurchNumeral{p(z)}$ for every $z$. Each stage tests one finite certificate;
    it never waits for the program indexed by $e$ to halt. The successor distinguishes a cylinder entry from padding.
    Every nonzero entry codes a binary word, so $p$ is a valid open name.
-/
theorem haltingOpenProgram_computes : NumericalComputes haltingOpenProgram haltingOpenName := by
  have he := projection_computes true
  have hk := projection_computes false
  have ht := he.apply3 he hk outputCandidateTerm_closed
    (fun e n k => if Term.outputCandidate e n k then 1 else 0) outputCandidateTerm_apply
  have hw := successor_computes.comp (haltingWordProgram_computes.comp he)
  have h := numericalIfZero_computes ht (numericalConstant_computes 0) hw
  refine ⟨h.1,fun z => ?_⟩
  have hz := h.2 z
  cases hc : Term.outputCandidate z.unpair.1 z.unpair.1 z.unpair.2 <;>
    simpa only [haltingOpenProgram,haltingOpenName,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
      Nat.one_ne_zero,Nat.succ_eq_add_one,hc] using hz

theorem haltingOpenName_valid : ValidOpenName haltingOpenName := by
  intro z
  unfold haltingOpenName
  split_ifs
  · right
    simpa only [Nat.add_sub_cancel,haltingWordCode_eq] using binary_encodeWord (haltingWord z.unpair.1)
  · exact Or.inl rfl

theorem diagonalHalts_iff_certificate (e : ℕ) :
    diagonalHalts e ↔ ∃ k, Term.outputCandidate e e k = true := by
  change (∃ m, Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral e)) (numeral m)) ↔ _
  simp only [program_output_iff_candidate,outputCandidate_accept_iff]
  constructor
  · rintro ⟨_,k,_,hk⟩; exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k.unpair.1,k,rfl,hk⟩

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

noncomputable def haltingCylinder (e : ℕ) : Set (ℕ → Bool) :=
  if diagonalHalts e then cyl (haltingWord e) else ∅

noncomputable def haltingOpen : Set (ℕ → Bool) := ⋃ e, haltingCylinder e

theorem haltingCylinder_measurable (e : ℕ) : MeasurableSet (haltingCylinder e) := by
  unfold haltingCylinder
  split_ifs <;> first | exact (isOpen_cyl _).measurableSet | exact MeasurableSet.empty

theorem haltingCylinder_disjoint : Pairwise (fun e f => Disjoint (haltingCylinder e) (haltingCylinder f)) := by
  intro e f h
  unfold haltingCylinder
  split_ifs <;> simp_all [haltingWord_disjoint h]

theorem haltingOpen_measure : fairCoinProduct.real haltingOpen = haltingSetReal diagonalHalts := by
  rw [Measure.real,haltingOpen,measure_iUnion haltingCylinder_disjoint haltingCylinder_measurable,
    ENNReal.tsum_toReal_eq (fun _ => by finiteness)]
  apply tsum_congr
  intro e
  change fairCoinProduct.real (haltingCylinder e) = haltingDigit diagonalHalts e
  unfold haltingCylinder haltingDigit
  split_ifs
  · exact haltingWord_measure e
  · simp


theorem haltingOpenName_set : namedOpen haltingOpenName = haltingOpen := by
  ext x
  simp only [namedOpen,haltingOpen,mem_iUnion]
  constructor
  · rintro ⟨z,hz⟩
    by_cases hc : Term.outputCandidate z.unpair.1 z.unpair.1 z.unpair.2 = true
    · refine ⟨z.unpair.1,?_⟩
      have hh := (diagonalHalts_iff_certificate _).mpr ⟨z.unpair.2,hc⟩
      simpa [haltingOpenName,entrySet,hc,haltingCylinder,hh,haltingWordCode_eq] using hz
    · simp [haltingOpenName,hc,entrySet] at hz
  · rintro ⟨e,he⟩
    have hh : diagonalHalts e := by
      by_contra hn
      simp [haltingCylinder,hn] at he
    obtain ⟨k,hk⟩ := (diagonalHalts_iff_certificate e).mp hh
    refine ⟨Nat.pair e k,?_⟩
    simpa [haltingOpenName,entrySet,Nat.unpair_pair,hk,haltingWordCode_eq,haltingCylinder,hh] using he

theorem haltingOpen_isOpen : IsOpen haltingOpen := by
  rw [← haltingOpenName_set]
  exact isOpen_namedOpen _

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    If $e\in K$, some accepted certificate causes $\cyl{s_e}$ to appear in the enumeration. Conversely, every
    nonempty entry comes from an accepted certificate, hence from an $e\in K$. Repetitions do not affect the union,
    so $U_p=U$. Countable additivity on the disjoint cylinders now gives
    $$\mu(U)=\sum_{e\in K}\mu(\cyl{s_e})=\sum_{e\in K}4^{-(e+1)}=\HaltingReal.$$
    By §{sec:tte-real-examples}, a computable fast Cauchy name of this real would let a closed numerical lambda
    program recover the digits of $K$ and decide diagonal halting. Thus the measure is noncomputable; since every
    rational has a constant computable name, it is also irrational. The lower-approximation theorem still applies
    to $p$, so the same measure has a computable increasing sequence of rational lower bounds converging to it.
    \end{proof}
-/
theorem haltingOpen_measure_not_computable :
    ¬ ∃ p : realRepresentation.domain, realRepresentation.toFun p = fairCoinProduct.real haltingOpen ∧
      ∃ P : AlphaTerm, NumericalComputes P p.val := by
  rw [haltingOpen_measure]
  exact haltingSetReal_not_computable

theorem haltingOpen_measure_irrational : Irrational (fairCoinProduct.real haltingOpen) := by
  rw [haltingOpen_measure]
  exact haltingSetReal_irrational


/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: example
  title: An effectively open set of noncomputable measure
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Null spheres are a sufficient condition. A set may have computable measure even when a sphere has positive
    measure, for instance when that measure is supplied separately. For an arbitrary effectively open set, only
    the lower computation is guaranteed, as the preceding Cantor-space example shows.
-/
theorem haltingOpen_example :
    ValidOpenName haltingOpenName ∧ NumericalComputes haltingOpenProgram haltingOpenName ∧
    IsOpen (namedOpen haltingOpenName) ∧
    fairCoinProduct.real (namedOpen haltingOpenName) = haltingSetReal diagonalHalts ∧
    (¬ ∃ p : realRepresentation.domain,
      realRepresentation.toFun p = fairCoinProduct.real (namedOpen haltingOpenName) ∧
      ∃ P : AlphaTerm, NumericalComputes P p.val) ∧
    Irrational (fairCoinProduct.real (namedOpen haltingOpenName)) := by
  rw [haltingOpenName_set]
  exact ⟨haltingOpenName_valid,haltingOpenProgram_computes,haltingOpen_isOpen,haltingOpen_measure,
    haltingOpen_measure_not_computable,haltingOpen_measure_irrational⟩

end PolishSpaceBook.CantorMeasure
