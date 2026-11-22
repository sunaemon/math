module

public import PolishSpaceBook.LambdaRealDoubling
public import PolishSpaceBook.LambdaHaltingObstruction
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

/-! # A uniform family of computable reals detecting numerical halting

Finite certificate checks construct total Cauchy names, including for programs
that never return a numeral. Equality with zero on indices would decide halting.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
open Filter Topology
set_option maxRecDepth 4096

/-- A numerical conditional, implemented by the existing Church zero test. -/
def numericalIfZero (C A B : AlphaTerm) : AlphaTerm := numericalApply3 zeroTestTerm C A B

theorem numericalIfZero_computes {C A B : AlphaTerm} {c a b : ℕ → ℕ}
    (hc : NumericalComputes C c) (ha : NumericalComputes A a) (hb : NumericalComputes B b) :
    NumericalComputes (numericalIfZero C A B) (fun n => if c n = 0 then a n else b n) := by
  apply hc.apply3 ha hb zeroTestTerm_closed (fun c a b => if c = 0 then a else b)
  intro c a b
  cases c with
  | zero => exact branch_zero _ _ (by rw [numeral_closed]; simp)
  | succ c => exact branch_succ c _ _

/-- Search the first n certificate candidates, retaining the first successful dyadic code. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    We can also make the obstruction to real comparison explicit. Use the rational enumeration $q_i$ and the
    computable-point assembly $A=A_{\rho_{\R}}$ from the doubling construction. Put $c_e(k)=1$ if the finite certificate
    candidate $k$ for $\varphi_e(e)$ is accepted, and put $c_e(k)=0$ otherwise. This is the total test computed by
    $\LambdaOutputCandidate$. There is an accepted candidate exactly when $e\in K$.
    Let $d_k:=\RationalCode{1}{0}{2^{k+2}-1}$, so $q_0=0$ and $q_{d_k}=2^{-(k+2)}$. Define a numerical name by
    $$\begin{aligned}
    p_e(0)&:=0,\\
    p_e(n+1)&:=\begin{cases}
    p_e(n),&p_e(n)\ne0,\\
    d_n,&p_e(n)=0\text{ and }c_e(n)=1,\\
    0,&\text{otherwise}.
    \end{cases}
    \end{aligned}$$
-/
def haltingRealName (e : ℕ) : ℕ → ℕ := primitiveRec 0 (fun k r =>
  if r = 0 then if Term.outputCandidate e e k then (RationalCode.dyadic (k+2)).natCode else 0 else r)

def haltingRealStep : AlphaTerm :=
  let E := numericalProjectionTerm true
  let K := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let R := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  numericalIfZero R
    (numericalIfZero (numericalApply3 outputCandidateTerm E E K) (numericalConstant 0)
      (numericalCompose rationalDyadicTerm (addNumerical K (numericalConstant 2)))) R

def haltingRealNameProgram : AlphaTerm := numericalRecursion (numericalConstant 0) haltingRealStep

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    This recurrence is computed by a closed lambda program $P$ on input $\NatPair{e}{n}$. For its step, the numerical
    projections read $e,n,r$ from $\NatPair{e}{\NatPair{n}{r}}$. A zero test preserves $r$ when it is nonzero. Otherwise,
    another zero test on $\LambdaOutputCandidate\ChurchNumeral{e}\ChurchNumeral{e}\ChurchNumeral{n}$ selects zero or
    $\LambdaDyadic(\LambdaAdd\ChurchNumeral{n}\ChurchNumeral{2})$.
    The parameterized recursor of §{sec:lambda-primitive-recursion}, with zero initial value, implements the recurrence.
    Every step terminates, including when the original indexed program diverges. Thus
    $$P\ChurchNumeral{\NatPair{e}{n}}\to_\beta^*\ChurchNumeral{p_e(n)}.$$
-/
theorem haltingRealName_computes : NumericalComputes haltingRealNameProgram
    (fun z => haltingRealName z.unpair.1 z.unpair.2) := by
  have he := projection_computes true
  have hk := (projection_computes true).comp (projection_computes false)
  have hr := (projection_computes false).comp (projection_computes false)
  have hc := he.apply3 he hk outputCandidateTerm_closed
    (fun e n k => if Term.outputCandidate e n k then 1 else 0) outputCandidateTerm_apply
  have hd := rationalDyadic_computes.comp (hk.add (numericalConstant_computes 2))
  have hs := numericalIfZero_computes hr
    (numericalIfZero_computes hc (numericalConstant_computes 0) hd) hr
  have hz (b : Bool) (r : ℕ) :
      (if (if b then 1 else 0 : ℕ) = 0 then 0 else r) = (if b then r else 0) := by
    cases b <;> rfl
  have hs' : NumericalComputes haltingRealStep (fun z =>
      if z.unpair.2.unpair.2 = 0 then
        if Term.outputCandidate z.unpair.1 z.unpair.1 z.unpair.2.unpair.1 then
          (RationalCode.dyadic (z.unpair.2.unpair.1+2)).natCode else 0
      else z.unpair.2.unpair.2) := by
    simpa only [haltingRealStep,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,hz] using hs
  simpa only [haltingRealNameProgram,haltingRealName,Nat.unpair_pair] using
    numericalRecursion_computes (numericalConstant_computes 0) hs'


@[simp] theorem rationalPoint_zero : rationalPoint 0 = 0 := by
  simp [rationalPoint,RationalCode.ofNat,RationalCode.value]

@[simp] theorem rationalPoint_dyadic (k : ℕ) :
    rationalPoint (RationalCode.dyadic k).natCode = (1/2 : ℝ)^k := by
  simp [rationalPoint]

theorem dyadic_code_ne_zero (k : ℕ) : (RationalCode.dyadic k).natCode ≠ 0 := by
  intro h
  have hv := rationalPoint_dyadic k
  rw [h,rationalPoint_zero] at hv
  exact (ne_of_gt (pow_pos (by norm_num : (0:ℝ)<1/2) k)) hv.symm

theorem haltingRealName_before (e n : ℕ)
    (h : ∀ k < n, Term.outputCandidate e e k = false) : haltingRealName e n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun k hk => h k (by omega))
    change (if haltingRealName e n = 0 then
      if Term.outputCandidate e e n then _ else 0 else _) = 0
    simp [hn,h n (by omega)]

theorem haltingRealName_first (e k : ℕ) (hk : Term.outputCandidate e e k = true)
    (hbefore : ∀ j < k, Term.outputCandidate e e j = false) (n : ℕ) :
    haltingRealName e n = if n ≤ k then 0 else (RationalCode.dyadic (k+2)).natCode := by
  induction n with
  | zero => simp [haltingRealName,primitiveRec]
  | succ n ih =>
    change (if haltingRealName e n = 0 then
      if Term.outputCandidate e e n then _ else 0 else _) = _
    rw [ih]
    by_cases hn : n < k
    · simp [show n ≤ k by omega,show n+1 ≤ k by omega,hbefore n hn]
    · by_cases he : n = k
      · subst n; simp [hk]
      · simp only [ite_eq_right (show ¬ n ≤ k by omega),ite_eq_right (show ¬ n+1 ≤ k by omega),
          dyadic_code_ne_zero,ite_false]
        exact ih.trans (ite_eq_right (by omega))

theorem candidate_exists_iff_halts (e : ℕ) :
    (∃ k, Term.outputCandidate e e k = true) ↔ diagonalHalts e := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k.unpair.1,(outputTest_exists_iff e e k.unpair.1).mp ⟨k.unpair.2,hk⟩⟩
  · rintro ⟨m,hm⟩
    obtain ⟨s,hs⟩ := (outputTest_exists_iff e e m).mpr hm
    exact ⟨Nat.pair m s,by simpa [Term.outputCandidate] using hs⟩

noncomputable def haltingReal (e : ℕ) : ℝ := by
  classical
  exact if h : ∃ k, Term.outputCandidate e e k = true then (1/2 : ℝ)^(Nat.find h+2) else 0

theorem haltingReal_ne_zero_iff (e : ℕ) : haltingReal e ≠ 0 ↔ diagonalHalts e := by
  classical
  rw [← candidate_exists_iff_halts]
  unfold haltingReal
  split_ifs with h
  · simp [h]
  · simp [h]


/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: lemma
  title: Computable reals encoding halting
  excerpt: |
    \begin{lemma*}[\termdefineas{halting-coded computable reals}{Computable reals encoding halting}]
    Every $p_e$ is a Cauchy name. Writing $x_e:=\rho_{\R}(p_e)$, we have
    $$x_e\ne0\quad\Longleftrightarrow\quad e\in K.$$
    Moreover, one total closed lambda program computes an index $t(e)$ of $p_e$ from $e$.
    \end{lemma*}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    If there is no accepted candidate, induction gives $p_e(n)=0$ for every $n$, so the name represents zero.
    Otherwise let $k$ be the least accepted candidate. Induction on the recurrence gives
    $$p_e(n)=\begin{cases}0,&n\le k,\\d_k,&n>k.\end{cases}$$
    Thus the rational sequence $q_{p_e(n)}$ is eventually constant at the positive value $2^{-(k+2)}$.
    For $n\le m$, the only case in which its values differ is $n\le k<m$, and in that case
    $$|q_{p_e(n)}-q_{p_e(m)}|=2^{-(k+2)}\le2^{-n}.$$
    This proves both the required pairwise Cauchy bound and the asserted value of the limit.
-/
theorem haltingRealName_isCauchy (e : ℕ) : IsCauchyName rationalPoint (haltingRealName e) := by
  classical
  by_cases h : ∃ k, Term.outputCandidate e e k = true
  · let k := Nat.find h
    have hk := Nat.find_spec h
    have hbefore : ∀ j < k, Term.outputCandidate e e j = false := by
      intro j hj
      exact Bool.eq_false_iff.mpr (Nat.find_min h hj)
    have hname := haltingRealName_first e k hk hbefore
    intro n m hnm
    rw [hname n,hname m]
    by_cases hn : n ≤ k <;> by_cases hm : m ≤ k
    · simp [hn,hm]
    · simp only [ite_eq_left hn,ite_eq_right hm,rationalPoint_zero,rationalPoint_dyadic,Real.dist_eq,
        zero_sub,abs_neg,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<1/2) _)]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · omega
    · simp [hn,hm]
  · have hz (n : ℕ) : haltingRealName e n = 0 := haltingRealName_before e n
      (fun k _ => Bool.eq_false_iff.mpr (fun hk => h ⟨k,hk⟩))
    intro n m _
    simp [hz]

theorem haltingRealName_tendsto (e : ℕ) :
    Tendsto (fun n => rationalPoint (haltingRealName e n)) atTop (𝓝 (haltingReal e)) := by
  classical
  by_cases h : ∃ k, Term.outputCandidate e e k = true
  · let k := Nat.find h
    have hbefore : ∀ j < k, Term.outputCandidate e e j = false := by
      intro j hj
      exact Bool.eq_false_iff.mpr (Nat.find_min h hj)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop k] with n hn
    rw [haltingRealName_first e k (Nat.find_spec h) hbefore n,ite_eq_right (by omega),rationalPoint_dyadic]
    simp [haltingReal,h,k]
  · have hz (n : ℕ) : haltingRealName e n = 0 := haltingRealName_before e n
      (fun k _ => Bool.eq_false_iff.mpr (fun hk => h ⟨k,hk⟩))
    simp only [hz,rationalPoint_zero,haltingReal,dite_eq_right h]
    exact tendsto_const_nhds

def haltingRealNamePoint (e : ℕ) : realRepresentation.domain :=
  ⟨haltingRealName e,haltingRealName_isCauchy e⟩

theorem haltingRealName_value (e : ℕ) :
    realRepresentation.toFun (haltingRealNamePoint e) = haltingReal e :=
  tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint (haltingRealNamePoint e))
    (haltingRealName_tendsto e)


/-- Insert a numeral into a closed binary program by computing finite syntax. -/
theorem numerical_parameter_indices (P : AlphaTerm) (hP : P.Closed) :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ e, Term.closedProgram (f e) = app (curryNumerical P) (numeral e) := by
  obtain ⟨M,hM⟩ := Quotient.exists_rep (curryNumerical P)
  have hm : mk M = curryNumerical P := hM
  let f (e : ℕ) := (Term.app M (Term.churchNumeral e)).code
  have hn : NumericalComputes numeralCodeTerm (fun e => (Term.churchNumeral e).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  have hf := (numericalConstant_computes M.code).applicationCode hn
  refine ⟨_,f,hf,fun e => ?_⟩
  have he : mk (Term.app M (Term.churchNumeral e)) = app (curryNumerical P) (numeral e) := by
    change app (mk M) (mk (Term.churchNumeral e)) = _
    rw [hm,Term.mk_churchNumeral]
  have hc := closed_app (curryNumerical_closed hP) (numeral_closed e)
  exact (closedProgram_code_of_closed _ (he.symm ▸ hc)).trans he

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    For the uniform index construction, put
    $$C:=\lambdaab{z}{\lambdaab{n}{P(\LambdaNumericPair\,z\,n)}},\qquad
      t(e):=\LambdaSyntaxCode{C\ChurchNumeral{e}},$$
    using a fixed named representative of $C$. Numeral-code and application-code construction compute this finite syntax
    from $e$, without running the indexed program. The resulting closed term computes $p_e$ by beta contraction,
    numerical pairing, and the preceding recursion calculation. Therefore $t(e)\Vdash_A x_e$ for every $e$.
    \end{proof}
-/
theorem haltingRealName_indices :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ e, ComputesName (f e) (haltingRealName e) := by
  obtain ⟨F,f,hf,hprogram⟩ := numerical_parameter_indices haltingRealNameProgram haltingRealName_computes.1
  refine ⟨F,f,hf,fun e n => ?_⟩
  unfold App
  rw [hprogram]
  exact (curryNumerical_apply haltingRealName_computes.1 e n).trans
    (by simpa only [Nat.unpair_pair] using haltingRealName_computes.2 (Nat.pair e n))

/-- Even a partial program that is only required to decide zero on valid name indices cannot exist. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: Undecidability of computable-real equality
  excerpt: |
    \begin{theorem*}[\termdefineas{undecidability of computable-real equality}{Undecidability of computable-real equality}]
    No closed lambda program, given an arbitrary index for a total Cauchy name of a computable real $x$, always terminates
    and returns $0$ when $x=0$ and $1$ when $x\ne0$. No behavior is required on invalid name indices.
    \end{theorem*}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Suppose such a program existed. Given $e$, first compute $t(e)$ and apply the proposed test to this valid name index.
    It returns $1$ exactly when $e\in K$, and $0$ otherwise. A final zero test exchanges the two answers, giving the
    halting decider excluded above.
-/
theorem real_zero_undecidable : ¬ ∃ D : AlphaTerm, D.Closed ∧
    (∀ (p : realRepresentation.domain) e, ComputesName e p.val →
      realRepresentation.toFun p = 0 → Runs D e 0) ∧
    (∀ (p : realRepresentation.domain) e, ComputesName e p.val →
      realRepresentation.toFun p ≠ 0 → Runs D e 1) := by
  classical
  rintro ⟨D,hD,hzero,hnonzero⟩
  obtain ⟨F,f,hf,hname⟩ := haltingRealName_indices
  have hcode : NumericalComputes (numericalCompose D F)
      (fun e => if diagonalHalts e then 1 else 0) := by
    refine ⟨composeProgram_closed hD hf.1,fun e => ?_⟩
    apply composeProgram_runs hD hf.1 (hf.2 e)
    by_cases he : diagonalHalts e
    · simp only [he, ↓reduceIte]
      exact hnonzero (haltingRealNamePoint e) (f e) (hname e)
        (by rw [haltingRealName_value]; exact (haltingReal_ne_zero_iff e).mpr he)
    · simp only [he, ↓reduceIte]
      apply hzero (haltingRealNamePoint e) (f e) (hname e)
      rw [haltingRealName_value]
      exact not_ne_iff.mp (fun hn => he ((haltingReal_ne_zero_iff e).mp hn))
  apply diagonalHalts_not_decidable
  refine ⟨numericalCompose reverseZeroTerm (numericalCompose D F),?_⟩
  convert reverseZero_computes.comp hcode using 1
  funext e
  split_ifs <;> simp_all


/-- The constant rational-zero name is valid independently of its chosen index. -/
def zeroRealNamePoint : realRepresentation.domain :=
  ⟨fun _ => 0,by intro n m _; simp⟩

theorem zeroRealName_value : realRepresentation.toFun zeroRealNamePoint = 0 := by
  apply tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint zeroRealNamePoint)
  simpa only [zeroRealNamePoint,rationalPoint_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

/-- Fixing the second real to zero reduces binary equality to the impossible unary test. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    In particular, equality of two computable reals cannot be decided from arbitrary name
    indices: fixing the second input to a constant name of zero would give the forbidden test.
    \end{proof}
-/
theorem real_equality_undecidable : ¬ ∃ D : AlphaTerm, D.Closed ∧
    (∀ (p q : realRepresentation.domain) e d, ComputesName e p.val → ComputesName d q.val →
      realRepresentation.toFun p = realRepresentation.toFun q → Runs D (Nat.pair e d) 0) ∧
    (∀ (p q : realRepresentation.domain) e d, ComputesName e p.val → ComputesName d q.val →
      realRepresentation.toFun p ≠ realRepresentation.toFun q → Runs D (Nat.pair e d) 1) := by
  rintro ⟨D,hD,heq,hne⟩
  obtain ⟨j,hj⟩ := Term.closedProgram_surjective _ (numericalConstant_computes 0).1
  have hzero : ComputesName j zeroRealNamePoint.val := by
    intro n
    unfold App
    rw [hj]
    exact (numericalConstant_computes 0).2 n
  have hp := numericalIdentity_computes.pair (numericalConstant_computes j)
  apply real_zero_undecidable
  refine ⟨numericalCompose D (pairNumerical numericalIdentity (numericalConstant j)),
    composeProgram_closed hD hp.1,?_,?_⟩
  · intro p e he hz
    apply composeProgram_runs hD hp.1 (hp.2 e)
    exact heq p zeroRealNamePoint e j he hzero (by simpa only [zeroRealName_value] using hz)
  · intro p e he hn
    apply composeProgram_runs hD hp.1 (hp.2 e)
    exact hne p zeroRealNamePoint e j he hzero (by simpa only [zeroRealName_value] using hn)

/-- Three distinct numerical answer tags would in particular decide equality with zero. -/
theorem real_trichotomy_undecidable : ¬ ∃ D : AlphaTerm, D.Closed ∧
    ∀ (p : realRepresentation.domain) e, ComputesName e p.val →
      ∃ b, Runs D e b ∧
        ((b = 0 ∧ realRepresentation.toFun p < 0) ∨
         (b = 1 ∧ realRepresentation.toFun p = 0) ∨
         (b = 2 ∧ 0 < realRepresentation.toFun p)) := by
  rintro ⟨D,hD,htri⟩
  let E := numericalCombine equalityTerm numericalIdentity (numericalConstant 1)
  have hE : NumericalComputes E (fun b => if b = 1 then 1 else 0) :=
    numericalIdentity_computes.combine (numericalConstant_computes 1)
      equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply
  let Z := numericalCompose reverseZeroTerm E
  have hZ := reverseZero_computes.comp hE
  apply real_zero_undecidable
  refine ⟨numericalCompose Z D,composeProgram_closed hZ.1 hD,?_,?_⟩
  · intro p e he hz
    obtain ⟨b,hb,hcases⟩ := htri p e he
    rcases hcases with ⟨rfl,hl⟩ | ⟨rfl,_⟩ | ⟨rfl,hr⟩
    · exact (lt_irrefl 0 (hz ▸ hl)).elim
    · exact composeProgram_runs hZ.1 hD hb (by simpa using hZ.2 1)
    · exact (lt_irrefl 0 (hz ▸ hr)).elim
  · intro p e he hn
    obtain ⟨b,hb,hcases⟩ := htri p e he
    rcases hcases with ⟨rfl,_⟩ | ⟨_,hz⟩ | ⟨rfl,_⟩
    · exact composeProgram_runs hZ.1 hD hb (by simpa using hZ.2 0)
    · exact (hn hz).elim
    · exact composeProgram_runs hZ.1 hD hb (by simpa using hZ.2 2)


/-- No sound realization of the three comparisons admits a uniform disjunction choice. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: corollary
  title: Failure of real trichotomy
  excerpt: |
    \begin{corollary*}[Failure of real trichotomy]
    There is no uniform realizer deciding $x<0$, $x=0$, or $0<x$ on the chosen computable-real object $A$.
    Consequently, there is no uniform realizer of trichotomy for two arbitrary such reals.
    \end{corollary*}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Read the disjunction as $x<0\lor(x=0\lor0<x)$. A realizer of the outer left branch has the form $\NatPair{0}{a}$;
    the other two branches have the forms $\NatPair{1}{\NatPair{0}{a}}$ and $\NatPair{1}{\NatPair{1}{a}}$.
    Numerical projections and zero tests convert these to answer tags $0,1,2$, respectively. Soundness of the three
    comparison predicates ensures that the middle tag occurs exactly when $x=0$; the other two tags imply $x\ne0$.
    Testing whether the tag is the middle one gives the forbidden zero test. This only uses the supplied name index and
    soundness of the comparison realizers, and does not assume a Type-Two operator on arbitrary nonrecursive names.
    \end{proof}
-/
theorem real_no_uniform_trichotomy
    (N Z P : (computablePointAssembly realRepresentation).Carrier → Set ℕ)
    (hN : ∀ x r, r ∈ N x → x.val < 0)
    (hZ : ∀ x r, r ∈ Z x → x.val = 0)
    (hP : ∀ x r, r ∈ P x → 0 < x.val) :
    ¬ Reduces (computablePointAssembly realRepresentation).realizes
      (realizabilityOr N (realizabilityOr Z P)) := by
  intro h
  obtain ⟨r,hr⟩ := (reduces_iff _ _).mp h
  let C := numericalIfZero (numericalProjectionTerm true) (numericalConstant 0)
    (numericalIfZero (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))
      (numericalConstant 1) (numericalConstant 2))
  have hc := numericalIfZero_computes (projection_computes true) (numericalConstant_computes 0)
    (numericalIfZero_computes ((projection_computes true).comp (projection_computes false))
      (numericalConstant_computes 1) (numericalConstant_computes 2))
  apply real_trichotomy_undecidable
  refine ⟨numericalCompose C (evalProgram r),composeProgram_closed hc.1 (evalProgram_closed r),?_⟩
  intro p e he
  let x : (computablePointAssembly realRepresentation).Carrier :=
    ⟨realRepresentation.toFun p,p,rfl,e,he⟩
  have hex : e ∈ (computablePointAssembly realRepresentation).realizes x := ⟨p,rfl,he⟩
  obtain ⟨z,hz,hzmem⟩ := hr x e hex
  have hout := composeProgram_runs hc.1 (evalProgram_closed r)
    ((evalProgram_runs_iff r e z).mpr hz) (hc.2 z)
  rcases hzmem with ⟨a,ha,rfl⟩ | ⟨b,hb,rfl⟩
  · exact ⟨0,by simpa using hout,Or.inl ⟨rfl,hN x a ha⟩⟩
  · rcases hb with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · exact ⟨1,by simpa using hout,Or.inr (Or.inl ⟨rfl,hZ x a ha⟩)⟩
    · exact ⟨2,by simpa using hout,Or.inr (Or.inr ⟨rfl,hP x a ha⟩)⟩

end PolishSpaceBook.LambdaIndexPCA
