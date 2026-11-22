module

public import PolishSpaceBook.LambdaZeroSelection
public import PolishSpaceBook.LambdaAssemblyExponentials
public import PolishSpaceBook.LambdaRecursionTheorem

@[expose] public section

/-! # No zero selector on numerical function realizers

Finite certificate search and lambda self-reference diagonalize even against
selectors whose answer depends on the chosen index of the input function.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm Filter Topology
set_option maxRecDepth 4096

/-- The sign opposes the output coordinate encoded in the candidate. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    For each candidate $k=\NatPair{m}{s}$, let $b_r(e,k)$ be the finite certificate test for the computation
    $\varphi_r(e)=m$, using certificate $s$. It is computed by $\LambdaOutputCandidate$ and always terminates.
    Put $\varepsilon_k:=2^{-(k+4)}$ and choose the following explicit rational code:
    $$j_k:=\begin{cases}
    \RationalCode{0}{1}{2^{k+4}-1},&q_m<1/2,\\
    \RationalCode{1}{0}{2^{k+4}-1},&q_m\ge1/2.
    \end{cases}$$
    Thus $q_{j_k}=-\varepsilon_k$ in the first case and $q_{j_k}=\varepsilon_k$ in the second.
    The dyadic-code, rational comparison, and negation programs compute $j_k$ from $k$.
-/
def zeroDiagonalCode (k : ℕ) : ℕ :=
  if (RationalCode.ofNat k.unpair.1).value < 1/2 then
    (RationalCode.dyadic (k+4)).neg.natCode
  else (RationalCode.dyadic (k+4)).natCode

def zeroDiagonalCodeProgram : AlphaTerm :=
  let D := numericalCompose rationalDyadicTerm (addNumerical numericalIdentity (numericalConstant 4))
  let C := numericalCompose rationalLessTerm
    (pairNumerical (numericalProjectionTerm true) (numericalConstant (RationalCode.dyadic 1).natCode))
  numericalIfZero C D (numericalCompose rationalNegTerm D)

theorem zeroDiagonalCode_computes : NumericalComputes zeroDiagonalCodeProgram zeroDiagonalCode := by
  have hd := rationalDyadic_computes.comp
    (numericalIdentity_computes.add (numericalConstant_computes 4))
  have hc := rationalLess_computes.comp
    ((projection_computes true).pair (numericalConstant_computes (RationalCode.dyadic 1).natCode))
  have h := numericalIfZero_computes hc hd (rationalNeg_computes.comp hd)
  convert h using 1
  · rfl
  · funext k
    simp only [zeroDiagonalCode,Nat.unpair_pair,RationalCode.ofNat_natCode,RationalCode.value_dyadic,
      ite_true,id_eq,pow_one]
    split_ifs <;> first | rfl | contradiction

theorem zeroDiagonalCode_value (k : ℕ) : rationalPoint (zeroDiagonalCode k) =
    if rationalPoint k.unpair.1 < 1/2 then -(1/2:ℝ)^(k+4) else (1/2:ℝ)^(k+4) := by
  have h : (RationalCode.ofNat k.unpair.1).value < 1/2 ↔ rationalPoint k.unpair.1 < 1/2 := by
    unfold rationalPoint
    rw [show (1/2:ℝ) = ((1/2:ℚ):ℝ) by norm_num, Rat.cast_lt]
  simp only [zeroDiagonalCode,h]
  split_ifs <;> simp [rationalPoint]

theorem zeroDiagonalCode_abs (k : ℕ) :
    |rationalPoint (zeroDiagonalCode k)| = (1/2:ℝ)^(k+4) := by
  rw [zeroDiagonalCode_value]
  split_ifs <;> simp

theorem zeroDiagonalCode_ne_zero (k : ℕ) : zeroDiagonalCode k ≠ 0 := by
  intro h
  have hv := zeroDiagonalCode_abs k
  rw [h,rationalPoint_zero,abs_zero] at hv
  exact (ne_of_gt (pow_pos (by norm_num : (0:ℝ)<1/2) _)) hv.symm

/-- No execution of the possibly divergent program is needed at a finite stage. -/
def zeroDiagonalName (r e : ℕ) : ℕ → ℕ := primitiveRec 0 (fun k v =>
  if v = 0 then if Term.outputCandidate r e k then zeroDiagonalCode k else 0 else v)

def zeroDiagonalNameStep (r : ℕ) : AlphaTerm :=
  let E := numericalProjectionTerm true
  let K := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let V := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  numericalIfZero V
    (numericalIfZero (numericalApply3 outputCandidateTerm (numericalConstant r) E K)
      (numericalConstant 0) (numericalCompose zeroDiagonalCodeProgram K)) V

def zeroDiagonalNameProgram (r : ℕ) : AlphaTerm :=
  numericalRecursion (numericalConstant 0) (zeroDiagonalNameStep r)

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    Define, for every numerical parameter $e$,
    $$\begin{aligned}
    p_e(0)&:=0,\\
    p_e(n+1)&:=\begin{cases}
    p_e(n),&p_e(n)\ne0,\\
    j_n,&p_e(n)=0\text{ and }b_r(e,n)=1,\\
    0,&\text{otherwise}.
    \end{cases}
    \end{aligned}$$
    The parameterized recursor implements this recurrence by a closed program $P$ on input $\NatPair{e}{n}$.
    Its step extracts $e,n,v$ from $\NatPair{e}{\NatPair{n}{v}}$. If $v\ne0$, it returns $v$; otherwise it runs
    $\LambdaOutputCandidate\ChurchNumeral{r}\ChurchNumeral{e}\ChurchNumeral{n}$ and returns $0$ or $j_n$.
    Every stage is a terminating numerical computation, whether or not $R\ChurchNumeral{e}$ terminates.
-/
theorem zeroDiagonalName_computes (r : ℕ) : NumericalComputes (zeroDiagonalNameProgram r)
    (fun z => zeroDiagonalName r z.unpair.1 z.unpair.2) := by
  have he := projection_computes true
  have hk := (projection_computes true).comp (projection_computes false)
  have hv := (projection_computes false).comp (projection_computes false)
  have hc := (numericalConstant_computes r).apply3 he hk outputCandidateTerm_closed
    (fun r e k => if Term.outputCandidate r e k then 1 else 0) outputCandidateTerm_apply
  have hs := numericalIfZero_computes hv
    (numericalIfZero_computes hc (numericalConstant_computes 0) (zeroDiagonalCode_computes.comp hk)) hv
  have hz (b : Bool) (v : ℕ) :
      (if (if b then 1 else 0 : ℕ) = 0 then 0 else v) = (if b then v else 0) := by
    cases b <;> rfl
  have hs' : NumericalComputes (zeroDiagonalNameStep r) (fun z =>
      if z.unpair.2.unpair.2 = 0 then
        if Term.outputCandidate r z.unpair.1 z.unpair.2.unpair.1 then
          zeroDiagonalCode z.unpair.2.unpair.1 else 0 else z.unpair.2.unpair.2) := by
    simpa only [zeroDiagonalNameStep,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,hz] using hs
  simpa only [zeroDiagonalNameProgram,zeroDiagonalName,Nat.unpair_pair] using
    numericalRecursion_computes (numericalConstant_computes 0) hs'

theorem zeroDiagonalName_before (r e n : ℕ)
    (h : ∀ k < n, Term.outputCandidate r e k = false) : zeroDiagonalName r e n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun k hk => h k (by omega))
    change (if zeroDiagonalName r e n = 0 then
      if Term.outputCandidate r e n then _ else 0 else _) = 0
    simp [hn,h n (by omega)]

theorem zeroDiagonalName_first (r e k : ℕ) (hk : Term.outputCandidate r e k = true)
    (hbefore : ∀ j < k, Term.outputCandidate r e j = false) (n : ℕ) :
    zeroDiagonalName r e n = if n ≤ k then 0 else zeroDiagonalCode k := by
  induction n with
  | zero => simp [zeroDiagonalName,primitiveRec]
  | succ n ih =>
    change (if zeroDiagonalName r e n = 0 then
      if Term.outputCandidate r e n then _ else 0 else _) = _
    rw [ih]
    by_cases hn : n < k
    · simp [show n ≤ k by omega,show n+1 ≤ k by omega,hbefore n hn]
    · by_cases he : n = k
      · subst n; simp [hk]
      · simp only [ite_eq_right (show ¬ n ≤ k by omega),ite_eq_right (show ¬ n+1 ≤ k by omega),
          zeroDiagonalCode_ne_zero,ite_false]
        exact ih.trans (ite_eq_right (by omega))

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    If no candidate is accepted, $p_e$ is the constant-zero name. Otherwise let $k$ be the first accepted candidate.
    The code $j_k$ is nonzero, and induction gives
    $$p_e(n)=\begin{cases}0,&n\le k,\\j_k,&n>k.\end{cases}$$
    For $n\le k<m$, the only case in which two approximants differ, their distance is
    $\varepsilon_k\le2^{-n}$. Thus every $p_e$ is a Cauchy name. Its value $a_e$ is either zero or $q_{j_k}$,
    and always satisfies $|a_e|\le1/16<1/4$. This validity argument does not assume that the selector terminates.
-/
theorem zeroDiagonalName_isCauchy (r e : ℕ) : IsCauchyName rationalPoint (zeroDiagonalName r e) := by
  classical
  by_cases h : ∃ k, Term.outputCandidate r e k = true
  · let k := Nat.find h
    have hbefore : ∀ j < k, Term.outputCandidate r e j = false :=
      fun j hj => Bool.eq_false_iff.mpr (Nat.find_min h hj)
    have hname := zeroDiagonalName_first r e k (Nat.find_spec h) hbefore
    intro n m hnm
    rw [hname n,hname m]
    by_cases hn : n ≤ k <;> by_cases hm : m ≤ k
    · simp [hn,hm]
    · simp only [ite_eq_left hn,ite_eq_right hm,rationalPoint_zero,Real.dist_eq,zero_sub,abs_neg,
        zeroDiagonalCode_abs]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · omega
    · simp [hn,hm]
  · have hz (n : ℕ) : zeroDiagonalName r e n = 0 := zeroDiagonalName_before r e n
      (fun k _ => Bool.eq_false_iff.mpr (fun hk => h ⟨k,hk⟩))
    intro n m _
    simp [hz]

def zeroDiagonalNamePoint (r e : ℕ) : realRepresentation.domain :=
  ⟨zeroDiagonalName r e,zeroDiagonalName_isCauchy r e⟩

theorem zeroDiagonalName_value (r e k : ℕ) (hk : Term.outputCandidate r e k = true)
    (hbefore : ∀ j < k, Term.outputCandidate r e j = false) :
    realRepresentation.toFun (zeroDiagonalNamePoint r e) = rationalPoint (zeroDiagonalCode k) := by
  apply tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint (zeroDiagonalNamePoint r e))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop k] with n hn
  change _ = rationalPoint (zeroDiagonalName r e n)
  rw [zeroDiagonalName_first r e k hk hbefore n,ite_eq_right (by omega)]

theorem zeroDiagonalName_small (r e : ℕ) :
    |realRepresentation.toFun (zeroDiagonalNamePoint r e)| < 1/4 := by
  classical
  by_cases h : ∃ k, Term.outputCandidate r e k = true
  · rw [zeroDiagonalName_value r e (Nat.find h) (Nat.find_spec h)
      (fun j hj => Bool.eq_false_iff.mpr (Nat.find_min h hj)),zeroDiagonalCode_abs]
    have hb : (1/2:ℝ)^(Nat.find h+4) ≤ (1/2:ℝ)^4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hb ⊢
    linarith
  · have hz (n : ℕ) : zeroDiagonalName r e n = 0 := zeroDiagonalName_before r e n
      (fun k _ => Bool.eq_false_iff.mpr (fun hk => h ⟨k,hk⟩))
    have hv : realRepresentation.toFun (zeroDiagonalNamePoint r e) = 0 := by
      apply tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint (zeroDiagonalNamePoint r e))
      have : (fun n => rationalPoint ((zeroDiagonalNamePoint r e).val n)) = fun _ => (0:ℝ) := by
        funext n; change rationalPoint (zeroDiagonalName r e n) = 0; rw [hz,rationalPoint_zero]
      rw [this]
      exact tendsto_const_nhds
    rw [hv]; norm_num

/-- The output may depend on the name index; no extensionality is assumed. -/
def SelectsIndexedPlateauZeros (D : AlphaTerm) : Prop :=
  ∀ (p : realRepresentation.domain) e, ComputesName e p.val →
    |realRepresentation.toFun p| < 1/4 →
    ∃ (d : ℕ) (q : realRepresentation.domain), Runs D e d ∧ ComputesName d q.val ∧
      plateauFunction (realRepresentation.toFun p) (realRepresentation.toFun q) = 0

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    Now apply self-reference to the closed binary program
    $$H:=\lambdaab{z}{\lambdaab{n}{P(\LambdaNumericPair\,z\,n)}}.$$
    It supplies an index $e$ with
    $$\varphi_e(n)=p_e(n)\qquad\text{for every }n.$$
    Indeed, the self-reference reductions give
    $P_e\ChurchNumeral{n}\to_\beta^*H\ChurchNumeral{e}\ChurchNumeral{n}$,
    and pairing followed by the computation of $P$ returns $\ChurchNumeral{p_e(n)}$.
    Hence $e$ is an index of the valid name just constructed. The hypothesis on $D$ now forces
    $D\ChurchNumeral{e}$ to return an index $d$ of a name $u$ of a zero $x$ of $f_{a_e}$.
    Consequently $R\ChurchNumeral{e}$ returns $\ChurchNumeral{c}$ with $c=u(3)$.
    Some certificate is accepted, and numerical output uniqueness implies that the output component of the
    first accepted candidate $k$ is exactly $c$.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    First suppose that a closed program $D$ takes any index $e$ of a Cauchy name $p$ of $a$ with $|a|<1/4$
    and returns an index $d$ of a Cauchy name of a zero of the preceding function $f_a$.
    Let $U:=\LambdaOutputSearch$, and fix an index $r$ of the closed program
    $$R:=\lambdaab{z}{U(Dz)\ChurchNumeral{3}}.$$
    Thus, whenever the selector returns a valid name index, $R$ computes coordinate $3$ of that name.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    The Cauchy error bound gives $|x-q_c|\le1/8$. If $q_c<1/2$, our construction makes
    $a_e=-\varepsilon_k<0$, so the plateau lemma gives $x>3/4$, whereas
    $x\le q_c+1/8<5/8$. If $q_c\ge1/2$, it makes $a_e=\varepsilon_k>0$, so the lemma gives
    $x<1/4$, whereas $x\ge q_c-1/8\ge3/8$. Both cases are impossible.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    We now treat numerical realizers of the function assembly from §{sec:effective-topos-assembly-functions}.
    An index can be inspected as a natural number, so the preceding finite-query argument does not apply directly.
    Instead, finite certificate search and the self-reference construction in §{sec:lambda-index-recursion}
    produce an input whose zeros contradict the proposed selector's own output.
-/
theorem no_indexed_plateau_zero_selector (D : AlphaTerm) (hD : D.Closed) :
    ¬ SelectsIndexedPlateauZeros D := by
  intro hS
  let R := numericalCombine outputSearchTerm D (numericalConstant 3)
  have hR : R.Closed := combineProgram_closed outputSearchTerm_closed hD (numericalConstant_computes 3).1
  obtain ⟨r,hr⟩ := Term.closedProgram_surjective R hR
  have hP := zeroDiagonalName_computes r
  obtain ⟨e,he⟩ := exists_self_reference (curryNumerical (zeroDiagonalNameProgram r))
    (curryNumerical_closed hP.1)
  have hname : ComputesName e (zeroDiagonalName r e) := by
    intro n
    exact (he (numeral n) (by rw [numeral_closed]; simp)).trans
      ((curryNumerical_apply hP.1 e n).trans (by simpa only [Nat.unpair_pair] using hP.2 (Nat.pair e n)))
  obtain ⟨d,q,hDd,hdq,hzero⟩ := hS (zeroDiagonalNamePoint r e) e hname (zeroDiagonalName_small r e)
  have hrun : App r e (q.val 3) := by
    unfold App; rw [hr]
    exact combineProgram_runs outputSearchTerm_closed hD (numericalConstant_computes 3).1
      hDd ((numericalConstant_computes 3).2 e) ((outputSearchTerm_runs_iff d 3 (q.val 3)).mpr (hdq 3))
  obtain ⟨s,hs⟩ := (outputTest_exists_iff r e (q.val 3)).mpr hrun
  have hex : ∃ k, Term.outputCandidate r e k = true :=
    ⟨Nat.pair (q.val 3) s,by simpa [Term.outputCandidate] using hs⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hbefore : ∀ j < k, Term.outputCandidate r e j = false :=
    fun j hj => Bool.eq_false_iff.mpr (Nat.find_min hex hj)
  have hout : k.unpair.1 = q.val 3 :=
    app_unique ((outputTest_exists_iff r e k.unpair.1).mp ⟨k.unpair.2,hk⟩) hrun
  have hv := zeroDiagonalName_value r e k hk hbefore
  rw [zeroDiagonalCode_value,hout] at hv
  have hb := cauchyRepresentation_dist_le rationalPoint q 3
  change dist (rationalPoint (q.val 3)) (realRepresentation.toFun q) ≤ (1/2:ℝ)^3 at hb
  rw [Real.dist_eq,abs_le] at hb
  have hpos : (0:ℝ) < (1/2:ℝ)^(k+4) := pow_pos (by norm_num) _
  by_cases hc : rationalPoint (q.val 3) < 1/2
  · rw [ite_eq_left hc] at hv
    have hz := plateauFunction_negative_root (by rw [hv]; linarith) hzero
    norm_num at hb
    linarith
  · rw [ite_eq_right hc] at hv
    have hz := plateauFunction_positive_root (by rw [hv]; exact hpos) hzero
    norm_num at hb
    linarith

/-- The actual assembly map used to compile a parameter name into a function tracker. -/
noncomputable def plateauAssemblyMap : Assembly.Hom
    (Assembly.prod (computablePointAssembly realRepresentation) (computablePointAssembly realRepresentation))
    (computablePointAssembly realRepresentation) :=
  (computablePointPair realRepresentation realRepresentation).comp
    (computablePointMap plateau_hasComputableRealizer)

/-- A semantic promise on the input function; it supplies no oracle or proof program. -/
def HasZeroSelectionPromise (f : Assembly.Hom (computablePointAssembly realRepresentation)
    (computablePointAssembly realRepresentation)) : Prop :=
  ∃ g : ℝ → ℝ, Continuous g ∧ g 0 < 0 ∧ 0 < g 1 ∧
    (∀ n x y, dist x y ≤ (1/2:ℝ)^(n+1) → dist (g x) (g y) ≤ (1/2:ℝ)^n) ∧
    ∀ x, (f.toFun x).val = g x.val

/-- Uniform numerical selection on function realizers, without extensionality of the selection. -/
def SelectsAssemblyZeros (D : AlphaTerm) : Prop :=
  ∀ (f : Assembly.Hom (computablePointAssembly realRepresentation) (computablePointAssembly realRepresentation)) e,
    e ∈ (Assembly.exponential (computablePointAssembly realRepresentation)
      (computablePointAssembly realRepresentation)).realizes f → HasZeroSelectionPromise f →
    ∃ (d : ℕ) (x : (computablePointAssembly realRepresentation).Carrier), Runs D e d ∧
      d ∈ (computablePointAssembly realRepresentation).realizes x ∧
      x.val ∈ Set.Icc (0:ℝ) 1 ∧ (f.toFun x).val = 0

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: No zero selection on function indices
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    Finally, the computable map $(a,x)\mapsto f_a(x)$ and the product construction induce an assembly morphism
    $h:A\times A\to A$. By the explicit currying construction, one total numerical program $C$ sends every
    name index $e$ of $a$ to a tracker $t(e)$ of the section $x\mapsto f_a(x)$.
    For $|a|<1/4$, this section has the continuous extension and the common modulus required in the theorem.
    If $S$ selected zeros from all such function trackers, then
    $$D:=\lambdaab{z}{S(Cz)}$$
    would satisfy the parameter-index selection hypothesis already contradicted. The beta reductions for composition
    and the total code factory justify this passage on every valid name index.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    A function name supplies information through queries, whereas a function tracker is a natural number on which a
    program can perform numerical computations. We keep the two selection problems separate: the first proof uses finite
    query dependence, and the second uses finite certificate search and self-reference. Both distinguish the existence of
    a zero from a uniform procedure that selects one from the specified input evidence.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    We now treat numerical realizers of the function assembly from §{sec:effective-topos-assembly-functions}.
    An index can be inspected as a natural number, so the preceding finite-query argument does not apply directly.
    Instead, finite certificate search and the self-reference construction in §{sec:lambda-index-recursion}
    produce an input whose zeros contradict the proposed selector's own output.
-/
theorem no_assembly_zero_selector (D : AlphaTerm) (hD : D.Closed) : ¬ SelectsAssemblyZeros D := by
  intro hS
  obtain ⟨t,⟨c,hc⟩,ht⟩ := Assembly.curry_indices plateauAssemblyMap
  let P := numericalCompose D (evalProgram c)
  apply no_indexed_plateau_zero_selector P (composeProgram_closed hD (evalProgram_closed c))
  intro p e he ha
  let a : (computablePointAssembly realRepresentation).Carrier :=
    ⟨realRepresentation.toFun p,⟨p,rfl,e,he⟩⟩
  let f := plateauAssemblyMap.section a
  have hf : t e ∈ (Assembly.exponential (computablePointAssembly realRepresentation)
      (computablePointAssembly realRepresentation)).realizes f := ht a e ⟨p,rfl,he⟩
  have hpromise : HasZeroSelectionPromise f := by
    obtain ⟨hl,hu⟩ := plateauFunction_endpoints ha
    exact ⟨plateauFunction a.val,plateauFunction_continuous _,hl,hu,
      fun n x y h => plateauFunction_modulus _ n h,fun x => rfl⟩
  obtain ⟨d,x,hDd,hx,_,hz⟩ := hS f (t e) hf hpromise
  obtain ⟨q,hq,hdq⟩ := hx
  refine ⟨d,q,composeProgram_runs hD (evalProgram_closed c)
    ((evalProgram_runs_iff c e (t e)).mpr (hc e)) hDd,hdq,?_⟩
  change plateauFunction a.val (realRepresentation.toFun q) = 0
  rw [hq]
  exact hz

/-- Restrict the function assembly by the semantic promises, keeping its realizers. -/
def zeroSelectionDomain : Assembly where
  Carrier := {f : Assembly.Hom (computablePointAssembly realRepresentation)
    (computablePointAssembly realRepresentation) // HasZeroSelectionPromise f}
  realizes f := (Assembly.exponential (computablePointAssembly realRepresentation)
    (computablePointAssembly realRepresentation)).realizes f.val
  inhabited f := (Assembly.exponential (computablePointAssembly realRepresentation)
    (computablePointAssembly realRepresentation)).inhabited f.val

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    This excludes a tracked zero-selection morphism on the subassembly defined by these promises.
    The index proof is stronger than that conclusion: it did not require the selected zero to depend only on the
    underlying function. It also does not deny the existence of zeros for individual inputs, or identify this promise
    subassembly with an unspecified internal space of all continuous functions.
-/
theorem no_zero_selection_morphism :
    ¬ ∃ F : Assembly.Hom zeroSelectionDomain (computablePointAssembly realRepresentation),
      ∀ f, (F.toFun f).val ∈ Set.Icc (0:ℝ) 1 ∧ (f.val.toFun (F.toFun f)).val = 0 := by
  rintro ⟨F,hF⟩
  obtain ⟨s,hs⟩ := (reduces_iff _ _).mp F.tracked
  apply no_assembly_zero_selector (evalProgram s) (evalProgram_closed s)
  intro f e he hf
  obtain ⟨d,hd,hdx⟩ := hs ⟨f,hf⟩ e he
  exact ⟨d,F.toFun ⟨f,hf⟩,(evalProgram_runs_iff s e d).mpr hd,hdx,hF ⟨f,hf⟩⟩

end PolishSpaceBook.LambdaIndexPCA
