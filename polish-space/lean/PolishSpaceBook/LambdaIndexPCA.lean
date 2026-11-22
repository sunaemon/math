module

public import PolishSpaceBook.LambdaNumericalResultSearch
public import Mathlib.Data.Part

@[expose] public section

/-! # A partial combinatory algebra of lambda program indices

The partial application graph is numerical beta reduction in the existing
closed-program enumeration. The S operation searches three finite reduction
certificates together, so its exact domain includes both intermediate values.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
/-- A PCA with Kleene equality expressed as equality of partial values.
`bind` enforces that all intermediate applications are defined. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: definition
-/
structure PartialCombinatoryAlgebra (A : Type*) where
  application : A → A → Part A
  k : A
  s : A
  k_defined : ∀ a, (application k a).Dom
  k_law : ∀ a b, (application k a).bind (fun u => application u b) = Part.some a
  s_defined : ∀ a b, ((application s a).bind (fun u => application u b)).Dom
  s_law : ∀ a b c,
    ((application s a).bind (fun u => application u b)).bind (fun v => application v c) =
      (application a c).bind (fun u => (application b c).bind (fun v => application u v))

namespace LambdaIndexPCA
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

/-- Numerical application in the fixed lambda-program enumeration. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    **Kleene's first algebra $K_1$.** The carrier is $\NN$, and application is
    $$e\cdot n\simeq\varphi_e(n),\qquad
    \varphi_e(n)=m\quad\Longleftrightarrow\quad P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}.$$
    Here $P_e$ is the closed lambda program with index $e$ from §{sec:lambda-indices}. Uniqueness of numerical outputs
    makes this a partial function. This is the algebra underlying $\EffCat$. We construct its combinators using the
    lambda programs for syntax codes and finite reduction certificates from §{sec:lambda-input-universal-evaluation}.
-/
def App (e n m : ℕ) : Prop :=
  Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m)

theorem app_unique {e n x y : ℕ} (hx : App e n x) (hy : App e n y) : x = y :=
  numeral_output_unique hx hy

/-- All three partial applications must have numerical values. -/
def SGraph (a b c m : ℕ) : Prop :=
  ∃ x y, App a c x ∧ App b c y ∧ App x y m

theorem sGraph_unique {a b c x y : ℕ} (hx : SGraph a b c x) (hy : SGraph a b c y) : x = y := by
  obtain ⟨u,v,hu,hv,hx⟩ := hx
  obtain ⟨u',v',hu',hv',hy⟩ := hy
  cases app_unique hu hu'
  cases app_unique hv hv'
  exact app_unique hx hy

def candidateValue (e n k : ℕ) : ℕ := if Term.outputCandidate e n k then 1 else 0

/-- Input `z` codes `(a,(b,c))`; candidate `t` codes three output/trace pairs. -/
def sTrial (w : ℕ) : ℕ :=
  let z := w.unpair.1
  let t := w.unpair.2
  candidateValue z.unpair.1 z.unpair.2.unpair.2 t.unpair.1 *
    candidateValue z.unpair.2.unpair.1 z.unpair.2.unpair.2 t.unpair.2.unpair.1 *
    candidateValue t.unpair.1.unpair.1 t.unpair.2.unpair.1.unpair.1 t.unpair.2.unpair.2

def sResult (t : ℕ) : ℕ := t.unpair.2.unpair.2.unpair.1

def sTrialProgram : AlphaTerm :=
  let L := numericalProjectionTerm true
  let R := numericalProjectionTerm false
  let a := numericalCompose L L
  let b := numericalCompose L (numericalCompose R L)
  let c := numericalCompose R (numericalCompose R L)
  let t1 := numericalCompose L R
  let t2 := numericalCompose L (numericalCompose R R)
  let t3 := numericalCompose R (numericalCompose R R)
  mulNumerical (mulNumerical
    (numericalApply3 outputCandidateTerm a c t1)
    (numericalApply3 outputCandidateTerm b c t2))
    (numericalApply3 outputCandidateTerm (numericalCompose L t1) (numericalCompose L t2) t3)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    For $\mathsf s$, the final computation must have a numerical output precisely when all three applications
    $a\cdot c$, $b\cdot c$, and $(a\cdot c)\cdot(b\cdot c)$ have values. Let $C(e,n,t)\in\{0,1\}$ be the numerical
    answer of $\LambdaOutputCandidate$ on these inputs. Thus if $t=\NatPair{m}{r}$, success certifies a finite reduction
    of $P_e\ChurchNumeral{n}$ to $\ChurchNumeral{m}$, and every such reduction is accepted at some bound $r$.
    Encode an input and a trial by
    $$
    \begin{aligned}
    z&=\NatPair{a}{\NatPair{b}{c}},&
    t&=\NatPair{v_1}{\NatPair{v_2}{v_3}},\\
    v_1&=\NatPair{x}{r_1},&v_2&=\NatPair{y}{r_2},\qquad v_3=\NatPair{m}{r_3}.
    \end{aligned}
    $$
    The total trial function is
    $$T(z,t):=C(a,c,v_1)\,C(b,c,v_2)\,C(x,y,v_3).$$
    Numerical projections, three applications of the candidate tester, and multiplication give a closed lambda program
    $\mathcal T$ computing $T$ on the paired input $\NatPair{z}{t}$. A successful trial certifies exactly
    $$a\cdot c=x,\qquad b\cdot c=y,\qquad x\cdot y=m.$$
-/
theorem sTrialProgram_computes : NumericalComputes sTrialProgram sTrial := by
  have hL := projection_computes true
  have hR := projection_computes false
  have hc := hR.comp (hR.comp hL)
  have h1 := (hL.comp hL).apply3 hc (hL.comp hR) outputCandidateTerm_closed candidateValue outputCandidateTerm_apply
  have h2 := (hL.comp (hR.comp hL)).apply3 hc (hL.comp (hR.comp hR))
    outputCandidateTerm_closed candidateValue outputCandidateTerm_apply
  have h3 := (hL.comp (hL.comp hR)).apply3 (hL.comp (hL.comp (hR.comp hR)))
    (hR.comp (hR.comp hR)) outputCandidateTerm_closed candidateValue outputCandidateTerm_apply
  exact (h1.mul h2).mul h3

def sResultProgram : AlphaTerm := numericalCompose (numericalProjectionTerm true)
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))

theorem sResultProgram_computes : NumericalComputes sResultProgram sResult :=
  (projection_computes true).comp ((projection_computes false).comp (projection_computes false))

theorem sTrial_nonzero (z t : ℕ) : sTrial (Nat.pair z t) ≠ 0 ↔
    Term.outputCandidate z.unpair.1 z.unpair.2.unpair.2 t.unpair.1 = true ∧
    Term.outputCandidate z.unpair.2.unpair.1 z.unpair.2.unpair.2 t.unpair.2.unpair.1 = true ∧
    Term.outputCandidate t.unpair.1.unpair.1 t.unpair.2.unpair.1.unpair.1 t.unpair.2.unpair.2 = true := by
  simp [sTrial,candidateValue]
  tauto

theorem sTrial_sound {z t : ℕ} (h : sTrial (Nat.pair z t) ≠ 0) :
    SGraph z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2 (sResult t) := by
  obtain ⟨h1,h2,h3⟩ := (sTrial_nonzero z t).mp h
  exact ⟨t.unpair.1.unpair.1,t.unpair.2.unpair.1.unpair.1,
    (outputTest_exists_iff _ _ _).mp ⟨_,h1⟩,
    (outputTest_exists_iff _ _ _).mp ⟨_,h2⟩,
    (outputTest_exists_iff _ _ _).mp ⟨_,h3⟩⟩

theorem sTrial_complete {z m : ℕ}
    (h : SGraph z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2 m) :
    ∃ t, sTrial (Nat.pair z t) ≠ 0 ∧ sResult t = m := by
  obtain ⟨x,y,hx,hy,hm⟩ := h
  obtain ⟨sx,hsx⟩ := (outputTest_exists_iff _ _ _).mpr hx
  obtain ⟨sy,hsy⟩ := (outputTest_exists_iff _ _ _).mpr hy
  obtain ⟨sm,hsm⟩ := (outputTest_exists_iff _ _ _).mpr hm
  refine ⟨Nat.pair (Nat.pair x sx) (Nat.pair (Nat.pair y sy) (Nat.pair m sm)),?_,by simp [sResult]⟩
  rw [sTrial_nonzero]
  simpa only [Nat.unpair_pair,Term.outputCandidate] using And.intro hsx (And.intro hsy hsm)

def sSearchProgram : AlphaTerm := numericalResultSearch sTrialProgram sResultProgram

theorem sSearchProgram_closed : sSearchProgram.Closed :=
  numericalResultSearch_closed sTrialProgram_computes sResultProgram_computes

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    Let $F$ extract $m$ from the trial code and search for a successful trial:
    $$
    \begin{aligned}
    F&:=\lambdaab{t}{\LambdaNumericProjection{1}
      (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}\,t))},\\
    Q&:=\lambdaab{z}{\LambdaResultSearch
      \bigl(\lambdaab{t}{\LambdaZeroTest\,(\mathcal T(\LambdaNumericPair\,z\,t))
        \,\ChurchNumeral{1}\,\ChurchNumeral{0}}\bigr)\,F}.
    \end{aligned}
    $$
    All these terms are closed. The zero test reverses the trial answer because result search stops at zero.
    If the three applications have values, their finite certificates give a successful trial. Every successful trial has
    the same output, by uniqueness of the two intermediate values and the final value. Result search therefore returns
    that value. If any required application lacks a value, every trial fails; the no-output part of the result-search
    lemma excludes every numerical output, regardless of reduction order. Consequently
    $$
    Q\ChurchNumeral{\NatPair{a}{\NatPair{b}{c}}}\to_\beta^*\ChurchNumeral{m}
    \quad\Longleftrightarrow\quad
    \exists x,y\;\bigl(a\cdot c=x\ \land\ b\cdot c=y\ \land\ x\cdot y=m\bigr).
    $$
-/
theorem sSearchProgram_runs_iff (a b c m : ℕ) :
    Relation.ReflTransGen Beta (app sSearchProgram (numeral (Nat.pair a (Nat.pair b c)))) (numeral m) ↔
      SGraph a b c m := by
  have hu (z i j : ℕ) (hi : sTrial (Nat.pair z i) ≠ 0) (hj : sTrial (Nat.pair z j) ≠ 0) :
      sResult i = sResult j := sGraph_unique (sTrial_sound hi) (sTrial_sound hj)
  rw [sSearchProgram,numericalResultSearch_runs_iff sTrialProgram_computes sResultProgram_computes
    _ _ (hu _)]
  constructor
  · rintro ⟨t,ht,rfl⟩
    simpa only [Nat.unpair_pair] using sTrial_sound ht
  · intro h
    apply sTrial_complete (z := Nat.pair a (Nat.pair b c))
    simpa only [Nat.unpair_pair] using h

/-- The syntax code of a constant numerical program. -/
def constantCode (a : ℕ) : ℕ := (Term.lam 40 (Term.churchNumeral a)).code

theorem closedProgram_code_of_closed (M : Term) (hM : (mk M).Closed) :
    Term.closedProgram M.code = mk M := by
  have hc : M.fv = ∅ := hM
  simp only [Term.closedProgram,Term.decode_code,hc,ite_true]

theorem constantCode_program (a : ℕ) : Term.closedProgram (constantCode a) = numericalConstant a := by
  have hm : mk (Term.lam 40 (Term.churchNumeral a)) = numericalConstant a := by
    change lam 40 (mk (Term.churchNumeral a)) = _
    rw [Term.mk_churchNumeral]
    rfl
  exact (closedProgram_code_of_closed _ (hm.symm ▸ (numericalConstant_computes a).1)).trans hm

theorem constantCode_apply (a b : ℕ) : App (constantCode a) b a := by
  unfold App
  rw [constantCode_program]
  exact (numericalConstant_computes a).2 b

theorem constantCode_computes : ∃ K, NumericalComputes K constantCode := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  exact ⟨_,hn.abstractionCode 40⟩

def sBody (a b : ℕ) : AlphaTerm := lam 42 (app sSearchProgram
  (app (app numericalPairTerm (numeral a)) (app (app numericalPairTerm (numeral b)) (var 42))))

theorem sBody_closed (a b : ℕ) : (sBody a b).Closed := by
  unfold sBody Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [sSearchProgram_closed,numericalPairTerm_closed,numeral_closed,numeral_closed]
  decide

theorem sBody_start (a b c : ℕ) :
    Relation.ReflTransGen Beta (app (sBody a b) (numeral c))
      (app sSearchProgram (numeral (Nat.pair a (Nat.pair b c)))) := by
  have hs : Beta (app (sBody a b) (numeral c)) (app sSearchProgram
      (app (app numericalPairTerm (numeral a)) (app (app numericalPairTerm (numeral b)) (numeral c)))) := by
    simpa only [sBody,subst_app,subst_var,ite_true,
      subst_closed _ _ _ sSearchProgram_closed,subst_closed _ _ _ numericalPairTerm_closed,
      subst_closed _ _ _ (numeral_closed a),subst_closed _ _ _ (numeral_closed b)] using
      Beta.contract 42 (app sSearchProgram
        (app (app numericalPairTerm (numeral a)) (app (app numericalPairTerm (numeral b)) (var 42)))) (numeral c)
  exact (Relation.ReflTransGen.single hs).trans (beta_steps_app_right sSearchProgram
    ((beta_steps_app_right (app numericalPairTerm (numeral a)) (numericalPairTerm_apply b c)).trans
      (numericalPairTerm_apply a (Nat.pair b c))))

theorem sBody_runs_iff (a b c m : ℕ) :
    Relation.ReflTransGen Beta (app (sBody a b) (numeral c)) (numeral m) ↔ SGraph a b c m := by
  rw [← sSearchProgram_runs_iff]
  exact ⟨numeral_after_reduction (sBody_start a b c),fun h => (sBody_start a b c).trans h⟩

def sBodySyntax (R B : Term) (a b : ℕ) : Term := .lam 42 (.app R
  (.app (.app B (Term.churchNumeral a)) (.app (.app B (Term.churchNumeral b)) (.var 42))))

theorem sBodySyntax_mk (R B : Term) (hR : mk R = sSearchProgram) (hB : mk B = numericalPairTerm)
    (a b : ℕ) : mk (sBodySyntax R B a b) = sBody a b := by
  change lam 42 (app (mk R) (app (app (mk B) (mk (Term.churchNumeral a)))
    (app (app (mk B) (mk (Term.churchNumeral b))) (var 42)))) = _
  rw [hR,hB,Term.mk_churchNumeral,Term.mk_churchNumeral]
  rfl

theorem sBodySyntax_program (R B : Term) (hR : mk R = sSearchProgram) (hB : mk B = numericalPairTerm)
    (a b : ℕ) : Term.closedProgram (sBodySyntax R B a b).code = sBody a b := by
  have hm := sBodySyntax_mk R B hR hB a b
  exact (closedProgram_code_of_closed _ (hm.symm ▸ sBody_closed a b)).trans hm

theorem sBodyCode_computes (R B : Term) :
    ∃ G, NumericalComputes G (fun w => (sBodySyntax R B w.unpair.1 w.unpair.2).code) := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  have ha := (numericalConstant_computes B.code).applicationCode (hn.comp (projection_computes true))
  have hb := ((numericalConstant_computes B.code).applicationCode
    (hn.comp (projection_computes false))).applicationCode (numericalConstant_computes (Term.var 42).code)
  exact ⟨_,((numericalConstant_computes R.code).applicationCode (ha.applicationCode hb)).abstractionCode 42⟩

/-- K is an index computing codes of constant functions, not the raw lambda K term. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    For $\mathsf k$, fix a variable name $u$ and put
    $$\kappa(a):=\LambdaSyntaxCode{\lambdaab{u}{\ChurchNumeral{a}}}.$$
    The numeral-code and abstraction-code programs compute this total numerical function. Choose an index
    $\mathsf k$ for that closed numerical program. Then
    $$
    \mathsf k\cdot a=\kappa(a),\qquad \kappa(a)\cdot b=a.
    $$
    The first application constructs a constant program's code; the second executes that constant program. Both are
    always defined. In particular, $\mathsf k$ is a numerical index computing codes, rather than the raw term
    $\lambdaab{x}{\lambdaab{y}{x}}$.
-/
theorem exists_k_index : ∃ k, ∀ a, App k a (constantCode a) := by
  obtain ⟨K,hK⟩ := constantCode_computes
  obtain ⟨k,hk⟩ := Term.closedProgram_surjective K hK.1
  refine ⟨k,fun a => ?_⟩
  unfold App
  rw [hk]
  exact hK.2 a

/-- Both preliminary applications of S are total syntax computations. Only
its third argument starts the search for the three application certificates. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    It remains to delay this computation until the third argument. Fix named representatives of $Q$ and numerical
    pairing, and define
    $$\sigma(a,b):=\LambdaSyntaxCode{\lambdaab{u}{
     Q(\LambdaNumericPair\,\ChurchNumeral{a}\,(\LambdaNumericPair\,\ChurchNumeral{b}\,u))}}.$$
    This is a total syntax operation: numeral-code, application-code, and abstraction-code programs compute it without
    executing $Q$. Let $G$ be the resulting closed program on the paired input, and put
    $$H:=\lambdaab{a}{\lambdaab{b}{G(\LambdaNumericPair\,a\,b)}},\qquad
    \sigma_0(a):=\LambdaSyntaxCode{H\ChurchNumeral{a}}.$$
    Fix a named representative of $H$. The function $\sigma_0$ is again a total computed syntax operation, so choose an
    index $\mathsf s$ for its program. Then
    $$\mathsf s\cdot a=\sigma_0(a),\qquad \sigma_0(a)\cdot b=\sigma(a,b).$$
    Both applications are always defined. Applying the program with code $\sigma(a,b)$ to $\ChurchNumeral{c}$ reduces
    to $Q\ChurchNumeral{\NatPair{a}{\NatPair{b}{c}}}$. The exact-output equivalence above therefore proves
    $$\mathsf s\cdot a\cdot b\cdot c\simeq(a\cdot c)\cdot(b\cdot c),$$
    including the case where either side is undefined. This completes the construction using only lambda terms and
    beta reduction.
-/
theorem exists_s_index :
    ∃ (s : ℕ) (first : ℕ → ℕ) (body : ℕ → ℕ → ℕ),
      (∀ a, App s a (first a)) ∧
      (∀ a b, App (first a) b (body a b)) ∧
      ∀ a b c m, App (body a b) c m ↔ SGraph a b c m := by
  obtain ⟨R,hR⟩ := Quotient.exists_rep sSearchProgram
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨G,hG⟩ := sBodyCode_computes R B
  obtain ⟨H,hH⟩ := Quotient.exists_rep (curryNumerical G)
  have hH' : mk H = curryNumerical G := hH
  let first (a : ℕ) := (Term.app H (Term.churchNumeral a)).code
  have hfirstProgram (a : ℕ) : Term.closedProgram (first a) = app (curryNumerical G) (numeral a) := by
    have hm : mk (Term.app H (Term.churchNumeral a)) = app (curryNumerical G) (numeral a) := by
      change app (mk H) (mk (Term.churchNumeral a)) = _
      rw [hH',Term.mk_churchNumeral]
    exact (closedProgram_code_of_closed _ (hm.symm ▸ closed_app (curryNumerical_closed hG.1) (numeral_closed a))).trans hm
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  have hf := (numericalConstant_computes H.code).applicationCode hn
  obtain ⟨s,hs⟩ := Term.closedProgram_surjective _ hf.1
  refine ⟨s,first,
    fun a b => (sBodySyntax R B a b).code,?_,?_,?_⟩
  · intro a
    unfold App
    rw [hs]
    exact hf.2 a
  · intro a b
    unfold App
    rw [hfirstProgram]
    exact (curryNumerical_apply hG.1 a b).trans (by simpa only [Nat.unpair_pair] using hG.2 (Nat.pair a b))
  · intro a b c m
    unfold App
    rw [sBodySyntax_program R B hR hB]
    exact sBody_runs_iff a b c m

/-- The canonical partial-value type packages the functional beta-reduction graph. -/
noncomputable def application (e n : ℕ) : Part ℕ where
  Dom := ∃ m, App e n m
  get h := h.choose

theorem mem_application_iff (e n m : ℕ) : m ∈ application e n ↔ App e n m := by
  change (∃ h : ∃ m, App e n m, h.choose = m) ↔ App e n m
  constructor
  · rintro ⟨h,rfl⟩
    exact h.choose_spec
  · intro h
    refine ⟨⟨m,h⟩,?_⟩
    exact app_unique (Exists.choose_spec (⟨m,h⟩ : ∃ m, App e n m)) h

theorem application_eq_some {e n m : ℕ} (h : App e n m) : application e n = Part.some m :=
  Part.eq_some_iff.mpr ((mem_application_iff e n m).mpr h)

/-- The existing numerical lambda evaluator supplies a PCA, with exact equality
of domains in the S law. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Lambda indices form a partial combinatory algebra
-/
theorem exists_indexPCA : ∃ K : PartialCombinatoryAlgebra ℕ, K.application = application := by
  obtain ⟨k,hk⟩ := exists_k_index
  obtain ⟨s,first,body,hs,hfirst,hbody⟩ := exists_s_index
  have hk' (a) := application_eq_some (hk a)
  have hc (a b) := application_eq_some (constantCode_apply a b)
  have hs' (a) := application_eq_some (hs a)
  have hf (a b) := application_eq_some (hfirst a b)
  refine ⟨{
    application := application
    k := k
    s := s
    k_defined := ?_
    k_law := ?_
    s_defined := ?_
    s_law := ?_ },rfl⟩
  · intro a
    rw [hk' a]
    trivial
  · intro a b
    rw [hk' a,Part.bind_some,hc a b]
  · intro a b
    rw [hs' a,Part.bind_some,hf a b]
    trivial
  · intro a b c
    rw [hs' a,Part.bind_some,hf a b,Part.bind_some]
    apply Part.ext
    intro m
    rw [mem_application_iff,hbody]
    simp only [Part.mem_bind_iff,mem_application_iff]
    constructor
    · rintro ⟨x,y,hx,hy,hm⟩
      exact ⟨x,hx,y,hy,hm⟩
    · rintro ⟨x,hx,y,hy,hm⟩
      exact ⟨x,y,hx,hy,hm⟩

noncomputable def indexPCA : PartialCombinatoryAlgebra ℕ := exists_indexPCA.choose

theorem indexPCA_application : indexPCA.application = application := exists_indexPCA.choose_spec

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The underlying realizers are natural numbers. Use Kleene's first partial combinatory algebra $K_1$ with
    $$e\cdot n\simeq\varphi_e(n),\qquad
    \varphi_e(n)=m\quad\Longleftrightarrow\quad P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}.$$
    Thus a realizer is an index in the fixed enumeration of closed lambda programs. The construction in
    §{sec:realizability-pca} gives the combinators $\mathsf k,\mathsf s$, including their definedness properties:
    the preliminary applications compute syntax codes, and the final S computation searches certificates for all
    required partial applications.
-/
theorem mem_indexPCA_iff (e n m : ℕ) : m ∈ indexPCA.application e n ↔ App e n m := by
  rw [indexPCA_application,mem_application_iff]

end LambdaIndexPCA
end PolishSpaceBook
