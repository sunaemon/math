module

public import PolishSpaceBook.LambdaProgramSpecialization
public import PolishSpaceBook.LambdaOutputSearch
public import PolishSpaceBook.LambdaNumericalFunctions
public import PolishSpaceBook.LambdaNumericalSearch

@[expose] public section

/-! # Self-reference and the recursion theorem for lambda program indices

The diagonal index uses the existing syntax specialization operation. All
simulation steps are beta reductions. The parameter-preserving version uses
the universal evaluator with input queries.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def diagonalBody (H X N : AlphaTerm) : AlphaTerm :=
  app (app H (app (app specializationCodeTerm X) X)) N

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The specialization formula can insert a program's own index without executing that program. We give the construction
    explicitly. In the following term, use the fixed variable names $n=x_{80}$ and $x=x_{81}$. For any closed term $H$, put
    \begin{mathmeta}
      \define{LambdaDiagonalTerm}
    \end{mathmeta}
    $$\LambdaDiagonalTerm{H}:=\lambdaab{n}{\lambdaab{x}{
     H(\LambdaSpecializationCodeProgram\,x\,x)n}}.$$
    Choose a named representative of this closed term, let $d$ be its syntax code, and set
    $$e:=\LambdaSpecializationCode{d}{d}.$$
    These are finite syntax constructions; no test of termination is involved.
-/
def diagonalTerm (H : AlphaTerm) : AlphaTerm :=
  lam 80 (lam 81 (diagonalBody H (var 81) (var 80)))

theorem diagonalTerm_closed {H : AlphaTerm} (hH : H.Closed) :
    (diagonalTerm H).Closed := by
  unfold diagonalTerm diagonalBody Closed
  simp only [fv_lam, fv_app, fv_var, (show H.fv = ∅ from hH),
    (show specializationCodeTerm.fv = ∅ from specializationCodeTerm_closed)]
  decide

theorem diagonalTerm_apply {H : AlphaTerm} (hH : H.Closed) (d : ℕ)
    (N : AlphaTerm) (hN : 81 ∉ N.fv) :
    Relation.ReflTransGen Beta (app (app (diagonalTerm H) N) (numeral d))
      (app (app H (numeral (Term.specializationCode d d))) N) := by
  have h₁ : Beta (app (diagonalTerm H) N)
      (lam 81 (diagonalBody H (var 81) N)) := by
    convert Beta.contract 80 (lam 81 (diagonalBody H (var 81) (var 80))) N using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 81 80 (by decide) hN]
    simp [diagonalBody, subst_app, subst_var, subst_closed _ _ _ hH,
      subst_closed _ _ _ specializationCodeTerm_closed]
  have h₂ : Beta (app (lam 81 (diagonalBody H (var 81) N)) (numeral d))
      (diagonalBody H (numeral d) N) := by
    convert Beta.contract 81 (diagonalBody H (var 81) N) (numeral d) using 1
    simp [diagonalBody, subst_app, subst_var, subst_closed _ _ _ hH,
      subst_closed _ _ _ specializationCodeTerm_closed, subst_not_free _ _ _ hN]
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    (beta_steps_app_left (beta_steps_app_right H (specializationCodeTerm_apply d d)) N)

/-- The same index works for every argument fresh for the internal binder. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Self-reference by specialization
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The specialization-code identity gives $P_e=\LambdaIndexSpecialization{\LambdaDiagonalTerm{H}}{d}$.
    One beta contraction supplies $N$, and two more supply $N$ and $\ChurchNumeral{d}$ to the diagonal term. Since
    $x_{81}$ is not free in $N$, this yields
    $$H(\LambdaSpecializationCodeProgram\,\ChurchNumeral{d}\,\ChurchNumeral{d})N.$$
    The specialization-code program reduces its inner argument to $\ChurchNumeral{e}$. Every step is a beta reduction,
    and the code was fixed before $N$ was supplied.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The specialization formula can insert a program's own index without executing that program. We give the construction
    explicitly. In the following term, use the fixed variable names $n=x_{80}$ and $x=x_{81}$. For any closed term $H$, put
    \begin{mathmeta}
      \define{LambdaDiagonalTerm}
    \end{mathmeta}
    $$\LambdaDiagonalTerm{H}:=\lambdaab{n}{\lambdaab{x}{
     H(\LambdaSpecializationCodeProgram\,x\,x)n}}.$$
    Choose a named representative of this closed term, let $d$ be its syntax code, and set
    $$e:=\LambdaSpecializationCode{d}{d}.$$
    These are finite syntax constructions; no test of termination is involved.
-/
theorem exists_self_reference (H : AlphaTerm) (hH : H.Closed) :
    ∃ e : ℕ, ∀ N : AlphaTerm, 81 ∉ N.fv →
      Relation.ReflTransGen Beta (app (Term.closedProgram e) N)
        (app (app H (numeral e)) N) := by
  obtain ⟨D,hD⟩ := Quotient.exists_rep (diagonalTerm H)
  have hc : D.fv = ∅ := by
    have := diagonalTerm_closed hH
    rw [← hD] at this
    exact this
  have hd : Term.closedProgram D.code = diagonalTerm H := by
    simp only [Term.closedProgram, Term.decode_code, hc, ite_true]
    exact hD
  refine ⟨Term.specializationCode D.code D.code, ?_⟩
  intro N hN
  rw [Term.closedProgram_specializationCode _ _ (by simpa using hc), hd]
  have hs : Beta (app (specializeProgram (diagonalTerm H) D.code) N)
      (app (app (diagonalTerm H) N) (numeral D.code)) := by
    simpa only [specializeProgram, subst_app, subst_var, ite_true,
      subst_closed _ _ _ (diagonalTerm_closed hH), subst_closed _ _ _ (numeral_closed D.code)] using
      Beta.contract 40 (app (app (diagonalTerm H) (var 40)) (numeral D.code)) N
  exact (Relation.ReflTransGen.single hs).trans (diagonalTerm_apply hH D.code N hN)

/-- Syntax constructors do not evaluate the coded terms. -/
theorem NumericalComputes.applicationCode {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) :
    NumericalComputes (numericalCombine applicationCodeTerm F G)
      (fun n => 3 * Nat.pair (f n) (g n) + 1) := by
  apply hf.combine hg (B := applicationCodeTerm)
    (show applicationCodeTerm.Closed from taggedPairCodeTerm_closed 1)
    (fun i j => 3 * Nat.pair i j + 1)
  intro i j
  simpa only [Term.code, Term.code_decode] using
    applicationCodeTerm_apply (Term.decode i) (Term.decode j)

theorem NumericalComputes.abstractionCode {F : AlphaTerm} {f : ℕ → ℕ}
    (hf : NumericalComputes F f) (x : ℕ) :
    NumericalComputes (numericalCombine abstractionCodeTerm (numericalConstant x) F)
      (fun n => 3 * Nat.pair x (f n) + 2) := by
  apply (numericalConstant_computes x).combine hf (B := abstractionCodeTerm)
    (show abstractionCodeTerm.Closed from taggedPairCodeTerm_closed 2)
    (fun i j => 3 * Nat.pair i j + 2)
  intro i j
  simpa only [Term.code, Term.code_decode] using
    abstractionCodeTerm_apply i (Term.decode j)

/-- The specialization term's representative is fixed independently of the input. -/
def diagonalSyntax (S P : Term) : Term :=
  .lam 80 (.lam 81 (.app (.app P (.app (.app S (.var 81)) (.var 81))) (.var 80)))

def diagonalCode (S : Term) (u : ℕ) : ℕ := (diagonalSyntax S (Term.decode u)).code

def selfReferenceIndex (S : Term) (u : ℕ) : ℕ :=
  Term.specializationCode (diagonalCode S u) (diagonalCode S u)

set_option maxHeartbeats 1000000 in
theorem diagonalCode_computable (S : Term) :
    ∃ D, NumericalComputes D (diagonalCode S) := by
  let K : Term := .app (.app S (.var 81)) (.var 81)
  have hd := ((numericalIdentity_computes.applicationCode
    (numericalConstant_computes K.code)).applicationCode
    (numericalConstant_computes 240)).abstractionCode 81 |>.abstractionCode 80
  refine ⟨_,hd.1,fun u => ?_⟩
  simpa only [diagonalCode, diagonalSyntax, Term.code, Term.code_decode, id_eq, K] using hd.2 u

theorem selfReferenceIndex_computable (S : Term) :
    ∃ F, NumericalComputes F (selfReferenceIndex S) := by
  obtain ⟨D,hd⟩ := diagonalCode_computable S
  exact ⟨_, hd.combine hd specializationCodeTerm_closed _ specializationCodeTerm_apply⟩

theorem selfReferenceIndex_spec (S : Term) (hS : mk S = specializationCodeTerm)
    (u : ℕ) (hu : (Term.decode u).fv = ∅)
    (N : AlphaTerm) (hN : 81 ∉ N.fv) :
    Relation.ReflTransGen Beta (app (Term.closedProgram (selfReferenceIndex S u)) N)
      (app (app (Term.closedProgram u) (numeral (selfReferenceIndex S u))) N) := by
  have hp : Term.closedProgram u = mk (Term.decode u) := by
    simp only [Term.closedProgram, hu, ite_true]
  have hd : mk (diagonalSyntax S (Term.decode u)) = diagonalTerm (Term.closedProgram u) := by
    change lam 80 (lam 81 (app (app (mk (Term.decode u))
      (app (app (mk S) (var 81)) (var 81))) (var 80))) = _
    rw [hS, ← hp]
    rfl
  have hc : (diagonalSyntax S (Term.decode u)).fv = ∅ := by
    have h := diagonalTerm_closed (Term.closedProgram_closed u)
    rw [← hd] at h
    exact h
  have hdecode : (Term.decode (diagonalCode S u)).fv = ∅ := by
    simpa only [diagonalCode, Term.decode_code] using hc
  have hprogram : Term.closedProgram (diagonalCode S u) = diagonalTerm (Term.closedProgram u) := by
    simp only [diagonalCode, Term.closedProgram, Term.decode_code, hc, ite_true]
    exact hd
  rw [selfReferenceIndex, Term.closedProgram_specializationCode _ _ hdecode, hprogram]
  have hs : Beta (app (specializeProgram (diagonalTerm (Term.closedProgram u)) (diagonalCode S u)) N)
      (app (app (diagonalTerm (Term.closedProgram u)) N) (numeral (diagonalCode S u))) := by
    simpa only [specializeProgram, subst_app, subst_var, ite_true,
      subst_closed _ _ _ (diagonalTerm_closed (Term.closedProgram_closed u)),
      subst_closed _ _ _ (numeral_closed (diagonalCode S u))] using
      Beta.contract 40 (app (app (diagonalTerm (Term.closedProgram u)) (var 40))
        (numeral (diagonalCode S u))) N
  exact (Relation.ReflTransGen.single hs).trans
    (diagonalTerm_apply (Term.closedProgram_closed u) (diagonalCode S u) N hN)

/-- One total index transformer works for every supplied closed syntax code. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Uniform self-reference indices
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Fix a named representative $S$ of $\LambdaSpecializationCodeProgram$ once. Write
    $$A(v,w):=3\NatPair{v}{w}+1,\qquad L(i,v):=3\NatPair{i}{v}+2$$
    for the numerical application and abstraction constructors, and put
    $$\begin{aligned}
    k&:=A\bigl(A(\LambdaSyntaxCode{S},243),243\bigr),\\
    d(u)&:=L\bigl(80,L(81,A(A(u,k),240))\bigr),\\
    e(u)&:=\LambdaSpecializationCode{d(u)}{d(u)}.
    \end{aligned}$$
    The constants $243$ and $240$ are the variable codes of $x_{81}$ and $x_{80}$, respectively.
    Thus $d(u)$ is the code of the displayed diagonal term with the decoded input term inserted for $H$.
    Application-code construction, abstraction-code construction and specialization compute $e(u)$ by beta reduction
    for every input. If the decoded term is closed, the preceding self-reference proof applies to this very
    representative and gives the asserted reduction. The representative $S$ is fixed before $u$ is supplied.
-/
theorem uniform_self_reference_indices :
    ∃ F f, NumericalComputes F f ∧ ∀ u, (Term.decode u).fv = ∅ →
      ∀ N : AlphaTerm, 81 ∉ N.fv →
        Relation.ReflTransGen Beta (app (Term.closedProgram (f u)) N)
          (app (app (Term.closedProgram u) (numeral (f u))) N) := by
  obtain ⟨S,hS⟩ := Quotient.exists_rep specializationCodeTerm
  obtain ⟨F,hF⟩ := selfReferenceIndex_computable S
  exact ⟨F,selfReferenceIndex S,hF,fun u hu N hN => selfReferenceIndex_spec S hS u hu N hN⟩

def currySyntax (B P : Term) : Term :=
  .lam 40 (.lam 41 (.app P (.app (.app B (.var 40)) (.var 41))))

def curryCode (B : Term) (u : ℕ) : ℕ := (currySyntax B (Term.decode u)).code

theorem curryCode_computable (B : Term) : ∃ C, NumericalComputes C (curryCode B) := by
  let K : Term := .app (.app B (.var 40)) (.var 41)
  have h := (numericalIdentity_computes.applicationCode
    (numericalConstant_computes K.code)).abstractionCode 41 |>.abstractionCode 40
  refine ⟨_,h.1,fun u => ?_⟩
  simpa only [curryCode, currySyntax, Term.code, Term.code_decode, id_eq, K] using h.2 u

theorem curryCode_spec (B : Term) (hB : mk B = numericalPairTerm)
    (u : ℕ) (hu : (Term.decode u).fv = ∅) :
    (Term.decode (curryCode B u)).fv = ∅ ∧
      Term.closedProgram (curryCode B u) = curryNumerical (Term.closedProgram u) := by
  have hp : Term.closedProgram u = mk (Term.decode u) := by
    simp only [Term.closedProgram, hu, ite_true]
  have hm : mk (currySyntax B (Term.decode u)) = curryNumerical (Term.closedProgram u) := by
    change lam 40 (lam 41 (app (mk (Term.decode u))
      (app (app (mk B) (var 40)) (var 41)))) = _
    rw [hB, ← hp]
    rfl
  have hc : (currySyntax B (Term.decode u)).fv = ∅ := by
    have h := curryNumerical_closed (Term.closedProgram_closed u)
    rw [← hm] at h
    exact h
  constructor
  · simpa only [curryCode, Term.decode_code] using hc
  · simp only [curryCode, Term.closedProgram, Term.decode_code, hc, ite_true]
    exact hm

/-- Pure parameter insertion is a total syntax operation, even for partial programs. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Uniform numerical parameter indices
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Fix a named representative of $\LambdaNumericPair$ before the inputs are supplied. Abstraction and application
    of syntax codes give the code $c(u)$ of $\lambdaab{v}{\lambdaab{n}{P_u(\LambdaNumericPair\,v\,n)}}$,
    with the decoded input syntax inserted literally. If $\nu(a)$ is the code of $\ChurchNumeral{a}$, set
    $$p(u,a):=3\NatPair{c(u)}{\nu(a)}+1.$$
    Each code operation is computed by a closed numerical term on every input. For closed input syntax, the
    constructed term is closed and its alpha-class is the displayed application. Applying it to $\ChurchNumeral{n}$
    and performing the two beta contractions and numerical pairing gives
    $$P_{p(u,a)}\ChurchNumeral{n}\to_\beta^*P_u\ChurchNumeral{\NatPair{a}{n}}.$$
    The computation of $f$ gives the asserted output. Constructing the index itself never runs $P_u$.
-/
theorem uniform_numerical_parameter_indices :
    ∃ S s, NumericalComputes S s ∧ ∀ u a,
      (Term.decode u).fv = ∅ →
      (Term.decode (s (Nat.pair u a))).fv = ∅ ∧
      Term.closedProgram (s (Nat.pair u a)) =
        app (curryNumerical (Term.closedProgram u)) (numeral a) ∧
      ∀ f, NumericalComputes (Term.closedProgram u) f →
        NumericalComputes (Term.closedProgram (s (Nat.pair u a)))
          (fun n => f (Nat.pair a n)) := by
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨C,hC⟩ := curryCode_computable B
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  let t (z : ℕ) : Term :=
    .app (currySyntax B (Term.decode z.unpair.1)) (Term.churchNumeral z.unpair.2)
  have hs := (hC.comp (projection_computes true)).applicationCode
    (hn.comp (projection_computes false))
  refine ⟨numericalCombine applicationCodeTerm (numericalCompose C (numericalProjectionTerm true))
    (numericalCompose numeralCodeTerm (numericalProjectionTerm false)),
    fun z => (t z).code,?_,fun u a hu => ?_⟩
  · exact ⟨hs.1,fun z => by simpa only [t,Term.code,curryCode,ite_true,Bool.false_eq_true,ite_false] using hs.2 z⟩
  have hm : mk (t (Nat.pair u a)) =
      app (curryNumerical (Term.closedProgram u)) (numeral a) := by
    obtain ⟨hc,hp⟩ := curryCode_spec B hB u hu
    have hc' : (currySyntax B (Term.decode u)).fv = ∅ := by
      simpa only [curryCode,Term.decode_code] using hc
    have hp' : mk (currySyntax B (Term.decode u)) = curryNumerical (Term.closedProgram u) := by
      simpa only [curryCode,Term.closedProgram,Term.decode_code,hc',ite_true] using hp
    simp only [t,Nat.unpair_pair]
    change app (mk (currySyntax B (Term.decode u))) (mk (Term.churchNumeral a)) = _
    rw [Term.mk_churchNumeral,hp']
  have ht : (t (Nat.pair u a)).fv = ∅ := by
    have h := closed_app (curryNumerical_closed (Term.closedProgram_closed u)) (numeral_closed a)
    rw [← hm] at h
    exact h
  have hp : Term.closedProgram (t (Nat.pair u a)).code =
      app (curryNumerical (Term.closedProgram u)) (numeral a) := by
    simpa only [Term.closedProgram,Term.decode_code,ht,ite_true] using hm
  refine ⟨by simpa only [Term.decode_code] using ht,hp,fun f hf => ?_⟩
  rw [hp]
  exact ⟨closed_app (curryNumerical_closed hf.1) (numeral_closed a),
    fun n => (curryNumerical_apply hf.1 a n).trans (hf.2 _)⟩

/-- Specialization preserves partial values and domains without assuming totality
of the original program. The numerical parameter can encode an entire finite tuple. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Parameterization.** If a computable procedure computes a partial function $\psi(\vec a,n)$ from parameters $\vec
        a$ and input $n$, then there is a computable function producing an index $e_{\vec a}$ such that
        $$
        \varphi_{e_{\vec a}}(n) \simeq \psi(\vec a,n).
        $$
        This is the lambda-calculus form of the $s$--$m$--$n$ theorem.
-/
theorem uniform_partial_parameter_indices :
    ∃ S s, NumericalComputes S s ∧ ∀ u a,
      (Term.decode u).fv = ∅ → ∀ n m,
      Relation.ReflTransGen Beta (app (Term.closedProgram (s (Nat.pair u a))) (numeral n)) (numeral m) ↔
        Relation.ReflTransGen Beta (app (Term.closedProgram u) (numeral (Nat.pair a n))) (numeral m) := by
  obtain ⟨S, s, hS, hs⟩ := uniform_numerical_parameter_indices
  refine ⟨S, s, hS, fun u a hu n m => ?_⟩
  rw [(hs u a hu).2.1]
  have hr := curryNumerical_apply (Term.closedProgram_closed u) a n
  exact ⟨fun h => numeral_after_reduction hr h, fun h => hr.trans h⟩

/-- The compiler receives the numerical code of the family constructor itself. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: corollary
  title: Uniform self-indexed numerical families
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Fix a representative of numerical pairing. The syntax constructors compute from $u$ the code $c(u)$ of
    $$\lambdaab{v}{\lambdaab{a}{P_u(\LambdaNumericPair\,v\,a)}}.$$
    Here the syntax decoded from the input is inserted literally; when it is closed, the displayed expression
    is its alpha-class. Set $q(u):=e(c(u))$. The preceding proposition gives the self-reference reduction,
    and numerical pairing followed by the computation of $f$ gives the required numeral output.
    Computing $c(u)$ and $q(u)$ never runs $P_u$.
-/
theorem uniform_self_indexed_family_indices :
    ∃ Q q, NumericalComputes Q q ∧ ∀ u, (Term.decode u).fv = ∅ →
      ∀ f, NumericalComputes (Term.closedProgram u) f →
        NumericalComputes (Term.closedProgram (q u)) (fun a => f (Nat.pair (q u) a)) := by
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨C,hC⟩ := curryCode_computable B
  obtain ⟨F,r,hF,hr⟩ := uniform_self_reference_indices
  refine ⟨_,fun u => r (curryCode B u),hF.comp hC,fun u hu f hf => ?_⟩
  obtain ⟨hc,hp⟩ := curryCode_spec B hB u hu
  refine ⟨Term.closedProgram_closed _,fun a => ?_⟩
  have hs := hr (curryCode B u) hc (numeral a) (by rw [numeral_closed]; simp)
  rw [hp] at hs
  exact hs.trans ((curryNumerical_apply hf.1 _ a).trans (hf.2 _))

/-- A computed index of a total numerical family gives a joint computation of its values. -/
theorem NumericalComputes.evaluateFamily {E : AlphaTerm} {e : ℕ → ℕ} {f : ℕ → ℕ → ℕ}
    (hE : NumericalComputes E e)
    (hf : ∀ a, NumericalComputes (Term.closedProgram (e a)) (f a)) :
    NumericalComputes (numericalCombine outputSearchTerm
      (numericalCompose E (numericalProjectionTerm true)) (numericalProjectionTerm false))
      (fun z => f z.unpair.1 z.unpair.2) := by
  have hc : NumericalComputes (numericalCompose E (numericalProjectionTerm true))
      (fun z => e z.unpair.1) := hE.comp (projection_computes true)
  have hn : NumericalComputes (numericalProjectionTerm false) (fun z => z.unpair.2) := projection_computes false
  refine ⟨?_,fun z => ?_⟩
  · unfold numericalCombine Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [outputSearchTerm_closed,hc.1,hn.1]
    simp
  · have hb : Beta (app (numericalCombine outputSearchTerm
        (numericalCompose E (numericalProjectionTerm true)) (numericalProjectionTerm false)) (numeral z))
        (app (app outputSearchTerm (app (numericalCompose E (numericalProjectionTerm true)) (numeral z)))
          (app (numericalProjectionTerm false) (numeral z))) := by
      simpa only [numericalCombine,subst_app,subst_var,ite_true,
        subst_closed _ _ _ outputSearchTerm_closed,subst_closed _ _ _ hc.1,subst_closed _ _ _ hn.1] using
        Beta.contract 40 (app (app outputSearchTerm
          (app (numericalCompose E (numericalProjectionTerm true)) (var 40)))
          (app (numericalProjectionTerm false) (var 40))) (numeral z)
    exact (Relation.ReflTransGen.single hb).trans
      ((beta_steps_app (beta_steps_app_right outputSearchTerm (hc.2 z)) (hn.2 z)).trans
        ((outputSearchTerm_runs_iff _ _ _).mpr ((hf z.unpair.1).2 z.unpair.2)))

def recursionOperator (F : AlphaTerm) : AlphaTerm :=
  lam 82 (app outputSearchTerm (app F (var 82)))

theorem recursionOperator_closed {F : AlphaTerm} (hF : F.Closed) :
    (recursionOperator F).Closed := by
  unfold recursionOperator Closed
  simp only [fv_lam, fv_app, fv_var, (show F.fv = ∅ from hF),
    (show outputSearchTerm.fv = ∅ from outputSearchTerm_closed)]
  decide

theorem recursionOperator_apply {F : AlphaTerm} {f : ℕ → ℕ}
    (hf : NumericalComputes F f) (e n : ℕ) :
    Relation.ReflTransGen Beta (app (app (recursionOperator F) (numeral e)) (numeral n))
      (app (app outputSearchTerm (numeral (f e))) (numeral n)) := by
  have hb : Beta (app (recursionOperator F) (numeral e))
      (app outputSearchTerm (app F (numeral e))) := by
    simpa only [recursionOperator, subst_app, subst_var, ite_true,
      subst_closed _ _ _ hf.1, subst_closed _ _ _ outputSearchTerm_closed] using
      Beta.contract 82 (app outputSearchTerm (app F (var 82))) (numeral e)
  exact (Relation.ReflTransGen.single (.app_left _ hb)).trans
    (beta_steps_app_left (beta_steps_app_right outputSearchTerm (hf.2 e)) (numeral n))

/-- Equality includes undefined partial values. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Recursion theorem for lambda indices
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the self-reference lemma with the closed term
    $$H:=\lambdaab{z}{\LambdaOutputSearch(Fz)}.$$
    It gives an index $e$ for which
    $$P_e\ChurchNumeral{n}\to_\beta^*
     \LambdaOutputSearch(F\ChurchNumeral{e})\ChurchNumeral{n}
     \to_\beta^*\LambdaOutputSearch\,\ChurchNumeral{f(e)}\,\ChurchNumeral{n}.$$
    The last reduction uses totality of $f$. Exact universal evaluation identifies the numeral outputs of the last term
    with those of $P_{f(e)}\ChurchNumeral{n}$. These reductions can be prepended to any such output. Conversely,
    confluence and normality of numerals imply that any numeral output of the starting term is also an output of the last
    term. Thus all values and the domains agree.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Recursion theorem.** Every total computable operator on program indices has an extensional fixed point:
        if $F$ is total computable, there is $e_0$ with $\varphi_{e_0}\simeq\varphi_{F(e_0)}$.
        §{sec:lambda-index-recursion} constructs the index explicitly from syntax specialization and proves
        equality of partial values, including undefined values. It also proves a version that preserves an arbitrary
        input function with the same index for all input functions.
-/
theorem recursion_theorem {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) :
    ∃ e : ℕ, ∀ n m : ℕ,
      Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral n)) (numeral m) ↔
      Relation.ReflTransGen Beta (app (Term.closedProgram (f e)) (numeral n)) (numeral m) := by
  obtain ⟨e,he⟩ := exists_self_reference (recursionOperator F) (recursionOperator_closed hf.1)
  refine ⟨e,fun n m => ?_⟩
  have hs := (he (numeral n) (by rw [numeral_closed]; simp)).trans
    (recursionOperator_apply hf e n)
  exact ⟨fun h => (outputSearchTerm_runs_iff (f e) n m).mp (numeral_after_reduction hs h),
    fun h => hs.trans ((outputSearchTerm_runs_iff (f e) n m).mpr h)⟩

/-- Supply the input function after fixing the diagonal index. -/
def oracleRecursionOperator (F : AlphaTerm) : AlphaTerm :=
  lam 82 (lam 83 (app (app oracleOutputSearchTerm (var 83)) (app F (var 82))))

theorem oracleRecursionOperator_closed {F : AlphaTerm} (hF : F.Closed) :
    (oracleRecursionOperator F).Closed := by
  unfold oracleRecursionOperator Closed
  simp only [fv_lam, fv_app, fv_var, (show F.fv = ∅ from hF),
    (show oracleOutputSearchTerm.fv = ∅ from oracleOutputSearchTerm_closed)]
  decide

theorem oracleRecursionOperator_apply {F : AlphaTerm} {f : ℕ → ℕ}
    (hf : NumericalComputes F f) (e : ℕ) :
    Relation.ReflTransGen Beta (app (app (oracleRecursionOperator F) (numeral e)) (var 0))
      (app (app oracleOutputSearchTerm (var 0)) (numeral (f e))) := by
  have h₁ : Beta (app (oracleRecursionOperator F) (numeral e))
      (lam 83 (app (app oracleOutputSearchTerm (var 83)) (app F (numeral e)))) := by
    unfold oracleRecursionOperator
    convert Beta.contract 82
      (lam 83 (app (app oracleOutputSearchTerm (var 83)) (app F (var 82)))) (numeral e) using 1
    rw [subst_lam_fresh _ _ 83 82 (by decide) (by rw [numeral_closed]; simp)]
    simp [subst_app, subst_var, subst_closed _ _ _ hf.1,
      subst_closed _ _ _ oracleOutputSearchTerm_closed]
  have h₂ : Beta
      (app (lam 83 (app (app oracleOutputSearchTerm (var 83)) (app F (numeral e)))) (var 0))
      (app (app oracleOutputSearchTerm (var 0)) (app F (numeral e))) := by
    convert Beta.contract 83
      (app (app oracleOutputSearchTerm (var 83)) (app F (numeral e))) (var 0) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ hf.1,
      subst_closed _ _ _ oracleOutputSearchTerm_closed, subst_closed _ _ _ (numeral_closed e)]
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    (beta_steps_app_right (app oracleOutputSearchTerm (var 0)) (hf.2 e))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Recursion with an unchanged input function
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Now use the closed term
    $$H:=\lambdaab{z}{\lambdaab{o}{\LambdaQueryOutputSearch\,o\,(Fz)}}.$$
    The self-reference construction fixes $e$ before $p$ is supplied. Apply its reduction to the argument $o=x_0$, then
    supply $\ChurchNumeral{n}$. Beta reduction and the computation of $F\ChurchNumeral{e}$ give
    $$P_eo\ChurchNumeral{n}\to_\beta^*
     \LambdaQueryOutputSearch\,o\,\ChurchNumeral{f(e)}\,\ChurchNumeral{n}.$$
    The exact evaluator theorem with input queries and confluence give both directions, just as above. Every query uses
    the same $p$ on both sides, and equality also holds when neither side has a numeral output.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Recursion theorem.** Every total computable operator on program indices has an extensional fixed point:
        if $F$ is total computable, there is $e_0$ with $\varphi_{e_0}\simeq\varphi_{F(e_0)}$.
        §{sec:lambda-index-recursion} constructs the index explicitly from syntax specialization and proves
        equality of partial values, including undefined values. It also proves a version that preserves an arbitrary
        input function with the same index for all input functions.
-/
theorem uniform_oracle_recursion_theorem {F : AlphaTerm} {f : ℕ → ℕ}
    (hf : NumericalComputes F f) :
    ∃ e : ℕ, ∀ p : ℕ → ℕ, ∀ n m : ℕ,
      OracleRuns p (Term.closedProgram e) n m ↔
      OracleRuns p (Term.closedProgram (f e)) n m := by
  obtain ⟨e,he⟩ := exists_self_reference (oracleRecursionOperator F)
    (oracleRecursionOperator_closed hf.1)
  refine ⟨e,fun p n m => ?_⟩
  have hs := beta_steps_oracle (p := p) (beta_steps_app_left
    ((he (var 0) (by change 81 ∉ ({0} : Finset ℕ); decide)).trans
      (oracleRecursionOperator_apply hf e)) (numeral n))
  exact ⟨fun h => (oracleOutputSearchTerm_runs_iff p (f e) n m).mp
      (oracle_numeral_after_reduction hs h),
    fun h => hs.trans ((oracleOutputSearchTerm_runs_iff p (f e) n m).mpr h)⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
