module

public import PolishSpaceBook.LambdaCertifiedDescent
public import PolishSpaceBook.LambdaNotationCoverage

@[expose] public section

/-! # Recursive ordinal bounds on valid Kleene notations

Finite beta certificates turn candidate edges into a recursive tree of
certified descending chains. Its Kleene--Brouwer order bounds the rank.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
set_option maxHeartbeats 1000000

/-- A unary wrapper for the existing total output-candidate tester. -/
def candidateTupleProgram : AlphaTerm := lam 90
  (app (app (app outputCandidateTerm (app (numericalProjectionTerm true) (var 90)))
    (app (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)) (var 90)))
    (app (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)) (var 90)))

theorem candidateTupleProgram_computes : NumericalComputes candidateTupleProgram
    (fun z => if Term.outputCandidate z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2 then 1 else 0) := by
  have he := projection_computes true
  have hn := (projection_computes true).comp (projection_computes false)
  have hk := (projection_computes false).comp (projection_computes false)
  refine ⟨?_,fun z => ?_⟩
  · unfold candidateTupleProgram Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [show outputCandidateTerm.fv = ∅ from outputCandidateTerm_closed,
      show (numericalProjectionTerm true).fv = ∅ from he.1,
      show (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)).fv = ∅ from hn.1,
      show (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)).fv = ∅ from hk.1]
    simp
  · have hs : Beta (app candidateTupleProgram (numeral z))
        (app (app (app outputCandidateTerm (app (numericalProjectionTerm true) (numeral z)))
          (app (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)) (numeral z)))
          (app (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)) (numeral z))) := by
      unfold candidateTupleProgram
      convert Beta.contract 90 _ (numeral z) using 1
      simp only [subst_app,subst_var,ite_true,subst_closed _ _ _ outputCandidateTerm_closed,
        subst_closed _ _ _ he.1,subst_closed _ _ _ hn.1,subst_closed _ _ _ hk.1]
    exact (Relation.ReflTransGen.single hs).trans
      ((beta_steps_app (beta_steps_app (beta_steps_app_right _ (he.2 z)) (hn.2 z)) (hk.2 z)).trans
        (outputCandidateTerm_apply _ _ _))

/-- Input is (parent,(child,(program,(input,certificate bound)))). -/
def edgeCertificate (z : ℕ) : Prop :=
  (0 < z.unpair.2.unpair.1 ∧ z.unpair.1 = successorCode z.unpair.2.unpair.1) ∨
  (z.unpair.1 = limitCode z.unpair.2.unpair.2.unpair.1 ∧
    Term.outputTest z.unpair.2.unpair.2.unpair.1 z.unpair.2.unpair.2.unpair.2.unpair.1
      z.unpair.2.unpair.1 z.unpair.2.unpair.2.unpair.2.unpair.2 = true)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    A candidate step need not be decidable, but it has a finite certificate.
    §{sec:lambda-certified-descent} constructs a total decision program for a predicate $C(p,\NatPair{b}{c})$
    such that
    $$\KleeneCandidateStep{b}{p}\quad\Longleftrightarrow\quad
     \exists c\;C(p,\NatPair{b}{c}).$$
    For a successor step, check the numerical equality and positivity. For a limit step, the certificate contains an
    index, an input, and a bound for the finite beta-certificate test. No test of notation validity is used.
-/
theorem edgeCertificate_sound (p x : ℕ) (h : edgeCertificate (Nat.pair p x)) :
    Edge x.unpair.1 p := by
  simp only [edgeCertificate,Nat.unpair_pair] at h
  rcases h with ⟨hp,rfl⟩ | ⟨rfl,hr⟩
  · exact .succ _ hp
  · exact .limit _ _ _ ((outputTest_exists_iff _ _ _).mp ⟨_,hr⟩)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the application to ordinal notations, call $b$ a candidate predecessor of $p$ when either $b>0$ and $p=2^b$,
    or $p=3\cdot5^e$ and $P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{b}$ for some $e,n$.
    On input $z=\NatPair{p}{\NatPair{b}{\NatPair{e}{\NatPair{n}{s}}}}$, use projections to extract the five fields.
    The certificate test accepts exactly when
    $$(b>0\text{ and }p=2^b)\quad\text{or}\quad
     (p=3\cdot5^e\text{ and }\LambdaOutputTest\,\ChurchNumeral{e}\,\ChurchNumeral{n}
     \,\ChurchNumeral{b}\,\ChurchNumeral{s}\to_\beta^*\ChurchNumeral{1}).$$
    The successor alternative ignores the certificate fields. For the limit alternative, the finite-output-test theorem
    proves both soundness and existence of an accepted certificate whenever the indicated numerical output exists.
-/
theorem edgeCertificate_complete (p b : ℕ) (h : Edge b p) :
    ∃ c, edgeCertificate (Nat.pair p (Nat.pair b c)) := by
  cases h with
  | succ b hb => exact ⟨0,by simp [edgeCertificate,hb]⟩
  | limit e n b hr =>
    obtain ⟨s,hs⟩ := (outputTest_exists_iff e n b).mpr hr
    exact ⟨Nat.pair e (Nat.pair n s),by simp [edgeCertificate,hs]⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Here is an explicit term for this test. For numerical terms $\LambdaTermName{left}, \LambdaTermName{right}$
    representing natural
    numbers or decision bits as appropriate, put
    $$\begin{aligned}
    \LambdaTermName{parent}(z)&:=\LambdaNumericProjection{1}z,\\
    \LambdaTermName{child}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{index}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z)),\\
    \LambdaTermName{position}(z)&:= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{2}( \LambdaNumericProjection{2}z))),\\
    \LambdaTermName{fuel}(z)&:= \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{2}( \LambdaNumericProjection{2}z))),\\
    \LambdaTermName{le}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{ \LambdaTermName{left}}{
    \LambdaTermName{right}}{ \ChurchNumeral{1}}{
    \ChurchNumeral{0}},\\
    \LambdaTermName{eq}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaMul\, \LambdaTermName{le}(
    \LambdaTermName{left}, \LambdaTermName{right})\,
    \LambdaTermName{le}( \LambdaTermName{right}, \LambdaTermName{left}),\\
    \LambdaTermName{nonzero}( \LambdaTermName{left})&:= \LambdaLeCase{ \LambdaTermName{left}}{ \ChurchNumeral{0}}{
    \ChurchNumeral{0}}{
    \ChurchNumeral{1}},\\
    \LambdaTermName{or}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaLeCase{ \LambdaTermName{left}}{
    \ChurchNumeral{0}}{ \LambdaTermName{right}}{
    \ChurchNumeral{1}},\\
     \LambdaTermName{powTwo}&:=\lambdaab{k}{k(\LambdaMul\,\ChurchNumeral{2})\ChurchNumeral{1}},\\
    \LambdaTermName{succCert}(z)&:=\LambdaMul\,
     (\LambdaTermName{nonzero}(\LambdaTermName{child}(z)))\,
     (\LambdaTermName{eq}(\LambdaTermName{parent}(z),\LambdaTermName{powTwo}(\LambdaTermName{child}(z)))),\\
    \LambdaTermName{limCert}(z)&:=\LambdaMul\,
     (\LambdaTermName{eq}(\LambdaTermName{parent}(z),\LambdaLimitCodeProgram(\LambdaTermName{index}(z))))\,
     (\LambdaOutputCandidate\,(\LambdaTermName{index}(z))\,(\LambdaTermName{position}(z))\,
       (\LambdaNumericPair\,(\LambdaTermName{child}(z))\,(\LambdaTermName{fuel}(z)))),\\
     \LambdaTermName{cert}&:=\lambdaab{z}{\LambdaTermName{or}(\LambdaTermName{succCert}(z),\LambdaTermName{limCert}(z))}.
    \end{aligned}$$
    All the term bodies are expanded before abstraction. Equality is two numerical
    comparisons, conjunction is multiplication, and the last alternative is disjunction of decision bits. Church
    iteration computes $2^b$, and §{sec:lambda-recursive-order-programs} supplies the limit-code term. Every component
    is total,
    so expanding these expressions gives the required closed certificate decider. It checks finite beta evidence;
    it neither runs a potentially divergent indexed computation to completion nor decides notation validity.
-/
theorem edgeCertificate_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε edgeCertificate := by
  have hp := projection_computes true
  have hx := (projection_computes true).comp (projection_computes false)
  have hc := (projection_computes false).comp (projection_computes false)
  have he := (projection_computes true).comp hc
  have hn := (projection_computes true).comp ((projection_computes false).comp hc)
  have hs := (projection_computes false).comp ((projection_computes false).comp hc)
  have hpow := powerTwo_computes.comp hx
  have hlim := limitCodeProgram_computes.comp he
  have hsuccessor := (LambdaTree.numerical_lt_decidable (numericalConstant_computes 0) hx ε).and
    ((LambdaTree.numerical_le_decidable hp hpow ε).and (LambdaTree.numerical_le_decidable hpow hp ε))
  have htest := candidateTupleProgram_computes.comp (he.pair (hn.pair (hx.pair hs)))
  have htestDecision : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ => Term.outputTest z.unpair.2.unpair.2.unpair.1
        z.unpair.2.unpair.2.unpair.2.unpair.1 z.unpair.2.unpair.1
        z.unpair.2.unpair.2.unpair.2.unpair.2 = true) := by
    apply LambdaTree.numericalDecision htest ε
    · intro z h
      simp [Term.outputCandidate,h]
    · intro z h
      simp [Term.outputCandidate,h]
  have hlimit := ((LambdaTree.numerical_le_decidable hp hlim ε).and
    (LambdaTree.numerical_le_decidable hlim hp ε)).and htestDecision
  unfold edgeCertificate
  simpa only [Bool.false_eq_true,ite_true,ite_false,← le_antisymm_iff,edgeCertificate,successorCode] using hsuccessor.or hlimit

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    For a node $s$, let $b(s)$ be its last notation, with $b(\emptySeq)=a$. All these notations are valid.
    Induction on candidate descent proves that $\KleeneValue{b(s)}$ is at most the strict-extension rank of $s$ in $T_a$.
    Indeed, each candidate predecessor $d$ of $b(s)$ has a certificate $c$, and appending $\NatPair{d}{c}$ gives a child.
    The induction hypothesis bounds $\KleeneValue{d}$ by the child's rank. Taking successors and then the supremum over
    all $d$ proves the assertion at $s$. Certificate choice is used only in this rank comparison, not in the membership
    program. At the root this gives $\KleeneValue{a}\le\rho(T_a)$. The recursive Kleene--Brouwer presentation from
    §{sec:edst-recursive-tree-ranks} has order type $\beta$ with
    $$\KleeneValue{a}\le\rho(T_a)<\beta<\churchKleeneOrd.$$
    Downward closure of recursive ordinals shows that $\KleeneValue{a}$ is recursive. The preceding coverage theorem
    supplies the other inclusion in the displayed equality.
    \end{proof}
-/
theorem value_recursive {a : ℕ} (ha : Valid a) :
    LambdaRelative.RecursiveOrdinal (fun _ => 0) (value a ha) := by
  obtain ⟨W,hW⟩ := CertifiedDescent.recursive_bound edgeCertificate
    (edgeCertificate_decidable (fun _ => 0)) edgeCertificate_sound edgeCertificate_complete ha.acc
  exact LambdaRelative.recursiveOrdinal_downward ⟨W,rfl⟩ hW

theorem value_lt_churchKleene {a : ℕ} (ha : Valid a) :
    value a ha < LambdaRelative.recursiveOrdinalBound (fun _ => 0) :=
  LambdaRelative.recursiveOrdinal_lt_bound (value_recursive ha)

theorem has_notation_iff_recursive (α : Ordinal) :
    (∃ a, ∃ ha : Valid a, value a ha = α) ↔ LambdaRelative.RecursiveOrdinal (fun _ => 0) α := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact value_recursive ha
  · exact recursiveOrdinal_has_notation

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: theorem
  title: Range of Kleene notations
-/
theorem has_notation_iff_below_churchKleene (α : Ordinal) :
    (∃ a, ∃ ha : Valid a, value a ha = α) ↔ α < LambdaRelative.recursiveOrdinalBound (fun _ => 0) := by
  rw [has_notation_iff_recursive,LambdaRelative.recursiveOrdinal_iff_lt_bound]

end KleeneNotation
end PolishSpaceBook
