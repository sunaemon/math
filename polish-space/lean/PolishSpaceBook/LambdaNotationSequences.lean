module

public import PolishSpaceBook.LambdaNotationPrograms
public import PolishSpaceBook.LambdaTemplateIndices

@[expose] public section

/-! # The sequence program for delayed upper notations

A numerical selector returns zero for no predecessor and b+1 for a selected b.
The template evaluates the self-index only at a selected predecessor, then
iterates the successor constructor n+1 times.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
set_option maxRecDepth 4096

def sequenceSlot (C A N : AlphaTerm) : AlphaTerm := app C (app (app numericalPairTerm A) N)

def sequenceBase (C Q A N : AlphaTerm) : AlphaTerm :=
  chooseLeBody (sequenceSlot C A N) (numeral 0) (numeral 1)
    (app (app outputSearchTerm Q) (app predecessorTerm (sequenceSlot C A N)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix any closed numerical selector $C$, and let $\sigma(a,n)$ be its value at $\NatPair{a}{n}$. This may be the
    predecessor selector just constructed. For numerical arguments $q,a,n$, expand the following expressions before
    abstracting their variables:
    $$\begin{aligned}
    Z&:=C(\LambdaNumericPair\,a\,n),\\
    V&:=\LambdaLeCase{Z}{\ChurchNumeral{0}}{\ChurchNumeral{1}}{
     \LambdaOutputSearch\,q\,(\LambdaPred\,Z)},\\
    L(q,a,n)&:=\LambdaNotationIterate\,(\LambdaNumericPair\,V\,(\LambdaSucc\,n)),\\
    T&:=\lambdaab{n}{\lambdaab{z}{
     L(\LambdaNumericProjection{1}z,\LambdaNumericProjection{2}z,n)}}.
    \end{aligned}$$
    Use $n=x_{84}$ and $z=x_{85}$ as the two outer binders. Fix a named representative of the closed term $T$, with code
    $u$, and put
    $$s(q,a):=\LambdaSpecializationCode{u}{\NatPair{q}{a}},\qquad
     g_q(a):=3\cdot5^{s(q,a)}.$$
    The specialization-code term, numerical pairing and $\LambdaLimitCodeProgram$ compute these total maps. They do not run
    $T$ or $P_q$ while producing the codes.
-/
def sequenceBody (C Q A N : AlphaTerm) : AlphaTerm :=
  app iterateSuccessorProgram
    (app (app numericalPairTerm (sequenceBase C Q A N)) (app successorTerm N))

theorem sequenceBody_fv {C : AlphaTerm} (hC : C.Closed) (Q A N : AlphaTerm) :
    (sequenceBody C Q A N).fv = Q.fv ∪ A.fv ∪ N.fv := by
  ext x
  simp only [sequenceBody,sequenceBase,sequenceSlot,chooseLeBody_fv,fv_app,
    (show C.fv = ∅ from hC),
    (show iterateSuccessorProgram.fv = ∅ from iterateSuccessorProgram_computes.1),
    (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed),
    (show outputSearchTerm.fv = ∅ from outputSearchTerm_closed),
    (show predecessorTerm.fv = ∅ from predecessorTerm_closed),
    (show successorTerm.fv = ∅ from successorTerm_closed),
    Finset.mem_union,Finset.notMem_empty]
  tauto

theorem sequenceBody_subst {C : AlphaTerm} (hC : C.Closed) (Q A N R : AlphaTerm) (x : ℕ) :
    (sequenceBody C Q A N).subst x R =
      sequenceBody C (Q.subst x R) (A.subst x R) (N.subst x R) := by
  simp only [sequenceBody,sequenceBase,sequenceSlot,chooseLeBody_subst,subst_app,
    subst_closed _ _ _ hC,subst_closed _ _ _ iterateSuccessorProgram_computes.1,
    subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ outputSearchTerm_closed,
    subst_closed _ _ _ predecessorTerm_closed,subst_closed _ _ _ successorTerm_closed,
    subst_closed _ _ _ (numeral_closed 0),subst_closed _ _ _ (numeral_closed 1)]

theorem sequenceBody_steps {C Q Q' A A' N N' : AlphaTerm}
    (hQ : Relation.ReflTransGen Beta Q Q') (hA : Relation.ReflTransGen Beta A A')
    (hN : Relation.ReflTransGen Beta N N') :
    Relation.ReflTransGen Beta (sequenceBody C Q A N) (sequenceBody C Q' A' N') := by
  have hs := beta_steps_app_right C (beta_steps_app (beta_steps_app_right numericalPairTerm hA) hN)
  have hb := chooseLeBody_steps (B := numeral 0) (X := numeral 1) hs .refl .refl
    (beta_steps_app (beta_steps_app_right outputSearchTerm hQ) (beta_steps_app_right predecessorTerm hs))
  exact beta_steps_app_right iterateSuccessorProgram
    (beta_steps_app (beta_steps_app_right numericalPairTerm hb) (beta_steps_app_right successorTerm hN))

def selectedBase (σ : ℕ → ℕ) (f : ℕ → ℕ) (a n : ℕ) : ℕ :=
  if σ (Nat.pair a n) = 0 then 1 else f (σ (Nat.pair a n)-1)

def upperSequence (σ f : ℕ → ℕ) (a n : ℕ) : ℕ :=
  iterateSuccessor (selectedBase σ f a n) (n+1)

theorem sequenceBody_apply {C : AlphaTerm} {σ : ℕ → ℕ}
    (hC : NumericalComputes C σ) {q : ℕ} {f : ℕ → ℕ}
    (hq : NumericalComputes (Term.closedProgram q) f) (a n : ℕ) :
    Relation.ReflTransGen Beta (sequenceBody C (numeral q) (numeral a) (numeral n))
      (numeral (upperSequence σ f a n)) := by
  have hs : Relation.ReflTransGen Beta (sequenceSlot C (numeral a) (numeral n))
      (numeral (σ (Nat.pair a n))) :=
    (beta_steps_app_right C (numericalPairTerm_apply a n)).trans (hC.2 _)
  have hp := (beta_steps_app_right predecessorTerm hs).trans (predecessorTerm_apply _)
  have he := (beta_steps_app_right (app outputSearchTerm (numeral q)) hp).trans
    ((outputSearchTerm_runs_iff q _ _).mpr (hq.2 _))
  have hb := (chooseLeBody_steps hs .refl .refl he).trans
    (chooseLeBody_apply (σ (Nat.pair a n)) 0 1 (f (σ (Nat.pair a n)-1)))
  have hb' : Relation.ReflTransGen Beta
      (sequenceBase C (numeral q) (numeral a) (numeral n))
      (numeral (selectedBase σ f a n)) := by
    simpa only [sequenceBase,selectedBase,Nat.le_zero] using hb
  have hpair := (beta_steps_app (beta_steps_app_right numericalPairTerm hb')
    (successorTerm_apply n)).trans (numericalPairTerm_apply _ (n+1))
  have h := (beta_steps_app_right iterateSuccessorProgram hpair).trans
    (iterateSuccessorProgram_computes.2 (Nat.pair (selectedBase σ f a n) (n+1)))
  simpa only [sequenceBody,Nat.unpair_pair,upperSequence] using h

/-- Its argument order is n,(q,a), so the existing right specialization applies. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix any closed numerical selector $C$, and let $\sigma(a,n)$ be its value at $\NatPair{a}{n}$. This may be the
    predecessor selector just constructed. For numerical arguments $q,a,n$, expand the following expressions before
    abstracting their variables:
    $$\begin{aligned}
    Z&:=C(\LambdaNumericPair\,a\,n),\\
    V&:=\LambdaLeCase{Z}{\ChurchNumeral{0}}{\ChurchNumeral{1}}{
     \LambdaOutputSearch\,q\,(\LambdaPred\,Z)},\\
    L(q,a,n)&:=\LambdaNotationIterate\,(\LambdaNumericPair\,V\,(\LambdaSucc\,n)),\\
    T&:=\lambdaab{n}{\lambdaab{z}{
     L(\LambdaNumericProjection{1}z,\LambdaNumericProjection{2}z,n)}}.
    \end{aligned}$$
    Use $n=x_{84}$ and $z=x_{85}$ as the two outer binders. Fix a named representative of the closed term $T$, with code
    $u$, and put
    $$s(q,a):=\LambdaSpecializationCode{u}{\NatPair{q}{a}},\qquad
     g_q(a):=3\cdot5^{s(q,a)}.$$
    The specialization-code term, numerical pairing and $\LambdaLimitCodeProgram$ compute these total maps. They do not run
    $T$ or $P_q$ while producing the codes.
-/
def sequenceTemplate (C : AlphaTerm) : AlphaTerm := lam 84 (lam 85
  (sequenceBody C (app (numericalProjectionTerm true) (var 85))
    (app (numericalProjectionTerm false) (var 85)) (var 84)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix any closed numerical selector $C$, and let $\sigma(a,n)$ be its value at $\NatPair{a}{n}$. This may be the
    predecessor selector just constructed. For numerical arguments $q,a,n$, expand the following expressions before
    abstracting their variables:
    $$\begin{aligned}
    Z&:=C(\LambdaNumericPair\,a\,n),\\
    V&:=\LambdaLeCase{Z}{\ChurchNumeral{0}}{\ChurchNumeral{1}}{
     \LambdaOutputSearch\,q\,(\LambdaPred\,Z)},\\
    L(q,a,n)&:=\LambdaNotationIterate\,(\LambdaNumericPair\,V\,(\LambdaSucc\,n)),\\
    T&:=\lambdaab{n}{\lambdaab{z}{
     L(\LambdaNumericProjection{1}z,\LambdaNumericProjection{2}z,n)}}.
    \end{aligned}$$
    Use $n=x_{84}$ and $z=x_{85}$ as the two outer binders. Fix a named representative of the closed term $T$, with code
    $u$, and put
    $$s(q,a):=\LambdaSpecializationCode{u}{\NatPair{q}{a}},\qquad
     g_q(a):=3\cdot5^{s(q,a)}.$$
    The specialization-code term, numerical pairing and $\LambdaLimitCodeProgram$ compute these total maps. They do not run
    $T$ or $P_q$ while producing the codes.
-/
theorem sequenceTemplate_closed {C : AlphaTerm} (hC : C.Closed) : (sequenceTemplate C).Closed := by
  unfold sequenceTemplate Closed
  simp only [fv_lam,sequenceBody_fv hC,fv_app,fv_var,
    (show (numericalProjectionTerm true).fv = ∅ from numericalProjectionTerm_closed true),
    (show (numericalProjectionTerm false).fv = ∅ from numericalProjectionTerm_closed false)]
  decide

theorem sequenceTemplate_start {C : AlphaTerm} (hC : C.Closed) (q a n : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (sequenceTemplate C) (numeral n)) (numeral (Nat.pair q a)))
      (sequenceBody C (numeral q) (numeral a) (numeral n)) := by
  have h₁ : Beta (app (sequenceTemplate C) (numeral n)) (lam 85
      (sequenceBody C (app (numericalProjectionTerm true) (var 85))
        (app (numericalProjectionTerm false) (var 85)) (numeral n))) := by
    unfold sequenceTemplate
    convert Beta.contract 84 (lam 85
      (sequenceBody C (app (numericalProjectionTerm true) (var 85))
        (app (numericalProjectionTerm false) (var 85)) (var 84))) (numeral n) using 1
    rw [subst_lam_fresh _ _ 85 84 (by decide) (by rw [numeral_closed]; simp)]
    simp [sequenceBody_subst hC,subst_app,subst_var,
      subst_closed _ _ _ (numericalProjectionTerm_closed true),
      subst_closed _ _ _ (numericalProjectionTerm_closed false)]
  have h₂ : Beta (app (lam 85
      (sequenceBody C (app (numericalProjectionTerm true) (var 85))
        (app (numericalProjectionTerm false) (var 85)) (numeral n))) (numeral (Nat.pair q a)))
      (sequenceBody C (app (numericalProjectionTerm true) (numeral (Nat.pair q a)))
        (app (numericalProjectionTerm false) (numeral (Nat.pair q a))) (numeral n)) := by
    convert Beta.contract 85
      (sequenceBody C (app (numericalProjectionTerm true) (var 85))
        (app (numericalProjectionTerm false) (var 85)) (numeral n)) (numeral (Nat.pair q a)) using 1
    simp [sequenceBody_subst hC,subst_app,subst_var,
      subst_closed _ _ _ (numericalProjectionTerm_closed true),
      subst_closed _ _ _ (numericalProjectionTerm_closed false),subst_closed _ _ _ (numeral_closed n)]
  apply (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
  have hp := sequenceBody_steps (C := C)
    (numericalProjectionTerm_apply true (Nat.pair q a))
    (numericalProjectionTerm_apply false (Nat.pair q a))
    (Relation.ReflTransGen.refl (a := numeral n))
  simpa only [Nat.unpair_pair,ite_true,ite_false,Bool.false_eq_true] using hp

/-- The family and every sequence program are total, before any well-order hypothesis. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: A total family of delayed limit codes
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    For any $q,a$, the specialization identity gives one beta step from the left-hand starting term in the displayed
    equivalence to the right-hand starting term. Confluence and normality of numerals give the reverse implication for
    outputs, so the equivalence is exact even when no output exists. For the selected self-index, two beta contractions
    and numerical projections supply $q,a,n$ to $L$. The selector returns its state. A zero state selects one; a state
    $b+1$ sends the numeral for $b$ to the universal evaluator, which returns $g_q(b)$ because $P_q$ is total.
    The successor-iteration program then returns the asserted value. All these reductions are finite.
    Applying the limit rule when the sequence is valid and increasing proves the final qualification.
    The well-founded argument in §{sec:edst-ordinal-notations} establishes those hypotheses for the predecessor selector.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The same section constructs a closed sequence template with code $u$. If a total indexed program $P_q$ computes a
    function $g$, its specialization with parameter $\NatPair{q}{a}$ has index $s(q,a)$ and computes
    $$\begin{aligned}
    b_a(n)&:=\begin{cases}
     1,&\KleenePredMax{a}{n}=0,\\
     g(b),&\KleenePredMax{a}{n}=b+1,
     \end{cases}\\
    c_a(n)&:=\KleeneSuccIter{b_a(n)}{n+1}.
    \end{aligned}$$
    The map $(q,a)\mapsto s(q,a)$ constructs finite syntax and is total. Apply the self-reference construction to the
    closed program computing $3\cdot5^{s(q,a)}$. It supplies a single index $q$ whose total numerical function is
    $$g(a):=3\cdot5^{s(q,a)}.$$
    This program returns a code without running the sequence it codes. Consequently there is no circular termination
    argument: $g$ is total first, and then every $c_a$ is total. The code $s(q,a)$ computes precisely $c_a$
    for this same $g$.
-/
theorem exists_computed_upper_sequences {C : AlphaTerm} {σ : ℕ → ℕ}
    (hC : NumericalComputes C σ) :
    ∃ (u q : ℕ), NumericalComputes (Term.closedProgram q) (delayedLimit u q) ∧
      ∀ a, NumericalComputes (Term.closedProgram (sequenceIndex u q a))
        (upperSequence σ (delayedLimit u q) a) := by
  obtain ⟨T,hT⟩ := Quotient.exists_rep (sequenceTemplate C)
  have hc : T.fv = ∅ := by
    have := sequenceTemplate_closed hC.1
    rw [← hT] at this
    exact this
  have ht : Term.closedProgram T.code = sequenceTemplate C := by
    simp only [Term.closedProgram,Term.decode_code,hc,ite_true]
    exact hT
  obtain ⟨q,hq⟩ := exists_delayed_limit_family T.code
  refine ⟨T.code,q,hq,fun a => ⟨Term.closedProgram_closed _,fun n => ?_⟩⟩
  apply (sequenceIndex_runs_iff _ _ _ _ _ (by simpa only [Term.decode_code] using hc)).mpr
  rw [ht]
  exact (sequenceTemplate_start hC.1 q a n).trans (sequenceBody_apply hC hq a n)

theorem sequenceTemplate_subst_selector (C : AlphaTerm) (hC : C.Closed) :
    (sequenceTemplate (var 86)).subst 86 C = sequenceTemplate C := by
  unfold sequenceTemplate
  rw [subst_lam_fresh _ _ 84 86 (by decide) (by rw [hC]; simp),
    subst_lam_fresh _ _ 85 86 (by decide) (by rw [hC]; simp)]
  simp only [sequenceBody, sequenceBase, sequenceSlot, subst_app, chooseLeBody_subst,
    subst_var, subst_closed _ _ _ iterateSuccessorProgram_computes.1,
    subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ outputSearchTerm_closed, subst_closed _ _ _ predecessorTerm_closed,
    subst_closed _ _ _ successorTerm_closed,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false),
    subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1)]
  norm_num

/-- A single template compiler works for every supplied closed selector syntax. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform upper-sequence indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    In $T(C)$, replace the selector by the free variable $x_{86}$, leaving the outer binders $x_{84},x_{85}$
    unchanged. Fix one named representative of this term. The substitution construction of
    §{sec:lambda-code-substitution} computes $u(c)$ by inserting the syntax decoded from $c$ for $x_{86}$.
    For a closed inserted term, substitution passes under the two outer binders and leaves every closed component
    unchanged; hence the result is exactly $T(P_c)$ up to alpha-equivalence. Apply the uniform delayed-limit
    constructor to $u(c)$ to obtain $q(c)$. Pairing and specialization compute $s(c,a)$ jointly in its two inputs.
    The delayed-limit identity proves totality of $g_c$ before the selector is executed. When the selector is total,
    the sequence-template reductions already proved give the displayed values. No representative is chosen as a
    function of the input code, and no test of totality or well-foundedness is performed by these constructors.
-/
theorem uniform_sequence_templates :
    ∃ U u, NumericalComputes U u ∧ ∀ c, (Term.decode c).fv = ∅ →
      (Term.decode (u c)).fv = ∅ ∧
      Term.closedProgram (u c) = sequenceTemplate (Term.closedProgram c) := by
  obtain ⟨U,u,hU,hu⟩ := uniform_closed_template_indices (sequenceTemplate (var 86)) 86
    (fun C hC => by rw [sequenceTemplate_subst_selector C hC]; exact sequenceTemplate_closed hC)
  refine ⟨U,u,hU,fun c hc => ?_⟩
  obtain ⟨ht,hp⟩ := hu c hc
  exact ⟨ht,hp.trans (sequenceTemplate_subst_selector _ (Term.closedProgram_closed c))⟩

theorem sequenceIndex_computable {U Q : AlphaTerm} {u q : ℕ → ℕ}
    (hU : NumericalComputes U u) (hQ : NumericalComputes Q q) :
    ∃ J, NumericalComputes J
      (fun z => sequenceIndex (u z.unpair.1) (q z.unpair.1) z.unpair.2) := by
  have h₁ := hU.comp (projection_computes true)
  have h₂ := (hQ.comp (projection_computes true)).pair (projection_computes false)
  exact ⟨_,h₁.combine h₂ specializationCodeTerm_closed _ specializationCodeTerm_apply⟩

/-- Both indices are generated from the selector's syntax code, before assuming it total. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform upper-sequence indices
-/
theorem uniform_computed_upper_sequences :
    ∃ U Q J u q, NumericalComputes U u ∧ NumericalComputes Q q ∧
      NumericalComputes J
        (fun z => sequenceIndex (u z.unpair.1) (q z.unpair.1) z.unpair.2) ∧
      (∀ c, NumericalComputes (Term.closedProgram (q c)) (delayedLimit (u c) (q c))) ∧
      ∀ c, (Term.decode c).fv = ∅ → ∀ σ,
        NumericalComputes (Term.closedProgram c) σ →
          ∀ a, NumericalComputes (Term.closedProgram (sequenceIndex (u c) (q c) a))
            (upperSequence σ (delayedLimit (u c) (q c)) a) := by
  obtain ⟨U,u,hU,hu⟩ := uniform_sequence_templates
  obtain ⟨R,r,hR,hr⟩ := uniform_delayed_limit_families
  have hQ := hR.comp hU
  obtain ⟨J,hJ⟩ := sequenceIndex_computable hU hQ
  refine ⟨U,_,J,u,fun c => r (u c),hU,hQ,hJ,fun c => hr (u c),fun c hc σ hC => ?_⟩
  obtain ⟨ht,hp⟩ := hu c hc
  have hq := hr (u c)
  refine fun a => ⟨Term.closedProgram_closed _,fun n => ?_⟩
  apply (sequenceIndex_runs_iff _ _ _ _ _ ht).mpr
  rw [hp]
  exact (sequenceTemplate_start hC.1 _ a n).trans (sequenceBody_apply hC hq a n)

end KleeneNotation
end PolishSpaceBook
