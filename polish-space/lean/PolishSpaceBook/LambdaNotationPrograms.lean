module

public import PolishSpaceBook.LambdaRecursionTheorem
public import PolishSpaceBook.LambdaKleeneNotations
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

/-! # Delayed limit codes for recursively defined notation families

Producing a limit code constructs syntax; it does not evaluate the sequence
whose program is being coded. The resulting numerical family is total even
when the supplied sequence template is partial.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation

def iterateSuccessor (a : ℕ) : ℕ → ℕ
  | 0 => a
  | n+1 => successorCode (iterateSuccessor a n)

def iterateSuccessorProgram : AlphaTerm := numericalRecursion numericalIdentity
  (numericalCompose powerTwoTerm
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    We also need numerical programs for the notation constructors. Recall
    $\KleeneSuccIter{a}{0}=a$ and $\KleeneSuccIter{a}{k+1}=2^{\KleeneSuccIter{a}{k}}$.
    \begin{mathmeta}
      \define{LambdaNotationIterate,LambdaLimitCodeProgram}
    \end{mathmeta}
    Primitive recursion, with initial value $a$ and update $r\mapsto2^r$, gives a closed term
    $\LambdaNotationIterate$ computing $\KleeneSuccIter{a}{n}$ on input $\NatPair{a}{n}$.
    Primitive recursion with initial value one and update $r\mapsto5r$, followed by multiplication by three, gives a closed
    term $\LambdaLimitCodeProgram$ computing $e\mapsto3\cdot5^e$. Both computations terminate on all numerical inputs.
    For a valid starting notation, successor iteration remains valid and is strictly increasing in its iteration count.
-/
theorem iterateSuccessorProgram_computes : NumericalComputes iterateSuccessorProgram
    (fun z => iterateSuccessor z.unpair.1 z.unpair.2) := by
  have h := numericalRecursion_computes numericalIdentity_computes
    (powerTwo_computes.comp ((projection_computes false).comp (projection_computes false)))
  simp only [id_eq,Bool.false_eq_true,ite_false,Nat.unpair_pair] at h
  convert h using 1 <;> try rfl
  funext z
  induction z.unpair.2 with
  | zero => rfl
  | succ n ih => simpa only [iterateSuccessor,successorCode,primitiveRec] using congrArg (2^·) ih

theorem iterateSuccessor_valid {a : ℕ} (ha : Valid a) (n : ℕ) : Valid (iterateSuccessor a n) := by
  induction n with
  | zero => exact ha
  | succ n ih => exact .succ ih

theorem iterateSuccessor_step {a : ℕ} (ha : Valid a) (n : ℕ) :
    RawPrecedes (iterateSuccessor a n) (iterateSuccessor a (n+1)) :=
  .single (.succ _ (iterateSuccessor_valid ha n).pos)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Write $\KleeneSuccIter{a}{0}:=a$ and $\KleeneSuccIter{a}{k+1}:=2^{\KleeneSuccIter{a}{k}}$.
    For a valid $a$, these are successive valid notations. In particular,
    $\KleenePrecedes{\KleeneSuccIter{a}{k}}{\KleeneSuccIter{a}{k+1}}$.
-/
/-- Successor iteration stays within valid notations and their generated precedence. -/
theorem iterateSuccessor_valid_precedes {a : ℕ} (ha : Valid a) (n : ℕ) :
    Valid (iterateSuccessor a n) ∧
      Precedes (iterateSuccessor a n) (iterateSuccessor a (n+1)) :=
  ⟨iterateSuccessor_valid ha n,
    (precedes_iff _ _).mpr ⟨iterateSuccessor_step ha n, iterateSuccessor_valid ha (n+1)⟩⟩

theorem iterateSuccessor_precedes {a : ℕ} (ha : Valid a) {m n : ℕ} (h : m < n) :
    RawPrecedes (iterateSuccessor a m) (iterateSuccessor a n) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt h)
  clear h
  induction k with
  | zero => simpa using iterateSuccessor_step ha m
  | succ k ih => exact .tail ih (.succ _ (iterateSuccessor_valid ha _).pos)

def powerFiveProgram : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant 1)
    (mulNumerical (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
      (numericalConstant 5)))
  (pairNumerical (numericalConstant 0) numericalIdentity)

theorem powerFiveProgram_computes : NumericalComputes powerFiveProgram (fun n => 5^n) := by
  have h := (numericalRecursion_computes (numericalConstant_computes 1)
    (((projection_computes false).comp (projection_computes false)).mul
      (numericalConstant_computes 5))).comp
    ((numericalConstant_computes 0).pair numericalIdentity_computes)
  simp only [id_eq,Bool.false_eq_true,ite_false,Nat.unpair_pair] at h
  convert h using 1 <;> try rfl
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ,primitiveRec] using congrArg (· * 5) ih

def limitCodeProgram : AlphaTerm := mulNumerical (numericalConstant 3) powerFiveProgram

theorem limitCodeProgram_computes : NumericalComputes limitCodeProgram limitCode :=
  (numericalConstant_computes 3).mul powerFiveProgram_computes

/-- q is the self-index, a the family argument, and u the fixed sequence template. -/
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
def sequenceIndex (u q a : ℕ) : ℕ := Term.specializationCode u (Nat.pair q a)

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
def delayedLimit (u q a : ℕ) : ℕ := limitCode (sequenceIndex u q a)

def delayedLimitProgram (u : ℕ) : AlphaTerm := numericalCompose limitCodeProgram
  (numericalCompose (app specializationCodeTerm (numeral u)) numericalIdentity)

theorem specializationAt_computes (u : ℕ) :
    NumericalComputes (app specializationCodeTerm (numeral u)) (Term.specializationCode u) :=
  ⟨closed_app specializationCodeTerm_closed (numeral_closed u),specializationCodeTerm_apply u⟩

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
theorem delayedLimitProgram_computes (u : ℕ) :
    NumericalComputes (delayedLimitProgram u)
      (fun z => delayedLimit u z.unpair.1 z.unpair.2) := by
  simpa only [delayedLimitProgram,delayedLimit,sequenceIndex,Nat.pair_unpair,id_eq] using
    limitCodeProgram_computes.comp ((specializationAt_computes u).comp numericalIdentity_computes)

/-- This total family returns limit codes without running their sequence programs. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    By numerical composition, construct a closed term $F_u$ computing
    $\NatPair{q}{a}\mapsto3\cdot5^{\LambdaSpecializationCode{u}{\NatPair{q}{a}}}$.
    Let $H$ be its numerical currying, so $H\ChurchNumeral{q}\ChurchNumeral{a}$ reduces to
    $F_u\ChurchNumeral{\NatPair{q}{a}}$. The self-reference lemma of §{sec:lambda-index-recursion} gives $q$ with
    $$P_q\ChurchNumeral{a}\to_\beta^*H\ChurchNumeral{q}\ChurchNumeral{a}
     \to_\beta^*\ChurchNumeral{g_q(a)}.$$
    This proves totality without a hypothesis about the sequence values.
-/
theorem exists_delayed_limit_family (u : ℕ) :
    ∃ q : ℕ, NumericalComputes (Term.closedProgram q) (delayedLimit u q) := by
  let H := curryNumerical (delayedLimitProgram u)
  have hH := curryNumerical_closed (delayedLimitProgram_computes u).1
  obtain ⟨q,hq⟩ := exists_self_reference H hH
  refine ⟨q,Term.closedProgram_closed q,fun a => ?_⟩
  have h := (hq (numeral a) (by rw [numeral_closed]; simp)).trans
    ((curryNumerical_apply (delayedLimitProgram_computes u).1 q a).trans
      ((delayedLimitProgram_computes u).2 (Nat.pair q a)))
  simpa only [Nat.unpair_pair] using h

def delayedFamilySyntax (L S : Term) (u : ℕ) : Term :=
  .lam 40 (.app L (.app (.app S (Term.churchNumeral u)) (.var 40)))

def delayedFamilyCode (L S : Term) (u : ℕ) : ℕ := (delayedFamilySyntax L S u).code

theorem delayedFamilyCode_computable (L S : Term) :
    ∃ D, NumericalComputes D (delayedFamilyCode L S) := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  have h := ((numericalConstant_computes L.code).applicationCode
    (((numericalConstant_computes S.code).applicationCode hn).applicationCode
      (numericalConstant_computes 120))).abstractionCode 40
  refine ⟨_,h.1,fun u => ?_⟩
  simpa only [delayedFamilyCode, delayedFamilySyntax, Term.code] using h.2 u

theorem delayedFamilyCode_spec (L S : Term) (hL : mk L = limitCodeProgram)
    (hS : mk S = specializationCodeTerm) (u : ℕ) :
    (Term.decode (delayedFamilyCode L S u)).fv = ∅ ∧
      NumericalComputes (Term.closedProgram (delayedFamilyCode L S u))
        (fun z => delayedLimit u z.unpair.1 z.unpair.2) := by
  have hm : mk (delayedFamilySyntax L S u) =
      numericalCompose limitCodeProgram (app specializationCodeTerm (numeral u)) := by
    change lam 40 (app (mk L) (app (app (mk S) (mk (Term.churchNumeral u))) (var 40))) = _
    rw [hL,hS,Term.mk_churchNumeral]
    rfl
  have h := limitCodeProgram_computes.comp (specializationAt_computes u)
  have hc : (delayedFamilySyntax L S u).fv = ∅ := by
    have hh := h.1
    rw [← hm] at hh
    exact hh
  constructor
  · simpa only [delayedFamilyCode, Term.decode_code] using hc
  · simp only [delayedFamilyCode, Term.closedProgram, Term.decode_code, hc, ite_true, hm]
    simpa only [delayedLimit, sequenceIndex, Nat.pair_unpair] using h

/-- The self-index is computed from the sequence-template code, even for partial templates. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: corollary
  title: Uniform delayed-limit indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Fix representatives of $\LambdaLimitCodeProgram$ and $\LambdaSpecializationCodeProgram$. The numeral-code,
    application-code and abstraction-code constructors compute from $u$ the code of the closed term
    $$F_u:=\lambdaab{z}{\LambdaLimitCodeProgram
     (\LambdaSpecializationCodeProgram\,\ChurchNumeral{u}\,z)}.$$
    This term computes $z\mapsto3\cdot5^{\LambdaSpecializationCode{u}{z}}$ on every input.
    Apply the uniform self-indexed-family constructor of §{sec:lambda-index-recursion} to its code.
    Composition computes the resulting $q(u)$ from $u$. The family identity gives the displayed value at every $a$.
    These assertions concern numerical codes; validity of a resulting ordinal notation still requires the
    validity and strict-increase hypotheses for the sequence it codes.
-/
theorem uniform_delayed_limit_families :
    ∃ Q q, NumericalComputes Q q ∧ ∀ u,
      NumericalComputes (Term.closedProgram (q u)) (delayedLimit u (q u)) := by
  obtain ⟨L,hL⟩ := Quotient.exists_rep limitCodeProgram
  obtain ⟨S,hS⟩ := Quotient.exists_rep specializationCodeTerm
  obtain ⟨D,hD⟩ := delayedFamilyCode_computable L S
  obtain ⟨F,r,hF,hr⟩ := uniform_self_indexed_family_indices
  refine ⟨_,fun u => r (delayedFamilyCode L S u),hF.comp hD,fun u => ?_⟩
  obtain ⟨hc,hp⟩ := delayedFamilyCode_spec L S hL hS u
  simpa only [Nat.unpair_pair] using hr (delayedFamilyCode L S u) hc _ hp

/-- Specialization retains exact numerical behavior, including lack of output. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: A total family of delayed limit codes
-/
theorem sequenceIndex_runs_iff (u q a n m : ℕ) (hu : (Term.decode u).fv = ∅) :
    Runs (sequenceIndex u q a) n m ↔
      Relation.ReflTransGen Beta
        (app (app (Term.closedProgram u) (numeral n)) (numeral (Nat.pair q a))) (numeral m) := by
  unfold Runs sequenceIndex
  rw [Term.closedProgram_specializationCode u _ hu]
  have hs : Beta
      (app (specializeProgram (Term.closedProgram u) (Nat.pair q a)) (numeral n))
      (app (app (Term.closedProgram u) (numeral n)) (numeral (Nat.pair q a))) := by
    simpa only [specializeProgram,subst_app,subst_var,ite_true,
      subst_closed _ _ _ (Term.closedProgram_closed u),
      subst_closed _ _ _ (numeral_closed (Nat.pair q a))] using
      Beta.contract 40 (app (app (Term.closedProgram u) (var 40)) (numeral (Nat.pair q a))) (numeral n)
  exact ⟨numeral_after_reduction (.single hs),fun h => (Relation.ReflTransGen.single hs).trans h⟩

/-- The constructor's totality does not assert validity of any of its outputs. -/
theorem delayedLimit_valid (u q a : ℕ) (hu : (Term.decode u).fv = ∅)
    (f : ℕ → ℕ)
    (hf : ∀ n, Relation.ReflTransGen Beta
      (app (app (Term.closedProgram u) (numeral n)) (numeral (Nat.pair q a))) (numeral (f n)))
    (hv : ∀ n, Valid (f n)) (hi : ∀ n, RawPrecedes (f n) (f (n+1))) :
    Valid (delayedLimit u q a) := by
  apply Valid.limit (sequenceIndex u q a) f
    ⟨Term.closedProgram_closed _,fun n => (sequenceIndex_runs_iff u q a n (f n) hu).mpr (hf n)⟩ hv hi

end KleeneNotation
end PolishSpaceBook
