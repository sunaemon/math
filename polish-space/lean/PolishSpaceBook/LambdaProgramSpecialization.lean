module

public import PolishSpaceBook.LambdaUniformInterpreter
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! # Constructing specialization codes in lambda calculus

The primitive-recursion claims concern numerical syntax constructors. The
executable code transformation is itself a closed lambda term.
-/
namespace PolishSpaceBook.NamedLambda
namespace Term

def specializeSyntax (P : Term) (e : ℕ) : Term :=
  .lam 40 (.app (.app P (.var 40)) (churchNumeral e))

theorem mk_specializeSyntax (P : Term) (e : ℕ) :
    AlphaTerm.mk (specializeSyntax P e) = AlphaTerm.specializeProgram (AlphaTerm.mk P) e := by
  change AlphaTerm.lam 40 (AlphaTerm.app (AlphaTerm.app (AlphaTerm.mk P) (AlphaTerm.var 40))
    (AlphaTerm.mk (churchNumeral e))) = _
  rw [mk_churchNumeral]
  rfl

def specializationCode (u e : ℕ) : ℕ :=
  3 * Nat.pair 40 (3 * Nat.pair (3 * Nat.pair u 120 + 1) (churchNumeral e).code + 1) + 2

theorem specializeSyntax_code (P : Term) (e : ℕ) :
    (specializeSyntax P e).code = specializationCode P.code e := rfl

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Specialization on syntax codes
-/
theorem decode_specializationCode (u e : ℕ) :
    decode (specializationCode u e) = specializeSyntax (decode u) e := by
  have h := decode_code (specializeSyntax (decode u) e)
  simpa only [specializeSyntax_code, code_decode] using h

theorem closedProgram_specializationCode (u e : ℕ) (hu : (decode u).fv = ∅) :
    closedProgram (specializationCode u e) =
      AlphaTerm.specializeProgram (closedProgram u) e := by
  have hc : (specializeSyntax (decode u) e).fv = ∅ := by
    have h := AlphaTerm.specializeProgram_closed (P := AlphaTerm.mk (decode u)) hu e
    rw [← mk_specializeSyntax] at h
    exact h
  simp only [closedProgram, decode_specializationCode, hc, hu, ite_true, mk_specializeSyntax]

/-- This is the numerical recurrence used by the already constructed numeral-code term. -/
theorem primrec_churchBody_code : Primrec (fun n => (churchBody n).code) := by
  let f : ℕ → ℕ → ℕ := fun _ b => 3 * Nat.pair 3 b + 1
  have hf : Primrec₂ f := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec₂.natPair.comp (Primrec.const 3) Primrec.snd)) (Primrec.const 1)
  have h := Primrec.nat_rec₁ 6 hf
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [f, churchBody, code, ih]

theorem primrec_churchNumeral_code : Primrec (fun n => (churchNumeral n).code) := by
  have h := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 3)
            (Primrec₂.natPair.comp (Primrec.const 2) primrec_churchBody_code)) (Primrec.const 2))))
    (Primrec.const 2)
  exact h

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Specialization on syntax codes
-/
theorem primrec_specializationCode : Primrec₂ specializationCode := by
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec₂.natPair.comp (Primrec.const 40)
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 3)
            (Primrec₂.natPair.comp
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp (Primrec.const 3)
                  (Primrec₂.natPair.comp Primrec.fst (Primrec.const 120))) (Primrec.const 1))
              (primrec_churchNumeral_code.comp Primrec.snd))) (Primrec.const 1)))) (Primrec.const 2)

end Term
namespace AlphaTerm
set_option maxRecDepth 4096

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1
private theorem abstractionCode_closed : abstractionCodeTerm.Closed := taggedPairCodeTerm_closed 2

def specializationCodeBody (U E : AlphaTerm) : AlphaTerm :=
  app (app abstractionCodeTerm (numeral 40))
    (app (app applicationCodeTerm (app (app applicationCodeTerm U) (numeral 120)))
      (app numeralCodeTerm E))

theorem specializationCodeBody_fv (U E : AlphaTerm) :
    (specializationCodeBody U E).fv = U.fv ∪ E.fv := by
  ext x
  simp only [specializationCodeBody, fv_app,
    (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed),
    (show applicationCodeTerm.fv = ∅ from applicationCode_closed),
    (show numeralCodeTerm.fv = ∅ from numeralCodeTerm_closed),
    (show (numeral 40).fv = ∅ from numeral_closed 40),
    (show (numeral 120).fv = ∅ from numeral_closed 120),
    Finset.mem_union, Finset.notMem_empty]
  tauto

theorem specializationCodeBody_subst (U E W : AlphaTerm) (x : ℕ) :
    (specializationCodeBody U E).subst x W =
      specializationCodeBody (U.subst x W) (E.subst x W) := by
  simp only [specializationCodeBody, subst_app,
    subst_closed _ _ _ abstractionCode_closed, subst_closed _ _ _ applicationCode_closed,
    subst_closed _ _ _ numeralCodeTerm_closed, subst_closed _ _ _ (numeral_closed 40),
    subst_closed _ _ _ (numeral_closed 120)]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical formula is implemented by the closed lambda term
    $$\begin{aligned}
    \LambdaSpecializationCodeProgram:=\lambdaab{u}{\lambdaab{e}{
     \LambdaTaggedCode{2}\,\ChurchNumeral{40}\,\bigl(\\
     \qquad\LambdaTaggedCode{1}\,
       (\LambdaTaggedCode{1}\,u\,\ChurchNumeral{120})\,
       (\LambdaNumeralCodeProgram\,e)\bigr)}}.
    \end{aligned}$$
-/
def specializationCodeTerm : AlphaTerm :=
  lam 30 (lam 31 (specializationCodeBody (var 30) (var 31)))

@[simp] theorem specializationCodeTerm_closed : specializationCodeTerm.Closed := by
  unfold specializationCodeTerm Closed
  simp only [fv_lam, specializationCodeBody_fv, fv_var]
  decide

theorem specializationCodeTerm_start (u e : ℕ) :
    Relation.ReflTransGen Beta (app (app specializationCodeTerm (numeral u)) (numeral e))
      (specializationCodeBody (numeral u) (numeral e)) := by
  have h₁ : Beta (app specializationCodeTerm (numeral u))
      (lam 31 (specializationCodeBody (numeral u) (var 31))) := by
    convert Beta.contract 30 (lam 31 (specializationCodeBody (var 30) (var 31))) (numeral u) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 31 30 (by decide) (by rw [numeral_closed]; simp)]
    simp [specializationCodeBody_subst, subst_var]
  have h₂ : Beta (app (lam 31 (specializationCodeBody (numeral u) (var 31))) (numeral e))
      (specializationCodeBody (numeral u) (numeral e)) := by
    convert Beta.contract 31 (specializationCodeBody (numeral u) (var 31)) (numeral e) using 1
    simp [specializationCodeBody_subst, subst_var, subst_closed _ _ _ (numeral_closed u)]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Specialization on syntax codes
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Two beta contractions supply the arguments. Compute the numeral code, then the two application codes, and finally the abstraction code. The code-decoding identities identify the result with the stated named term for every $u$. On alpha-classes this term is $\LambdaIndexSpecialization{P}{e}$ when $P$ is the decoded closed term; its only additional variable is bound by the outer abstraction.

    For primitive recursiveness, let $c_n$ be the code of the body of the fixed Church numeral before its two abstractions. Then
    $$c_0=6,\qquad c_{n+1}=3\NatPair{3}{c_n}+1,
    \qquad\LambdaSyntaxCode{\ChurchNumeral{n}}=3\NatPair{1}{3\NatPair{2}{c_n}+2}+2.$$
    Primitive recursion computes $c_n$. Pairing, addition and multiplication then compute the numeral code and the displayed specialization formula. This proves the primitive-recursion claim without assuming an unspecified compiler.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The numerical formula is implemented by the closed lambda term
    $$\begin{aligned}
    \LambdaSpecializationCodeProgram:=\lambdaab{u}{\lambdaab{e}{
     \LambdaTaggedCode{2}\,\ChurchNumeral{40}\,\bigl(\\
     \qquad\LambdaTaggedCode{1}\,
       (\LambdaTaggedCode{1}\,u\,\ChurchNumeral{120})\,
       (\LambdaNumeralCodeProgram\,e)\bigr)}}.
    \end{aligned}$$
-/
theorem specializationCodeTerm_apply (u e : ℕ) :
    Relation.ReflTransGen Beta (app (app specializationCodeTerm (numeral u)) (numeral e))
      (numeral (Term.specializationCode u e)) := by
  apply (specializationCodeTerm_start u e).trans
  have hv := applicationCodeTerm_apply (Term.decode u) (.var 40)
  rw [Term.code_decode] at hv
  have hi := (beta_steps_app
    (beta_steps_app_right applicationCodeTerm hv) (numeralCodeTerm_apply e)).trans
      (applicationCodeTerm_apply (.app (Term.decode u) (.var 40)) (Term.churchNumeral e))
  have ho := (beta_steps_app_right (app abstractionCodeTerm (numeral 40)) hi).trans
    (abstractionCodeTerm_apply 40 (.app (.app (Term.decode u) (.var 40)) (Term.churchNumeral e)))
  change Relation.ReflTransGen Beta (specializationCodeBody (numeral u) (numeral e))
    (numeral (Term.specializeSyntax (Term.decode u) e).code) at ho
  simpa only [Term.specializeSyntax_code, Term.code_decode] using ho

theorem specializationCode_evaluator (u e : ℕ)
    (hu : mk (Term.decode u) = oracleOutputSearchTerm) (p : ℕ → ℕ) (n m : ℕ) :
    OracleRuns p (Term.closedProgram (Term.specializationCode u e)) n m ↔
      OracleRuns p (Term.closedProgram e) n m := by
  have hc : (Term.decode u).fv = ∅ := by
    have h := oracleOutputSearchTerm_closed
    rw [← hu] at h
    exact h
  rw [Term.closedProgram_specializationCode u e hc]
  have he : Term.closedProgram u = oracleOutputSearchTerm := by
    simp only [Term.closedProgram, hc, ite_true, hu]
  rw [he]
  exact specializedEvaluator_runs_iff p e n m

/-- The syntax of the evaluator is fixed once, before any oracle or index is supplied. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Choose one named representative of $\LambdaQueryOutputSearch$ and fix its code $u$ once. The single primitive-recursive map $e\mapsto\LambdaSpecializationCode{u}{e}$ then gives, for every input name, a program with exactly the same partial numerical evaluation as $P_e$. Its code is computed by $\LambdaSpecializationCodeProgram\,\ChurchNumeral{u}$, which is closed. Thus the transformation is fixed before the input name and the program index are supplied.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    We next compute the syntax code of the specialized program. For the fixed named representatives, set
    $$\begin{aligned}
    \LambdaSpecializationCode{u}{e}:=
     3\NatPair{40}{3\NatPair{3\NatPair{u}{120}+1}{\LambdaSyntaxCode{\ChurchNumeral{e}}}+1}+2.
    \end{aligned}$$
    Here $120$ is the code of $x_{40}$. The inner two application codes attach this variable and the numeral to the term
    coded by $u$; the final abstraction binds $x_{40}$. This formula is defined for every pair of natural numbers, even when
    the decoded term is open.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The universal interpreter in §{sec:lambda-program-specialization} evaluates a supplied program index on a supplied
    numerical input with the same name argument. It preserves both numerical outputs and undefinedness, and fixing
    the program index is a primitive-recursive transformation of syntax codes. We use it below to evaluate function names.
-/
theorem exists_uniform_specialization_code :
    ∃ u : ℕ, Primrec (Term.specializationCode u) ∧
      ∀ e p n m, OracleRuns p (Term.closedProgram (Term.specializationCode u e)) n m ↔
        OracleRuns p (Term.closedProgram e) n m := by
  obtain ⟨U,hU⟩ := Quotient.exists_rep oracleOutputSearchTerm
  have hu : mk (Term.decode U.code) = oracleOutputSearchTerm := by
    rw [Term.decode_code]
    exact hU
  exact ⟨U.code, Term.primrec_specializationCode.comp (Primrec.const U.code) Primrec.id,
    fun e p n m => specializationCode_evaluator U.code e hu p n m⟩

end AlphaTerm
end PolishSpaceBook.NamedLambda
