module

public import PolishSpaceBook.LambdaRelativeJump
public import PolishSpaceBook.LambdaUniformPredicates

@[expose] public section

/-! # Uniform halting questions answered by one lambda jump

The index transformation inserts a fixed numerical argument into a closed
program and ignores the eventual diagonal argument. Both the transformation
and the decision procedure are concrete closed lambda terms.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def fixedInputProgram (P : AlphaTerm) (n : ℕ) : AlphaTerm :=
  lam 1 (lam 2 (app (app P (var 1)) (numeral n)))

theorem fixedInputProgram_closed {P : AlphaTerm} (hP : P.Closed) (n : ℕ) :
    (fixedInputProgram P n).Closed := by
  unfold fixedInputProgram Closed
  simp only [fv_lam,fv_app,fv_var,(show P.fv = ∅ from hP),(show (numeral n).fv = ∅ from numeral_closed n)]
  decide

theorem fixedInputProgram_start {P : AlphaTerm} (hP : P.Closed) (n t : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (fixedInputProgram P n) (var 0)) (numeral t))
      (app (app P (var 0)) (numeral n)) := by
  have h₁ : Beta (app (fixedInputProgram P n) (var 0))
      (lam 2 (app (app P (var 0)) (numeral n))) := by
    unfold fixedInputProgram
    convert Beta.contract 1 _ (var 0) using 1
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app,subst_var,subst_closed _ _ _ hP,subst_closed _ _ _ (numeral_closed n)]
  have h₂ : Beta (app (lam 2 (app (app P (var 0)) (numeral n))) (numeral t))
      (app (app P (var 0)) (numeral n)) := by
    convert Beta.contract 2 _ (numeral t) using 1
    simp [subst_app,subst_var,subst_closed _ _ _ hP,subst_closed _ _ _ (numeral_closed n)]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The enumeration supplies the code of the selected closed program from $e$, and
    $\LambdaNumeralCodeProgram$ supplies the code of $\ChurchNumeral{n}$. Two application-code constructors
    and two abstraction-code constructors form the displayed term. Composing their closed numerical
    implementations gives $F$, independently of $\varepsilon$.
    For every numerical input $t$, two beta contractions reduce $D_{e,n}o\ChurchNumeral{t}$ to
    $P_eo\ChurchNumeral{n}$. Prefixing those steps preserves every output. Conversely, confluence and
    terminality of numerals carry every output of the first term to the second. Set $t=h(e,n)$ to obtain
    the equivalence. The term $H$ computes this index and makes one query, so it returns exactly the
    zero-or-one answer to the halting question.
    \end{proof}
-/
theorem fixedInputProgram_runs_iff {P : AlphaTerm} (hP : P.Closed)
    (ε : ℕ → ℕ) (n t m : ℕ) :
    OracleRuns ε (fixedInputProgram P n) t m ↔ OracleRuns ε P n m := by
  have hs := beta_steps_oracle (p := ε) (fixedInputProgram_start hP n t)
  exact ⟨oracle_numeral_after_reduction hs,fun h => hs.trans h⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Retain $K^\varepsilon$ from §{sec:lambda-relative-jump}, and put $\varepsilon':=\chi_{K^\varepsilon}$.
    Choose the named closed representative of $P_e$ supplied by the program enumeration. Define
    $$D_{e,n}:=\lambdaab{o}{\lambdaab{t}{P_eo\ChurchNumeral{n}}},\qquad
     h(e,n):=\LambdaSyntaxCode{D_{e,n}}.$$
    Here the syntax code is formed from that named representative, and the bound variables are fresh.
    The program enumeration retains this closed term at its syntax index.
-/
def fixedInputSyntax (P : Term) (n : ℕ) : Term :=
  .lam 1 (.lam 2 (.app (.app P (.var 1)) (Term.churchNumeral n)))

theorem mk_fixedInputSyntax (P : Term) (n : ℕ) :
    mk (fixedInputSyntax P n) = fixedInputProgram (mk P) n := by
  change lam 1 (lam 2 (app (app (mk P) (var 1)) (mk (Term.churchNumeral n)))) = _
  rw [Term.mk_churchNumeral]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Retain $K^\varepsilon$ from §{sec:lambda-relative-jump}, and put $\varepsilon':=\chi_{K^\varepsilon}$.
    Choose the named closed representative of $P_e$ supplied by the program enumeration. Define
    $$D_{e,n}:=\lambdaab{o}{\lambdaab{t}{P_eo\ChurchNumeral{n}}},\qquad
     h(e,n):=\LambdaSyntaxCode{D_{e,n}}.$$
    Here the syntax code is formed from that named representative, and the bound variables are fresh.
    The program enumeration retains this closed term at its syntax index.
-/
def haltingIndex (z : ℕ) : ℕ :=
  (fixedInputSyntax (Term.programSyntax z.unpair.1) z.unpair.2).code

def haltingIndexProgram : AlphaTerm :=
  codeTagProgram 2 (numericalConstant 1)
    (codeTagProgram 2 (numericalConstant 2)
      (codeTagProgram 1
        (codeTagProgram 1 (numericalCompose programCodeTerm (numericalProjectionTerm true))
          (numericalConstant 3))
        (numericalCompose numeralCodeTerm (numericalProjectionTerm false))))

theorem haltingIndexProgram_computes : NumericalComputes haltingIndexProgram haltingIndex := by
  have hP : NumericalComputes programCodeTerm (fun e => (Term.programSyntax e).code) :=
    ⟨programCodeTerm_closed,programCodeTerm_apply⟩
  have hN : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  unfold haltingIndex
  simpa [haltingIndexProgram,fixedInputSyntax,Term.code] using
    codeTagProgram_computes (numericalConstant_computes 1)
      (codeTagProgram_computes (numericalConstant_computes 2)
        (codeTagProgram_computes
          (codeTagProgram_computes (hP.comp (projection_computes true)) (numericalConstant_computes 3) 1)
          (hN.comp (projection_computes false)) 1) 2) 2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Retain $K^\varepsilon$ from §{sec:lambda-relative-jump}, and put $\varepsilon':=\chi_{K^\varepsilon}$.
    Choose the named closed representative of $P_e$ supplied by the program enumeration. Define
    $$D_{e,n}:=\lambdaab{o}{\lambdaab{t}{P_eo\ChurchNumeral{n}}},\qquad
     h(e,n):=\LambdaSyntaxCode{D_{e,n}}.$$
    Here the syntax code is formed from that named representative, and the bound variables are fresh.
    The program enumeration retains this closed term at its syntax index.
-/
theorem closedProgram_haltingIndex (z : ℕ) :
    Term.closedProgram (haltingIndex z) = fixedInputProgram (Term.closedProgram z.unpair.1) z.unpair.2 := by
  have hc : (fixedInputSyntax (Term.programSyntax z.unpair.1) z.unpair.2).fv = ∅ := by
    have h := fixedInputProgram_closed (Term.closedProgram_closed z.unpair.1) z.unpair.2
    rw [← Term.mk_programSyntax,← mk_fixedInputSyntax] at h
    exact h
  simp only [haltingIndex,Term.closedProgram,Term.decode_code,hc,ite_true,mk_fixedInputSyntax,
    Term.mk_programSyntax]

theorem haltingIndex_mem_jump (ε : ℕ → ℕ) (z : ℕ) :
    haltingIndex z ∈ Jump ε ↔ ∃ m, OracleRuns ε (Term.closedProgram z.unpair.1) z.unpair.2 m := by
  simp only [Jump,Set.mem_ofPred_eq,closedProgram_haltingIndex,
    fixedInputProgram_runs_iff (Term.closedProgram_closed z.unpair.1)]

def haltingDecisionProgram : AlphaTerm :=
  queryOutputProgram (liftNumericalProgram haltingIndexProgram)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Uniform reduction of numerical halting
-/
theorem haltingDecisionProgram_decides (ε : ℕ → ℕ) :
    Decides (characteristic (Jump ε)) haltingDecisionProgram
      (fun z : ℕ => ∃ m, OracleRuns ε (Term.closedProgram z.unpair.1) z.unpair.2 m) := by
  classical
  have hc := haltingIndexProgram_computes.uniform.query
  refine ⟨hc.1,fun z => ⟨?_,?_⟩⟩ <;> intro hz
  · simpa only [characteristic,haltingIndex_mem_jump,hz,ite_true,Encodable.encode_nat,haltingDecisionProgram] using hc.2 (characteristic (Jump ε)) z
  · simpa only [characteristic,haltingIndex_mem_jump,hz,ite_false,Encodable.encode_nat,haltingDecisionProgram] using hc.2 (characteristic (Jump ε)) z

/-- Acceptance is first converted to exact numerical halting, including divergent inputs. -/
theorem SemidecidablePredicate.decidable_jump {ε : ℕ → ℕ} {R : ℕ → Prop}
    (hR : SemidecidablePredicate ε R) : DecidablePredicate (characteristic (Jump ε)) R := by
  obtain ⟨P,hP,hdom⟩ := (semidecidable_iff_domain ε R).mp hR
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
  have h := (haltingDecisionProgram_decides ε).precompNumerical
    ((numericalConstant_computes e).pair numericalIdentity_computes)
    (g := fun n : ℕ => Nat.pair e n) (by simp)
  simp only [Encodable.encode_nat] at hdom
  refine ⟨reindexProgram haltingDecisionProgram (pairNumerical (numericalConstant e) numericalIdentity),?_⟩
  simpa only [Nat.unpair_pair,he,← hdom] using h

end LambdaRelative
end PolishSpaceBook
