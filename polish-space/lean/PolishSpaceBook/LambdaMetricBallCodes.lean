module

public import PolishSpaceBook.LambdaMetricBalls
public import PolishSpaceBook.LambdaFunctionCodes

@[expose] public section

/-! # Compiling a rational ball into its lambda semidecider

The compiler inserts a numerical ball code into fixed named syntax templates.
It is both primitive recursive on codes and computed by a closed lambda term.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaFunction

private theorem syntax_const (T : Term) : CodeTransform (fun _ : ℕ => T.code) := CodeTransform.const _
private theorem syntax_app {F G : ℕ → Term}
    (hF : CodeTransform (fun b => (F b).code)) (hG : CodeTransform (fun b => (G b).code)) :
    CodeTransform (fun b => (Term.app (F b) (G b)).code) := hF.app hG
private theorem syntax_lam {F : ℕ → Term} (hF : CodeTransform (fun b => (F b).code)) (x : ℕ) :
    CodeTransform (fun b => (Term.lam x (F b)).code) := hF.lam x

def insertBallSyntax (K : Term) (b : ℕ) : Term :=
  .lam 40 (.app (.app K (Term.churchNumeral b)) (.var 40))

def reindexSyntax (P F : Term) : Term :=
  .lam 1 (.lam 2 (.app (.app P (.var 1)) (.app F (.var 2))))

def digitSearchSyntax (Z S I P : Term) : Term :=
  .lam 40 (.lam 42 (.app (.app S
    (.lam 41 (.app (.app (.app Z (.app (.app P (.var 40)) (.var 41)))
      (Term.churchNumeral 1)) (Term.churchNumeral 0)))) I))

def ballSemideciderSyntax (K P Z S I : Term) (b : ℕ) : Term :=
  digitSearchSyntax Z S I (reindexSyntax P (insertBallSyntax K b))

theorem insertBallSyntax_transform (K : Term) : CodeTransform (fun b => (insertBallSyntax K b).code) := by
  exact syntax_lam (syntax_app (syntax_app (syntax_const K) numeralCode_transform)
    (syntax_const (.var 40))) 40

theorem reindexSyntax_transform (P : Term) {F : ℕ → Term}
    (hF : CodeTransform (fun b => (F b).code)) :
    CodeTransform (fun b => (reindexSyntax P (F b)).code) := by
  exact syntax_lam (syntax_lam
    (syntax_app (syntax_app (syntax_const P) (syntax_const (.var 1)))
      (syntax_app hF (syntax_const (.var 2)))) 2) 1

theorem digitSearchSyntax_transform (Z S I : Term) {P : ℕ → Term}
    (hP : CodeTransform (fun b => (P b).code)) :
    CodeTransform (fun b => (digitSearchSyntax Z S I (P b)).code) := by
  have hp := syntax_app (syntax_app hP (syntax_const (.var 40))) (syntax_const (.var 41))
  have hg := syntax_lam (syntax_app (syntax_app (syntax_app (syntax_const Z) hp)
    (syntax_const (Term.churchNumeral 1))) (syntax_const (Term.churchNumeral 0))) 41
  exact syntax_lam (syntax_lam (syntax_app (syntax_app (syntax_const S) hg) (syntax_const I)) 42) 40

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    For the code transformation, fix named representatives of $T$, numerical pairing, zero testing, result search and the identity. First compute the code of $\ChurchNumeral{b}$. Application and abstraction constructors then build $F_b$, insert it into the fixed template $\LambdaBallTest{b}$, and insert that result into $G_{b,o}$ and $\LambdaBallSemidecider{b}$. Decoding each constructed code recovers exactly the corresponding named term. Closedness ensures that the program enumeration retains this term. The constructors are the numerical maps $(u,v)\mapsto3\NatPair{u}{v}+1$ and $(x,u)\mapsto3\NatPair{x}{u}+2$. They and the numeral-code map are primitive recursive and computed by closed lambda terms. Their finite composition proves both assertions about the compiler. No digit of $p$ is used in constructing the code.
-/
theorem ballSemideciderSyntax_transform (K P Z S I : Term) :
    CodeTransform (fun b => (ballSemideciderSyntax K P Z S I b).code) :=
  digitSearchSyntax_transform Z S I (reindexSyntax_transform P (insertBallSyntax_transform K))

theorem mk_insertBallSyntax (K : Term) (hK : mk K = numericalPairTerm) (b : ℕ) :
    mk (insertBallSyntax K b) = insertBallCode b := by
  change lam 40 (app (app (mk K) (mk (Term.churchNumeral b))) (var 40)) = _
  rw [hK,Term.mk_churchNumeral]; rfl

theorem mk_reindexSyntax (P F : Term) :
    mk (reindexSyntax P F) = reindexProgram (mk P) (mk F) := rfl

theorem mk_digitSearchSyntax (Z S I P : Term)
    (hZ : mk Z = zeroTestTerm) (hS : mk S = resultSearchTerm) (hI : mk I = identityProgram) :
    mk (digitSearchSyntax Z S I P) = digitSearchProgram (mk P) := by
  change lam 40 (lam 42 (app (app (mk S)
    (lam 41 (app (app (app (mk Z) (app (app (mk P) (var 40)) (var 41)))
      (mk (Term.churchNumeral 1))) (mk (Term.churchNumeral 0))))) (mk I))) = _
  rw [hZ,hS,hI,Term.mk_churchNumeral,Term.mk_churchNumeral]; rfl

/-- For fixed distance data, the ball code alone determines the compiled syntax. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact semidecision and its code transformation
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    At the code level, insert the numeral for $b$ into a fixed stage template and then into the displayed search template.
    The syntax constructors and the numeral-code program compute this transformation by a closed lambda term; the same
    formulas prove primitive recursiveness. The construction is independent of the input name.
    §{sec:lambda-rational-ball-programs} gives the stage term, the code templates and their correctness proofs. No positive
    lower bound on the distance to the boundary is required as input.
-/
theorem exists_metric_ball_compiler (M : AlphaTerm) (hM : M.Closed) :
    ∃ f : ℕ → ℕ, CodeTransform f ∧
      ∀ b, Term.closedProgram (f b) = metricBallSemidecider M b := by
  obtain ⟨K,hK⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨P,hP⟩ := Quotient.exists_rep (metricStageProgram M)
  obtain ⟨Z,hZ⟩ := Quotient.exists_rep zeroTestTerm
  obtain ⟨S,hS⟩ := Quotient.exists_rep resultSearchTerm
  obtain ⟨I,hI⟩ := Quotient.exists_rep identityProgram
  change mk K = numericalPairTerm at hK
  change mk P = metricStageProgram M at hP
  change mk Z = zeroTestTerm at hZ
  change mk S = resultSearchTerm at hS
  change mk I = identityProgram at hI
  refine ⟨fun b => (ballSemideciderSyntax K P Z S I b).code,
    ballSemideciderSyntax_transform K P Z S I,fun b => ?_⟩
  apply closedProgram_eq_of_mk_decode
  · simp only [Term.decode_code,ballSemideciderSyntax,mk_digitSearchSyntax Z S I _ hZ hS hI,
      mk_reindexSyntax,mk_insertBallSyntax K hK,hP]
    rfl
  · exact metricBallSemidecider_closed hM b

end LambdaFunction
end PolishSpaceBook
