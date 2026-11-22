module

public import PolishSpaceBook.LambdaCantorDerivative
public import PolishSpaceBook.LambdaJumpCompiler
public import PolishSpaceBook.LambdaRelativeComposition

@[expose] public section

/-! # A numerical lambda compiler for Cantor derivative programs

Choose one finite-matrix program with a membership oracle. Substitute the
supplied tree program for that oracle by a computable syntax construction,
then apply the two-quantifier index transformation twice.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaRelative LambdaTree
namespace CantorDerivative
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private def SyntaxComputable (T : ℕ → Term) : Prop :=
  ∃ F, NumericalComputes F (fun e => (T e).code)

private theorem syntax_const (P : Term) : SyntaxComputable (fun _ => P) :=
  ⟨numericalConstant P.code,numericalConstant_computes P.code⟩

private theorem syntax_app {P Q : ℕ → Term} (hP : SyntaxComputable P)
    (hQ : SyntaxComputable Q) : SyntaxComputable (fun e => .app (P e) (Q e)) := by
  obtain ⟨F,hF⟩ := hP
  obtain ⟨G,hG⟩ := hQ
  exact ⟨codeTagProgram 1 F G,codeTagProgram_computes hF hG 1⟩

private theorem syntax_lam {P : ℕ → Term} (hP : SyntaxComputable P) (x : ℕ) :
    SyntaxComputable (fun e => .lam x (P e)) := by
  obtain ⟨F,hF⟩ := hP
  exact ⟨codeTagProgram 2 (numericalConstant x) F,
    codeTagProgram_computes (numericalConstant_computes x) hF 2⟩

private theorem syntax_program : SyntaxComputable Term.programSyntax :=
  ⟨programCodeTerm,programCodeTerm_closed,programCodeTerm_apply⟩

private def matrixSyntax (M : Term) (e : ℕ) : Term :=
  .lam 1 (.lam 2 (.app (.app M (.app (Term.programSyntax e) (.var 1))) (.var 2)))

private theorem mk_matrixSyntax (M : Term) (e : ℕ) :
    mk (matrixSyntax M e) = compositionProgram (mk M) (Term.closedProgram e) := by
  simp only [matrixSyntax,← lam_mk,← app_mk,Term.mk_programSyntax]
  rfl

private theorem matrixSyntax_computable (M : Term) : SyntaxComputable (matrixSyntax M) :=
  syntax_lam (syntax_lam (syntax_app
    (syntax_app (syntax_const M) (syntax_app syntax_program (syntax_const (.var 1))))
    (syntax_const (.var 2))) 2) 1

/-- The matrix compiler is chosen once, before the tree, its index, and its parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    To compute a derivative-program index directly from a tree-program index, fix
    $I:=\lambdaab{o}{o}$ and let $M$ be the finite matrix program constructed above
    with $P=I$. For a tree $T$, let $\chi_T$ be the function on word codes that returns $1$ for
    membership in $T$ and $0$ otherwise. At input function $\chi_T$, the term $I$ decides membership
    in $T$, so $M$ decides the finite matrix. If $P_e$ decides membership in $T$ at $\varepsilon$,
    it computes $\chi_T$ at that parameter. Substitution of this accessor therefore gives
    $$A_e:=\lambdaab{o}{\lambdaab{z}{M\,(P_eo)\,z}},$$
    which decides the same matrix at $\varepsilon$.
    
    Choose a named representative $M_0$ of $M$ once. Let $Q_e$ be the closed named representative
    of $P_e$ from §{sec:lambda-program-input-codes}, whose code is computed from $e$ by
    $\LambdaProgramCode$. With $o=x_1$ and $z=x_2$, define
    $$a(e):=\LambdaSyntaxCode{\lambdaab{x_1}{\lambdaab{x_2}{M_0\,(Q_ex_1)\,x_2}}}.$$
    Starting from the fixed code of $M_0$ and the computed code of $Q_e$, apply the application-code
    constructor three times and the abstraction-code constructor twice. Thus a closed numerical
    lambda term computes $a$ on every natural number, even when $e$ decodes to an open term;
    in that case the definition of $Q_e$ supplies the closed zero numeral. Decoding gives exactly
    $A_e$, since both inserted terms are closed.
-/
theorem matrix_index_transform :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (T : Set (List ℕ)),
        Decides ε (Term.closedProgram e) (fun n : ℕ => NatListCode.decode n ∈ T) →
        Decides ε (Term.closedProgram (f e)) (matrix T) := by
  classical
  have hI : UniformNumericalComputes identityProgram (fun p n => p n) :=
    ⟨identityProgram_closed,identityProgram_runs⟩
  obtain ⟨M,hM,hm⟩ := matrix_program _ hI.1
  obtain ⟨A,hA⟩ := Quotient.exists_rep M
  change mk A = M at hA
  obtain ⟨F,hF⟩ := matrixSyntax_computable A
  refine ⟨F,(fun e => (matrixSyntax A e).code),hF,?_⟩
  intro e ε T hd
  let χ : ℕ → ℕ := fun n => if NatListCode.decode n ∈ T then 1 else 0
  have hi : Decides χ identityProgram
      (fun n : ℕ => NatListCode.decode n ∈ T) := by
    refine ⟨hI.1,fun n => ⟨?_,?_⟩⟩
    · intro hn
      simpa [χ,hn] using hI.2 χ n
    · intro hn
      simpa [χ,hn] using hI.2 χ n
  have hc : Computes ε (Term.closedProgram e) χ := ⟨hd.1,fun n => hd.runs n⟩
  have he : Term.closedProgram (matrixSyntax A e).code =
      compositionProgram M (Term.closedProgram e) := by
    have hk : mk (matrixSyntax A e) = compositionProgram M (Term.closedProgram e) := by
      rw [mk_matrixSyntax,hA]
    have hf : (matrixSyntax A e).fv = ∅ := by
      change (mk (matrixSyntax A e)).Closed
      rw [hk]
      exact compositionProgram_closed hM hd.1
    simp only [Term.closedProgram,Term.decode_code,hf,ite_true,hk]
  rw [he]
  exact (hm χ T hi).changeParameter hc

/-- Four jumps suffice, with a total numerical lambda transformation of the tree index. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    It follows that the required transformation of tree-program indices is
    $$d(e):=\upsilon(\xi(\upsilon(\xi(a(e))))).$$
    All five numerical transformations have closed lambda implementations, so their composition does
    too. This supplies a computable choice of derivative indices, in addition to the uniform
    existence of a derivative program for each fixed tree program.
-/
theorem derivative_test_index_transform :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (T : Set (List ℕ)),
        Decides ε (Term.closedProgram e) (fun n : ℕ => NatListCode.decode n ∈ T) →
        Decides (fourthJump ε) (Term.closedProgram (f e))
          (fun s : ℕ => ∀ m, ∃ c, ∀ n, ∃ V, NumericTest T s m c n V) := by
  obtain ⟨F,f,hF,hf⟩ := matrix_index_transform
  obtain ⟨G,g,hG,hg⟩ := forall_exists_jump_index_transform
  refine ⟨numericalCompose G (numericalCompose G F),(fun e => g (g (f e))),
    hG.comp (hG.comp hF),?_⟩
  intro e ε T hd
  have hi := hg (f e) ε
    (fun a n V => NumericTest T a.unpair.1.unpair.1 a.unpair.1.unpair.2 a.unpair.2 n V)
    (hf e ε T hd)
  exact hg (g (f e)) (jumpName (jumpName ε))
    (fun s m c => ∀ n, ∃ V, NumericTest T s m c n V) hi

/-- The numeric criterion rejects nonbinary words as well as deciding valid word codes. -/
theorem derivative_code_iff {T : Set (List ℕ)} (hT : IsSubtree T) (s : ℕ) :
    (∀ m, ∃ c, ∀ n, ∃ V, NumericTest T s m c n V) ↔
      Binary s ∧ decodeWord s ∈ derivativeTree (binaryTree T) := by
  constructor
  · intro h
    obtain ⟨c,hc⟩ := h 0
    obtain ⟨V,hV⟩ := hc 0
    refine ⟨hV.1,?_⟩
    apply (derivative_numeric_iff hT (decodeWord s)).mpr
    rwa [encodeWord_decodeWord hV.1]
  · rintro ⟨hb,hs⟩
    have h := (derivative_numeric_iff hT (decodeWord s)).mp hs
    rwa [encodeWord_decodeWord hb] at h

/-- The compiler decides every numerical input, including invalid words and the empty tree. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Computable derivative indices
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the finite matrix construction with a membership oracle, obtaining one fixed closed term $M$.
    Given $e$, replace that oracle by $P_e$: the resulting term is
    $\lambdaab{o}{\lambdaab{z}{M\,(P_eo)\,z}}$.
    The syntax-code constructors compute its index $\CantorMatrixIndex{e}$ from $e$, as detailed in
    §{sec:lambda-cantor-derivative-programs}. Every query to the membership oracle is then answered
    by the supplied tree decider, so this term decides the finite matrix at $\varepsilon$.
    Compose this index map with the four numerical-quantifier index transformations. This gives a total
    lambda-computable function $\delta$; correctness follows from the finite matrix criterion and the
    quantifier transformations. The construction chooses $M$ once, before $e,T,\varepsilon$ are supplied.
    \end{proof}
-/
theorem derivative_index_transform :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (T : Set (List ℕ)), IsSubtree T →
        Decides ε (Term.closedProgram e) (fun n : ℕ => NatListCode.decode n ∈ T) →
        Decides (fourthJump ε) (Term.closedProgram (f e))
          (fun s : ℕ => Binary s ∧ decodeWord s ∈ derivativeTree (binaryTree T)) := by
  obtain ⟨F,f,hF,hf⟩ := derivative_test_index_transform
  refine ⟨F,f,hF,fun e ε T hsub hd => ?_⟩
  have h := hf e ε T hd
  refine ⟨h.1,fun s => ⟨?_,?_⟩⟩
  · intro hs
    exact (h.2 s).1 ((derivative_code_iff hsub s).mpr hs)
  · intro hs
    exact (h.2 s).2 (fun hn => hs ((derivative_code_iff hsub s).mp hn))

theorem derivative_word_index_transform :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ (e : ℕ) (ε : ℕ → ℕ) (T : Set (List ℕ)), IsSubtree T →
        Decides ε (Term.closedProgram e) (fun n : ℕ => NatListCode.decode n ∈ T) →
        ∀ s : List Bool,
          (s ∈ derivativeTree (binaryTree T) →
            OracleRuns (fourthJump ε) (Term.closedProgram (f e)) (encodeWord s) 1) ∧
          (s ∉ derivativeTree (binaryTree T) →
            OracleRuns (fourthJump ε) (Term.closedProgram (f e)) (encodeWord s) 0) := by
  obtain ⟨F,f,hF,hf⟩ := derivative_index_transform
  refine ⟨F,f,hF,fun e ε T hsub hd s => ?_⟩
  have h := hf e ε T hsub hd
  simpa only [binary_encodeWord,decodeWord_encodeWord,true_and,Encodable.encode_nat]
    using h.2 (encodeWord s)

end CantorDerivative
end PolishSpaceBook
