module

public import PolishSpaceBook.LambdaContinuousFunctionSpaces
public import PolishSpaceBook.LambdaProgramSpecialization

@[expose] public section

/-! # Explicit syntax-code transformations for function-space programs

The arithmetic formulas encode named lambda terms. Each formula is also
implemented by a closed lambda term; primitive recursiveness is not used as
an external execution backend.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaFunction
set_option maxRecDepth 4096

/-- Both the arithmetic classification and the actual lambda implementation. -/
def CodeTransform (f : ℕ → ℕ) : Prop := Primrec f ∧ ComputableName f

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    For completeness, these arithmetic compositions have actual lambda implementations. If closed terms $F,G$ compute two numerical functions and a closed term $B$ computes a binary operation, the term
    $$\lambdaab{x}{B\,(Fx)\,(Gx)}$$
    computes their pointwise combination: one beta step supplies the input, reduce the two inner computations, then reduce the application of $B$. Unary composition uses $\lambdaab{x}{F(Gx)}$ in the same way. Constants and the identity have closed numerical implementations. Iterating these constructions with the code constructors and numeral-code term gives a single closed program for each recipe. Induction through the named syntax, using the coding and decoding identities, identifies its output with the exact template code. Closedness follows because the inserted program terms have no free variables and the templates bind their displayed variables. This verifies both the code-level construction and the lambda program that performs it.
-/
private theorem computableName_binary {f g : ℕ → ℕ} (hf : ComputableName f)
    (hg : ComputableName g) (B : AlphaTerm) (hB : B.Closed) (b : ℕ → ℕ → ℕ)
    (hb : ∀ i j, Relation.ReflTransGen Beta (app (app B (numeral i)) (numeral j)) (numeral (b i j))) :
    ComputableName (fun n => b (f n) (g n)) := by
  obtain ⟨F,hF,hrF⟩ := hf
  obtain ⟨G,hG,hrG⟩ := hg
  let A := lam 40 (app (app B (app F (var 40))) (app G (var 40)))
  have hc : A.Closed := by
    unfold A Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [hB,hF,hG]
    simp
  refine ⟨A,hc,fun n => ?_⟩
  have he : (app (app B (app F (var 40))) (app G (var 40))).subst 40 (numeral n) =
      app (app B (app F (numeral n))) (app G (numeral n)) := by
    simp only [subst_app,subst_var,ite_true,subst_closed _ _ _ hB,
      subst_closed _ _ _ hF,subst_closed _ _ _ hG]
  have hs : Beta (app A (numeral n))
      (app (app B (app F (numeral n))) (app G (numeral n))) := by
    rw [← he]
    exact Beta.contract 40 _ _
  exact (Relation.ReflTransGen.single hs).trans ((beta_steps_app (beta_steps_app_right B (hrF n)) (hrG n)).trans (hb _ _))

private theorem computableName_comp {f g : ℕ → ℕ} (hf : ComputableName f)
    (hg : ComputableName g) : ComputableName (fun n => f (g n)) := by
  obtain ⟨F,hF,hrF⟩ := hf
  obtain ⟨G,hG,hrG⟩ := hg
  let A := lam 40 (app F (app G (var 40)))
  have hc : A.Closed := by
    unfold A Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [hF,hG]; simp
  refine ⟨A,hc,fun n => ?_⟩
  have he : (app F (app G (var 40))).subst 40 (numeral n) = app F (app G (numeral n)) := by
    simp only [subst_app,subst_var,ite_true,subst_closed _ _ _ hF,subst_closed _ _ _ hG]
  have hs : Beta (app A (numeral n)) (app F (app G (numeral n))) := by
    rw [← he]; exact Beta.contract 40 _ _
  exact (Relation.ReflTransGen.single hs).trans ((beta_steps_app_right F (hrG n)).trans (hrF _))

theorem CodeTransform.const (a : ℕ) : CodeTransform (fun _ => a) := by
  refine ⟨Primrec.const a, lam 40 (numeral a), ?_, fun n => ?_⟩
  · unfold Closed; rw [fv_lam,numeral_closed]; rfl
  · exact .single (by simpa only [subst_closed _ _ _ (numeral_closed a)] using
      (Beta.contract 40 (numeral a) (numeral n)))

theorem CodeTransform.id : CodeTransform id := by
  refine ⟨Primrec.id, lam 40 (var 40), ?_, fun n => ?_⟩
  · unfold Closed; rw [fv_lam,fv_var]; simp
  · exact .single (by simpa only [subst_var,ite_true,id_eq] using Beta.contract 40 (var 40) (numeral n))

theorem CodeTransform.comp {f g : ℕ → ℕ} (hf : CodeTransform f) (hg : CodeTransform g) :
    CodeTransform (fun n => f (g n)) := ⟨hf.1.comp hg.1, computableName_comp hf.2 hg.2⟩

def appCode (a b : ℕ) : ℕ := 3 * Nat.pair a b + 1
def lamCode (x a : ℕ) : ℕ := 3 * Nat.pair x a + 2

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    The code constructors for application and abstraction are, respectively,
    $$ (a,b)\longmapsto3\NatPair{a}{b}+1,
    \qquad (i,a)\longmapsto3\NatPair{i}{a}+2.$$
    They are primitive recursive and are computed by the closed terms $\LambdaTaggedCode{1}$ and $\LambdaTaggedCode{2}$. The variable codes of $x_1,x_2$ are $3,6$. The map $e\mapsto\LambdaSyntaxCode{\ChurchNumeral{e}}$ is primitive recursive and is computed by $\LambdaNumeralCodeProgram$, by §{sec:lambda-program-specialization}. For a composition template, attach $x_1$ to the inner program, apply the outer program to that result and $x_2$, then add the two abstractions. For a pairing template, apply each inserted program to $x_1,x_2$, apply numerical pairing to those two results, then add the abstractions. For a prefix template, insert the numeral code, form the zero test and predecessor-query branch, then add the abstractions. Applying these finite recipes to the nested uncurrying template gives the third transformation.
-/
theorem CodeTransform.tagged {f g : ℕ → ℕ} (hf : CodeTransform f) (hg : CodeTransform g)
    (t : ℕ) : CodeTransform (fun n => 3 * Nat.pair (f n) (g n) + t) := by
  refine ⟨Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 3) (Primrec₂.natPair.comp hf.1 hg.1)) (Primrec.const t), ?_⟩
  exact computableName_binary hf.2 hg.2 (taggedPairCodeTerm t) (taggedPairCodeTerm_closed t)
    (fun a b => 3 * Nat.pair a b + t) (taggedPairCodeTerm_apply t)

theorem CodeTransform.app {f g : ℕ → ℕ} (hf : CodeTransform f) (hg : CodeTransform g) :
    CodeTransform (fun n => appCode (f n) (g n)) := hf.tagged hg 1

theorem CodeTransform.lam {f : ℕ → ℕ} (hf : CodeTransform f) (x : ℕ) :
    CodeTransform (fun n => lamCode x (f n)) := (CodeTransform.const x).tagged hf 2

theorem numeralCode_transform : CodeTransform (fun n => (Term.churchNumeral n).code) :=
  ⟨Term.primrec_churchNumeral_code, numeralCodeTerm, numeralCodeTerm_closed, numeralCodeTerm_apply⟩

/-- Raw formula for the named composition term, with binders 1 and 2. -/
def composeCode (p q : ℕ) : ℕ :=
  lamCode 1 (lamCode 2 (appCode (appCode p (appCode q 3)) 6))

theorem CodeTransform.compose {f g : ℕ → ℕ} (hf : CodeTransform f) (hg : CodeTransform g) :
    CodeTransform (fun n => composeCode (f n) (g n)) :=
  ((hf.app (hg.app (CodeTransform.const 3))).app (CodeTransform.const 6)).lam 2 |>.lam 1

/-- Code of the pairing program, with a fixed representative of numerical pairing. -/
def pairCode (b p q : ℕ) : ℕ :=
  lamCode 1 (lamCode 2
    (appCode (appCode b (appCode (appCode p 3) 6)) (appCode (appCode q 3) 6)))

theorem CodeTransform.pair {f g : ℕ → ℕ} (b : ℕ) (hf : CodeTransform f) (hg : CodeTransform g) :
    CodeTransform (fun n => pairCode b (f n) (g n)) :=
  (((CodeTransform.const b).app ((hf.app (CodeTransform.const 3)).app (CodeTransform.const 6))).app
    ((hg.app (CodeTransform.const 3)).app (CodeTransform.const 6))).lam 2 |>.lam 1

/-- The raw named syntax behind the composition formula. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
def composeSyntax (P Q : Term) : Term :=
  .lam 1 (.lam 2 (.app (.app P (.app Q (.var 1))) (.var 2)))

theorem composeSyntax_code (P Q : Term) : (composeSyntax P Q).code = composeCode P.code Q.code := rfl

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
theorem mk_composeSyntax (P Q : Term) :
    mk (composeSyntax P Q) = compositionProgram (mk P) (mk Q) := rfl

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
def pairSyntax (B P Q : Term) : Term := .lam 1 (.lam 2
  (.app (.app B (.app (.app P (.var 1)) (.var 2))) (.app (.app Q (.var 1)) (.var 2))))

theorem pairSyntax_code (B P Q : Term) : (pairSyntax B P Q).code = pairCode B.code P.code Q.code := rfl

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
theorem mk_pairSyntax (B P Q : Term) (hB : mk B = numericalPairTerm) :
    mk (pairSyntax B P Q) = pairOutputProgram (mk P) (mk Q) := by
  change lam 1 (lam 2 (app (app (mk B) (app (app (mk P) (var 1)) (var 2)))
    (app (app (mk Q) (var 1)) (var 2)))) = _
  rw [hB]; rfl

/-- Prefix the input index itself; the numerical index is encoded as a Church numeral. -/
def curryCode (z d e : ℕ) : ℕ := lamCode 1 (lamCode 2
  (appCode (appCode (appCode z 6) (Term.churchNumeral e).code) (appCode 3 (appCode d 6))))

theorem curryCode_transform (z d : ℕ) : CodeTransform (curryCode z d) :=
  ((((CodeTransform.const z).app (CodeTransform.const 6)).app numeralCode_transform).app
    ((CodeTransform.const 3).app ((CodeTransform.const d).app (CodeTransform.const 6)))).lam 2 |>.lam 1

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
def currySyntax (Z D : Term) (e : ℕ) : Term := .lam 1 (.lam 2
  (.app (.app (.app Z (.var 2)) (Term.churchNumeral e)) (.app (.var 1) (.app D (.var 2)))))

theorem currySyntax_code (Z D : Term) (e : ℕ) :
    (currySyntax Z D e).code = curryCode Z.code D.code e := rfl

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
theorem mk_currySyntax (Z D : Term) (hZ : mk Z = zeroTestTerm) (hD : mk D = predecessorTerm) (e : ℕ) :
    mk (currySyntax Z D e) = tagProgram e := by
  change lam 1 (lam 2 (app (app (app (mk Z) (var 2)) (mk (Term.churchNumeral e)))
    (app (var 1) (app (mk D) (var 2))))) = _
  rw [hZ,hD,Term.mk_churchNumeral]; rfl

/-- Compile the explicit uncurrying term with fixed evaluator and projection codes. -/
def uncurryCode (b u l r e : ℕ) : ℕ := composeCode u (pairCode b (composeCode e l) r)

theorem uncurryCode_transform (b u l r : ℕ) : CodeTransform (uncurryCode b u l r) :=
  (CodeTransform.const u).compose
    ((CodeTransform.id.compose (CodeTransform.const l)).pair b (CodeTransform.const r))

/-- All arithmetic constructors decode to the very syntax they purport to build. -/
theorem decode_composeCode (p q : ℕ) :
    Term.decode (composeCode p q) = composeSyntax (Term.decode p) (Term.decode q) := by
  simpa only [composeSyntax_code,Term.code_decode] using Term.decode_code (composeSyntax (Term.decode p) (Term.decode q))

theorem decode_curryCode (Z D : Term) (e : ℕ) :
    Term.decode (curryCode Z.code D.code e) = currySyntax Z D e :=
  Term.decode_code (currySyntax Z D e)

theorem decode_pairCode (B : Term) (p q : ℕ) :
    Term.decode (pairCode B.code p q) = pairSyntax B (Term.decode p) (Term.decode q) := by
  simpa only [pairSyntax_code,Term.code_decode] using Term.decode_code (pairSyntax B (Term.decode p) (Term.decode q))

theorem closedProgram_eq_of_mk_decode {e : ℕ} {P : AlphaTerm}
    (he : mk (Term.decode e) = P) (hP : P.Closed) : Term.closedProgram e = P := by
  have hc : (Term.decode e).fv = ∅ := by rw [← he] at hP; exact hP
  simp only [Term.closedProgram,hc,ite_true,he]

/-- Constants are chosen once; the compiler thereafter is uniform in the input index. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Function-space transformations on syntax codes
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The code transformations used above have concrete lambda implementations: §{sec:lambda-function-code-transforms}
    constructs prefixing and uncurrying directly from syntax constructors and the numeral-code program. For an arbitrary
    enumeration index, first specialize the universal evaluator to that index. This gives a closed syntax code with the same
    partial numerical behavior for every input name, to which the templates apply. The normalization and subsequent
    transformation are both primitive recursive and are computed by closed lambda terms.
-/
theorem exists_curry_compiler : ∃ f : ℕ → ℕ, CodeTransform f ∧
    ∀ e, Term.closedProgram (f e) = tagProgram e := by
  obtain ⟨Z,hZ⟩ := Quotient.exists_rep zeroTestTerm
  obtain ⟨D,hD⟩ := Quotient.exists_rep predecessorTerm
  refine ⟨curryCode Z.code D.code,curryCode_transform _ _,fun e => ?_⟩
  apply closedProgram_eq_of_mk_decode _ (tagProgram_closed e)
  rw [decode_curryCode,mk_currySyntax Z D hZ hD]

/-- The result is exactly the lambda expression used to realize uncurrying. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Function-space transformations on syntax codes
-/
theorem exists_uncurry_compiler : ∃ f : ℕ → ℕ, CodeTransform f ∧
    ∀ e, (Term.decode e).fv = ∅ → Term.closedProgram (f e) =
      compositionProgram evaluationProgram
        (pairOutputProgram (compositionProgram (Term.closedProgram e) leftProgram) rightProgram) := by
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨U,hU⟩ := Quotient.exists_rep evaluationProgram
  obtain ⟨L,hL⟩ := Quotient.exists_rep leftProgram
  obtain ⟨R,hR⟩ := Quotient.exists_rep rightProgram
  change mk U = evaluationProgram at hU
  change mk L = leftProgram at hL
  change mk R = rightProgram at hR
  refine ⟨uncurryCode B.code U.code L.code R.code,uncurryCode_transform _ _ _ _,fun e he => ?_⟩
  have hp : mk (Term.decode e) = Term.closedProgram e := by simp [Term.closedProgram,he]
  apply closedProgram_eq_of_mk_decode
  · simp only [uncurryCode,decode_composeCode,Term.decode_code,decode_pairCode,
      mk_composeSyntax,mk_pairSyntax B _ _ hB,hp,hU,hL,hR]
  · exact compositionProgram_closed evaluationProgram_closed
      (pairOutputProgram_closed
        (compositionProgram_closed (Term.closedProgram_closed e) (leftProgram_computes Set.univ).1)
        (rightProgram_computes Set.univ).1)

/-- Reassociation is another instance of the same composition-code constructor. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Function-space transformations on syntax codes
-/
theorem exists_continuous_curry_compiler : ∃ f : ℕ → ℕ, CodeTransform f ∧
    ∀ e, (Term.decode e).fv = ∅ →
      Term.closedProgram (f e) = continuousCurryProgram (Term.closedProgram e) := by
  obtain ⟨A,hA⟩ := Quotient.exists_rep associateProgram
  change mk A = associateProgram at hA
  refine ⟨fun e => composeCode e A.code,CodeTransform.id.compose (CodeTransform.const _),fun e he => ?_⟩
  have hp : mk (Term.decode e) = Term.closedProgram e := by simp [Term.closedProgram,he]
  apply closedProgram_eq_of_mk_decode
  · simp only [decode_composeCode,mk_composeSyntax,Term.decode_code,hp,hA,continuousCurryProgram]
  · exact continuousCurryProgram_closed (Term.closedProgram_closed e)

/-- Normalize every enumeration index to a genuinely closed syntax code by
specializing the already proved evaluator. This also handles open input syntax. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Finally, fix the code $u$ of a named representative of $\LambdaQueryOutputSearch$. On any enumeration index $e$, first compute $\LambdaSpecializationCode{u}{e}$. By §{sec:lambda-program-specialization}, it decodes to a closed term with exactly the same partial numerical behavior as $P_e$, even if the raw syntax decoded from $e$ is open. The preceding transformations therefore apply to this closed code. Composition preserves primitive recursiveness and the closed lambda implementations. No answers from an input name are placed in these finite codes.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The code transformations used above have concrete lambda implementations: §{sec:lambda-function-code-transforms}
    constructs prefixing and uncurrying directly from syntax constructors and the numeral-code program. For an arbitrary
    enumeration index, first specialize the universal evaluator to that index. This gives a closed syntax code with the same
    partial numerical behavior for every input name, to which the templates apply. The normalization and subsequent
    transformation are both primitive recursive and are computed by closed lambda terms.
-/
theorem exists_normalization_compiler : ∃ f : ℕ → ℕ, CodeTransform f ∧
    ∀ e, (Term.decode (f e)).fv = ∅ ∧ ∀ p n m,
      OracleRuns p (Term.closedProgram (f e)) n m ↔ OracleRuns p (Term.closedProgram e) n m := by
  obtain ⟨U,hU⟩ := Quotient.exists_rep oracleOutputSearchTerm
  change mk U = oracleOutputSearchTerm at hU
  have huc : U.fv = ∅ := by
    have h := oracleOutputSearchTerm_closed
    rw [← hU] at h
    exact h
  have ht : CodeTransform (Term.specializationCode U.code) := by
    refine ⟨Term.primrec_specializationCode.comp (Primrec.const U.code) Primrec.id, ?_⟩
    exact computableName_binary (CodeTransform.const U.code).2 CodeTransform.id.2
      specializationCodeTerm specializationCodeTerm_closed Term.specializationCode specializationCodeTerm_apply
  refine ⟨Term.specializationCode U.code,ht,fun e => ⟨?_,?_⟩⟩
  · have hc := specializeProgram_closed (P := mk U) huc e
    rw [← Term.mk_specializeSyntax] at hc
    change (Term.specializeSyntax U e).fv = ∅ at hc
    simpa only [Term.decode_specializationCode,Term.decode_code] using hc
  · intro p n m
    apply specializationCode_evaluator U.code e
    simpa only [Term.decode_code] using hU

/-- Uncurrying can be compiled from every enumeration index, including those
whose raw syntax is open. The retained input program has exactly the same graph. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Function-space transformations on syntax codes
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The code transformations used above have concrete lambda implementations: §{sec:lambda-function-code-transforms}
    constructs prefixing and uncurrying directly from syntax constructors and the numeral-code program. For an arbitrary
    enumeration index, first specialize the universal evaluator to that index. This gives a closed syntax code with the same
    partial numerical behavior for every input name, to which the templates apply. The normalization and subsequent
    transformation are both primitive recursive and are computed by closed lambda terms.
-/
theorem exists_total_uncurry_compiler : ∃ f v : ℕ → ℕ,
    CodeTransform f ∧ CodeTransform v ∧ ∀ e,
      (∀ p n m, OracleRuns p (Term.closedProgram (v e)) n m ↔
        OracleRuns p (Term.closedProgram e) n m) ∧
      Term.closedProgram (f e) = compositionProgram evaluationProgram
        (pairOutputProgram (compositionProgram (Term.closedProgram (v e)) leftProgram) rightProgram) := by
  obtain ⟨v,hv,hr⟩ := exists_normalization_compiler
  obtain ⟨u,hu,he⟩ := exists_uncurry_compiler
  exact ⟨fun e => u (v e),v,hu.comp hv,hv,fun e => ⟨(hr e).2,he (v e) (hr e).1⟩⟩

/-- The continuous rearrangement has the same total-index normalization. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Function-space transformations on syntax codes
-/
theorem exists_total_continuous_curry_compiler : ∃ f v : ℕ → ℕ,
    CodeTransform f ∧ CodeTransform v ∧ ∀ e,
      (∀ p n m, OracleRuns p (Term.closedProgram (v e)) n m ↔
        OracleRuns p (Term.closedProgram e) n m) ∧
      Term.closedProgram (f e) = continuousCurryProgram (Term.closedProgram (v e)) := by
  obtain ⟨v,hv,hr⟩ := exists_normalization_compiler
  obtain ⟨u,hu,he⟩ := exists_continuous_curry_compiler
  exact ⟨fun e => u (v e),v,hu.comp hv,hv,fun e => ⟨(hr e).2,he (v e) (hr e).1⟩⟩

end LambdaFunction
end PolishSpaceBook
