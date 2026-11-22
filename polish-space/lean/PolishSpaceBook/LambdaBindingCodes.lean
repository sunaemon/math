module

public import PolishSpaceBook.LambdaFreeVariables
public import PolishSpaceBook.LambdaAlphaEncoding

@[expose] public section

/-! # Binding-tree codes and alpha-equivalence by closed lambda programs

The representation uses the existing numerical syntax constructors as data:
free leaves have even variable indices, bound leaves odd indices, and each
abstraction is represented by a node with binder index zero. No evaluation
of these data terms is involved.
-/
namespace PolishSpaceBook.NamedLambda
namespace BindingTree

/-- Encode the four kinds of binding-tree node in the existing three-constructor syntax. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    We now implement equality of these indexed syntax trees. Assign each finite indexed syntax tree $A$ a numerical code $\LambdaBindingCode{A}$ by the following rules. A free leaf with index $i$ has code $6i$, and a bound leaf with index $i$ has code $6i+3$. An application whose children have codes $a,b$ has code $3\NatPair{a}{b}+1$. An abstraction whose child has code $a$ has code $3\NatPair{0}{a}+2$. This reuses the syntax-code constructors: leaf indices are $2i$ for free leaves and $2i+1$ for bound leaves, and every abstraction uses the dummy binder index zero. These are codes of data; no beta-reduction of the encoded data term is intended.
-/
def dataTerm : BindingTree → Term
  | .free i => .var (2 * i)
  | .bound i => .var (2 * i + 1)
  | .app A B => .app A.dataTerm B.dataTerm
  | .lam A => .lam 0 A.dataTerm

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The syntax tag distinguishes leaves, applications and abstractions. At a leaf, parity of its variable index distinguishes free from bound, and the index determines its label. At an application, injectivity of numerical pairing recovers both child codes. At an abstraction, it recovers the child code. Induction on the trees proves injectivity. The converse is immediate.
    \end{proof}
-/
theorem dataTerm_injective : Function.Injective dataTerm := by
  intro A
  induction A with
  | free i =>
    intro B h
    cases B <;> simp [dataTerm] at h
    · congr 1
    · omega
  | bound i =>
    intro B h
    cases B <;> simp [dataTerm] at h
    · omega
    · congr 1
  | app A B ihA ihB =>
    intro C h
    cases C <;> simp [dataTerm] at h
    exact congrArg₂ BindingTree.app (ihA h.1) (ihB h.2)
  | lam A ih =>
    intro B h
    cases B <;> simp [dataTerm] at h
    exact congrArg BindingTree.lam (ih h)

def code (A : BindingTree) : ℕ := A.dataTerm.code

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Injectivity of indexed syntax codes
-/
theorem code_injective : Function.Injective code := fun _ _ h =>
  dataTerm_injective (Term.code_injective h)

end BindingTree
namespace AlphaTerm

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1
private theorem abstractionCode_closed : abstractionCodeTerm.Closed := taggedPairCodeTerm_closed 2

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Write $\LambdaCloseTree{A}{i}{k}$ for closing the free variable $x_i$ in $A$ starting at depth $k$. At a free $x_i$
    leaf, put a bound leaf labeled by the current depth; leave other free leaves and all existing bound leaves unchanged.
    Descend through application with the same depth and through abstraction with depth increased by one. This is the closing
    operation used to construct $\LambdaBindingTree{M}$.

    To compute closing, let each syntax-fold value be a function of the index to be closed and the starting depth. Use the
    abbreviations
    $$\begin{aligned}
    D(v,i,k)&:=\LambdaZeroTest\,(\LambdaEqual\,v\,(\LambdaMul\,\ChurchNumeral{2}\,i))\\
     &\qquad(\LambdaVarCode\,v)\\
     &\qquad\bigl(\LambdaVarCode\,(\LambdaSucc(\LambdaMul\,\ChurchNumeral{2}\,k))\bigr),\\
    V_c&:=\lambdaab{v}{\lambdaab{i}{\lambdaab{k}{D(v,i,k)}}},\\
    A_c&:=\lambdaab{f}{\lambdaab{g}{\lambdaab{i}{\lambdaab{k}{
     \LambdaTaggedCode{1}\,(f\,i\,k)\,(g\,i\,k)}}}},\\
    L_c&:=\lambdaab{y}{\lambdaab{f}{\lambdaab{i}{\lambdaab{k}{
     \LambdaTaggedCode{2}\,y\,(f\,i\,(\LambdaSucc\,k))}}}},\\
    \LambdaCloseCode&:=\LambdaSyntaxFold{V_c}{A_c}{L_c}.
    \end{aligned}$$
    Expand $D$ inside the abstraction. All three handlers are closed. The abstraction handler preserves the dummy binder
    field and passes the increased depth to its body function.
-/
def closeVariableBody (V X K : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app (app equalityTerm V) (app (app multiplicationTerm (numeral 2)) X))) (app variableCodeTerm V)) (app variableCodeTerm (app successorTerm (app (app multiplicationTerm (numeral 2)) K)))

theorem closeVariableBody_fv (V X K : AlphaTerm) :
    (closeVariableBody V X K).fv = V.fv ∪ X.fv ∪ K.fv := by
  ext x
  simp only [closeVariableBody, fv_app, (show zeroTestTerm.fv = ∅ from zeroTestTerm_closed), (show equalityTerm.fv = ∅ from equalityTerm_closed), (show multiplicationTerm.fv = ∅ from multiplicationTerm_closed), (show variableCodeTerm.fv = ∅ from variableCodeTerm_closed), (show successorTerm.fv = ∅ from successorTerm_closed) ,(show (numeral 2).fv = ∅ from numeral_closed 2), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem closeVariableBody_subst (V X K W : AlphaTerm) (x : ℕ) :
    (closeVariableBody V X K).subst x W =
      closeVariableBody (V.subst x W) (X.subst x W) (K.subst x W) := by
  simp only [closeVariableBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ equalityTerm_closed, subst_closed _ _ _ multiplicationTerm_closed, subst_closed _ _ _ variableCodeTerm_closed, subst_closed _ _ _ successorTerm_closed ,subst_closed _ _ _ (numeral_closed 2)]

def closeVariableTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (closeVariableBody (var 30) (var 31) (var 32)))))

@[simp] theorem closeVariableTerm_closed : closeVariableTerm.Closed := by
  unfold closeVariableTerm Closed
  simp only [fv_lam, closeVariableBody_fv, fv_var]
  decide

theorem closeVariableTerm_start {V X K : AlphaTerm}
    (hV : V.Closed) (hX : X.Closed) (hK : K.Closed) :
    Relation.ReflTransGen Beta (app (app (app closeVariableTerm V) X) K)
      (closeVariableBody V X K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfV : V.fv = ∅ := hV
  have hfX : X.fv = ∅ := hX
  have hfK : K.fv = ∅ := hK
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (closeVariableBody (var 30) (var 31) (var 32))))) V) (lam 31 (lam 32 (closeVariableBody V (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (closeVariableBody (var 30) (var 31) (var 32)))) V using 1

    simp [subst_lam_fresh, subst_var, closeVariableBody_subst, hfV]
  have h1 : Beta (app (lam 31 (lam 32 (closeVariableBody V (var 31) (var 32)))) X) (lam 32 (closeVariableBody V X (var 32))) := by
    convert Beta.contract 31 (lam 32 (closeVariableBody V (var 31) (var 32))) X using 1

    simp [subst_lam_fresh, subst_var, closeVariableBody_subst, subst_closed, hV, hfX]
  have h2 : Beta (app (lam 32 (closeVariableBody V X (var 32))) K) (closeVariableBody V X K) := by
    convert Beta.contract 32 (closeVariableBody V X (var 32)) K using 1

    simp [subst_var, closeVariableBody_subst, subst_closed, hV, hX]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) X) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) K).trans
  exact (Relation.ReflTransGen.single h2)

def closeApplicationBody (F G X K : AlphaTerm) : AlphaTerm :=
  app (app applicationCodeTerm (app (app F X) K)) (app (app G X) K)

theorem closeApplicationBody_fv (F G X K : AlphaTerm) :
    (closeApplicationBody F G X K).fv = F.fv ∪ G.fv ∪ X.fv ∪ K.fv := by
  ext x
  simp only [closeApplicationBody, fv_app, (show applicationCodeTerm.fv = ∅ from applicationCode_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem closeApplicationBody_subst (F G X K W : AlphaTerm) (x : ℕ) :
    (closeApplicationBody F G X K).subst x W =
      closeApplicationBody (F.subst x W) (G.subst x W) (X.subst x W) (K.subst x W) := by
  simp only [closeApplicationBody, subst_app, subst_closed _ _ _ applicationCode_closed]

def closeApplicationTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (closeApplicationBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem closeApplicationTerm_closed : closeApplicationTerm.Closed := by
  unfold closeApplicationTerm Closed
  simp only [fv_lam, closeApplicationBody_fv, fv_var]
  decide

theorem closeApplicationTerm_start {F G X K : AlphaTerm}
    (hF : F.Closed) (hG : G.Closed) (hX : X.Closed) (hK : K.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app closeApplicationTerm F) G) X) K)
      (closeApplicationBody F G X K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfF : F.fv = ∅ := hF
  have hfG : G.fv = ∅ := hG
  have hfX : X.fv = ∅ := hX
  have hfK : K.fv = ∅ := hK
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (closeApplicationBody (var 30) (var 31) (var 32) (var 33)))))) F) (lam 31 (lam 32 (lam 33 (closeApplicationBody F (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (closeApplicationBody (var 30) (var 31) (var 32) (var 33))))) F using 1

    simp [subst_lam_fresh, subst_var, closeApplicationBody_subst, hfF]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (closeApplicationBody F (var 31) (var 32) (var 33))))) G) (lam 32 (lam 33 (closeApplicationBody F G (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (closeApplicationBody F (var 31) (var 32) (var 33)))) G using 1

    simp [subst_lam_fresh, subst_var, closeApplicationBody_subst, subst_closed, hF, hfG]
  have h2 : Beta (app (lam 32 (lam 33 (closeApplicationBody F G (var 32) (var 33)))) X) (lam 33 (closeApplicationBody F G X (var 33))) := by
    convert Beta.contract 32 (lam 33 (closeApplicationBody F G (var 32) (var 33))) X using 1

    simp [subst_lam_fresh, subst_var, closeApplicationBody_subst, subst_closed, hF, hG, hfX]
  have h3 : Beta (app (lam 33 (closeApplicationBody F G X (var 33))) K) (closeApplicationBody F G X K) := by
    convert Beta.contract 33 (closeApplicationBody F G X (var 33)) K using 1

    simp [subst_var, closeApplicationBody_subst, subst_closed, hF, hG, hX]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) G) X) K).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) X) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) K).trans
  exact (Relation.ReflTransGen.single h3)

def closeAbstractionBody (I F X K : AlphaTerm) : AlphaTerm :=
  app (app abstractionCodeTerm I) (app (app F X) (app successorTerm K))

theorem closeAbstractionBody_fv (I F X K : AlphaTerm) :
    (closeAbstractionBody I F X K).fv = I.fv ∪ F.fv ∪ X.fv ∪ K.fv := by
  ext x
  simp only [closeAbstractionBody, fv_app, (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed), (show successorTerm.fv = ∅ from successorTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem closeAbstractionBody_subst (I F X K W : AlphaTerm) (x : ℕ) :
    (closeAbstractionBody I F X K).subst x W =
      closeAbstractionBody (I.subst x W) (F.subst x W) (X.subst x W) (K.subst x W) := by
  simp only [closeAbstractionBody, subst_app, subst_closed _ _ _ abstractionCode_closed, subst_closed _ _ _ successorTerm_closed]

def closeAbstractionTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (closeAbstractionBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem closeAbstractionTerm_closed : closeAbstractionTerm.Closed := by
  unfold closeAbstractionTerm Closed
  simp only [fv_lam, closeAbstractionBody_fv, fv_var]
  decide

theorem closeAbstractionTerm_start {I F X K : AlphaTerm}
    (hI : I.Closed) (hF : F.Closed) (hX : X.Closed) (hK : K.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app closeAbstractionTerm I) F) X) K)
      (closeAbstractionBody I F X K) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have hfF : F.fv = ∅ := hF
  have hfX : X.fv = ∅ := hX
  have hfK : K.fv = ∅ := hK
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (closeAbstractionBody (var 30) (var 31) (var 32) (var 33)))))) I) (lam 31 (lam 32 (lam 33 (closeAbstractionBody I (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (closeAbstractionBody (var 30) (var 31) (var 32) (var 33))))) I using 1

    simp [subst_lam_fresh, subst_var, closeAbstractionBody_subst, hfI]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (closeAbstractionBody I (var 31) (var 32) (var 33))))) F) (lam 32 (lam 33 (closeAbstractionBody I F (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (closeAbstractionBody I (var 31) (var 32) (var 33)))) F using 1

    simp [subst_lam_fresh, subst_var, closeAbstractionBody_subst, subst_closed, hI, hfF]
  have h2 : Beta (app (lam 32 (lam 33 (closeAbstractionBody I F (var 32) (var 33)))) X) (lam 33 (closeAbstractionBody I F X (var 33))) := by
    convert Beta.contract 32 (lam 33 (closeAbstractionBody I F (var 32) (var 33))) X using 1

    simp [subst_lam_fresh, subst_var, closeAbstractionBody_subst, subst_closed, hI, hF, hfX]
  have h3 : Beta (app (lam 33 (closeAbstractionBody I F X (var 33))) K) (closeAbstractionBody I F X K) := by
    convert Beta.contract 33 (closeAbstractionBody I F X (var 33)) K using 1

    simp [subst_var, closeAbstractionBody_subst, subst_closed, hI, hF, hX]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) F) X) K).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) X) K).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) K).trans
  exact (Relation.ReflTransGen.single h3)

theorem closeVariableTerm_numeric (v x k : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app closeVariableTerm (numeral v)) (numeral x)) (numeral k))
      (numeral (Term.var (if v = 2 * x then 2 * k + 1 else v)).code) := by
  apply (closeVariableTerm_start (numeral_closed v) (numeral_closed x) (numeral_closed k)).trans
  have he := (beta_steps_app_right (app equalityTerm (numeral v))
    (multiplicationTerm_apply 2 x)).trans (equalityTerm_apply v (2 * x))
  unfold closeVariableBody
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm he) _) _).trans
  by_cases hv : v = 2 * x
  · simp only [ite_eq_left hv]
    apply (branch_succ 0 _ _).trans
    exact (beta_steps_app_right variableCodeTerm
      ((beta_steps_app_right successorTerm (multiplicationTerm_apply 2 k)).trans
        (successorTerm_apply (2 * k)))).trans (variableCodeTerm_apply _)
  · simp only [ite_eq_right hv]
    have hc : (app variableCodeTerm (numeral v)).Closed :=
      closed_app variableCodeTerm_closed (numeral_closed v)
    exact (branch_zero _ _ (by rw [hc]; simp)).trans (variableCodeTerm_apply v)

/-- A fold value is a closed function of the variable being closed and the depth. -/
def closeValue : Term → AlphaTerm
  | .var v => app closeVariableTerm (numeral v)
  | .app M N => app (app closeApplicationTerm (closeValue M)) (closeValue N)
  | .lam i M => app (app closeAbstractionTerm (numeral i)) (closeValue M)

theorem closeValue_closed (M : Term) : (closeValue M).Closed := by
  induction M with
  | var v => exact closed_app closeVariableTerm_closed (numeral_closed v)
  | app M N ihM ihN => exact closed_app (closed_app closeApplicationTerm_closed ihM) ihN
  | lam i M ih => exact closed_app (closed_app closeAbstractionTerm_closed (numeral_closed i)) ih

def closeTreeTerm : AlphaTerm := syntaxFold closeVariableTerm closeApplicationTerm closeAbstractionTerm

@[simp] theorem closeTreeTerm_closed : closeTreeTerm.Closed :=
  syntaxFold_closed closeVariableTerm_closed closeApplicationTerm_closed closeAbstractionTerm_closed

theorem closeTreeTerm_value (M : Term) :
    Relation.ReflTransGen Beta (app closeTreeTerm (numeral M.code)) (closeValue M) :=
  syntaxFold_apply closeVariableTerm_closed closeApplicationTerm_closed closeAbstractionTerm_closed
    closeValue (fun _ => .refl) (fun _ _ => .refl) (fun _ _ => .refl) M

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The structural recursor produces the function built from the three handlers. Prove its required action by induction on the tree, for every starting depth. At a free leaf with label $j$, the variable index is $2j$. The equality test succeeds precisely when $j=i$, producing a bound leaf with index $k$; otherwise it preserves the leaf. At a bound leaf the variable index is odd, so equality with $2i$ fails and the leaf is preserved. Application combines the two results at the same depth. Abstraction uses the induction hypothesis at depth $k+1$ and restores the abstraction node. All numerical tests and constructors have finite reductions. The handlers and structural recursor are closed, so the assembled program is closed as well.
    \end{proof}
-/
theorem closeValue_tree (A : BindingTree) (x k : ℕ) :
    Relation.ReflTransGen Beta (app (app (closeValue A.dataTerm) (numeral x)) (numeral k))
      (numeral (A.close x k).code) := by
  induction A generalizing k with
  | free y =>
    have h := closeVariableTerm_numeric (2 * y) x k
    by_cases hy : y = x
    · subst y
      simpa only [closeValue, BindingTree.dataTerm, BindingTree.close, BindingTree.code, ite_eq_left rfl, ite_true] using h
    · have hne : 2 * y ≠ 2 * x := by omega
      simpa only [closeValue, BindingTree.dataTerm, BindingTree.close, BindingTree.code,
        ite_eq_right hy, ite_eq_right hne] using h
  | bound i =>
    have hne : 2 * i + 1 ≠ 2 * x := by omega
    simpa only [closeValue, BindingTree.dataTerm, BindingTree.close, BindingTree.code, ite_eq_right hne]
      using closeVariableTerm_numeric (2 * i + 1) x k
  | app A B ihA ihB =>
    apply (closeApplicationTerm_start (closeValue_closed A.dataTerm) (closeValue_closed B.dataTerm)
      (numeral_closed x) (numeral_closed k)).trans
    exact (beta_steps_app (beta_steps_app_right applicationCodeTerm (ihA k)) (ihB k)).trans
      (applicationCodeTerm_apply _ _)
  | lam A ih =>
    apply (closeAbstractionTerm_start (numeral_closed 0) (closeValue_closed A.dataTerm)
      (numeral_closed x) (numeral_closed k)).trans
    have h := (beta_steps_app_right (app (closeValue A.dataTerm) (numeral x))
      (successorTerm_apply k)).trans (ih (k + 1))
    exact (beta_steps_app_right (app abstractionCodeTerm (numeral 0)) h).trans
      (abstractionCodeTerm_apply _ _)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Closing a free variable by a lambda term
-/
theorem closeTreeTerm_tree (A : BindingTree) (x k : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app closeTreeTerm (numeral A.code)) (numeral x)) (numeral k))
      (numeral (A.close x k).code) :=
  (beta_steps_app_left (beta_steps_app_left (closeTreeTerm_value A.dataTerm) _) _).trans
    (closeValue_tree A x k)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Now fold over the original named term to compute its indexed syntax code. Set
    $$\begin{aligned}
    V_b&:=\lambdaab{i}{\LambdaVarCode\,(\LambdaMul\,\ChurchNumeral{2}\,i)},\\
    L_b&:=\lambdaab{i}{\lambdaab{b}{\LambdaTaggedCode{2}\,\ChurchNumeral{0}\,
     (\LambdaCloseCode\,b\,i\,\ChurchNumeral{0})}},\\
    \LambdaBindingProgram&:=\LambdaSyntaxFold{V_b}{\LambdaTaggedCode{1}}{L_b},\\
    \LambdaAlphaTest&:=\lambdaab{e}{\lambdaab{d}{
     \LambdaEqual\,(\LambdaBindingProgram\,e)\,(\LambdaBindingProgram\,d)}}.
    \end{aligned}$$
    The abstraction handler closes its binder in the already computed body tree, then adds an abstraction node. The final program compares the two resulting numerical codes.
-/
def bindingVariableBody (I : AlphaTerm) : AlphaTerm :=
  app variableCodeTerm (app (app multiplicationTerm (numeral 2)) I)

theorem bindingVariableBody_fv (I : AlphaTerm) :
    (bindingVariableBody I).fv = I.fv := by
  ext x
  simp only [bindingVariableBody, fv_app, (show variableCodeTerm.fv = ∅ from variableCodeTerm_closed), (show multiplicationTerm.fv = ∅ from multiplicationTerm_closed) ,(show (numeral 2).fv = ∅ from numeral_closed 2), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem bindingVariableBody_subst (I W : AlphaTerm) (x : ℕ) :
    (bindingVariableBody I).subst x W =
      bindingVariableBody (I.subst x W) := by
  simp only [bindingVariableBody, subst_app, subst_closed _ _ _ variableCodeTerm_closed, subst_closed _ _ _ multiplicationTerm_closed ,subst_closed _ _ _ (numeral_closed 2)]

def bindingVariableTerm : AlphaTerm := (lam 30 (bindingVariableBody (var 30)))

@[simp] theorem bindingVariableTerm_closed : bindingVariableTerm.Closed := by
  unfold bindingVariableTerm Closed
  simp only [fv_lam, bindingVariableBody_fv, fv_var]
  decide

theorem bindingVariableTerm_start {I : AlphaTerm}
    (hI : I.Closed) :
    Relation.ReflTransGen Beta (app bindingVariableTerm I)
      (bindingVariableBody I) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have h0 : Beta (app (lam 30 (bindingVariableBody (var 30))) I) (bindingVariableBody I) := by
    convert Beta.contract 30 (bindingVariableBody (var 30)) I using 1

    simp [subst_var, bindingVariableBody_subst]
  exact (Relation.ReflTransGen.single h0)

def bindingAbstractionBody (I B : AlphaTerm) : AlphaTerm :=
  app (app abstractionCodeTerm (numeral 0)) (app (app (app closeTreeTerm B) I) (numeral 0))

theorem bindingAbstractionBody_fv (I B : AlphaTerm) :
    (bindingAbstractionBody I B).fv = I.fv ∪ B.fv := by
  ext x
  simp only [bindingAbstractionBody, fv_app, (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed), (show closeTreeTerm.fv = ∅ from closeTreeTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem bindingAbstractionBody_subst (I B W : AlphaTerm) (x : ℕ) :
    (bindingAbstractionBody I B).subst x W =
      bindingAbstractionBody (I.subst x W) (B.subst x W) := by
  simp only [bindingAbstractionBody, subst_app, subst_closed _ _ _ abstractionCode_closed, subst_closed _ _ _ closeTreeTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def bindingAbstractionTerm : AlphaTerm := (lam 30 (lam 31 (bindingAbstractionBody (var 30) (var 31))))

@[simp] theorem bindingAbstractionTerm_closed : bindingAbstractionTerm.Closed := by
  unfold bindingAbstractionTerm Closed
  simp only [fv_lam, bindingAbstractionBody_fv, fv_var]
  decide

theorem bindingAbstractionTerm_start {I B : AlphaTerm}
    (hI : I.Closed) (hB : B.Closed) :
    Relation.ReflTransGen Beta (app (app bindingAbstractionTerm I) B)
      (bindingAbstractionBody I B) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have hfB : B.fv = ∅ := hB
  have h0 : Beta (app (lam 30 (lam 31 (bindingAbstractionBody (var 30) (var 31)))) I) (lam 31 (bindingAbstractionBody I (var 31))) := by
    convert Beta.contract 30 (lam 31 (bindingAbstractionBody (var 30) (var 31))) I using 1

    simp [subst_lam_fresh, subst_var, bindingAbstractionBody_subst, hfI]
  have h1 : Beta (app (lam 31 (bindingAbstractionBody I (var 31))) B) (bindingAbstractionBody I B) := by
    convert Beta.contract 31 (bindingAbstractionBody I (var 31)) B using 1

    simp [subst_var, bindingAbstractionBody_subst, subst_closed, hI]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) B).trans
  exact (Relation.ReflTransGen.single h1)

theorem bindingVariableTerm_apply (i : ℕ) :
    Relation.ReflTransGen Beta (app bindingVariableTerm (numeral i))
      (numeral (BindingTree.free i).code) :=
  (bindingVariableTerm_start (numeral_closed i)).trans
    ((beta_steps_app_right variableCodeTerm (multiplicationTerm_apply 2 i)).trans
      (variableCodeTerm_apply _))

theorem bindingAbstractionTerm_apply (i : ℕ) (A : BindingTree) :
    Relation.ReflTransGen Beta (app (app bindingAbstractionTerm (numeral i)) (numeral A.code))
      (numeral (BindingTree.lam (A.close i 0)).code) :=
  (bindingAbstractionTerm_start (numeral_closed i) (numeral_closed A.code)).trans
    ((beta_steps_app_right (app abstractionCodeTerm (numeral 0)) (closeTreeTerm_tree A i 0)).trans
      (abstractionCodeTerm_apply 0 _))

def bindingTreeTerm : AlphaTerm :=
  syntaxFold bindingVariableTerm applicationCodeTerm bindingAbstractionTerm

@[simp] theorem bindingTreeTerm_closed : bindingTreeTerm.Closed :=
  syntaxFold_closed bindingVariableTerm_closed applicationCode_closed bindingAbstractionTerm_closed

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Alpha-equivalence by a lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For the first reduction, apply structural recursion with the value at $M$ equal to the numeral of its indexed syntax code. The variable handler produces a free leaf. The application handler combines the two child codes. The abstraction handler first uses the closing lemma at depth zero and then adds an abstraction node. These are precisely the recursive clauses defining $\LambdaBindingTree{M}$. This proves the first reduction by induction on $M$.
-/
theorem bindingTreeTerm_code (M : Term) :
    Relation.ReflTransGen Beta (app bindingTreeTerm (numeral M.code)) (numeral M.bindingTree.code) :=
  syntaxFold_apply bindingVariableTerm_closed applicationCode_closed bindingAbstractionTerm_closed
    (fun M => numeral M.bindingTree.code) bindingVariableTerm_apply
    (fun M N => applicationCodeTerm_apply M.bindingTree.dataTerm N.bindingTree.dataTerm)
    (fun i M => bindingAbstractionTerm_apply i M.bindingTree) M

theorem bindingTreeTerm_apply (e : ℕ) :
    Relation.ReflTransGen Beta (app bindingTreeTerm (numeral e)) (numeral (Term.decode e).bindingTree.code) := by
  simpa only [Term.code_decode] using bindingTreeTerm_code (Term.decode e)

def alphaDecisionBody (E D : AlphaTerm) : AlphaTerm :=
  app (app equalityTerm (app bindingTreeTerm E)) (app bindingTreeTerm D)

theorem alphaDecisionBody_fv (E D : AlphaTerm) :
    (alphaDecisionBody E D).fv = E.fv ∪ D.fv := by
  ext x
  simp only [alphaDecisionBody, fv_app, (show equalityTerm.fv = ∅ from equalityTerm_closed), (show bindingTreeTerm.fv = ∅ from bindingTreeTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem alphaDecisionBody_subst (E D W : AlphaTerm) (x : ℕ) :
    (alphaDecisionBody E D).subst x W =
      alphaDecisionBody (E.subst x W) (D.subst x W) := by
  simp only [alphaDecisionBody, subst_app, subst_closed _ _ _ equalityTerm_closed, subst_closed _ _ _ bindingTreeTerm_closed]

def alphaDecisionTerm : AlphaTerm := (lam 30 (lam 31 (alphaDecisionBody (var 30) (var 31))))

@[simp] theorem alphaDecisionTerm_closed : alphaDecisionTerm.Closed := by
  unfold alphaDecisionTerm Closed
  simp only [fv_lam, alphaDecisionBody_fv, fv_var]
  decide

theorem alphaDecisionTerm_start {E D : AlphaTerm}
    (hE : E.Closed) (hD : D.Closed) :
    Relation.ReflTransGen Beta (app (app alphaDecisionTerm E) D)
      (alphaDecisionBody E D) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfD : D.fv = ∅ := hD
  have h0 : Beta (app (lam 30 (lam 31 (alphaDecisionBody (var 30) (var 31)))) E) (lam 31 (alphaDecisionBody E (var 31))) := by
    convert Beta.contract 30 (lam 31 (alphaDecisionBody (var 30) (var 31))) E using 1

    simp [subst_lam_fresh, subst_var, alphaDecisionBody_subst, hfE]
  have h1 : Beta (app (lam 31 (alphaDecisionBody E (var 31))) D) (alphaDecisionBody E D) := by
    convert Beta.contract 31 (alphaDecisionBody E (var 31)) D using 1

    simp [subst_var, alphaDecisionBody_subst, subst_closed, hE]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) D).trans
  exact (Relation.ReflTransGen.single h1)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Alpha-equivalence by a lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Two beta steps in the comparison program expose numerical equality of the computed codes. Code injectivity identifies equality of these codes with equality of the indexed syntax trees, which characterizes alpha-equivalence by the earlier theorem. Equality testing gives the stated one-or-zero answer. Closedness follows from the closed handlers and recursor. The decoding identity extends both computations to arbitrary numerical syntax codes.
    \end{proof}
-/
theorem alphaDecisionTerm_code (M N : Term) :
    Relation.ReflTransGen Beta (app (app alphaDecisionTerm (numeral M.code)) (numeral N.code))
      (numeral (if M.Alpha N then 1 else 0)) := by
  apply (alphaDecisionTerm_start (numeral_closed M.code) (numeral_closed N.code)).trans
  have h := (beta_steps_app (beta_steps_app_right equalityTerm (bindingTreeTerm_code M))
    (bindingTreeTerm_code N)).trans (equalityTerm_apply M.bindingTree.code N.bindingTree.code)
  have he : M.bindingTree.code = N.bindingTree.code ↔ M.Alpha N :=
    ⟨fun h => (Term.alpha_iff_bindingTree M N).mpr (BindingTree.code_injective h),
      fun h => congrArg BindingTree.code ((Term.alpha_iff_bindingTree M N).mp h)⟩
  simpa only [alphaDecisionBody, he] using h

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Alpha-equivalence by a lambda term
-/
theorem alphaDecisionTerm_apply (e d : ℕ) :
    Relation.ReflTransGen Beta (app (app alphaDecisionTerm (numeral e)) (numeral d))
      (numeral (if (Term.decode e).Alpha (Term.decode d) then 1 else 0)) := by
  simpa only [Term.code_decode] using alphaDecisionTerm_code (Term.decode e) (Term.decode d)


end AlphaTerm
end PolishSpaceBook.NamedLambda
