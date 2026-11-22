module

public import PolishSpaceBook.LambdaNumericalPairing

@[expose] public section

/-! # Explicit natural-number codes for the existing named lambda syntax

These codes are data for lambda terms, not a second program language.
-/
namespace PolishSpaceBook.NamedLambda.Term

/-- Tags modulo three distinguish the three syntax constructors. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Number the variables as $x_0,x_1,\ldots$ in their fixed order. A code records a named term before passage to its alpha-class. Define its \termdefine{lambda syntax code} by
    $$\begin{aligned}
    \LambdaSyntaxCode{x_i}&:=3i,\\
    \LambdaSyntaxCode{MN}&:=3\NatPair{\LambdaSyntaxCode{M}}{\LambdaSyntaxCode{N}}+1,\\
    \LambdaSyntaxCode{\lambdaab{x_i}{M}}&:=3\NatPair{i}{\LambdaSyntaxCode{M}}+2.
    \end{aligned}$$
    The residue modulo three records the constructor. Different names for a bound variable may give different codes; equality of alpha-classes is checked by comparing the decoded named terms under equality of free names.
-/
def code : Term → ℕ
  | .var x => 3 * x
  | .app M N => 3 * Nat.pair M.code N.code + 1
  | .lam x M => 3 * Nat.pair x M.code + 2

/-- Every natural number decodes; recursive subterm codes are strictly smaller. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Given $e$, put $q:=\lfloor e/3\rfloor$ and $r:=e\bmod3$. If $r=0$, return $x_q$. Otherwise unpair $q$ as $\NatPair{a}{b}$: for $r=1$, return the application of $\LambdaSyntaxDecode{a}$ to $\LambdaSyntaxDecode{b}$; for $r=2$, return the abstraction with binder $x_a$ and body $\LambdaSyntaxDecode{b}$. Each unpaired component is at most $q$, and $q<e$ in these two cases. Recursion on the code therefore terminates. Induction on a term proves the first identity, using the inverse equations for numerical pairing. Strong induction on $e$ proves the second: the recursive calls recover the component codes, pairing recovers $q$, and $e=3q+r$. The same inequalities prove the assertion about subterm codes.
-/
def decode (e : ℕ) : Term :=
  if h : e % 3 = 0 then .var (e / 3)
  else if e % 3 = 1 then
    .app (decode (Nat.unpair (e / 3)).1) (decode (Nat.unpair (e / 3)).2)
  else .lam (Nat.unpair (e / 3)).1 (decode (Nat.unpair (e / 3)).2)
termination_by e
decreasing_by
  all_goals
    have hl := Nat.unpair_left_le (e / 3)
    have hr := Nat.unpair_right_le (e / 3)
    omega

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Coding and decoding lambda syntax
-/
@[simp] theorem decode_code (M : Term) : decode M.code = M := by
  induction M with
  | var x => simp [code, decode]
  | app M N hM hN =>
    rw [code, decode]
    simp [Nat.add_div, Nat.unpair_pair, hM, hN]
  | lam x M hM =>
    rw [code, decode]
    simp [Nat.add_div, Nat.unpair_pair, hM]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Coding and decoding lambda syntax
-/
@[simp] theorem code_decode (e : ℕ) : (decode e).code = e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [decode]
    split_ifs with h0 h1
    · simp only [code]
      omega
    · simp only [code]
      rw [ih _ (by have := Nat.unpair_left_le (e / 3); omega),
        ih _ (by have := Nat.unpair_right_le (e / 3); omega), Nat.pair_unpair]
      omega
    · simp only [code]
      rw [ih _ (by have := Nat.unpair_right_le (e / 3); omega), Nat.pair_unpair]
      omega

theorem code_injective : Function.Injective code :=
  Function.LeftInverse.injective decode_code

/-- The distinguished input variable is the unique term with syntax code zero. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We implement the finite-table reduction tests by closed lambda terms. At this stage the answer table is numerical data:
    the programs inspect the stored pairs without querying any input name. Agreement of these stored answers with the actual
    name is the separate finite check in §{sec:lambda-input-certificates}. Choose the distinguished input variable to be
    $o=x_0$, whose syntax code is zero. All other syntax codes are positive.
-/
theorem code_eq_zero_iff (M : Term) : M.code = 0 ↔ M = .var 0 := by
  change M.code = (Term.var 0).code ↔ M = .var 0
  exact code_injective.eq_iff

def codeEquiv : Term ≃ ℕ where
  toFun := code
  invFun := decode
  left_inv := decode_code
  right_inv := code_decode

theorem code_app_left_lt (M N : Term) : M.code < (Term.app M N).code := by
  have := Nat.left_le_pair M.code N.code
  simp only [code]
  omega

theorem code_app_right_lt (M N : Term) : N.code < (Term.app M N).code := by
  have := Nat.right_le_pair M.code N.code
  simp only [code]
  omega

theorem code_lam_body_lt (x : ℕ) (M : Term) : M.code < (Term.lam x M).code := by
  have := Nat.right_le_pair x M.code
  simp only [code]
  omega

/-- Decide closedness on syntax before passing to the alpha-quotient. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Define $P_e$ to be the alpha-class of $\LambdaSyntaxDecode{e}$ when this term is closed, and to be $\ChurchNumeral{0}$ otherwise. Then every $P_e$ is closed and every closed alpha-class occurs in the sequence. Indeed, free variables are determined by a finite traversal, and for a closed representative $M$, its code gives $P_{\LambdaSyntaxCode{M}}=[M]$. Repetitions in this enumeration are harmless.
-/
def closedProgram (e : ℕ) : AlphaTerm :=
  if (decode e).fv = ∅ then AlphaTerm.mk (decode e) else AlphaTerm.numeral 0

theorem closedProgram_closed (e : ℕ) : (closedProgram e).Closed := by
  unfold closedProgram
  split_ifs with h
  · exact h
  · exact AlphaTerm.numeral_closed 0

theorem closedProgram_surjective (P : AlphaTerm) (hP : P.Closed) :
    ∃ e, closedProgram e = P := by
  induction P using Quotient.inductionOn with
  | h M =>
    refine ⟨M.code, ?_⟩
    have hM : M.fv = ∅ := hP
    simp only [closedProgram, decode_code, hM, ite_true]
    rfl

end PolishSpaceBook.NamedLambda.Term

namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Arithmetic encoding of a variable constructor. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The numerical constructor functions themselves have closed lambda implementations:
    $$\begin{aligned}
    \LambdaVarCode&:=\lambdaab{a}{\LambdaMul\,\ChurchNumeral{3}\,a},\\
    \LambdaTaggedCode{t}&:=\lambdaab{a}{\lambdaab{b}{
    \LambdaAdd\,(\LambdaMul\,\ChurchNumeral{3}\,(\LambdaNumericPair\,a\,b))\,\ChurchNumeral{t}}}.
    \end{aligned}$$
    Use $t=1$ for application and $t=2$ for abstraction.
-/
def variableCodeTerm : AlphaTerm := lam 3 (app (app multiplicationTerm (numeral 3)) (var 3))

@[simp] theorem variableCodeTerm_closed : variableCodeTerm.Closed := by
  unfold variableCodeTerm Closed
  rw [fv_lam, fv_app, fv_app, multiplicationTerm_closed, numeral_closed, fv_var]
  decide

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda terms constructing syntax codes
-/
theorem variableCodeTerm_apply (x : ℕ) :
    Relation.ReflTransGen Beta (app variableCodeTerm (numeral x)) (numeral (Term.var x).code) := by
  have h : Beta (app variableCodeTerm (numeral x))
      (app (app multiplicationTerm (numeral 3)) (numeral x)) := by
    simpa only [variableCodeTerm, subst_app, subst_var, ite_true,
      subst_closed _ _ _ multiplicationTerm_closed,
      subst_closed _ _ _ (numeral_closed 3)] using
      Beta.contract 3 (app (app multiplicationTerm (numeral 3)) (var 3)) (numeral x)
  exact (Relation.ReflTransGen.single h).trans (multiplicationTerm_apply 3 x)

/-- The two-argument constructor code with tag one or two. -/
def taggedPairCodeBody (t : ℕ) (M N : AlphaTerm) : AlphaTerm :=
  app (app additionTerm
    (app (app multiplicationTerm (numeral 3)) (app (app numericalPairTerm M) N))) (numeral t)

theorem taggedPairCodeBody_fv (t : ℕ) (M N : AlphaTerm) :
    (taggedPairCodeBody t M N).fv = M.fv ∪ N.fv := by
  unfold taggedPairCodeBody
  simp only [fv_app]
  rw [additionTerm_closed, multiplicationTerm_closed, numericalPairTerm_closed,
    numeral_closed, numeral_closed]
  simp

theorem taggedPairCodeBody_subst (t x : ℕ) (M N R : AlphaTerm) :
    (taggedPairCodeBody t M N).subst x R =
      taggedPairCodeBody t (M.subst x R) (N.subst x R) := by
  simp only [taggedPairCodeBody, subst_app, subst_closed _ _ _ additionTerm_closed,
    subst_closed _ _ _ multiplicationTerm_closed, subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ (numeral_closed 3), subst_closed _ _ _ (numeral_closed t)]

def taggedPairCodeTerm (t : ℕ) : AlphaTerm :=
  lam 3 (lam 4 (taggedPairCodeBody t (var 3) (var 4)))

@[simp] theorem taggedPairCodeTerm_closed (t : ℕ) : (taggedPairCodeTerm t).Closed := by
  unfold taggedPairCodeTerm Closed
  rw [fv_lam, fv_lam, taggedPairCodeBody_fv]
  simp [fv_var]
  decide

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda terms constructing syntax codes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For a variable code, one beta step substitutes the input numeral and multiplication gives the result. For a tagged pair, two beta steps substitute both numerals. Reduce numerical pairing, multiply its output by three, and add the tag. Each reduction is lifted through its application context. All constants are closed, and the displayed abstractions bind the remaining variables.
-/
theorem taggedPairCodeTerm_apply (t a b : ℕ) :
    Relation.ReflTransGen Beta (app (app (taggedPairCodeTerm t) (numeral a)) (numeral b))
      (numeral (3 * Nat.pair a b + t)) := by
  have h₁ : Beta (app (taggedPairCodeTerm t) (numeral a))
      (lam 4 (taggedPairCodeBody t (numeral a) (var 4))) := by
    convert Beta.contract 3 (lam 4 (taggedPairCodeBody t (var 3) (var 4))) (numeral a)
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) (by rw [numeral_closed]; simp),
      taggedPairCodeBody_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 4 (taggedPairCodeBody t (numeral a) (var 4))) (numeral b))
      (taggedPairCodeBody t (numeral a) (numeral b)) := by
    convert Beta.contract 4 (taggedPairCodeBody t (numeral a) (var 4)) (numeral b) using 1
    simp [taggedPairCodeBody_subst, subst_var, subst_closed _ _ _ (numeral_closed a)]
  have hs : Relation.ReflTransGen Beta
      (app (app (taggedPairCodeTerm t) (numeral a)) (numeral b))
      (taggedPairCodeBody t (numeral a) (numeral b)) :=
    .tail (.single (.app_left _ h₁)) h₂
  apply hs.trans
  have hp := (beta_steps_app_right (app multiplicationTerm (numeral 3))
    (numericalPairTerm_apply a b)).trans (multiplicationTerm_apply 3 (Nat.pair a b))
  exact (beta_steps_app_left (beta_steps_app_right additionTerm hp) (numeral t)).trans
    (additionTerm_apply (3 * Nat.pair a b) t)

/-- Application and abstraction codes are constructed by closed lambda terms. -/
def applicationCodeTerm : AlphaTerm := taggedPairCodeTerm 1
def abstractionCodeTerm : AlphaTerm := taggedPairCodeTerm 2

theorem applicationCodeTerm_apply (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app applicationCodeTerm (numeral M.code)) (numeral N.code))
      (numeral (Term.app M N).code) := taggedPairCodeTerm_apply 1 M.code N.code

theorem abstractionCodeTerm_apply (x : ℕ) (M : Term) :
    Relation.ReflTransGen Beta
      (app (app abstractionCodeTerm (numeral x)) (numeral M.code))
      (numeral (Term.lam x M).code) := taggedPairCodeTerm_apply 2 x M.code

end PolishSpaceBook.NamedLambda.AlphaTerm
