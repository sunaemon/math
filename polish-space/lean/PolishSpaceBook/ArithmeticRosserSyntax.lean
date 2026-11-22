module

public import PolishSpaceBook.LambdaIncompleteness
public import PolishSpaceBook.FirstOrderBoundedToNamed
public import PolishSpaceBook.FirstOrderCompleteness

@[expose] public section

/-! # Robinson arithmetic and the literal Rosser sentence

The language and seven axioms below have no induction or ordered-semiring
assumptions. The representing formula is supplied by the cited numeralwise
representability theorem; its substitution into the Rosser sentence is explicit.
-/

namespace PolishSpaceBook.ArithmeticRosser
open FirstOrder Language

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    The arithmetic language has symbols $0,S,+,\cdot$. Write $\ArithmeticNumeral{n}:=S^n0$ for its numeral;
    this is an arithmetic term, whereas $\ChurchNumeral{n}$ denotes a Church numeral in a lambda program.
-/
inductive ArithmeticFunction : ℕ → Type
  | zero : ArithmeticFunction 0
  | succ : ArithmeticFunction 1
  | add : ArithmeticFunction 2
  | mul : ArithmeticFunction 2

def arithmetic : Language where
  Functions := ArithmeticFunction
  Relations := fun _ => Empty

def zero {α : Type*} : arithmetic.Term α := .func .zero Fin.elim0
def succ {α : Type*} (t : arithmetic.Term α) : arithmetic.Term α := .func .succ ![t]
def add {α : Type*} (t r : arithmetic.Term α) : arithmetic.Term α := .func .add ![t, r]
def mul {α : Type*} (t r : arithmetic.Term α) : arithmetic.Term α := .func .mul ![t, r]

def numeral {α : Type*} : ℕ → arithmetic.Term α
  | 0 => zero
  | n + 1 => succ (numeral n)

def bound {n : ℕ} (i : Fin n) : arithmetic.Term (Empty ⊕ Fin n) := .var (.inr i)

def eqn {n : ℕ} (t r : arithmetic.Term (Empty ⊕ Fin n)) :
    arithmetic.BoundedFormula Empty n := .equal t r

def axiom₁ : arithmetic.Sentence :=
  (eqn (succ (bound (0 : Fin 1))) zero).not.all
def axiom₂ : arithmetic.Sentence :=
  ((eqn (succ (bound (0 : Fin 2))) (succ (bound 1))).imp
    (eqn (bound 0) (bound 1))).all.all
def axiom₃ : arithmetic.Sentence :=
  ((eqn (bound (0 : Fin 1)) zero).not.imp
    (eqn (bound (0 : Fin 2)) (succ (bound 1))).ex).all
def axiom₄ : arithmetic.Sentence :=
  (eqn (add (bound (0 : Fin 1)) zero) (bound 0)).all
def axiom₅ : arithmetic.Sentence :=
  (eqn (add (bound (0 : Fin 2)) (succ (bound 1)))
    (succ (add (bound 0) (bound 1)))).all.all
def axiom₆ : arithmetic.Sentence :=
  (eqn (mul (bound (0 : Fin 1)) zero) zero).all
def axiom₇ : arithmetic.Sentence :=
  (eqn (mul (bound (0 : Fin 2)) (succ (bound 1)))
    (add (mul (bound 0) (bound 1)) (bound 0))).all.all

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    \termdefineas{Robinson arithmetic}{Robinson arithmetic} $\RobinsonArithmetic$ consists of the universal closures of
    $$\begin{aligned}
    Sx&\ne0,& Sx=Sy&\to x=y,& x\ne0&\to\exists y\,x=Sy,\\
    x+0&=x,& x+Sy&=S(x+y),\\
    x\cdot0&=0,& x\cdot Sy&=x\cdot y+x.
    \end{aligned}$$
-/
/-- Exactly the seven displayed universal closures, with no induction scheme. -/
def robinson : arithmetic.Theory :=
  Set.range (![axiom₁, axiom₂, axiom₃, axiom₄, axiom₅, axiom₆, axiom₇] : Fin 7 → _)

def liftTerm {n : ℕ} (t : arithmetic.Term (Empty ⊕ Fin n)) :
    arithmetic.Term (Empty ⊕ Fin (n + 1)) := t.relabel (Sum.map id Fin.castSucc)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    Use $x\le y$ as an abbreviation for $\exists z\,(z+x=y)$. No induction scheme is part of
    $\RobinsonArithmetic$.
-/
/-- The book's abbreviation `x ≤ y` is `∃ z, z + x = y`. -/
def leFormula {n : ℕ} (x y : arithmetic.Term (Empty ⊕ Fin n)) :
    arithmetic.BoundedFormula Empty n :=
  (eqn (add (bound (Fin.last n)) (liftTerm x)) (liftTerm y)).ex

/-- Capture-safe substitution of the three free variables, then binding the
ambient finite context. Internal quantifiers of `B` remain intact. -/
def instanceB {n : ℕ} (B : arithmetic.Formula (Fin 3))
    (ts : Fin 3 → arithmetic.Term (Empty ⊕ Fin n)) : arithmetic.BoundedFormula Empty n :=
  BoundedFormula.relabel id (B.subst ts)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    Define the following computable family of arithmetic sentences:
    $$\sigma_e:=\exists u\,\bigl(B(\ArithmeticNumeral{e},\ArithmeticNumeral{0},u)
      \land\forall v\,(v\le u\to\neg B(\ArithmeticNumeral{e},\ArithmeticNumeral{1},v))\bigr).$$
    The comparison of certificate sizes is a Rosser comparison: a certificate for output $0$ is accepted only if no
    certificate for output $1$ has appeared at or below its size. We need only the following two implications.
-/
/-- The actual displayed arithmetic sentence, rather than a supplied family specification. -/
def sigma (B : arithmetic.Formula (Fin 3)) (e : ℕ) : arithmetic.Sentence :=
  ((instanceB B ![numeral e, numeral 0, bound (0 : Fin 1)]) ⊓
    ((leFormula (bound (1 : Fin 2)) (bound 0)).imp
      (instanceB B ![numeral e, numeral 1, bound (1 : Fin 2)]).not).all).ex

section Semantics
variable {M : Type*} [arithmetic.Structure M]

def modelNumeral (M : Type*) [arithmetic.Structure M] (n : ℕ) : M :=
  (numeral n : arithmetic.Term Empty).realize Empty.elim

def modelAdd (x y : M) : M := Structure.funMap (L := arithmetic) ArithmeticFunction.add ![x, y]
def modelLe (x y : M) : Prop := ∃ z, modelAdd z x = y

@[simp] theorem realize_numeral {α : Type*} (v : α → M) (n : ℕ) :
    (numeral n : arithmetic.Term α).realize v = modelNumeral M n := by
  induction n with
  | zero =>
    simp only [numeral, zero, modelNumeral, Term.realize]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih => simp [numeral, succ, modelNumeral, ih, Term.realize]

@[simp] theorem realize_add {α : Type*} (v : α → M) (t r : arithmetic.Term α) :
    (add t r).realize v = modelAdd (t.realize v) (r.realize v) := by
  simp only [add, Term.realize, modelAdd]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem realize_liftTerm {n : ℕ} (t : arithmetic.Term (Empty ⊕ Fin n))
    (v : Fin n → M) (a : M) :
    (liftTerm t).realize (Sum.elim Empty.elim (Fin.snoc v a)) =
      t.realize (Sum.elim Empty.elim v) := by
  rw [liftTerm, Term.realize_relabel]
  congr 1
  funext i
  cases i with
  | inl x => exact Empty.elim x
  | inr i => simp

theorem realize_leFormula {n : ℕ} (x y : arithmetic.Term (Empty ⊕ Fin n))
    (v : Fin n → M) :
    (leFormula x y).Realize Empty.elim v ↔
      modelLe (x.realize (Sum.elim Empty.elim v)) (y.realize (Sum.elim Empty.elim v)) := by
  simp [leFormula, eqn, BoundedFormula.realize_ex, BoundedFormula.Realize, bound, modelLe]

theorem realize_instanceB {n : ℕ} (B : arithmetic.Formula (Fin 3))
    (ts : Fin 3 → arithmetic.Term (Empty ⊕ Fin n)) (v : Fin n → M) :
    (instanceB B ts).Realize Empty.elim v ↔
      B.Realize (fun i => (ts i).realize (Sum.elim Empty.elim v)) := by
  simp [instanceB, BoundedFormula.realize_relabel, BoundedFormula.realize_subst,
    FirstOrder.Language.Formula.Realize, Subsingleton.elim (v ∘ Fin.natAdd n) (default : Fin 0 → M)]

def certificateRelation (B : arithmetic.Formula (Fin 3)) (e b : ℕ) (u : M) : Prop :=
  B.Realize ![modelNumeral M e, modelNumeral M b, u]

theorem realize_instanceB_three {n : ℕ} (B : arithmetic.Formula (Fin 3))
    (a b c : arithmetic.Term (Empty ⊕ Fin n)) (v : Fin n → M) :
    (instanceB B ![a, b, c]).Realize Empty.elim v ↔
      B.Realize ![a.realize (Sum.elim Empty.elim v), b.realize (Sum.elim Empty.elim v),
        c.realize (Sum.elim Empty.elim v)] := by
  rw [realize_instanceB]
  have ht : (fun i => (![a, b, c] i).realize (Sum.elim Empty.elim v)) =
      ![a.realize (Sum.elim Empty.elim v), b.realize (Sum.elim Empty.elim v),
        c.realize (Sum.elim Empty.elim v)] := by
    funext i
    fin_cases i <;> rfl
  rw [ht]

/-- The semantic identity follows from the defined syntax and substitution. -/
theorem realize_sigma (B : arithmetic.Formula (Fin 3)) (e : ℕ) :
    M ⊨ sigma B e ↔ ∃ u : M, certificateRelation B e 0 u ∧
      ∀ v, modelLe v u → ¬certificateRelation B e 1 v := by
  unfold Sentence.Realize FirstOrder.Language.Formula.Realize
  rw [Subsingleton.elim (default : Empty → M) Empty.elim]
  simp only [sigma, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_not,
    realize_instanceB_three, realize_leFormula]
  simp [certificateRelation, bound, Fin.snoc]


end Semantics

open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- Acceptance of the literal certificate code `s`, not a bounded search up to `s`. -/
def accepts (e b s : ℕ) : Bool :=
  NamedLambda.Term.checkBetaCertificate
    (.app (NamedLambda.Term.programSyntax e) (NamedLambda.Term.churchNumeral e))
    (NamedLambda.Term.churchNumeral b) (NamedLambda.Term.decodeCertificate s)

theorem exists_accepts_iff (e b : ℕ) : (∃ s, accepts e b s = true) ↔ App e e b := by
  have h := NamedLambda.Term.beta_steps_iff_certificate
    (.app (NamedLambda.Term.programSyntax e) (NamedLambda.Term.churchNumeral e))
    (NamedLambda.Term.churchNumeral b)
  have h' : App e e b ↔ ∃ cs, NamedLambda.Term.checkBetaCertificate
      (.app (NamedLambda.Term.programSyntax e) (NamedLambda.Term.churchNumeral e))
      (NamedLambda.Term.churchNumeral b) cs = true := by
    simpa only [App, Runs, ← app_mk, NamedLambda.Term.mk_programSyntax,
      NamedLambda.Term.mk_churchNumeral] using h
  constructor
  · rintro ⟨s, hs⟩
    exact h'.mpr ⟨_, hs⟩
  · intro he
    obtain ⟨cs, hcs⟩ := h'.mp he
    exact ⟨NamedLambda.Term.certificateCode cs, by simpa [accepts] using hcs⟩

end PolishSpaceBook.ArithmeticRosser
