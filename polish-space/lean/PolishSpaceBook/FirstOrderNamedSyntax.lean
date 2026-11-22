module

public import Mathlib.ModelTheory.Semantics
public import PolishSpaceBook.LambdaSyntaxSubstitution

@[expose] public section

/-!
# First-order formulas with the named binders used in the logic appendix

Terms, languages and structures are mathlib's canonical objects. Formula
constructors retain natural-number variable names so that capture avoidance can
be checked against the displayed clauses. The translation to mathlib formulas
below preserves interpretation, including shadowing of an earlier binder.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language

universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

/-- Single-variable substitution on the standard first-order terms. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Languages.** A first-order language is a tuple
    $$L=(\mathrm{Rel}_L,\mathrm{Fun}_L,\mathrm{ar}_L),$$
    where $\mathrm{Rel}_L$ is a set of relation symbols, $\mathrm{Fun}_L$ is a set of function symbols, disjoint
    from the relation symbols and from the logical symbols and variables, and
    $$\mathrm{ar}_L : \mathrm{Rel}_L \cup \mathrm{Fun}_L \to \omega$$
    assigns each symbol its \termdefine{arity}. Syntactically, an $n$-ary symbol is one that expects $n$ input terms. A
    constant symbol is just a $0$-ary function symbol. Equality $=$ is logical, not part of $L$. The language of set theory
    is the special case $L_\in=(\{\in\},\emptyset,\mathrm{ar})$, where $\mathrm{ar}(\in)=2$. The definitional extensions
    used to add symbols such as $\emptyset$, $\cup$, and $\mathrm{dom}$ are formalized in §{sec:definitional-extensions}.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Syntax.** Fix a countably infinite set of \termdefineas{variable}{variables} $\mathrm{Var}=\{x_0,x_1,x_2,\ldots\}$,
    indexed by $\omega$ and well-ordered by the index — so phrases like "the first variable not in a given finite set $S
    \IncludedIn \mathrm{Var}$" pick out a unique $x_n$, namely the one with smallest index. We usually write elements as
    $x,y,z,\ldots$. The \termdefineas{term}{terms} of a language $L$ are defined recursively:
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   Every variable $x$ is a term.
    *   If $f$ is an $n$-ary function symbol and $t_1,\ldots,t_n$ are terms, then $f(t_1,\ldots,t_n)$ is a term.
    *   Nothing else is a term.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Equivalently, in EBNF summary form,
    $$
    \textit{Term} ::= \textit{Var} \mid f(\textit{Term},\ldots,\textit{Term}),
    $$
    where $f$ ranges over function symbols and the number of displayed arguments is the arity of $f$. The case of arity $0$
    gives a constant symbol.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Substitution.** Fix a variable $x$ and a term $t$. The \termdefine{substitution} $t_0\subst{x}{t}$ of $t$ for $x$ in a
    term $t_0$ is defined by induction on $t_0$:
    $$\begin{aligned}
    y\subst{x}{t} &:= \begin{cases}
    t & \text{if } y = x, \\
    y & \text{if } y \ne x,
    \end{cases}\\
    f(t_1,\ldots,t_n)\subst{x}{t} &:= f(t_1\subst{x}{t},\ldots,t_n\subst{x}{t}),
    \end{aligned}$$
    where $y$ is a variable and $f$ is an $n$-ary function symbol; the $n=0$ case covers constants.
-/
def termSubst (t : L.Term ℕ) (x : ℕ) (r : L.Term ℕ) : L.Term ℕ :=
  t.subst (fun y => if y = x then r else .var y)

/-- The term part of the appendix's substitution proof, by structural induction. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The term statement follows by induction on terms: interpreting $t_0\subst{x}{t}$ under $s$ gives the same element as
    interpreting $t_0$ under $s[x\mapsto t^{\mathcal M,s}]$. Use strong induction on the number of formula constructors
    for the formula statement. This applies to each renamed body as well as to each literal subformula, since renaming
    does not change that number. The atomic and Boolean cases follow from the term statement and the semantic clauses.
-/
theorem termSubst_realize (t : L.Term ℕ) (x : ℕ) (r : L.Term ℕ) (s : ℕ → M) :
    (termSubst t x r).realize s = t.realize (Function.update s x (r.realize s)) := by
  induction t with
  | var y => by_cases hy : y = x <;> simp [termSubst, Term.subst, hy]
  | func f ts ih =>
    simp only [termSubst, Term.subst, Term.realize]
    congr 1
    funext i
    exact ih i

/-- In a relational language, every term is a variable. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $n=0$ the second clause gives a constant term, usually written $c$ rather than $c()$. For pure $L_\in$, the only
    terms are variables.
-/
theorem term_is_variable [L.IsRelational] (t : L.Term ℕ) : ∃ x, t = .var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f _ => exact isEmptyElim f

/-- Term interpretation depends only on the variables occurring in the term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Assignments and free variables
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    An occurrence of a variable $x$ inside the scope of a binding $\forall x$ or $\exists x$ is
    \termdefineas{bound variable occurrence}{bound}; an occurrence not so bound is
    \termdefineas{free variable occurrence}{free}. A variable is
    \termdefineas{free variable}{free in} a term or formula when it has at least one free occurrence there. The set
    $\FreeVars{t}$ of free variables of a term $t$ is defined by induction on $t$:
    $$\begin{aligned}
    \FreeVars{x} &= \{x\}, \\
    \FreeVars{f(t_1,\ldots,t_n)} &= \bigcup_i \FreeVars{t_i},
    \end{aligned}$$
    where $x$ is a variable and $f$ is an $n$-ary function symbol; the $n=0$ case covers constants, for which the empty
    union gives $\emptyset$.
-/
theorem term_realize_congr (t : L.Term ℕ) (s s' : ℕ → M)
    (h : ∀ x ∈ t.varFinset, s x = s' x) : t.realize s = t.realize s' := by
  induction t with
  | var x => exact h x (by simp)
  | func f ts ih =>
    simp only [Term.realize]
    congr 1
    funext i
    apply ih i
    intro x hx
    exact h x (by simp only [Term.varFinset, Finset.mem_biUnion]; exact ⟨i, by simp, hx⟩)

inductive Connective where
  | conj | disj | imp

inductive Quantifier where
  | all | ex

def Connective.eval : Connective → Prop → Prop → Prop
  | .conj, P, Q => P ∧ Q
  | .disj, P, Q => P ∨ Q
  | .imp, P, Q => P → Q

def Quantifier.eval (q : Quantifier) (P : M → Prop) : Prop :=
  match q with
  | .all => ∀ a, P a
  | .ex => ∃ a, P a

theorem Connective.eval_congr (c : Connective) {P P' Q Q' : Prop}
    (hP : P ↔ P') (hQ : Q ↔ Q') : c.eval P Q ↔ c.eval P' Q' := by
  cases c <;> simp [eval, hP, hQ]

theorem Quantifier.eval_congr (q : Quantifier) {P Q : M → Prop}
    (h : ∀ a, P a ↔ Q a) : q.eval P ↔ q.eval Q := by
  cases q <;> simp only [eval] <;> simp_rw [h]

/-- Each binary connective and each named quantifier is a formula constructor. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefineas{atomic formula}{atomic formulas} are:
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\bot$, called \termdefine{falsum}, satisfied in no interpretation.
    *   $t_0=t_1$, where $t_0,t_1$ are terms.
    *   $R(t_1,\ldots,t_n)$, where $R$ is an $n$-ary relation symbol and $t_1,\ldots,t_n$ are terms.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefineas{formula}{formulas} are defined recursively:
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   Every atomic formula is a formula.
    *   If $\varphi$ and $\psi$ are formulas, then $(\varphi \land \psi)$, $(\varphi \lor \psi)$, and $(\varphi \to \psi)$
        are formulas.
    *   If $\varphi$ is a formula and $x$ is a variable, then $(\forallbind{x}{\varphi})$ and $(\existsbind{x}{\varphi})$
        are formulas.
    *   Nothing else is a formula.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Equivalently, in EBNF summary form,
    $$
    \begin{aligned}
    \textit{Atom} &::= \bot\\
    &\mid \textit{Term}=\textit{Term}\\
    &\mid R(\textit{Term},\ldots,\textit{Term}),\\
    \textit{Formula} &::= \textit{Atom}\\
    &\mid (\textit{Formula}\land\textit{Formula})\\
    &\mid (\textit{Formula}\lor\textit{Formula})\\
    &\mid (\textit{Formula}\to\textit{Formula})\\
    &\mid (\forallbind{\textit{Var}}{\textit{Formula}})\\
    &\mid (\existsbind{\textit{Var}}{\textit{Formula}}).
    \end{aligned}
    $$
    Here $R$ ranges over relation symbols, again with the arity determining the number of arguments.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In $L_\in$, the relation-symbol atomic formulas are exactly $t_0 \in t_1$; $\bot$ and equalities $t_0=t_1$ are still
    atomic formulas.
-/
inductive Formula (L : Language.{u,v}) : Type (max u v) where
  | falsum : Formula L
  | equal (t r : L.Term ℕ) : Formula L
  | rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term ℕ) : Formula L
  | binary (c : Connective) (φ ψ : Formula L) : Formula L
  | quant (q : Quantifier) (x : ℕ) (φ : Formula L) : Formula L

namespace Formula

/-- Negation is the abbreviation using implication and falsity. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Negation and the biconditional are abbreviations:
    $$\neg\varphi \;:=\; \varphi \to \bot, \qquad
    \varphi \leftrightarrow \psi \;:=\; (\varphi \to \psi) \land (\psi \to \varphi).$$
    When parentheses are omitted, we use the precedence convention
    $$\forall x,\ \exists x \;>\; \neg \;>\; \land \;>\; \lor \;>\; \to \;>\; \leftrightarrow,$$
    with $\land$ and $\lor$ parsed left-associatively and $\to$ parsed right-associatively.
-/
def negation (φ : Formula L) : Formula L := .binary .imp φ .falsum

/-- The biconditional abbreviates the conjunction of both implications. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Negation and the biconditional are abbreviations:
    $$\neg\varphi \;:=\; \varphi \to \bot, \qquad
    \varphi \leftrightarrow \psi \;:=\; (\varphi \to \psi) \land (\psi \to \varphi).$$
    When parentheses are omitted, we use the precedence convention
    $$\forall x,\ \exists x \;>\; \neg \;>\; \land \;>\; \lor \;>\; \to \;>\; \leftrightarrow,$$
    with $\land$ and $\lor$ parsed left-associatively and $\to$ parsed right-associatively.
-/
def biconditional (φ ψ : Formula L) : Formula L :=
  .binary .conj (.binary .imp φ ψ) (.binary .imp ψ φ)


/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set $\FreeVars{\varphi}$ of free variables of a formula $\varphi$ is then defined by induction on $\varphi$:
    $$\begin{aligned}
    \FreeVars{\bot} &= \emptyset, \\
    \FreeVars{R(t_1,\ldots,t_n)} &= \bigcup_i \FreeVars{t_i}, \\
    \FreeVars{t_0=t_1} &= \FreeVars{t_0} \cup \FreeVars{t_1}, \\
    \FreeVars{\varphi \land \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
    \FreeVars{\varphi \lor \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
    \FreeVars{\varphi \to \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
    \FreeVars{\forallbind{x}{\varphi}} &= \SetDifference{\FreeVars{\varphi}}{\{x\}}, \\
    \FreeVars{\existsbind{x}{\varphi}} &= \SetDifference{\FreeVars{\varphi}}{\{x\}}.
    \end{aligned}$$
    A \termdefine{sentence}, also called a \termdefineas{logical proposition}{proposition}, is a formula with
    $\FreeVars{\varphi} = \emptyset$ — its truth value depends only on the interpretation of the non-logical symbols of $L$,
    not on a variable assignment. For $L_\in$, the only such symbol is $\in$.
-/
def fv : Formula L → Finset ℕ
  | .falsum => ∅
  | .equal t r => t.varFinset ∪ r.varFinset
  | .rel _ ts => Finset.univ.biUnion (fun i => (ts i).varFinset)
  | .binary _ φ ψ => φ.fv ∪ ψ.fv
  | .quant _ x φ => φ.fv.erase x

/-- Count formula constructors, ignoring the sizes of the terms in atomic formulas. -/
def nodes : Formula L → ℕ
  | .falsum | .equal .. | .rel .. => 1
  | .binary _ φ ψ => φ.nodes + ψ.nodes + 1
  | .quant _ _ φ => φ.nodes + 1

theorem nodes_pos (φ : Formula L) : 0 < φ.nodes := by cases φ <;> simp [nodes]

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{variable assignment} is a function $s : \mathrm{Var} \to M$; write $s[x \mapsto a]$ for the assignment
    defined by
    $$s[x \mapsto a](y) = \begin{cases} a & \text{if } y = x, \\ s(y) & \text{if } y \ne x. \end{cases}$$ Terms are
    interpreted recursively:
    $$\begin{aligned}
    x^{\mathcal M,s} &= s(x),\\
    f(t_1,\ldots,t_n)^{\mathcal M,s} &= f^{\mathcal M}(t_1^{\mathcal M,s},\ldots,t_n^{\mathcal M,s}),
    \end{aligned}$$
    where $x$ is a variable and $f$ is an $n$-ary function symbol; the $n=0$ case covers constants, giving $c^{\mathcal
    M,s}=c^{\mathcal M}$.
    In pure $L_\in$, every term is a variable, so $t^{\mathcal M,s}=s(t)$. Satisfaction $\mathcal M,s \models \varphi$ is
    defined by induction on formulas:
    $$\begin{aligned}
    \mathcal M,s &\nvDash \bot,\\
    \mathcal M,s \models t = u &\iff t^{\mathcal M,s} = u^{\mathcal M,s},\\
    \mathcal M,s \models R(t_1,\ldots,t_n) &\iff (t_1^{\mathcal M,s},\ldots,t_n^{\mathcal M,s}) \in R^{\mathcal M},\\
    \mathcal M,s \models \varphi \land \psi &\iff \mathcal M,s \models \varphi \text{ and } \mathcal M,s \models \psi,\\
    \mathcal M,s \models \varphi \lor \psi &\iff \mathcal M,s \models \varphi \text{ or } \mathcal M,s \models \psi,\\
    \mathcal M,s \models \varphi \to \psi &\iff \mathcal M,s \nvDash \varphi \text{ or } \mathcal M,s \models \psi,\\
    \mathcal M,s \models \forall x\,\varphi &\iff \mathcal M,s[x \mapsto a] \models \varphi \text{ for every } a \in M,\\
    \mathcal M,s \models \exists x\,\varphi &\iff \mathcal M,s[x \mapsto a] \models \varphi \text{ for some } a \in M.
    \end{aligned}$$
    For $L_\in$, the relation clause says $\mathcal M,s \models t \in u$ iff $(t^{\mathcal M,s},u^{\mathcal M,s})\in E$.
-/
def Realize : Formula L → (ℕ → M) → Prop
  | .falsum, _ => False
  | .equal t r, s => t.realize s = r.realize s
  | .rel R ts, s => Structure.RelMap R (fun i => (ts i).realize s)
  | .binary c φ ψ, s => c.eval (φ.Realize s) (ψ.Realize s)
  | .quant q x φ, s => q.eval (fun a => φ.Realize (Function.update s x a))

/-- Assignment locality is proved before substitution or alpha invariance. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Assignments and free variables
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Induct first on terms and then on formulas. For a variable, the claim is the agreement hypothesis. For a function
    application, it follows by applying the function interpretation to the equal values of its arguments. The atomic and
    Boolean formula cases then follow from their semantic clauses. At a quantified formula with binder $x$, the two
    assignments agree on the free variables of the body other than $x$. For each $a\in M$, the updated assignments
    $s[x\mapsto a]$ and $s'[x\mapsto a]$ agree on all free variables of the body. The induction hypothesis applies for every
    $a$, giving both the universal and existential cases. A sentence has no free variables, so the agreement hypothesis
    is vacuous.
-/
theorem realize_congr (φ : Formula L) (s s' : ℕ → M)
    (h : ∀ x ∈ φ.fv, s x = s' x) : φ.Realize s ↔ φ.Realize s' := by
  induction φ generalizing s s' with
  | falsum => rfl
  | equal t r =>
    dsimp [Realize]
    rw [term_realize_congr t s s' (fun x hx => h x (Finset.mem_union_left _ hx)),
      term_realize_congr r s s' (fun x hx => h x (Finset.mem_union_right _ hx))]
  | rel R ts =>
    have ht : (fun i => (ts i).realize s) = (fun i => (ts i).realize s') := by
      funext i
      apply term_realize_congr
      intro x hx
      apply h x
      simp only [fv, Finset.mem_biUnion]
      exact ⟨i, by simp, hx⟩
    simp only [Realize, ht]
  | binary c φ ψ ihφ ihψ =>
    exact c.eval_congr (ihφ s s' (fun x hx => h x (Finset.mem_union_left _ hx)))
      (ihψ s s' (fun x hx => h x (Finset.mem_union_right _ hx)))
  | quant q x φ ih =>
    apply q.eval_congr
    intro a
    apply ih
    intro y hy
    by_cases hxy : y = x
    · simp [hxy]
    · simp only [Function.update_of_ne hxy]
      exact h y (Finset.mem_erase.mpr ⟨hxy, hy⟩)

/-- A sentence has the same truth value under every assignment. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set $\FreeVars{\varphi}$ of free variables of a formula $\varphi$ is then defined by induction on $\varphi$:
    $$\begin{aligned}
    \FreeVars{\bot} &= \emptyset, \\
    \FreeVars{R(t_1,\ldots,t_n)} &= \bigcup_i \FreeVars{t_i}, \\
    \FreeVars{t_0=t_1} &= \FreeVars{t_0} \cup \FreeVars{t_1}, \\
    \FreeVars{\varphi \land \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
    \FreeVars{\varphi \lor \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
    \FreeVars{\varphi \to \psi} &= \FreeVars{\varphi} \cup \FreeVars{\psi}, \\
    \FreeVars{\forallbind{x}{\varphi}} &= \SetDifference{\FreeVars{\varphi}}{\{x\}}, \\
    \FreeVars{\existsbind{x}{\varphi}} &= \SetDifference{\FreeVars{\varphi}}{\{x\}}.
    \end{aligned}$$
    A \termdefine{sentence}, also called a \termdefineas{logical proposition}{proposition}, is a formula with
    $\FreeVars{\varphi} = \emptyset$ — its truth value depends only on the interpretation of the non-logical symbols of $L$,
    not on a variable assignment. For $L_\in$, the only such symbol is $\in$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    If $\varphi$ is a sentence, its truth does not depend on $s$, and we write $\mathcal M \models \varphi$. A model
    $\mathcal M$ satisfies a theory $T$, written $\mathcal M \models T$, if $\mathcal M \models \sigma$ for every sentence
    $\sigma \in T$.
-/
theorem realize_sentence (φ : Formula L) (hφ : φ.fv = ∅) (s s' : ℕ → M) :
    φ.Realize s ↔ φ.Realize s' :=
  φ.realize_congr s s' (by simp [hφ])


/-- Move the named variable into the single bound-variable slot. -/
def bind (x : ℕ) (φ : L.Formula ℕ) : L.BoundedFormula ℕ 1 :=
  BoundedFormula.relabel (fun y => if y = x then Sum.inr 0 else Sum.inl y) φ

theorem realize_bind (x : ℕ) (φ : L.Formula ℕ) (s : ℕ → M) (a : M) :
    (bind x φ).Realize s (Fin.snoc default a) ↔
      φ.Realize (Function.update s x a) := by
  rw [bind, BoundedFormula.realize_relabel]
  have hs : (Sum.elim s ((Fin.snoc (default : Fin 0 → M) a) ∘ Fin.castAdd 0) ∘
      (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y)) =
      Function.update s x a := by
    funext y
    by_cases hy : y = x
    · subst y
      simp [Fin.snoc_zero]
    · simp [hy]
  rw [hs]
  have hv : (Fin.snoc (default : Fin 0 → M) a ∘ Fin.natAdd 1) = (default : Fin 0 → M) :=
    Subsingleton.elim _ _
  rw [hv]
  rfl

/-- Translation into mathlib's standard first-order syntax. -/
def toStandard : Formula L → L.Formula ℕ
  | .falsum => ⊥
  | .equal t r => t.equal r
  | .rel R ts => R.formula ts
  | .binary c φ ψ => match c with
    | .conj => φ.toStandard ⊓ ψ.toStandard
    | .disj => φ.toStandard ⊔ ψ.toStandard
    | .imp => φ.toStandard.imp ψ.toStandard
  | .quant q x φ => match q with
    | .all => (bind x φ.toStandard).all
    | .ex => (bind x φ.toStandard).ex

/-- The named syntax has precisely the usual first-order interpretation. -/
theorem realize_toStandard (φ : Formula L) (s : ℕ → M) :
    φ.toStandard.Realize s ↔ φ.Realize s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t r => exact FirstOrder.Language.Formula.realize_equal
  | rel R ts => exact FirstOrder.Language.Formula.realize_rel
  | binary c φ ψ ihφ ihψ =>
    cases c <;> simp [toStandard, Realize, Connective.eval, ihφ, ihψ]
  | quant q x φ ih =>
    cases q <;>
      simp only [toStandard, FirstOrder.Language.Formula.Realize,
        BoundedFormula.realize_all, BoundedFormula.realize_ex, Realize, Quantifier.eval] <;>
      simp_rw [realize_bind, ih]

end Formula
end PolishSpaceBook.NamedFirstOrder
