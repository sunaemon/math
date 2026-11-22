module

public import PolishSpaceBook.FirstOrderAlphaSubstitution

@[expose] public section

/-!
# Semantic clauses on alpha-classes and finite contexts

These are the appendix's assignment clauses, lifted through the already proved
alpha invariance. Freshness at existential elimination is used exactly on the
free variables of the quantified formula, the context and the conclusion.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

namespace AlphaFormula

def falsum : AlphaFormula L := mk .falsum
def equal (t r : L.Term ℕ) : AlphaFormula L := mk (.equal t r)
def neg (φ : AlphaFormula L) : AlphaFormula L := binary .imp φ falsum

@[simp] theorem realize_falsum (s : ℕ → M) : ¬(falsum : AlphaFormula L).Realize s := id

@[simp] theorem realize_equal (t r : L.Term ℕ) (s : ℕ → M) :
    (equal t r).Realize s ↔ t.realize s = r.realize s := Iff.rfl

theorem realize_binary (c : Connective) (φ ψ : AlphaFormula L) (s : ℕ → M) :
    (binary c φ ψ).Realize s ↔ c.eval (φ.Realize s) (ψ.Realize s) := by
  induction φ, ψ using Quotient.inductionOn₂ with
  | _ φ ψ => rfl

theorem realize_quant (q : Quantifier) (x : ℕ) (φ : AlphaFormula L) (s : ℕ → M) :
    (quant q x φ).Realize s ↔ q.eval (fun a => φ.Realize (Function.update s x a)) := by
  induction φ using Quotient.inductionOn with
  | _ φ => rfl

@[simp] theorem realize_conj (φ ψ : AlphaFormula L) (s : ℕ → M) :
    (binary .conj φ ψ).Realize s ↔ φ.Realize s ∧ ψ.Realize s := realize_binary _ _ _ _

@[simp] theorem realize_disj (φ ψ : AlphaFormula L) (s : ℕ → M) :
    (binary .disj φ ψ).Realize s ↔ φ.Realize s ∨ ψ.Realize s := realize_binary _ _ _ _

@[simp] theorem realize_imp (φ ψ : AlphaFormula L) (s : ℕ → M) :
    (binary .imp φ ψ).Realize s ↔ (φ.Realize s → ψ.Realize s) := realize_binary _ _ _ _

/-- The book's classical disjunctive clause agrees with the canonical implication clause. -/
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
theorem realize_imp_classical (φ ψ : AlphaFormula L) (s : ℕ → M) :
    (binary .imp φ ψ).Realize s ↔ ¬φ.Realize s ∨ ψ.Realize s :=
  (realize_imp φ ψ s).trans imp_iff_not_or

@[simp] theorem realize_neg (φ : AlphaFormula L) (s : ℕ → M) :
    (neg φ).Realize s ↔ ¬φ.Realize s := by
  simp [neg]

@[simp] theorem realize_all (x : ℕ) (φ : AlphaFormula L) (s : ℕ → M) :
    (quant .all x φ).Realize s ↔ ∀ a, φ.Realize (Function.update s x a) := realize_quant _ _ _ _

@[simp] theorem realize_ex (x : ℕ) (φ : AlphaFormula L) (s : ℕ → M) :
    (quant .ex x φ).Realize s ↔ ∃ a, φ.Realize (Function.update s x a) := realize_quant _ _ _ _

@[simp] theorem fv_quant (q : Quantifier) (x : ℕ) (φ : AlphaFormula L) :
    (quant q x φ).fv = φ.fv.erase x := by
  induction φ using Quotient.inductionOn with
  | _ φ => rfl

theorem realize_congr (φ : AlphaFormula L) (s s' : ℕ → M)
    (h : ∀ x ∈ φ.fv, s x = s' x) : φ.Realize s ↔ φ.Realize s' := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Formula.realize_congr φ s s' h

theorem realize_update (φ : AlphaFormula L) (s : ℕ → M) (x : ℕ) (a : M)
    (hx : x ∉ φ.fv) : φ.Realize (Function.update s x a) ↔ φ.Realize s := by
  apply φ.realize_congr
  intro z hz
  exact Function.update_of_ne (by intro h; subst z; exact hx hz) _ _

/-- The eigenvariable can name the existential witness without altering other parameters. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Put $s'=s[y\mapsto a]$. This assignment still satisfies $\Gamma$. Moreover, the substitution lemma gives
    $$\mathcal M,s'\models\varphi\subst{x}{y}
    \quad\Longleftrightarrow\quad
    \mathcal M,s[y\mapsto a][x\mapsto a]\models\varphi.$$
    The assignments on the right and $s[x\mapsto a]$ agree on $\FreeVars{\varphi}$:
    both assign $a$ to $x$, and a free variable of the body different from $x$ cannot be $y$ by the side condition.
    This also covers $y=x$.
-/
theorem realize_eigeninstance (φ : AlphaFormula L) (x y : ℕ) (s : ℕ → M) (a : M)
    (hy : y ∉ (quant .ex x φ).fv) :
    (φ.subst x (.var y)).Realize (Function.update s y a) ↔
      φ.Realize (Function.update s x a) := by
  rw [realize_subst]
  simp only [Term.realize_var, Function.update_self]
  apply φ.realize_congr
  intro z hz
  by_cases hzx : z = x
  · subst z; simp
  · have hzy : z ≠ y := by
      intro he
      subst z
      exact hy (by simpa only [fv_quant, Finset.mem_erase] using And.intro hzx hz)
    simp [hzx, hzy]

end AlphaFormula

abbrev Context (L : Language.{u,v}) := Finset (AlphaFormula L)

namespace Context

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a finite set of formulas $\Gamma$, write
    $$\FreeVars{\Gamma} := \bigcup_{\varphi \in \Gamma}\FreeVars{\varphi}.$$
-/
def fv (Γ : Context L) : Finset ℕ := Γ.biUnion AlphaFormula.fv

def Realize (Γ : Context L) (s : ℕ → M) : Prop := ∀ φ ∈ Γ, φ.Realize s

theorem realize_congr (Γ : Context L) (s s' : ℕ → M)
    (h : ∀ x ∈ Γ.fv, s x = s' x) : Γ.Realize s ↔ Γ.Realize s' := by
  have hφ (φ : AlphaFormula L) (hφ : φ ∈ Γ) : φ.Realize s ↔ φ.Realize s' := by
    apply φ.realize_congr
    intro x hx
    exact h x (Finset.mem_biUnion.mpr ⟨φ, hφ, hx⟩)
  constructor
  · intro hs φ hmem; exact (hφ φ hmem).mp (hs φ hmem)
  · intro hs φ hmem; exact (hφ φ hmem).mpr (hs φ hmem)

theorem realize_update (Γ : Context L) (s : ℕ → M) (x : ℕ) (a : M)
    (hx : x ∉ Γ.fv) : Γ.Realize (Function.update s x a) ↔ Γ.Realize s := by
  apply Γ.realize_congr
  intro z hz
  exact Function.update_of_ne (by intro h; subst z; exact hx hz) _ _

@[simp] theorem realize_insert [DecidableEq (AlphaFormula L)]
    (Γ : Context L) (φ : AlphaFormula L) (s : ℕ → M) :
    (insert φ Γ).Realize s ↔ φ.Realize s ∧ Γ.Realize s := by
  simp [Realize]

end Context
end PolishSpaceBook.NamedFirstOrder
