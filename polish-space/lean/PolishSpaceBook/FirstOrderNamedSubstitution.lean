module

public import PolishSpaceBook.FirstOrderNamedSyntax

@[expose] public section

/-!
# Capture-avoiding substitution in named first-order formulas

The fresh name is the least natural outside the finite set in the book.
Counting formula constructors, rather than term constructors, makes substitution
size-preserving. This justifies both recursive calls in the renaming case.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

namespace Formula

/-- Bounded evaluation of exactly the appendix's recursive clauses. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termuse{substitution} $\varphi\subst{x}{t}$ of $t$ for $x$ in a formula $\varphi$ replaces every free occurrence of
    $x$ by $t$, defined by induction on $\varphi$:
    $$\begin{aligned}
    \bot\subst{x}{t} &:= \bot, \\
    R(t_1,\ldots,t_n)\subst{x}{t} &:= R(t_1\subst{x}{t},\ldots,t_n\subst{x}{t}), \\
    (t_0=t_1)\subst{x}{t} &:= t_0\subst{x}{t}=t_1\subst{x}{t}, \\
    (\varphi \land \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \land \psi\subst{x}{t}, \\
    (\varphi \lor \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \lor \psi\subst{x}{t}, \\
    (\varphi \to \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \to \psi\subst{x}{t}, \\
    (\forallbind{y}{\varphi})\subst{x}{t} &:= \begin{cases}
    \forallbind{y}{\varphi} & \text{if } y = x, \\
    \forallbind{y}{(\varphi\subst{x}{t})} & \text{if } y \ne x \text{ and } y \notin \FreeVars{t}, \\
    \forallbind{z}{(\varphi\subst{y}{z}\subst{x}{t})} & \text{if } y \ne x \text{ and } y \in \FreeVars{t},
    \end{cases}\\
    (\existsbind{y}{\varphi})\subst{x}{t} &:= \begin{cases}
    \existsbind{y}{\varphi} & \text{if } y = x, \\
    \existsbind{y}{(\varphi\subst{x}{t})} & \text{if } y \ne x \text{ and } y \notin \FreeVars{t}, \\
    \existsbind{z}{(\varphi\subst{y}{z}\subst{x}{t})} & \text{if } y \ne x \text{ and } y \in \FreeVars{t},
    \end{cases}
    \end{aligned}$$
    where in the renaming clauses $z$ is the first variable (in the well-order on $\mathrm{Var}$) not in $\FreeVars{\varphi}
    \cup \FreeVars{t} \cup \{x\}$. By construction, substitution is \termdefine{capture-avoiding}: a bound variable $y$ that
    would otherwise capture a free occurrence in $t$ is first renamed to a fresh $z$, so $\varphi\subst{x}{t}$ is defined
    for every $\varphi$, $x$, $t$.
-/
def substFuel : ℕ → Formula L → ℕ → L.Term ℕ → Formula L
  | 0, φ, _, _ => φ
  | _ + 1, .falsum, _, _ => .falsum
  | _ + 1, .equal t r, x, a => .equal (termSubst t x a) (termSubst r x a)
  | _ + 1, .rel R ts, x, a => .rel R (fun i => termSubst (ts i) x a)
  | k + 1, .binary c φ ψ, x, a => .binary c (substFuel k φ x a) (substFuel k ψ x a)
  | k + 1, .quant q y φ, x, a =>
    if y = x then .quant q y φ
    else if y ∉ a.varFinset then .quant q y (substFuel k φ x a)
    else
      let z := NamedLambda.Term.fresh (φ.fv ∪ a.varFinset ∪ {x})
      .quant q z (substFuel k (substFuel k φ y (.var z)) x a)

/-- Atomic terms can grow, but the number of formula constructors is unchanged. -/
theorem nodes_substFuel (k : ℕ) (φ : Formula L) (x : ℕ) (a : L.Term ℕ) :
    (substFuel k φ x a).nodes = φ.nodes := by
  induction k generalizing φ x a with
  | zero => rfl
  | succ k ih =>
    cases φ with
    | falsum | equal | rel => rfl
    | binary c φ ψ => simp only [substFuel, nodes, ih]
    | quant q y φ =>
      simp only [substFuel]
      split_ifs <;> simp only [nodes, ih]

/-- All sufficient recursion budgets agree, including after renaming a body. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    To justify the recursion in the renaming clauses, count formula constructors, counting each atomic formula as one
    regardless of the sizes of its terms. Substitution preserves this count. More precisely, first evaluate the displayed
    clauses with a finite recursion budget: at budget zero return the original formula, and at each recursive call
    use one less unit. Induction on the budget proves that the formula-constructor count is unchanged, including through
    both calls in a renaming clause. A second induction shows that any two budgets at least the original formula's count
    give the same result. In the renaming case, the intermediate body has the same count as the original body, so both
    recursive calls have sufficient smaller budgets. Taking the original count as budget therefore defines a total
    operation satisfying the displayed clauses.
-/
theorem substFuel_stable (k : ℕ) (φ : Formula L) (x : ℕ) (a : L.Term ℕ) (l : ℕ)
    (hk : φ.nodes ≤ k) (hl : φ.nodes ≤ l) :
    substFuel k φ x a = substFuel l φ x a := by
  induction k generalizing φ x a l with
  | zero => have := nodes_pos φ; omega
  | succ k ih =>
    cases l with
    | zero => have := nodes_pos φ; omega
    | succ l =>
      cases φ with
      | falsum | equal | rel => rfl
      | binary c φ ψ =>
        have hφk : φ.nodes ≤ k := by simp only [nodes] at hk; omega
        have hφl : φ.nodes ≤ l := by simp only [nodes] at hl; omega
        have hψk : ψ.nodes ≤ k := by simp only [nodes] at hk; omega
        have hψl : ψ.nodes ≤ l := by simp only [nodes] at hl; omega
        simp only [substFuel, ih φ x a l hφk hφl, ih ψ x a l hψk hψl]
      | quant q y φ =>
        have hφk : φ.nodes ≤ k := by simpa only [nodes, Nat.add_le_add_iff_right] using hk
        have hφl : φ.nodes ≤ l := by simpa only [nodes, Nat.add_le_add_iff_right] using hl
        simp only [substFuel]
        by_cases hy : y = x
        · simp only [ite_eq_left hy]
        · simp only [ite_eq_right hy]
          by_cases hfree : y ∉ a.varFinset
          · simp only [ite_eq_left hfree]
            rw [ih φ x a l hφk hφl]
          · simp only [ite_eq_right hfree]
            let z := NamedLambda.Term.fresh (φ.fv ∪ a.varFinset ∪ {x})
            have hr := ih φ y (.var z) l hφk hφl
            have ho := ih (substFuel k φ y (.var z)) x a l
              (by simpa only [nodes_substFuel] using hφk)
              (by simpa only [nodes_substFuel] using hφl)
            rw [ho, hr]

/-- Total capture-avoiding substitution with the prescribed least fresh name. -/
def subst (φ : Formula L) (x : ℕ) (a : L.Term ℕ) : Formula L :=
  substFuel φ.nodes φ x a

theorem substFuel_eq_subst (φ : Formula L) (x : ℕ) (a : L.Term ℕ) (k : ℕ)
    (hk : φ.nodes ≤ k) : substFuel k φ x a = φ.subst x a :=
  substFuel_stable k φ x a φ.nodes hk le_rfl

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termuse{substitution} $\varphi\subst{x}{t}$ of $t$ for $x$ in a formula $\varphi$ replaces every free occurrence of
    $x$ by $t$, defined by induction on $\varphi$:
    $$\begin{aligned}
    \bot\subst{x}{t} &:= \bot, \\
    R(t_1,\ldots,t_n)\subst{x}{t} &:= R(t_1\subst{x}{t},\ldots,t_n\subst{x}{t}), \\
    (t_0=t_1)\subst{x}{t} &:= t_0\subst{x}{t}=t_1\subst{x}{t}, \\
    (\varphi \land \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \land \psi\subst{x}{t}, \\
    (\varphi \lor \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \lor \psi\subst{x}{t}, \\
    (\varphi \to \psi)\subst{x}{t} &:= \varphi\subst{x}{t} \to \psi\subst{x}{t}, \\
    (\forallbind{y}{\varphi})\subst{x}{t} &:= \begin{cases}
    \forallbind{y}{\varphi} & \text{if } y = x, \\
    \forallbind{y}{(\varphi\subst{x}{t})} & \text{if } y \ne x \text{ and } y \notin \FreeVars{t}, \\
    \forallbind{z}{(\varphi\subst{y}{z}\subst{x}{t})} & \text{if } y \ne x \text{ and } y \in \FreeVars{t},
    \end{cases}\\
    (\existsbind{y}{\varphi})\subst{x}{t} &:= \begin{cases}
    \existsbind{y}{\varphi} & \text{if } y = x, \\
    \existsbind{y}{(\varphi\subst{x}{t})} & \text{if } y \ne x \text{ and } y \notin \FreeVars{t}, \\
    \existsbind{z}{(\varphi\subst{y}{z}\subst{x}{t})} & \text{if } y \ne x \text{ and } y \in \FreeVars{t},
    \end{cases}
    \end{aligned}$$
    where in the renaming clauses $z$ is the first variable (in the well-order on $\mathrm{Var}$) not in $\FreeVars{\varphi}
    \cup \FreeVars{t} \cup \{x\}$. By construction, substitution is \termdefine{capture-avoiding}: a bound variable $y$ that
    would otherwise capture a free occurrence in $t$ is first renamed to a fresh $z$, so $\varphi\subst{x}{t}$ is defined
    for every $\varphi$, $x$, $t$.
-/
theorem subst_quant (q : Quantifier) (y : ℕ) (φ : Formula L) (x : ℕ) (a : L.Term ℕ) :
    (quant q y φ).subst x a =
      if y = x then quant q y φ
      else if y ∉ a.varFinset then quant q y (φ.subst x a)
      else
        let z := NamedLambda.Term.fresh (φ.fv ∪ a.varFinset ∪ {x})
        quant q z ((φ.subst y (.var z)).subst x a) := by
  simp only [subst, nodes, substFuel]
  split_ifs <;> try rfl
  congr 1
  exact substFuel_stable φ.nodes _ x a _ (by simp [nodes_substFuel]) le_rfl


private theorem term_realize_update (t : L.Term ℕ) (s : ℕ → M) (x : ℕ) (a : M)
    (hx : x ∉ t.varFinset) : t.realize (Function.update s x a) = t.realize s := by
  apply term_realize_congr
  intro y hy
  exact Function.update_of_ne (by intro h; subst y; exact hx hy) _ _

/-- Semantic substitution, with enough fuel for both recursive calls at a binder. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Finally suppose $y\ne x$ and $y\in\FreeVars{t}$. Let $z$ be the fresh variable specified by the substitution rule.
    Then
    $$(\forall y\,\psi)\subst{x}{t}=\forall z\,(\psi\subst{y}{z}\subst{x}{t}).$$
    Fix $b\in M$ and evaluate the body on the right under $s[z\mapsto b]$.
    Since $z\notin\FreeVars{t}$, the value of $t$ is still $a$. Apply the induction hypothesis first to substitution of
    $t$ into the renamed body, and then to substitution of $z$ into $\psi$. Since $z\ne x$, the resulting condition is
    $$\mathcal M,s[z\mapsto b][x\mapsto a][y\mapsto b]\models\psi.$$
    Because $z\notin\FreeVars{\psi}$, assignment locality allows us to remove the initial update at $z$. We obtain
    $$\mathcal M,s[x\mapsto a][y\mapsto b]\models\psi.$$
    Quantifying over $b$ proves the universal case. The existential case uses the same argument with "some" in place of
    "every". Thus the renaming step is justified directly by assignment locality, without presupposing that
    $\alpha$-equivalence preserves truth.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Write $a=t^{\mathcal M,s}$. For $\forall y\,\psi$, if $y=x$, substitution leaves the formula unchanged, and
    $s[x\mapsto a][x\mapsto b]=s[x\mapsto b]$ for every $b\in M$. If $y\ne x$ and $y\notin\FreeVars{t}$,
    \termuseas{assignment locality lemma}{assignment locality} gives $t^{\mathcal M,s[y\mapsto b]}=a$.
    The induction hypothesis identifies the substituted body's interpretation with that of $\psi$ under
    $s[y\mapsto b][x\mapsto a]$. The updates commute, giving the required universal clause.
-/
theorem realize_substFuel (k : ℕ) (φ : Formula L) (x : ℕ) (t : L.Term ℕ) (s : ℕ → M)
    (hk : φ.nodes ≤ k) :
    (substFuel k φ x t).Realize s ↔ φ.Realize (Function.update s x (t.realize s)) := by
  induction k generalizing φ x t s with
  | zero => have := nodes_pos φ; omega
  | succ k ih =>
    cases φ with
    | falsum => rfl
    | equal a b => simp only [substFuel, Realize, termSubst_realize]
    | rel R ts => simp only [substFuel, Realize, termSubst_realize]
    | binary c φ ψ =>
      have hφ : φ.nodes ≤ k := by simp only [nodes] at hk; omega
      have hψ : ψ.nodes ≤ k := by simp only [nodes] at hk; omega
      exact c.eval_congr (ih φ x t s hφ) (ih ψ x t s hψ)
    | quant q y φ =>
      have hφ : φ.nodes ≤ k := by simpa only [nodes, Nat.add_le_add_iff_right] using hk
      by_cases hy : y = x
      · subst y
        simp [substFuel, Realize]
      · by_cases hfree : y ∉ t.varFinset
        · simp only [substFuel, ite_eq_right hy, ite_eq_left hfree, Realize]
          apply q.eval_congr
          intro a
          rw [ih φ x t (Function.update s y a) hφ, term_realize_update t s y a hfree]
          apply φ.realize_congr
          intro z hz
          by_cases hzx : z = x <;> by_cases hzy : z = y <;>
            simp_all
        · simp only [substFuel, ite_eq_right hy, ite_eq_right hfree, Realize]
          let z := NamedLambda.Term.fresh (φ.fv ∪ t.varFinset ∪ {x})
          have hz : z ∉ φ.fv ∪ t.varFinset ∪ {x} := NamedLambda.Term.fresh_not_mem _
          have hzφ : z ∉ φ.fv := by simp only [Finset.mem_union] at hz; tauto
          have hzt : z ∉ t.varFinset := by simp only [Finset.mem_union] at hz; tauto
          have hzx : z ≠ x := by simp only [Finset.mem_union, Finset.mem_singleton] at hz; tauto
          apply q.eval_congr
          intro a
          change (substFuel k (substFuel k φ y (.var z)) x t).Realize (Function.update s z a) ↔ _
          rw [ih _ x t (Function.update s z a) (by simpa only [nodes_substFuel] using hφ),
            term_realize_update t s z a hzt,
            ih φ y (.var z) (Function.update (Function.update s z a) x (t.realize s)) hφ]
          simp only [Term.realize_var, Function.update_of_ne hzx, Function.update_self]
          apply φ.realize_congr
          intro w hw
          have hwz : w ≠ z := by intro h; subst w; exact hzφ hw
          by_cases hwy : w = y <;> by_cases hwx : w = x <;>
            simp_all

/-- The capture-avoiding substitution lemma for the book's named formula syntax. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: substitution lemma
-/
theorem realize_subst (φ : Formula L) (x : ℕ) (t : L.Term ℕ) (s : ℕ → M) :
    (φ.subst x t).Realize s ↔ φ.Realize (Function.update s x (t.realize s)) :=
  realize_substFuel φ.nodes φ x t s le_rfl

/-- Fresh bound-variable renaming preserves truth without assuming alpha invariance. -/
theorem realize_rename_quant (q : Quantifier) (y z : ℕ) (φ : Formula L)
    (hz : z ∉ φ.fv) (s : ℕ → M) :
    (quant q z (φ.subst y (.var z))).Realize s ↔ (quant q y φ).Realize s := by
  apply q.eval_congr
  intro a
  rw [realize_subst]
  simp only [Term.realize_var, Function.update_self]
  apply φ.realize_congr
  intro w hw
  have hwz : w ≠ z := by intro h; subst w; exact hz hw
  by_cases hwy : w = y <;> simp [hwy, hwz]

/-- The same theorem stated with mathlib's canonical first-order satisfaction. -/
theorem realize_toStandard_subst (φ : Formula L) (x : ℕ) (t : L.Term ℕ) (s : ℕ → M) :
    (φ.subst x t).toStandard.Realize s ↔
      φ.toStandard.Realize (Function.update s x (t.realize s)) := by
  rw [realize_toStandard, realize_subst, realize_toStandard]

end Formula
end PolishSpaceBook.NamedFirstOrder
