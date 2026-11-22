module

public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Relation
public import Mathlib.Tactic

@[expose] public section

/-!
# Named lambda terms and the book's capture-avoiding substitution

Variables are natural numbers in their usual effective order. The fresh variable
is the least outside exactly the finite set specified in the text. A bounded
recursive implementation is proved independent of every sufficient bound.
This module treats raw named syntax. `LambdaAlphaEquivalence` constructs
alpha-classes and their compatible substitution and reduction operations.
The later lambda modules prove confluence, Church numeral properties, and the
input-query semantics directly; no cross-model simulation is assumed.
-/
namespace PolishSpaceBook
namespace NamedLambda

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix countably infinitely many variables $x,y,z,\ldots$ in an effective order. We use $M,N,P,\ldots$ as
    metavariables ranging over lambda terms. The
    \termdefineas{lambda term}{lambda terms} are defined recursively:

    *   Every variable $x$ is a lambda term.
    *   If $M$ and $N$ are lambda terms, then $(MN)$ is a lambda term, called
        \termdefineas{lambda application}{application}.
    *   If $x$ is a variable and $M$ is a lambda term, then $(\lambdaab{x}{M})$ is a lambda term, called
        \termdefineas{lambda abstraction}{abstraction}.
    *   Nothing else is a lambda term.

    Equivalently, in EBNF summary form,
    $$
    \textit{Term} ::= \textit{Var} \mid (\textit{Term}\ \textit{Term}) \mid (\lambdaab{\textit{Var}}{\textit{Term}}).
    $$
-/
inductive Term where
  | var : ℕ → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term
  deriving DecidableEq, Repr

namespace Term

def nodes : Term → ℕ
  | .var _ => 1
  | .app M N => nodes M + nodes N + 1
  | .lam _ M => nodes M + 1

theorem nodes_pos (M : Term) : 0 < M.nodes := by cases M <;> simp [nodes]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Free variables are defined recursively by
    $$\begin{aligned}
    \FreeVars{x} &= \{x\},\\
    \FreeVars{MN} &= \FreeVars{M}\cup\FreeVars{N},\\
    \FreeVars{\lambdaab{x}{M}} &= \SetDifference{\FreeVars{M}}{\{x\}}.
    \end{aligned}$$
-/
def fv : Term → Finset ℕ
  | .var x => {x}
  | .app M N => fv M ∪ fv N
  | .lam x M => (fv M).erase x

theorem exists_fresh (s : Finset ℕ) : ∃ n, n ∉ s := by
  refine ⟨s.sup id + 1, ?_⟩
  intro h
  have := Finset.le_sup (f := id) h
  simp only [id_eq] at this
  omega

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first define capture-avoiding substitution on named terms. For a term $N$ substituted for a variable $x$, the clauses
    for $M\subst{x}{N}$ are:
    $$\begin{aligned}
    y\subst{x}{N}
    &:=
    \begin{cases}
    N & \text{if } y=x,\\
    y & \text{if } y\ne x,
    \end{cases}\\
    (MP)\subst{x}{N}
    &:= (M\subst{x}{N})(P\subst{x}{N}),\\
    (\lambdaab{y}{M})\subst{x}{N}
    &:=
    \begin{cases}
    \lambdaab{y}{M}
        & \text{if } y=x,\\
    \lambdaab{y}{(M\subst{x}{N})}
        & \text{if } y\ne x \text{ and } y\notin\FreeVars{N},\\
    \lambdaab{z}{\bigl(M\subst{y}{z}\subst{x}{N}\bigr)}
        & \text{if } y\ne x \text{ and } y\in\FreeVars{N},
    \end{cases}
    \end{aligned}$$
    where in the last case $z$ is the first variable not in $\FreeVars{M}\cup\FreeVars{N}\cup\{x\}$. The last clause is the
    hygiene step: before $N$ is moved under a binder whose variable occurs free in $N$, that binder is renamed to the fresh
    variable $z$.
-/
def fresh (s : Finset ℕ) : ℕ := Nat.find (exists_fresh s)

theorem fresh_not_mem (s : Finset ℕ) : fresh s ∉ s := Nat.find_spec (exists_fresh s)

theorem lt_fresh_mem (s : Finset ℕ) {n : ℕ} (h : n < fresh s) : n ∈ s := by
  by_contra hn
  exact Nat.find_min (exists_fresh s) h hn

/-- Both recursive calls in the renaming branch consume one unit of depth. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    First evaluate the clauses with a finite depth budget. At budget zero, temporarily return the input term; at a positive budget, use the displayed clause and decrease the budget by one for each recursive call. In the renaming branch, both the inner renaming call and the subsequent substitution call receive this smaller budget. This bounded procedure is defined by ordinary recursion on the budget.
-/
def substFuel : ℕ → Term → ℕ → Term → Term
  | 0, M, _, _ => M
  | _ + 1, .var y, x, N => if y = x then N else .var y
  | k + 1, .app M P, x, N => .app (substFuel k M x N) (substFuel k P x N)
  | k + 1, .lam y M, x, N =>
    if y = x then .lam y M
    else if y ∉ N.fv then .lam y (substFuel k M x N)
    else
      let z := fresh (M.fv ∪ N.fv ∪ {x})
      .lam z (substFuel k (substFuel k M y (.var z)) x N)

/-- Renaming free occurrences cannot change the number of syntax-tree nodes. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Termination of capture-avoiding substitution
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For a variable replacement, induction on the budget shows that the output has the same number of nodes as the input: variables remain variables, applications retain their two branches, and abstractions retain one binder node. In the renaming branch this assertion applies to both recursive calls. It holds even at budget zero.
-/
theorem nodes_substFuel_var (k : ℕ) (M : Term) (x z : ℕ) :
    (substFuel k M x (.var z)).nodes = M.nodes := by
  induction k generalizing M x z with
  | zero => rfl
  | succ k ih =>
    cases M with
    | var y => simp [substFuel]; split_ifs <;> rfl
    | app M P => simp only [substFuel, nodes, ih]
    | lam y M =>
      simp only [substFuel]
      split_ifs <;> simp only [nodes, ih]

/-- Every bound at least the original node count yields the same substitution. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Termination of capture-avoiding substitution
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Now compare two budgets that are each at least the number of nodes of the input term. Induct on the smaller budget. The variable case is immediate, and each proper subterm of an application or abstraction has fewer nodes. In the renaming branch, first apply the induction hypothesis to the body with a variable replacement. The resulting bodies agree and have exactly the original body's node count. Apply the induction hypothesis again to this renamed body with the intended replacement. Both calls have sufficient smaller budgets, so their results agree as well. Thus the bounded procedures stabilize, and choosing the original node count gives a total operation satisfying precisely the displayed clauses. This also explains why recursion merely on literal subterms would not justify the renaming branch.
-/
theorem substFuel_stable (k : ℕ) (M : Term) (x : ℕ) (N : Term) (l : ℕ)
    (hk : M.nodes ≤ k) (hl : M.nodes ≤ l) : substFuel k M x N = substFuel l M x N := by
  induction k generalizing M x N l with
  | zero => have := nodes_pos M; omega
  | succ k ih =>
    cases l with
    | zero => have := nodes_pos M; omega
    | succ l =>
      cases M with
      | var y => rfl
      | app M P =>
        have hMk : M.nodes ≤ k := by simp only [nodes] at hk; omega
        have hMl : M.nodes ≤ l := by simp only [nodes] at hl; omega
        have hPk : P.nodes ≤ k := by simp only [nodes] at hk; omega
        have hPl : P.nodes ≤ l := by simp only [nodes] at hl; omega
        simp only [substFuel, ih M x N l hMk hMl, ih P x N l hPk hPl]
      | lam y M =>
        have hMk : M.nodes ≤ k := by simpa only [nodes, Nat.add_le_add_iff_right] using hk
        have hMl : M.nodes ≤ l := by simpa only [nodes, Nat.add_le_add_iff_right] using hl
        simp only [substFuel]
        by_cases hy : y = x
        · simp only [ite_eq_left hy]
        · simp only [ite_eq_right hy]
          by_cases hfree : y ∉ N.fv
          · simp only [ite_eq_left hfree]
            rw [ih M x N l hMk hMl]
          · simp only [ite_eq_right hfree]
            let z := fresh (M.fv ∪ N.fv ∪ {x})
            have hr := ih M y (.var z) l hMk hMl
            have ho := ih (substFuel k M y (.var z)) x N l
              (by simpa only [nodes_substFuel_var] using hMk)
              (by simpa only [nodes_substFuel_var] using hMl)
            rw [ho, hr]

/-- The total substitution operation uses a sufficient bound, with no change to the book's clauses. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first define capture-avoiding substitution on named terms. For a term $N$ substituted for a variable $x$, the clauses
    for $M\subst{x}{N}$ are:
    $$\begin{aligned}
    y\subst{x}{N}
    &:=
    \begin{cases}
    N & \text{if } y=x,\\
    y & \text{if } y\ne x,
    \end{cases}\\
    (MP)\subst{x}{N}
    &:= (M\subst{x}{N})(P\subst{x}{N}),\\
    (\lambdaab{y}{M})\subst{x}{N}
    &:=
    \begin{cases}
    \lambdaab{y}{M}
        & \text{if } y=x,\\
    \lambdaab{y}{(M\subst{x}{N})}
        & \text{if } y\ne x \text{ and } y\notin\FreeVars{N},\\
    \lambdaab{z}{\bigl(M\subst{y}{z}\subst{x}{N}\bigr)}
        & \text{if } y\ne x \text{ and } y\in\FreeVars{N},
    \end{cases}
    \end{aligned}$$
    where in the last case $z$ is the first variable not in $\FreeVars{M}\cup\FreeVars{N}\cup\{x\}$. The last clause is the
    hygiene step: before $N$ is moved under a binder whose variable occurs free in $N$, that binder is renamed to the fresh
    variable $z$.
-/
def subst (M : Term) (x : ℕ) (N : Term) : Term := substFuel M.nodes M x N

theorem substFuel_eq_subst (M : Term) (x : ℕ) (N : Term) (k : ℕ) (hk : M.nodes ≤ k) :
    substFuel k M x N = M.subst x N := substFuel_stable k M x N M.nodes hk le_rfl

@[simp] theorem subst_var (y x : ℕ) (N : Term) :
    (.var y : Term).subst x N = if y = x then N else .var y := rfl

@[simp] theorem subst_app (M P : Term) (x : ℕ) (N : Term) :
    (app M P).subst x N = .app (M.subst x N) (P.subst x N) := by
  simp only [subst, nodes, substFuel]
  rw [substFuel_stable (M.nodes + P.nodes) M x N M.nodes (by omega) le_rfl,
    substFuel_stable (M.nodes + P.nodes) P x N P.nodes (by omega) le_rfl]

@[simp] theorem nodes_subst_var (M : Term) (x z : ℕ) :
    (M.subst x (.var z)).nodes = M.nodes := nodes_substFuel_var _ _ _ _

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first define capture-avoiding substitution on named terms. For a term $N$ substituted for a variable $x$, the clauses
    for $M\subst{x}{N}$ are:
    $$\begin{aligned}
    y\subst{x}{N}
    &:=
    \begin{cases}
    N & \text{if } y=x,\\
    y & \text{if } y\ne x,
    \end{cases}\\
    (MP)\subst{x}{N}
    &:= (M\subst{x}{N})(P\subst{x}{N}),\\
    (\lambdaab{y}{M})\subst{x}{N}
    &:=
    \begin{cases}
    \lambdaab{y}{M}
        & \text{if } y=x,\\
    \lambdaab{y}{(M\subst{x}{N})}
        & \text{if } y\ne x \text{ and } y\notin\FreeVars{N},\\
    \lambdaab{z}{\bigl(M\subst{y}{z}\subst{x}{N}\bigr)}
        & \text{if } y\ne x \text{ and } y\in\FreeVars{N},
    \end{cases}
    \end{aligned}$$
    where in the last case $z$ is the first variable not in $\FreeVars{M}\cup\FreeVars{N}\cup\{x\}$. The last clause is the
    hygiene step: before $N$ is moved under a binder whose variable occurs free in $N$, that binder is renamed to the fresh
    variable $z$.
-/
theorem subst_lam (y : ℕ) (M : Term) (x : ℕ) (N : Term) :
    (lam y M).subst x N =
      if y = x then .lam y M
      else if y ∉ N.fv then .lam y (M.subst x N)
      else let z := fresh (M.fv ∪ N.fv ∪ {x}); .lam z ((M.subst y (.var z)).subst x N) := by
  unfold subst
  simp only [nodes, substFuel, nodes_substFuel_var]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Induct using the node-count bound from the preceding lemma. For a variable, check whether it is the variable being replaced; for an application, take the union of the two free-variable sets. Under an abstraction binding the variable being replaced, substitution stops. Under any other binder whose variable is absent from the replacement's free-variable set, remove that binder variable after applying the induction hypothesis to the body.

    In the remaining branch, let $y$ be the old binder and $z$ the fresh variable. The induction hypothesis applies to the variable substitution in the body, which removes the free occurrences of $y$ and replaces them by occurrences of $z$. The renamed body's node count is unchanged, so the hypothesis also applies to the subsequent substitution. Since $z$ is absent from the free-variable sets of both the original body and the replacement, and differs from $x$, the final abstraction binds only the renamed occurrences. The replacement's free variables remain free. These cases give the stated formula, including the case where the replaced variable was absent.
-/
private theorem mem_fv_subst_bounded (k : ℕ) (M : Term) (x : ℕ) (N : Term) (v : ℕ)
    (hM : M.nodes ≤ k) :
    v ∈ (M.subst x N).fv ↔ (v ∈ M.fv ∧ v ≠ x) ∨ (x ∈ M.fv ∧ v ∈ N.fv) := by
  induction k generalizing M x N v with
  | zero => have := nodes_pos M; omega
  | succ k ih =>
    cases M with
    | var y =>
      by_cases hy : y = x
      · subst y; simp [fv]
      · simp [fv, hy, Ne.symm hy]; aesop
    | app M P =>
      have hm : M.nodes ≤ k := by simp only [nodes] at hM; omega
      have hp : P.nodes ≤ k := by simp only [nodes] at hM; omega
      simp only [subst_app, fv, Finset.mem_union, ih M x N v hm, ih P x N v hp]
      tauto
    | lam y M =>
      have hm : M.nodes ≤ k := by simpa only [nodes, Nat.add_le_add_iff_right] using hM
      rw [subst_lam]
      by_cases hy : y = x
      · simp only [ite_eq_left hy]
        subst y
        simp only [fv, Finset.mem_erase]
        tauto
      · simp only [ite_eq_right hy]
        by_cases hfree : y ∉ N.fv
        · simp only [ite_eq_left hfree, fv, Finset.mem_erase, ih M x N v hm]
          have hv : v ∈ N.fv → v ≠ y := fun hv he => hfree (he ▸ hv)
          have hxy : x ≠ y := Ne.symm hy
          tauto
        · simp only [ite_eq_right hfree]
          let z := fresh (M.fv ∪ N.fv ∪ {x})
          have hz : z ∉ M.fv ∧ z ∉ N.fv ∧ z ≠ x := by
            have hh := fresh_not_mem (M.fv ∪ N.fv ∪ {x})
            simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc] using hh
          have hv := ih M y (.var z) v hm
          have hx := ih M y (.var z) x hm
          simp only [fv, Finset.mem_singleton] at hv hx
          have ho := ih (M.subst y (.var z)) x N v (by simpa only [nodes_subst_var] using hm)
          change v ∈ ((M.subst y (.var z)).subst x N).fv.erase z ↔ _
          simp only [fv, Finset.mem_erase]
          rw [ho, hv, hx]
          have hvM : v ∈ M.fv → v ≠ z := fun hv he => hz.1 (he ▸ hv)
          have hvN : v ∈ N.fv → v ≠ z := fun hv he => hz.2.1 (he ▸ hv)
          have hxy : x ≠ y := Ne.symm hy
          have hxz : x ≠ z := Ne.symm hz.2.2
          clear ih hv hx ho hM hm hfree hz
          tauto

/-- Exact free variables: the replacement contributes precisely when a free occurrence is replaced. -/
theorem mem_fv_subst (M : Term) (x : ℕ) (N : Term) (v : ℕ) :
    v ∈ (M.subst x N).fv ↔ (v ∈ M.fv ∧ v ≠ x) ∨ (x ∈ M.fv ∧ v ∈ N.fv) :=
  mem_fv_subst_bounded M.nodes M x N v le_rfl

theorem fv_subst (M : Term) (x : ℕ) (N : Term) :
    (M.subst x N).fv = M.fv.erase x ∪ if x ∈ M.fv then N.fv else ∅ := by
  ext v
  simp only [mem_fv_subst, Finset.mem_union, Finset.mem_erase]
  split_ifs <;> simp_all <;> tauto

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Free variables under substitution
-/
theorem fv_subst_cases (M : Term) (x : ℕ) (N : Term) :
    (M.subst x N).fv = if x ∈ M.fv then M.fv.erase x ∪ N.fv else M.fv := by
  rw [fv_subst]
  split_ifs with hx
  · rfl
  · simp [hx]

/-- A free replacement variable stays free instead of being captured by the old binder. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For example, if $x\ne y$ and $z$ is the first variable outside $\{x,y\}$, then
    $$
    \SubstLambda{(\lambdaab{y}{x})}{x}{y}=\lambdaab{z}{y}.
    $$
    The occurrence of $y$ introduced by the substitution remains free; returning $\lambdaab{y}{y}$ would capture it.
-/
theorem capture_avoidance_example {x y : ℕ} (hxy : x ≠ y) :
    (lam y (var x)).subst x (var y) = lam (fresh ({x} ∪ {y} ∪ {x})) (var y) := by
  rw [subst_lam]
  simp only [Ne.symm hxy, ite_false, fv, Finset.mem_singleton, not_true_eq_false]
  simp only [subst_var, hxy, ite_false, ite_true]

/-- The book's context closure is a relation on actual named syntax. -/
inductive Beta : Term → Term → Prop where
  | contract (x : ℕ) (M N : Term) : Beta (.app (.lam x M) N) (M.subst x N)
  | app_left {M M' : Term} (N : Term) : Beta M M' → Beta (.app M N) (.app M' N)
  | app_right (M : Term) {N N' : Term} : Beta N N' → Beta (.app M N) (.app M N')
  | lam (x : ℕ) {M M' : Term} : Beta M M' → Beta (.lam x M) (.lam x M')

/-- Reduction introduces no new free variables, even when it renames a binder. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For a contracted redex, the substitution formula places every free variable of the result in the body's free variables other than its binder, or in the argument's free variables. These are precisely the two contributions to the original redex's free-variable set. The application contexts preserve inclusion by taking unions, and an abstraction context preserves it by removing the same binder variable on both sides. Thus one beta step introduces no new free variables. Induction on the length of a finite reduction gives the result, including the zero-step case. A subset of the empty free-variable set is empty, proving the assertion about closed terms.
-/
theorem Beta.fv_subset {M N : Term} (h : Beta M N) : N.fv ⊆ M.fv := by
  induction h with
  | contract x M N =>
    intro v hv
    rcases (mem_fv_subst M x N v).mp hv with h | h
    · simp only [fv, Finset.mem_union, Finset.mem_erase]; exact Or.inl ⟨h.2, h.1⟩
    · simp only [fv, Finset.mem_union]; exact Or.inr h.2
  | app_left N _ ih => exact Finset.union_subset_union_left ih
  | app_right M _ ih => exact Finset.union_subset_union_right ih
  | lam x _ ih => exact Finset.erase_subset_erase x ih

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Free variables under beta-reduction
-/
theorem beta_steps_fv_subset {M N : Term} (h : Relation.ReflTransGen Beta M N) :
    N.fv ⊆ M.fv := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ h ih => exact Finset.Subset.trans h.fv_subset ih

def Closed (M : Term) : Prop := M.fv = ∅

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Free variables under beta-reduction
-/
theorem closed_of_beta_steps {M N : Term} (hM : M.Closed)
    (h : Relation.ReflTransGen Beta M N) : N.Closed := by
  have hs := beta_steps_fv_subset h
  rw [hM] at hs
  exact Finset.subset_empty.mp hs

end Term
end NamedLambda
end PolishSpaceBook
