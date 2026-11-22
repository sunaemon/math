module

public import PolishSpaceBook.LambdaParallelReduction

@[expose] public section

/-!
# Church numerals in the book's lambda calculus

Numerals are closed alpha-classes of finite named terms. Their normality and
injectivity are proved by named-term structure and binder-renaming invariants,
independently of machine codes.
-/
namespace PolishSpaceBook.NamedLambda
namespace AlphaTerm

/-- Count nodes of a named representative; binder renaming preserves this count. -/
def namedNodes : AlphaTerm → ℕ := Quotient.lift Term.nodes
  (fun M N h => ((Term.alpha_iff_renameEq M N).mp h).nodes_eq)

@[simp] theorem namedNodes_var (x : ℕ) : (var x).namedNodes = 1 := rfl
@[simp] theorem namedNodes_app (M N : AlphaTerm) :
    (app M N).namedNodes = M.namedNodes + N.namedNodes + 1 := by
  refine Quotient.inductionOn₂ M N ?_; intro M N; rfl
@[simp] theorem namedNodes_lam (x : ℕ) (M : AlphaTerm) :
    (lam x M).namedNodes = M.namedNodes + 1 := by
  refine Quotient.inductionOn M ?_; intro M; rfl

/-- Redex-freeness of a named representative, invariant under binder renaming. -/
def NamedRedexFree : AlphaTerm → Prop := Quotient.lift Term.RedexFree
  (fun M N h => propext (((Term.alpha_iff_renameEq M N).mp h).redexFree_iff))

@[simp] theorem namedRedexFree_var (x : ℕ) : NamedRedexFree (var x) := True.intro
@[simp] theorem namedRedexFree_app (M N : AlphaTerm) :
    NamedRedexFree (app M N) ↔ NamedRedexFree M ∧ NamedRedexFree N ∧ M.namedConstructor ≠ 2 := by
  refine Quotient.inductionOn₂ M N ?_; intro M N; rfl
@[simp] theorem namedRedexFree_lam (x : ℕ) (M : AlphaTerm) :
    NamedRedexFree (lam x M) ↔ NamedRedexFree M := by
  refine Quotient.inductionOn M ?_; intro M; rfl

theorem normal_of_namedRedexFree {M : AlphaTerm} (h : NamedRedexFree M) : Normal M := by
  intro N hs
  obtain ⟨A, B, rfl, rfl, hab⟩ := hs.exists_raw
  exact hab.not_redexFree h

def iterateBody : ℕ → AlphaTerm
  | 0 => var 2
  | n + 1 => app (var 1) (iterateBody n)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Use the following \termdefineas{Church numeral}{Church numerals} for natural-number data. Choose distinct variables $f,x$ and define
    $$
    \ChurchNumeral{n}:=\lambdaab{f}{\lambdaab{x}{\LambdaIterationExpansion{f}{x}{n}}}.
    $$
    The brace indicates $n$ nested applications of $f$ to $x$. For $n=0$, the body is just $x$. Write $B_n$ for this body.
    For example,
    $$\begin{aligned}
    \ChurchNumeral{0}&=\lambdaab{f}{\lambdaab{x}{x}},\\
    \ChurchNumeral{1}&=\lambdaab{f}{\lambdaab{x}{f\,x}},\\
    \ChurchNumeral{2}&=\lambdaab{f}{\lambdaab{x}{f(f\,x)}}.
    \end{aligned}$$
-/
def numeral (n : ℕ) : AlphaTerm := lam 1 (lam 2 (iterateBody n))

theorem iterateBody_fv (n : ℕ) : (iterateBody n).fv ⊆ {1, 2} := by
  induction n with
  | zero => change ({2} : Finset ℕ) ⊆ {1, 2}; simp
  | succ n ih =>
    rw [iterateBody, fv_app]
    exact Finset.union_subset (by change ({1} : Finset ℕ) ⊆ {1, 2}; simp) ih

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Church numerals as numerical outputs
-/
@[simp] theorem numeral_closed (n : ℕ) : (numeral n).Closed := by
  unfold Closed numeral
  rw [fv_lam, fv_lam]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx1, hx2, hx⟩ := Finset.mem_erase.mp hx |>.imp_right Finset.mem_erase.mp
  have hh := iterateBody_fv n hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  exact hh.elim hx1 hx2

@[simp] theorem iterateBody_size (n : ℕ) : (iterateBody n).namedNodes = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateBody, namedNodes_app, ih]; omega

@[simp] theorem numeral_size (n : ℕ) : (numeral n).namedNodes = 2 * n + 3 := by
  simp [numeral, namedNodes_lam]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Count variable occurrences, applications and abstractions in the named term. The body has $2n+1$ nodes and the numeral has $2n+3$. Binder renaming preserves this count by \termuse{Invariants of binder renaming}, so the count is well-defined on alpha-classes. Equal numerals have equal counts and therefore equal indices. Finally apply uniqueness of normal forms to two reductions of one term to numerals, and then apply this injectivity.
-/
theorem numeral_injective : Function.Injective numeral := by
  intro n m h
  have hh := congrArg (fun M : AlphaTerm => M.namedNodes) h
  simp only [numeral_size] at hh
  omega

theorem iterateBody_redexFree (n : ℕ) : NamedRedexFree (iterateBody n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [iterateBody, namedRedexFree_app, namedRedexFree_var, namedConstructor_var]
    exact ⟨trivial, ih, by decide⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Church numerals as numerical outputs
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Induction shows that the free variables of $B_n$ lie in $\{f,x\}$, so the two abstractions bind all of them. In the displayed named numeral, every application has a variable as its operator, so there is no beta-redex. Binder renaming preserves the absence of redexes by \termuse{Invariants of binder renaming}. Thus no representative of this alpha-class admits a beta step, and the numeral is a normal form.
-/
theorem numeral_normal (n : ℕ) : Normal (numeral n) := by
  apply normal_of_namedRedexFree
  simpa only [numeral, namedRedexFree_lam]
    using iterateBody_redexFree n

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Church numerals as numerical outputs
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A computation is a finite or infinite sequence of beta-reductions. A term \termdefine{halts with value} $V$ when it
    reduces in finitely many steps to a numeral or data value $V$ in the chosen encoding.
    For natural-number outputs we use distinct normal-form numerals. By
    \termuseas{Uniqueness of lambda normal forms}{uniqueness of normal forms}, a term cannot reduce to two distinct such
    numerals.
-/
theorem numeral_output_unique {M : AlphaTerm} {n m : ℕ}
    (hn : Relation.ReflTransGen Beta M (numeral n))
    (hm : Relation.ReflTransGen Beta M (numeral m)) : n = m :=
  numeral_injective (normal_form_unique hn hm (numeral_normal n) (numeral_normal m))
end AlphaTerm
end PolishSpaceBook.NamedLambda
