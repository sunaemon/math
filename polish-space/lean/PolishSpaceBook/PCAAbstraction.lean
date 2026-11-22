module

public import PolishSpaceBook.LambdaIndexPCA

@[expose] public section

/-!
# Abstraction in a partial combinatory algebra

Terms are algebraic expressions in the existing PCA, not a new computation
model. Option.none names the variable being abstracted; Option.some retains
all parameters. Evaluation is strict and every theorem equates partial values.
-/

namespace PolishSpaceBook
namespace PartialCombinatoryAlgebra
universe u v
variable {A : Type u}

inductive Expression (A : Type u) (α : Type v)
  | var : α → Expression A α
  | const : A → Expression A α
  | app : Expression A α → Expression A α → Expression A α

namespace Expression
variable (K : PartialCombinatoryAlgebra A)

def eval {α : Type v} : Expression A α → (α → A) → Part A
  | .var x, ρ => Part.some (ρ x)
  | .const a, _ => Part.some a
  | .app t r, ρ => (eval t ρ).bind (fun a => (eval r ρ).bind (K.application a))

/-- The constant case is separate: no compound expression is evaluated prematurely. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    First construct a term abstracting one variable by structural recursion:
    $$\begin{aligned}
    \PCAAbstract{\xi}{\xi}&:=\mathsf s\mathsf k\mathsf k,\\
    \PCAAbstract{\xi}{\eta}&:=\mathsf k \eta&&(\eta\ne \xi),\\
    \PCAAbstract{\xi}{\gamma}&:=\mathsf k \gamma&&(\gamma\in A),\\
    \PCAAbstract{\xi}{(uv)}&:=\mathsf s\,(\PCAAbstract{\xi}{u})\,(\PCAAbstract{\xi}{v}).
    \end{aligned}$$
    The constant clause applies to an element of the algebra, not to an unevaluated compound expression.
    Keep two assertions in the induction: the abstracted term has a value for every assignment of the remaining
    parameters, and applying that value gives exactly the original partial value after substitution.
-/
def abstract {α : Type v} : Expression A (Option α) → Expression A α
  | .var none => .app (.app (.const K.s) (.const K.k)) (.const K.k)
  | .var (some x) => .app (.const K.k) (.var x)
  | .const a => .app (.const K.k) (.const a)
  | .app t r => .app (.app (.const K.s) (abstract t)) (abstract r)

/-- An abstracted expression has a value for every assignment of the remaining parameters. -/
theorem abstract_defined {α : Type v} (t : Expression A (Option α)) (ρ : α → A) :
    ((t.abstract K).eval K ρ).Dom := by
  induction t with
  | var x =>
    cases x with
    | none => simpa only [abstract,eval,Part.bind_some] using K.s_defined K.k K.k
    | some x => simpa only [abstract,eval,Part.bind_some] using K.k_defined (ρ x)
  | const a => simpa only [abstract,eval,Part.bind_some] using K.k_defined a
  | app t r iht ihr =>
    have ht := Part.some_get iht
    have hr := Part.some_get ihr
    simp only [abstract,eval,Part.bind_some]
    rw [← ht,← hr]
    simpa only [Part.bind_some] using K.s_defined _ _

/-- Abstracting and then applying gives exactly the original partial value. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    In the variable case, the $\mathsf s$ axiom ensures that $\mathsf s\mathsf k\mathsf k$ is defined, and
    $$\mathsf s\mathsf k\mathsf k\,\alpha\simeq(\mathsf k \alpha)(\mathsf k \alpha)\simeq \alpha.$$
    The last equality uses both the definedness of the constant-function application and its defining law.
    For another variable or an algebra constant, the constant-function axioms give both assertions directly.

    For an application, let $\pi,\rho$ be the values of the two abstracted subterms. They exist by induction.
    The element $\mathsf s \pi\rho$ is defined, and
    $$\mathsf s \pi\rho\,\alpha\simeq(\pi\alpha)(\rho\alpha)
    \simeq (u\subst{\xi}{\alpha})(v\subst{\xi}{\alpha}).$$
    Every application here is strict: if an argument computation or the final application is undefined, both sides
    are undefined. Thus the induction proves equality of partial values, including their domains.
-/
theorem abstract_apply {α : Type v} (t : Expression A (Option α)) (ρ : α → A) (a : A) :
    ((t.abstract K).eval K ρ).bind (fun f => K.application f a) =
      t.eval K (fun x => x.elim a ρ) := by
  induction t with
  | var x =>
    cases x with
    | none =>
      simp only [abstract,eval,Part.bind_some]
      rw [K.s_law]
      obtain ⟨q,hq⟩ : ∃ q, K.application K.k a = Part.some q :=
        ⟨_,(Part.some_get (K.k_defined a)).symm⟩
      rw [hq]
      simp only [Part.bind_some,Option.elim_none]
      simpa only [hq,Part.bind_some] using K.k_law a q
    | some x => simpa only [abstract,eval,Part.bind_some,Option.elim_some] using K.k_law (ρ x) a
  | const c => simpa only [abstract,eval,Part.bind_some] using K.k_law c a
  | app t r iht ihr =>
    have ht := Part.some_get (abstract_defined K t ρ)
    have hr := Part.some_get (abstract_defined K r ρ)
    simp only [abstract,eval,Part.bind_some]
    rw [← ht,← hr]
    simp only [Part.bind_some]
    rw [K.s_law]
    rw [← ht,Part.bind_some] at iht
    rw [← hr,Part.bind_some] at ihr
    rw [iht,ihr]

/-- Nested scopes retain parameters and add one variable at each abstraction step. -/
abbrev Scope (α : Type v) : ℕ → Type v
  | 0 => α
  | n+1 => Option (Scope α n)

def abstractMany {α : Type v} : (n : ℕ) → Expression A (Scope α n) → Expression A α
  | 0, t => t
  | n+1, t => abstractMany n (t.abstract K)

def parameters {α : Type v} : (n : ℕ) → (Scope α n → A) → (α → A)
  | 0, ρ => ρ
  | n+1, ρ => parameters n (fun x => ρ (some x))

def applyMany {α : Type v} : (n : ℕ) → Part A → (Scope α n → A) → Part A
  | 0, f, _ => f
  | n+1, f, ρ => (applyMany n f (fun x => ρ (some x))).bind (fun g => K.application g (ρ none))

/-- The final application may diverge; every nonempty abstraction itself is defined. -/
theorem abstractMany_defined {α : Type v} (n : ℕ) (t : Expression A (Scope α (n+1))) (ρ : α → A) :
    ((t.abstractMany K (n+1)).eval K ρ).Dom := by
  induction n with
  | zero => exact abstract_defined K t ρ
  | succ n ih => exact ih (t.abstract K)

/-- Successive applications preserve exact domains, including for nested undefined subterms. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For several variables, abstract the last displayed variable first and repeat toward the first.
    Successive uses of the one-variable identity give the displayed equality. After any proper prefix of arguments,
    the remaining expression is still an abstraction and hence has a value by the first assertion of the induction.
    In particular, all arguments except the last can be supplied without losing definedness. The construction
    retains every undisplayed parameter and does not use the argument values when choosing the abstracted element.
-/
theorem abstractMany_apply {α : Type v} (n : ℕ) (t : Expression A (Scope α n))
    (ρ : Scope α n → A) :
    applyMany K n ((t.abstractMany K n).eval K (parameters n ρ)) ρ = t.eval K ρ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [abstractMany,parameters,applyMany]
    rw [ih,abstract_apply]
    have he : (fun x => x.elim (ρ none) (fun x => ρ (some x))) = ρ := by
      funext x
      cases x <;> rfl
    rw [he]

/-- All proper arguments can be supplied before the final potentially undefined application. -/
theorem abstractMany_prefix_defined {α : Type v} (n : ℕ) (t : Expression A (Scope α (n+1)))
    (ρ : Scope α n → A) :
    (applyMany K n ((t.abstractMany K (n+1)).eval K (parameters n ρ)) ρ).Dom := by
  change (applyMany K n (((t.abstract K).abstractMany K n).eval K (parameters n ρ)) ρ).Dom
  rw [abstractMany_apply]
  exact abstract_defined K t ρ

/-- One element works for every tuple of arguments with the fixed remaining parameters. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Abstraction theorem
-/
theorem exists_abstraction {α : Type v} (n : ℕ) (t : Expression A (Scope α (n+1)))
    (ρ₀ : α → A) :
    ∃ f : A, ∀ ρ : Scope α (n+1) → A, parameters (n+1) ρ = ρ₀ →
      applyMany K (n+1) (Part.some f) ρ = t.eval K ρ := by
  refine ⟨((t.abstractMany K (n+1)).eval K ρ₀).get (abstractMany_defined K n t ρ₀),?_⟩
  intro ρ hρ
  rw [Part.some_get,← hρ]
  exact abstractMany_apply K (n+1) t ρ

end Expression
end PartialCombinatoryAlgebra
end PolishSpaceBook
