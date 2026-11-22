module

public import PolishSpaceBook.LambdaNumericalFunctions
public import PolishSpaceBook.LambdaHeadNormalization
public import Mathlib.Data.Part

@[expose] public section

/-! # Finite-arity partial numerical functions in the book's lambda calculus -/

noncomputable section
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Apply the actual numeral arguments from left to right, retaining every parameter. -/
def applyNumerals : {k : ℕ} → AlphaTerm → (Fin k → ℕ) → AlphaTerm
  | 0, P, _ => P
  | k + 1, P, v => applyNumerals (k := k) (app P (numeral (v 0))) (fun i => v i.succ)

/-- Undefined means that there is no finite reduction to any numeral. -/
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
def numericalValue (P : AlphaTerm) : Part ℕ where
  Dom := ∃ m, Relation.ReflTransGen Beta P (numeral m)
  get h := h.choose

theorem mem_numericalValue_iff (P : AlphaTerm) (m : ℕ) :
    m ∈ numericalValue P ↔ Relation.ReflTransGen Beta P (numeral m) := by
  change (∃ h : ∃ m, Relation.ReflTransGen Beta P (numeral m), h.choose = m) ↔ _
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · intro h
    exact ⟨⟨m, h⟩, numeral_output_unique (Exists.choose_spec
      (⟨m, h⟩ : ∃ m, Relation.ReflTransGen Beta P (numeral m))) h⟩

/-- Exact partial values, including exclusion of numeral outputs off the domain. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A partial function
    $$
    \PartialFunctionMap{\varphi}{\seqPower{\omega}{k}}{\omega}
    $$
    is \termdefine{lambda-computable} if there is a closed lambda term $P$ such that, on numerals for $\vec n$, the term
    $P\vec n$ reduces to the numeral for $m$ exactly when $\varphi(\vec n)=m$, and otherwise has no normal-form numeral
    output. A total function is computable if it is lambda-computable and defined on every input. A set $A\IncludedIn\omega$
    is \termdefine{decidable} if its characteristic function is computable, and \termdefine{recursively enumerable} if some
    computable partial function halts exactly on the members of $A$.
-/
def ComputesPartial {k : ℕ} (P : AlphaTerm) (f : (Fin k → ℕ) → Part ℕ) : Prop :=
  P.Closed ∧ ∀ v m, Relation.ReflTransGen Beta (applyNumerals P v) (numeral m) ↔ m ∈ f v

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A partial function
    $$
    \PartialFunctionMap{\varphi}{\seqPower{\omega}{k}}{\omega}
    $$
    is \termdefine{lambda-computable} if there is a closed lambda term $P$ such that, on numerals for $\vec n$, the term
    $P\vec n$ reduces to the numeral for $m$ exactly when $\varphi(\vec n)=m$, and otherwise has no normal-form numeral
    output. A total function is computable if it is lambda-computable and defined on every input. A set $A\IncludedIn\omega$
    is \termdefine{decidable} if its characteristic function is computable, and \termdefine{recursively enumerable} if some
    computable partial function halts exactly on the members of $A$.
-/
def LambdaComputable {k : ℕ} (f : (Fin k → ℕ) → Part ℕ) : Prop :=
  ∃ P, ComputesPartial P f

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A partial function
    $$
    \PartialFunctionMap{\varphi}{\seqPower{\omega}{k}}{\omega}
    $$
    is \termdefine{lambda-computable} if there is a closed lambda term $P$ such that, on numerals for $\vec n$, the term
    $P\vec n$ reduces to the numeral for $m$ exactly when $\varphi(\vec n)=m$, and otherwise has no normal-form numeral
    output. A total function is computable if it is lambda-computable and defined on every input. A set $A\IncludedIn\omega$
    is \termdefine{decidable} if its characteristic function is computable, and \termdefine{recursively enumerable} if some
    computable partial function halts exactly on the members of $A$.
-/
def LambdaComputableTotal {k : ℕ} (f : (Fin k → ℕ) → ℕ) : Prop :=
  LambdaComputable (fun v => Part.some (f v))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A partial function
    $$
    \PartialFunctionMap{\varphi}{\seqPower{\omega}{k}}{\omega}
    $$
    is \termdefine{lambda-computable} if there is a closed lambda term $P$ such that, on numerals for $\vec n$, the term
    $P\vec n$ reduces to the numeral for $m$ exactly when $\varphi(\vec n)=m$, and otherwise has no normal-form numeral
    output. A total function is computable if it is lambda-computable and defined on every input. A set $A\IncludedIn\omega$
    is \termdefine{decidable} if its characteristic function is computable, and \termdefine{recursively enumerable} if some
    computable partial function halts exactly on the members of $A$.
-/
def LambdaDecidable (A : Set ℕ) : Prop := by
  classical
  exact ∃ P, NumericalComputes P (fun n => if n ∈ A then 1 else 0)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A partial function
    $$
    \PartialFunctionMap{\varphi}{\seqPower{\omega}{k}}{\omega}
    $$
    is \termdefine{lambda-computable} if there is a closed lambda term $P$ such that, on numerals for $\vec n$, the term
    $P\vec n$ reduces to the numeral for $m$ exactly when $\varphi(\vec n)=m$, and otherwise has no normal-form numeral
    output. A total function is computable if it is lambda-computable and defined on every input. A set $A\IncludedIn\omega$
    is \termdefine{decidable} if its characteristic function is computable, and \termdefine{recursively enumerable} if some
    computable partial function halts exactly on the members of $A$.
-/
def LambdaEnumerable (A : Set ℕ) : Prop :=
  ∃ f : (Fin 1 → ℕ) → Part ℕ, LambdaComputable f ∧ ∀ n, (f ![n]).Dom ↔ n ∈ A

theorem computesPartial_numericalValue {k : ℕ} {P : AlphaTerm} (hP : P.Closed) :
    ComputesPartial P (fun v : Fin k → ℕ => numericalValue (applyNumerals P v)) :=
  ⟨hP, fun _v m => (mem_numericalValue_iff _ m).symm⟩

/-- The existing total unary API is the special case of the exact partial API. -/
theorem computesPartial_some_iff (P : AlphaTerm) (f : ℕ → ℕ) :
    ComputesPartial P (fun v : Fin 1 → ℕ => Part.some (f (v 0))) ↔ NumericalComputes P f := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun n => ?_⟩
    exact (h ![n] (f n)).mpr (by simp)
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun v m => ?_⟩
    change Relation.ReflTransGen Beta (app P (numeral (v 0))) (numeral m) ↔ _
    constructor
    · intro hm
      have he := numeral_output_unique hm (h (v 0))
      simpa only [Part.mem_some_iff] using he
    · intro hm
      have he : m = f (v 0) := by simpa only [Part.mem_some_iff] using hm
      exact he.symm ▸ h (v 0)

/-- Halting semidecision and domains of computable partial functions agree. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A partial function
    $$
    \PartialFunctionMap{\varphi}{\seqPower{\omega}{k}}{\omega}
    $$
    is \termdefine{lambda-computable} if there is a closed lambda term $P$ such that, on numerals for $\vec n$, the term
    $P\vec n$ reduces to the numeral for $m$ exactly when $\varphi(\vec n)=m$, and otherwise has no normal-form numeral
    output. A total function is computable if it is lambda-computable and defined on every input. A set $A\IncludedIn\omega$
    is \termdefine{decidable} if its characteristic function is computable, and \termdefine{recursively enumerable} if some
    computable partial function halts exactly on the members of $A$.
-/
theorem lambdaEnumerable_iff (A : Set ℕ) :
    LambdaEnumerable A ↔ ∃ P : AlphaTerm, P.Closed ∧ ∀ n,
      (∃ m, Relation.ReflTransGen Beta (app P (numeral n)) (numeral m)) ↔ n ∈ A := by
  constructor
  · rintro ⟨f, ⟨P, hc, hp⟩, hd⟩
    refine ⟨P, hc, fun n => ?_⟩
    rw [← hd n]
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨h, _⟩ := (hp ![n] m).mp hm
      exact h
    · intro h
      exact ⟨(f ![n]).get h, (hp ![n] _).mpr ⟨h, rfl⟩⟩
  · rintro ⟨P, hc, hd⟩
    exact ⟨fun v => numericalValue (applyNumerals P v),
      ⟨P, computesPartial_numericalValue hc⟩, hd⟩

/-- A total numerical input transformation preserves the exact semidecision domain. -/
theorem LambdaEnumerable.preimage {A : Set ℕ} (hA : LambdaEnumerable A)
    {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) : LambdaEnumerable (f ⁻¹' A) := by
  obtain ⟨P, hc, hp⟩ := (lambdaEnumerable_iff A).mp hA
  apply (lambdaEnumerable_iff _).mpr
  refine ⟨numericalCompose P F, ?_, fun n => ?_⟩
  · unfold numericalCompose Closed
    simp only [fv_lam, fv_app, fv_var]
    rw [hc, hf.1]
    simp
  · have hb : Beta (app (numericalCompose P F) (numeral n))
        (app P (app F (numeral n))) := by
      simpa only [numericalCompose, subst_app, subst_var, ite_true,
        subst_closed _ _ _ hc, subst_closed _ _ _ hf.1] using
        Beta.contract 40 (app P (app F (var 40))) (numeral n)
    have hs := (Relation.ReflTransGen.single hb).trans (beta_steps_app_right P (hf.2 n))
    change (∃ m, Relation.ReflTransGen Beta (app (numericalCompose P F) (numeral n)) (numeral m)) ↔ f n ∈ A
    rw [← hp (f n)]
    exact exists_congr (fun m => ⟨fun h => numeral_after_reduction hs h, fun h => hs.trans h⟩)

end PolishSpaceBook.NamedLambda.AlphaTerm
