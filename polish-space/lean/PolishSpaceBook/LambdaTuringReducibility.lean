module

public import PolishSpaceBook.LambdaBasicRealizers

@[expose] public section

/-! # Turing reducibility using the book's beta/query programs -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm

/-- One closed program computes every digit, with the same fixed input name. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A real $b\in\BaireSpace$ is \termdefineas{Turing reducibility}{Turing reducible} to $a$, written $b\leq_T a$, if some
    lambda program relative to $a$ computes the function $n\mapsto b(n)$. Two reals $a,b$ are
    \termdefine{Turing equivalent}, written $a\equiv_T b$, if $a\leq_T b$ and $b\leq_T a$.
-/
def TuringReducible (b a : ℕ → ℕ) : Prop :=
  ∃ P : AlphaTerm, P.Closed ∧ ∀ n, OracleRuns a P n (b n)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A real $b\in\BaireSpace$ is \termdefineas{Turing reducibility}{Turing reducible} to $a$, written $b\leq_T a$, if some
    lambda program relative to $a$ computes the function $n\mapsto b(n)$. Two reals $a,b$ are
    \termdefine{Turing equivalent}, written $a\equiv_T b$, if $a\leq_T b$ and $b\leq_T a$.
-/
def TuringEquivalent (a b : ℕ → ℕ) : Prop :=
  TuringReducible a b ∧ TuringReducible b a

theorem TuringReducible.refl (a : ℕ → ℕ) : TuringReducible a a :=
  ⟨identityProgram, identityProgram_closed, identityProgram_runs a⟩

/-- The intermediate name is supplied by actual lambda substitution. -/
theorem TuringReducible.trans {a b c : ℕ → ℕ}
    (hcb : TuringReducible c b) (hba : TuringReducible b a) : TuringReducible c a := by
  obtain ⟨P, hP, hp⟩ := hcb
  obtain ⟨Q, hQ, hq⟩ := hba
  exact ⟨compositionProgram P Q, compositionProgram_closed hP hQ,
    fun n => compositionProgram_runs hP hQ (hp n) hq⟩

end PolishSpaceBook
