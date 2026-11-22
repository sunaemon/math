module

public import PolishSpaceBook.LambdaRelativePredicates

@[expose] public section

/-! # Relative decisions on a specified injection into the natural numbers -/
namespace PolishSpaceBook.LambdaRelative
open NamedLambda NamedLambda.AlphaTerm
universe u

/-- Only the codes in the given image have prescribed behavior. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix $\varepsilon:\NN\to\NN$ and an injective numerical coding $c:S\to\NN$. A closed term $P$ decides a predicate
    $R$ on $S$ relative to $\varepsilon$ when, for every $s\in S$, it returns one on code $c(s)$ if $R(s)$ holds and
    zero otherwise, using the beta/query rule with input $\varepsilon$. Both alternatives must terminate. This definition
    requires no decision procedure for the range of $c$ and says nothing about other numerical inputs.
-/
def DecidesOnCode {S : Type u} (c : S → ℕ) (ε : ℕ → ℕ)
    (P : AlphaTerm) (R : S → Prop) : Prop :=
  P.Closed ∧ ∀ s, (R s → OracleRuns ε P (c s) 1) ∧
    (¬ R s → OracleRuns ε P (c s) 0)

/-- An injective coding fits the existing relative-predicate interface exactly.
The classical partial inverse supplies mathematical encoding data only; it is
never run by a lambda program or claimed to decide the range of the coding. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix $\varepsilon:\NN\to\NN$ and an injective numerical coding $c:S\to\NN$. A closed term $P$ decides a predicate
    $R$ on $S$ relative to $\varepsilon$ when, for every $s\in S$, it returns one on code $c(s)$ if $R(s)$ holds and
    zero otherwise, using the beta/query rule with input $\varepsilon$. Both alternatives must terminate. This definition
    requires no decision procedure for the range of $c$ and says nothing about other numerical inputs.
-/
theorem decidesOnCode_iff {S : Type u} (c : S → ℕ) (hc : Function.Injective c)
    (ε : ℕ → ℕ) (P : AlphaTerm) (R : S → Prop) :
    DecidesOnCode c ε P R ↔ @Decides S (Encodable.ofInj c hc) ε P R := Iff.rfl

end PolishSpaceBook.LambdaRelative
