module

public import PolishSpaceBook.FirstOrderRelationDefinitions

@[expose] public section

/-! # Theory completeness and bounded quantifiers in the logic appendix -/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v w w'
variable {L : Language.{u,v}}

/-- The sentence consequences of a theory. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{theory} in a language $L$ is a set $T$ of $L$-sentences, called its \termdefineas{axiom}{axioms}; the
    notation $T\vdash\varphi$ means that $\Gamma\vdash\varphi$ for some finite $\Gamma\IncludedIn T$. The
    consequences of $T$ are the sentences in its \termdefine{deductive closure} $\{\varphi : T \vdash \varphi\}$. When an
    axiom schema is written using an open formula, each instance is its universal closure: all free variables not explicitly
    bound in the displayed formula are universally quantified outside the displayed expression. In schemas with parameters,
    such as Replacement and Separation, the parameters are precisely those additional free variables before this universal
    closure is applied. \termdefine{ZFC} is the $L_\in$-theory whose axioms are listed in §{sec:zfc-axioms}.
-/
def deductiveClosure (T : Set (AlphaFormula L)) : Set (AlphaFormula L) :=
  {φ | φ ∈ Sentences L ∧ ProvesFrom T φ}

/-- Completeness in the book means deciding every sentence; it does not include consistency. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Completeness of a proof system and completeness of a theory are different assertions. A theory $T$ is
    \termdefineas{complete theory}{complete} if, for every sentence $\varphi$ in its language, either
    $T\vdash\varphi$ or $T\vdash\neg\varphi$. Gödel completeness identifies derivability with truth in every model of
    $T$; it does not say that all models of $T$ agree on every sentence. We now prove that sufficiently strong consistent
    arithmetic theories with effective axioms cannot decide every sentence. All programs below use the lambda calculus of
    §{sec:appendix-lambda-computability}.
-/
def SyntacticallyComplete (T : Set (AlphaFormula L)) : Prop :=
  ∀ φ ∈ Sentences L, ProvesFrom T φ ∨ ProvesFrom T (neg φ)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Completeness of a proof system and completeness of a theory are different assertions. A theory $T$ is
    \termdefineas{complete theory}{complete} if, for every sentence $\varphi$ in its language, either
    $T\vdash\varphi$ or $T\vdash\neg\varphi$. Gödel completeness identifies derivability with truth in every model of
    $T$; it does not say that all models of $T$ agree on every sentence. We now prove that sufficiently strong consistent
    arithmetic theories with effective axioms cannot decide every sentence. All programs below use the lambda calculus of
    §{sec:appendix-lambda-computability}.
-/
theorem not_complete_of_independent {T : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (hφ : φ ∈ Sentences L) (hp : ¬ProvesFrom T φ) (hn : ¬ProvesFrom T (neg φ)) :
    ¬SyntacticallyComplete T :=
  fun h => (h φ hφ).elim hp hn

/-- Models of a complete theory agree on every sentence, without a standard-model assumption. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Completeness of a proof system and completeness of a theory are different assertions. A theory $T$ is
    \termdefineas{complete theory}{complete} if, for every sentence $\varphi$ in its language, either
    $T\vdash\varphi$ or $T\vdash\neg\varphi$. Gödel completeness identifies derivability with truth in every model of
    $T$; it does not say that all models of $T$ agree on every sentence. We now prove that sufficiently strong consistent
    arithmetic theories with effective axioms cannot decide every sentence. All programs below use the lambda calculus of
    §{sec:appendix-lambda-computability}.
-/
theorem SyntacticallyComplete.models_agree {T : Set (AlphaFormula L)}
    (hT : SyntacticallyComplete T) {M : Type w} {N : Type w'}
    (A : L.Structure M) (B : L.Structure N) (hA : TheoryRealize A T) (hB : TheoryRealize B T)
    {φ : AlphaFormula L} (hφ : φ ∈ Sentences L) (s : ℕ → M) (t : ℕ → N) :
    @AlphaFormula.Realize L M A φ s ↔ @AlphaFormula.Realize L N B φ t := by
  let := A
  let := B
  rcases hT φ hφ with hp | hn
  · exact iff_of_true (hp.sound s (hA s)) (hp.sound t (hB t))
  · exact iff_of_false ((realize_neg φ s).mp (hn.sound s (hA s)))
      ((realize_neg φ t).mp (hn.sound t (hB t)))

namespace AlphaFormula

/-- Bounded universal quantification abbreviates membership implication. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    When the language contains a binary relation symbol $\in$, we also use **bounded quantifiers** as abbreviations:
    $$
    (\exists u \in v)\,\varphi
    \quad:\equiv\quad
    \exists u\,(u\in v \land \varphi),
    \qquad
    (\forall u \in v)\,\varphi
    \quad:\equiv\quad
    \forall u\,(u\in v \to \varphi).
    $$
    The variable $u$ is bound in $\varphi$, and $v$ is the bounding term, in which $u$ must not occur freely. Thus
    bounded quantification is not an additional
    logical primitive; it is notation available in set-theoretic languages such as $L_\in$.
-/
def boundedForall (R : L.Relations 2) (x : ℕ) (bound : L.Term ℕ)
    (φ : AlphaFormula L) : AlphaFormula L :=
  quant .all x (binary .imp (rel R ![.var x, bound]) φ)

/-- Bounded existential quantification abbreviates membership conjunction. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    When the language contains a binary relation symbol $\in$, we also use **bounded quantifiers** as abbreviations:
    $$
    (\exists u \in v)\,\varphi
    \quad:\equiv\quad
    \exists u\,(u\in v \land \varphi),
    \qquad
    (\forall u \in v)\,\varphi
    \quad:\equiv\quad
    \forall u\,(u\in v \to \varphi).
    $$
    The variable $u$ is bound in $\varphi$, and $v$ is the bounding term, in which $u$ must not occur freely. Thus
    bounded quantification is not an additional
    logical primitive; it is notation available in set-theoretic languages such as $L_\in$.
-/
def boundedExists (R : L.Relations 2) (x : ℕ) (bound : L.Term ℕ)
    (φ : AlphaFormula L) : AlphaFormula L :=
  quant .ex x (binary .conj (rel R ![.var x, bound]) φ)

private theorem realize_bound_relation {M : Type w} [L.Structure M] (R : L.Relations 2)
    (x : ℕ) (bound : L.Term ℕ) (hx : x ∉ bound.varFinset) (s : ℕ → M) (a : M) :
    (rel R ![.var x, bound]).Realize (Function.update s x a) ↔
      Structure.RelMap R ![a, bound.realize s] := by
  have hb : bound.realize (Function.update s x a) = bound.realize s := by
    apply term_realize_congr
    intro y hy
    have hne : y ≠ x := by
      intro he
      subst y
      exact hx hy
    exact Function.update_of_ne hne _ _
  change Structure.RelMap R (fun i => (![Term.var x, bound] i).realize (Function.update s x a)) ↔ _
  have he : (fun i => (![Term.var x, bound] i).realize (Function.update s x a)) =
      ![a, bound.realize s] := by
    funext i
    fin_cases i <;> simp [hb]
  rw [he]

/-- The fresh-bound condition keeps the bounding term evaluated in the original assignment. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    When the language contains a binary relation symbol $\in$, we also use **bounded quantifiers** as abbreviations:
    $$
    (\exists u \in v)\,\varphi
    \quad:\equiv\quad
    \exists u\,(u\in v \land \varphi),
    \qquad
    (\forall u \in v)\,\varphi
    \quad:\equiv\quad
    \forall u\,(u\in v \to \varphi).
    $$
    The variable $u$ is bound in $\varphi$, and $v$ is the bounding term, in which $u$ must not occur freely. Thus
    bounded quantification is not an additional
    logical primitive; it is notation available in set-theoretic languages such as $L_\in$.
-/
theorem realize_boundedForall {M : Type w} [L.Structure M] (R : L.Relations 2)
    (x : ℕ) (bound : L.Term ℕ) (hx : x ∉ bound.varFinset) (φ : AlphaFormula L) (s : ℕ → M) :
    (boundedForall R x bound φ).Realize s ↔
      ∀ a, Structure.RelMap R ![a, bound.realize s] → φ.Realize (Function.update s x a) := by
  simp only [boundedForall, realize_all, realize_imp]
  exact forall_congr' (fun a => imp_congr (realize_bound_relation R x bound hx s a) Iff.rfl)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    When the language contains a binary relation symbol $\in$, we also use **bounded quantifiers** as abbreviations:
    $$
    (\exists u \in v)\,\varphi
    \quad:\equiv\quad
    \exists u\,(u\in v \land \varphi),
    \qquad
    (\forall u \in v)\,\varphi
    \quad:\equiv\quad
    \forall u\,(u\in v \to \varphi).
    $$
    The variable $u$ is bound in $\varphi$, and $v$ is the bounding term, in which $u$ must not occur freely. Thus
    bounded quantification is not an additional
    logical primitive; it is notation available in set-theoretic languages such as $L_\in$.
-/
theorem realize_boundedExists {M : Type w} [L.Structure M] (R : L.Relations 2)
    (x : ℕ) (bound : L.Term ℕ) (hx : x ∉ bound.varFinset) (φ : AlphaFormula L) (s : ℕ → M) :
    (boundedExists R x bound φ).Realize s ↔
      ∃ a, Structure.RelMap R ![a, bound.realize s] ∧ φ.Realize (Function.update s x a) := by
  simp only [boundedExists, realize_ex, realize_conj]
  exact exists_congr (fun a => and_congr (realize_bound_relation R x bound hx s a) Iff.rfl)

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
