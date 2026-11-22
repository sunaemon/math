module

public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-!
# Compositional bounded unfolding

An expansion is a membership-language formula with its Delta-zero certificate
and semantic correctness theorem. Value binding uses a bound already present in
the environment and a graph that identifies exactly the chosen value there.
This is logical syntax, not an additional model of computation.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u v

namespace BoundedUnfolding

/-- The membership relation of an arbitrary structure, including nontransitive models. -/
def memberIn {M : Type v} [membershipLanguage.Structure M] (a b : M) : Prop :=
  Structure.RelMap (L := membershipLanguage) MembershipSymbol.mem ![a,b]

private theorem realize_member {M : Type v} [membershipLanguage.Structure M] {n : ℕ}
    (i j : Fin n) (xs : Fin n → M) :
    (memberAt i j).Realize Empty.elim xs ↔ memberIn (xs i) (xs j) := by
  change Structure.RelMap (L := membershipLanguage) MembershipSymbol.mem _ ↔ _
  unfold memberIn
  apply iff_of_eq
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem realize_all {M : Type v} [membershipLanguage.Structure M] {n : ℕ}
    (b : Fin n) (φ : ForcingFormulas.Formula (n+1)) (xs : Fin n → M) :
    (boundedAll b φ).Realize Empty.elim xs ↔
      ∀ y : M, memberIn y (xs b) → φ.Realize Empty.elim (Fin.snoc xs y) := by
  simp only [boundedAll,BoundedFormula.realize_all,BoundedFormula.realize_imp,
    realize_member,Fin.snoc_last,Fin.snoc_castSucc]

private theorem realize_ex {M : Type v} [membershipLanguage.Structure M] {n : ℕ}
    (b : Fin n) (φ : ForcingFormulas.Formula (n+1)) (xs : Fin n → M) :
    (boundedExists b φ).Realize Empty.elim xs ↔
      ∃ y : M, memberIn y (xs b) ∧ φ.Realize Empty.elim (Fin.snoc xs y) := by
  classical
  simp only [boundedExists,BoundedFormula.realize_not,realize_all,not_forall,not_not,exists_prop]

/-- A bounded expansion of a predicate in a fixed membership structure. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Iterate this step from the innermost function occurrences outward. Introduce a fresh variable for each value,
    and retain each bounded witness inside the scope of every parameter on which it depends. A later bound may
    use values already introduced, but may not rely on its own witness or on an unexpanded function term.
    Induction on the finite construction now proves the assertion, including nested function occurrences and
    function values used as bounds. No unbounded quantifier is introduced.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    There is, however, a systematic bounded version. A definition is \termdefine{$\DeltaZero$-safe} when eliminating it
    introduces only bounded quantifiers and formulas already known to be $\Delta_0$-safe. For relation symbols, this means
    that the defining formula is $\Delta_0$ after recursively unfolding earlier safe definitions. For function symbols, the
    graph must have a bounded definition in the following stronger sense: there is an already available term or
    contextual parameter $B(\vec{x})$
    such that
    $$
    T \vdash \forall \vec{x}\,\exists! y \in B(\vec{x})\,\theta(\vec{x},y),
    $$
    with $\theta$ itself $\Delta_0$ after recursively unfolding earlier safe definitions. In this bounded version,
    the defining axiom is
    $$f(\vec{x})=y\quad\longleftrightarrow\quad
     y\in B(\vec{x})\land\theta(\vec{x},y).$$
    If the function was already defined by its graph without a bound, verify that its unique value lies in the
    proposed bound. An atomic formula containing $f(\vec{t})$ can then be translated by a bounded witness:
    $$
    P(f(x),z)
    \quad\leadsto\quad
    \exists u \in B(x)\,\bigl(\theta(x,u) \land P(u,z)\bigr).
    $$
    This keeps the translation $\Delta_0$ whenever the surrounding atomic formula and the defining graph are $\Delta_0$.
    The bound itself must already admit bounded elimination, or be supplied as a parameter; introducing an
    unboundedly defined bound would defeat the argument. Multiple function terms are handled by adding one bounded
    witness for each occurrence.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Call the recursive replacement of expanded notation by these bounded clauses \termdefine{bounded unfolding}. Thus
    definitional extension preserves old-language theorems in general, while Lévy-complexity preservation requires
    $\Delta_0$-safe definitions or explicitly contextual notation. When this text claims that a formula is $\Delta_0$,
    $\Sigma_n$, or $\Pi_n$ in §{sec:zfc-absoluteness}, the claim is made after bounded unfolding, so no hidden unbounded
    quantifier is being counted as harmless.\termref{absoluteness}
-/
structure Expansion (M : Type v) [membershipLanguage.Structure M] (n : ℕ) (P : (Fin n → M) → Prop) where
  formula : ForcingFormulas.Formula n
  bounded : IsDeltaZero formula
  correct : ∀ xs, formula.Realize Empty.elim xs ↔ P xs

namespace Expansion
variable {M : Type v} [membershipLanguage.Structure M] {n : ℕ} {P Q : (Fin n → M) → Prop}

/-- An already unfolded bounded atom may be used without changing its formula. -/
def atom (φ : ForcingFormulas.Formula n) (hφ : IsDeltaZero φ) :
    Expansion M n (fun xs => φ.Realize Empty.elim xs) := ⟨φ,hφ,fun _ => Iff.rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Keep, at each step, both a formula in the membership language and the facts that it is bounded and expresses
    the intended predicate. A relation abbreviation supplies the initial formula. Boolean connectives preserve both
    facts. For a quantifier bounded by an available variable, apply the equivalence for its body separately to each
    value in that bound. Adding this bounded quantifier preserves $\Delta_0$ complexity.
-/
def imp (p : Expansion M n P) (q : Expansion M n Q) :
    Expansion M n (fun xs => P xs → Q xs) where
  formula := p.formula.imp q.formula
  bounded := p.bounded.imp q.bounded
  correct xs := by simp only [BoundedFormula.realize_imp,p.correct xs,q.correct xs]

def neg (p : Expansion M n P) : Expansion M n (fun xs => ¬P xs) where
  formula := p.formula.not
  bounded := p.bounded.not
  correct xs := by simp only [BoundedFormula.realize_not,p.correct xs]

def conj (p : Expansion M n P) (q : Expansion M n Q) :
    Expansion M n (fun xs => P xs ∧ Q xs) where
  formula := p.formula ⊓ q.formula
  bounded := p.bounded.and q.bounded
  correct xs := by simp only [BoundedFormula.realize_inf,p.correct xs,q.correct xs]

def disj (p : Expansion M n P) (q : Expansion M n Q) :
    Expansion M n (fun xs => P xs ∨ Q xs) where
  formula := p.formula ⊔ q.formula
  bounded := p.bounded.or q.bounded
  correct xs := by simp only [BoundedFormula.realize_sup,p.correct xs,q.correct xs]

def all (b : Fin n) {R : (Fin (n+1) → M) → Prop} (p : Expansion M (n+1) R) :
    Expansion M n (fun xs => ∀ y : M, memberIn y (xs b) → R (Fin.snoc xs y)) where
  formula := boundedAll b p.formula
  bounded := .all b p.bounded
  correct xs := by simp only [realize_all,p.correct]

def ex (b : Fin n) {R : (Fin (n+1) → M) → Prop} (p : Expansion M (n+1) R) :
    Expansion M n (fun xs => ∃ y : M, memberIn y (xs b) ∧ R (Fin.snoc xs y)) where
  formula := boundedExists b p.formula
  bounded := .exists b p.bounded
  correct xs := by simp only [realize_ex,p.correct]

/-- Bind the unique bounded graph value before evaluating the surrounding expression. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: proposition
  title: Bounded unfolding
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For a function value, let $\chi(u)$ denote the already expanded surrounding formula, with its other parameters
    fixed. The defining axiom and bounded unique existence give
    $$\chi(f(\vec{x}))\quad\longleftrightarrow\quad
    \exists u\in B(\vec{x})\,\bigl(\theta(\vec{x},u)\land\chi(u)\bigr).$$
    In the forward direction, use the value of the function as the witness; it lies in the bound and satisfies the
    graph. In the reverse direction, uniqueness identifies every witness with that value, so the surrounding
    formula holds at the function value. The displayed right-hand side is $\Delta_0$ because its graph and body
    are $\Delta_0$ and its existential quantifier is bounded. All other parameters are retained.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    There is, however, a systematic bounded version. A definition is \termdefine{$\DeltaZero$-safe} when eliminating it
    introduces only bounded quantifiers and formulas already known to be $\Delta_0$-safe. For relation symbols, this means
    that the defining formula is $\Delta_0$ after recursively unfolding earlier safe definitions. For function symbols, the
    graph must have a bounded definition in the following stronger sense: there is an already available term or
    contextual parameter $B(\vec{x})$
    such that
    $$
    T \vdash \forall \vec{x}\,\exists! y \in B(\vec{x})\,\theta(\vec{x},y),
    $$
    with $\theta$ itself $\Delta_0$ after recursively unfolding earlier safe definitions. In this bounded version,
    the defining axiom is
    $$f(\vec{x})=y\quad\longleftrightarrow\quad
     y\in B(\vec{x})\land\theta(\vec{x},y).$$
    If the function was already defined by its graph without a bound, verify that its unique value lies in the
    proposed bound. An atomic formula containing $f(\vec{t})$ can then be translated by a bounded witness:
    $$
    P(f(x),z)
    \quad\leadsto\quad
    \exists u \in B(x)\,\bigl(\theta(x,u) \land P(u,z)\bigr).
    $$
    This keeps the translation $\Delta_0$ whenever the surrounding atomic formula and the defining graph are $\Delta_0$.
    The bound itself must already admit bounded elimination, or be supplied as a parameter; introducing an
    unboundedly defined bound would defeat the argument. Multiple function terms are handled by adding one bounded
    witness for each occurrence.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Call the recursive replacement of expanded notation by these bounded clauses \termdefine{bounded unfolding}. Thus
    definitional extension preserves old-language theorems in general, while Lévy-complexity preservation requires
    $\Delta_0$-safe definitions or explicitly contextual notation. When this text claims that a formula is $\Delta_0$,
    $\Sigma_n$, or $\Pi_n$ in §{sec:zfc-absoluteness}, the claim is made after bounded unfolding, so no hidden unbounded
    quantifier is being counted as harmless.\termref{absoluteness}
-/
def value (b : Fin n) (θ : ForcingFormulas.Formula (n+1)) (hθ : IsDeltaZero θ)
    (f : (Fin n → M) → M)
    (hf : ∀ xs y, (memberIn y (xs b) ∧ θ.Realize Empty.elim (Fin.snoc xs y)) ↔ y = f xs)
    {R : (Fin (n+1) → M) → Prop} (p : Expansion M (n+1) R) :
    Expansion M n (fun xs => R (Fin.snoc xs (f xs))) where
  formula := boundedExists b (θ ⊓ p.formula)
  bounded := .exists b (hθ.and p.bounded)
  correct xs := by
    rw [realize_ex]
    simp only [BoundedFormula.realize_inf,p.correct]
    constructor
    · rintro ⟨y,hy,hθy,hp⟩
      have he := (hf xs y).mp ⟨hy,hθy⟩
      simpa only [he] using hp
    · intro hp
      obtain ⟨hy,hθy⟩ := (hf xs (f xs)).mpr rfl
      exact ⟨f xs,hy,hθy,hp⟩

/-- Bounded unique existence supplies the semantic value; it does not assert computable choice. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    There is, however, a systematic bounded version. A definition is \termdefine{$\DeltaZero$-safe} when eliminating it
    introduces only bounded quantifiers and formulas already known to be $\Delta_0$-safe. For relation symbols, this means
    that the defining formula is $\Delta_0$ after recursively unfolding earlier safe definitions. For function symbols, the
    graph must have a bounded definition in the following stronger sense: there is an already available term or
    contextual parameter $B(\vec{x})$
    such that
    $$
    T \vdash \forall \vec{x}\,\exists! y \in B(\vec{x})\,\theta(\vec{x},y),
    $$
    with $\theta$ itself $\Delta_0$ after recursively unfolding earlier safe definitions. In this bounded version,
    the defining axiom is
    $$f(\vec{x})=y\quad\longleftrightarrow\quad
     y\in B(\vec{x})\land\theta(\vec{x},y).$$
    If the function was already defined by its graph without a bound, verify that its unique value lies in the
    proposed bound. An atomic formula containing $f(\vec{t})$ can then be translated by a bounded witness:
    $$
    P(f(x),z)
    \quad\leadsto\quad
    \exists u \in B(x)\,\bigl(\theta(x,u) \land P(u,z)\bigr).
    $$
    This keeps the translation $\Delta_0$ whenever the surrounding atomic formula and the defining graph are $\Delta_0$.
    The bound itself must already admit bounded elimination, or be supplied as a parameter; introducing an
    unboundedly defined bound would defeat the argument. Multiple function terms are handled by adding one bounded
    witness for each occurrence.
-/
theorem exists_value (b : Fin n) (θ : ForcingFormulas.Formula (n+1))
    (h : ∀ xs : Fin n → M,
      ∃! y : M, memberIn y (xs b) ∧ θ.Realize Empty.elim (Fin.snoc xs y)) :
    ∃ f : (Fin n → M) → M,
      ∀ xs y, (memberIn y (xs b) ∧ θ.Realize Empty.elim (Fin.snoc xs y)) ↔ y = f xs := by
  classical
  choose f hf using fun xs => (h xs).exists
  refine ⟨f,fun xs y => ?_⟩
  constructor
  · intro hy
    obtain ⟨z,_,hz⟩ := h xs
    exact (hz y hy).trans (hz (f xs) (hf xs)).symm
  · rintro rfl
    exact hf xs

/-- Reuse the existing reflection theorem for the book's bounded set predicates. -/
def reflected {M : ZFSet.{u}} (hM : M.IsTransitive) (p : BoundedSetPredicate n) :
    Expansion M n (fun xs => p.eval (Subtype.val ∘ xs)) :=
  ⟨p.compile,p.compile_deltaZero,p.realize_compile hM⟩

/-- Inclusion uses its already verified bounded expansion. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    As a sample relation abbreviation, $y \IncludedIn x$ unfolds to
    $$\forall z \in y\; z \in x,$$
    so $\IncludedIn$ is $\Delta_0$-safe.
-/
def subset {M : ZFSet.{u}} (hM : M.IsTransitive) (x y : Fin n) :
    Expansion M n (fun xs => (xs y).val ⊆ (xs x).val) :=
  reflected hM (.subset y x)

/-- Membership in a union can be expanded directly without a value bound for the union. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    For the common membership context, use the direct bounded expansion
    $$z\in x\cup y\quad\Longleftrightarrow\quad z\in x\lor z\in y.$$
-/
def memberUnion {C : ZFClass.{u}} (x y z : Fin n) :
    Expansion (ClassDomain C) n (fun xs => (xs z).val ∈ (xs x).val ∪ (xs y).val) where
  formula := memberAt z x ⊔ memberAt z y
  bounded := (IsDeltaZero.member _).or (.member _)
  correct xs := by simp only [BoundedFormula.realize_sup,realize_memberAt_class,ZFSet.mem_union]

end Expansion

/-- The union graph uses only quantification bounded by its three parameters. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    As a sample function abbreviation, the graph of binary union can be written
    $$
    \theta_\cup(x,y,u) \;:\equiv\;
    (\forall z \in u)(z\in x \lor z\in y)
    \land (\forall z \in x)\,z\in u
    \land (\forall z \in y)\,z\in u.
    $$
    This graph is $\Delta_0$.
-/
def binaryUnionGraph {n : ℕ} (x y v : Fin n) : ForcingFormulas.Formula n :=
  boundedAll v (memberAt (Fin.last n) x.castSucc ⊔ memberAt (Fin.last n) y.castSucc) ⊓
    (boundedAll x (memberAt (Fin.last n) v.castSucc) ⊓
     boundedAll y (memberAt (Fin.last n) v.castSucc))

theorem binaryUnionGraph_bounded {n : ℕ} (x y v : Fin n) : IsDeltaZero (binaryUnionGraph x y v) :=
  (IsDeltaZero.all v ((IsDeltaZero.member _).or (.member _))).and
    ((IsDeltaZero.all x (.member _)).and (.all y (.member _)))

/-- On a transitive domain the bounded graph specifies the actual binary union. -/
theorem realize_binaryUnionGraph (C : ZFClass.{u})
    (hC : ∀ a, C a → ∀ b ∈ a, C b) {n : ℕ} (x y v : Fin n) (xs : Fin n → ClassDomain C) :
    (binaryUnionGraph x y v).Realize Empty.elim xs ↔ (xs v).val = (xs x).val ∪ (xs y).val := by
  simp only [binaryUnionGraph,BoundedFormula.realize_inf,realize_boundedAll,
    BoundedFormula.realize_sup,realize_memberAt_class,Fin.snoc_last,Fin.snoc_castSucc]
  constructor
  · rintro ⟨hv,hx,hy⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union]
    constructor
    · intro hz
      exact hv ⟨z,hC _ (xs v).property z hz⟩ hz
    · rintro (hz | hz)
      · exact hx ⟨z,hC _ (xs x).property z hz⟩ hz
      · exact hy ⟨z,hC _ (xs y).property z hz⟩ hz
  · intro he
    constructor
    · intro z hz
      simpa only [he,ZFSet.mem_union] using hz
    · constructor
      · intro z hz
        rw [he,ZFSet.mem_union]
        exact Or.inl hz
      · intro z hz
        rw [he,ZFSet.mem_union]
        exact Or.inr hz

end BoundedUnfolding
end PolishSpaceBook.SetTheoryModels
