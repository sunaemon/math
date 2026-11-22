module

public import PolishSpaceBook.FirstOrderSkolemStages

@[expose] public section

/-!
# The countable downward Löwenheim--Skolem construction

Choose Skolem functions once in the given structure, close the seed under them
and the original functions by the explicit finite stages, and then apply the
proved Tarski--Vaught test. The ambient domain is assumed nonempty, as in the
book's semantics. The arbitrary fallback element is included in the seed.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- Closure under the chosen Skolem functions supplies the witness clause directly. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    If $\mathcal A\models\exists y\,\varphi(y,\vec b)$ with $\vec b\in B$, the value $F_\varphi(\vec b)$ belongs to
    $B$ and satisfies the body in $\mathcal A$. The \termuse{Tarski--Vaught test} therefore makes the restricted
    structure on $B$ an elementary substructure of $\mathcal A$.
-/
theorem witnessClosed_skolemReduct (S : (L.sum L.skolem₁).Substructure M) :
    WitnessClosed (LHom.sumInl.substructureReduct S) := by
  intro n φ s a ha
  let f : (L.sum L.skolem₁).Functions n := LHom.sumInr.onFunction φ
  refine ⟨⟨Structure.funMap f (Subtype.val ∘ s), S.fun_mem f _ (fun i => (s i).property)⟩, ?_⟩
  exact Classical.epsilon_spec (p := fun a => φ.Realize default (Fin.snoc (Subtype.val ∘ s) a)) ⟨a, ha⟩

/-- The elementary substructure obtained from the actual stage union. -/
def skolemStageModel (X : Set M) : L.ElementarySubstructure M :=
  let S := operationSubstructure (L := L.sum L.skolem₁) (insert (Classical.choice ‹Nonempty M›) X)
  ⟨LHom.sumInl.substructureReduct S,
    (isElementary_iff_witnessClosed _).mpr (witnessClosed_skolemReduct S)⟩

theorem subset_skolemStageModel (X : Set M) : X ⊆ skolemStageModel (L := L) X :=
  Set.Subset.trans (Set.subset_insert _ _) (subset_operationSubstructure _)

/-- Countability of the added function symbols follows from countability of formulas. -/
theorem countable_skolem_functions [Countable L.Symbols] :
    Countable (Σ n, (L.sum L.skolem₁).Functions n) := by
  let (n : ℕ) : Countable (L.Functions n) :=
    Function.Injective.countable (f := fun f => (⟨n, f⟩ : Σ n, L.Functions n)) sigma_mk_injective
  let (n : ℕ) : Countable (L.BoundedFormula Empty (n + 1)) :=
    Function.Injective.countable (f := fun φ => (⟨n + 1, φ⟩ : Σ n, L.BoundedFormula Empty n)) sigma_mk_injective
  change Countable (Σ n, L.Functions n ⊕ L.BoundedFormula Empty (n + 1))
  infer_instance

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Fix $a_0\in A$. For each formula $\exists y\,\varphi(y,\vec x)$, choose a
    \termdefine{Skolem function} $F_\varphi$ that returns a witness when one exists and $a_0$ otherwise.
    Let $\mathcal F$ consist of these functions and the interpretations of the original function symbols.
    The language is countable and formulas are finite strings, so $\mathcal F$ is countable.
    Each $F\in\mathcal F$ has a finite arity $r(F)$, which may be zero. Define
    $$\begin{aligned}
    B_0&:=X\cup\{a_0\},\\
    B_{n+1}&:=B_n\cup\bigcup_{F\in\mathcal F}F[B_n^{r(F)}],\\
    B&:=\bigcup_{n<\omega}B_n.
    \end{aligned}$$
    Each finite power of a countable set is countable, including its zeroth power, which consists of the empty tuple.
    Thus each successor step adds a countable union of countable images. Induction shows that every $B_n$ is countable,
    and their union $B$ is countable. It contains $X$ and is nonempty.
-/
theorem countable_skolemStageModel [Countable L.Symbols] {X : Set M} (hX : X.Countable) :
    (skolemStageModel (L := L) X : Set M).Countable := by
  let := countable_skolem_functions (L := L)
  exact countable_operationSubstructure (L := L.sum L.skolem₁) (hX.insert _)

/-- The book's countable downward theorem, with the explicitly constructed model. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: downward Löwenheim–Skolem
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Arbitrary countable collections
    of objects may also be included in the Löwenheim--Skolem construction
-/
theorem exists_countable_elementarySubstructure [Countable L.Symbols] {X : Set M} (hX : X.Countable) :
    ∃ B : L.ElementarySubstructure M, X ⊆ B ∧ (B : Set M).Countable :=
  ⟨skolemStageModel X, subset_skolemStageModel X, countable_skolemStageModel hX⟩

end PolishSpaceBook.NamedFirstOrder
