module

public import PolishSpaceBook.FirstOrderFunctionDefinitions

@[expose] public section

/-! # Model expansions by total, possibly nonunique, graph values -/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Total existence, with no uniqueness clause. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Uniqueness is essential for treating function and constant definitions as mere abbreviations.
    If $T$ proves only $\forall \vec{x}\,\exists y\,\theta(\vec{x},y)$, adding a function $f$ with
    $\theta(\vec{x},f(\vec{x}))$ chooses a witness at each input. Using the set-theoretic axiom of choice,
    every model admits such a \termuse{Skolem function}, so the model-expansion criterion still gives a
    \termuse{conservative extension}. However, the expansion need not be unique and the new function is not determined
    by the old structure. In
    §{sec:appendix-set-theory}, total term notations such as $\emptyset$, $\{a,b\}$, and $\bigcup x$ are
    introduced only where
    ZFC proves unique existence. Partial notations such as $f(a)$ are treated contextually rather than as total function
    symbols.
-/
def totalExistence {n : ℕ} (f : ι n) : AlphaFormula L :=
  closeAll n (quant .ex n (D.graph f))

theorem totalValues {T : Set (AlphaFormula L)} {M : Type w} (A : L.Structure M)
    (hT : TheoryRealize A T) (hp : ∀ n (f : ι n), ProvesFrom T (D.totalExistence f)) :
    ∀ n (f : ι n) (s : ℕ → M), ∃ b, @AlphaFormula.Realize L M A (D.graph f) (Function.update s n b) := by
  let := A
  intro n f s
  have h : ∀ t : ℕ → M, (D.totalExistence f).Realize t := fun t => (hp n f).sound t (hT t)
  exact (realize_ex n (D.graph f) s).mp ((forall_realize_closeAll n _).mp h s)

/-- Set-theoretic choice supplies a witness at each input tuple. -/
abbrev skolemStructure {M : Type w} [L.Structure M] (d : M)
    (h : ∀ n (f : ι n) (s : ℕ → M), ∃ b, (D.graph f).Realize (Function.update s n b)) :
    (functionSymbols ι).Structure M where
  funMap := fun {n} f a => Classical.choose (h n f (RelationDefinitions.assignment d a))
  RelMap := fun R => nomatch R

theorem skolemStructure_satisfies {M : Type w} [L.Structure M] (d : M)
    (h : ∀ n (f : ι n) (s : ℕ → M), ∃ b, (D.graph f).Realize (Function.update s n b))
    {n : ℕ} (f : ι n) :
    let := D.skolemStructure d h
    ∀ s : ℕ → M, (D.definingAxiom f).Realize s := by
  let := D.skolemStructure d h
  apply (D.realize_axiom_iff f).mpr
  intro s
  exact (D.realize_graph_assignment d f s _).mp
    (Classical.choose_spec (h n f (RelationDefinitions.assignment d (fun i : Fin n => s i.val))))

/-- Every old model expands using total graphs, without assuming unique outputs. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Uniqueness is essential for treating function and constant definitions as mere abbreviations.
    If $T$ proves only $\forall \vec{x}\,\exists y\,\theta(\vec{x},y)$, adding a function $f$ with
    $\theta(\vec{x},f(\vec{x}))$ chooses a witness at each input. Using the set-theoretic axiom of choice,
    every model admits such a \termuse{Skolem function}, so the model-expansion criterion still gives a
    \termuse{conservative extension}. However, the expansion need not be unique and the new function is not determined
    by the old structure. In
    §{sec:appendix-set-theory}, total term notations such as $\emptyset$, $\{a,b\}$, and $\bigcup x$ are
    introduced only where
    ZFC proves unique existence. Partial notations such as $f(a)$ are treated contextually rather than as total function
    symbols.
-/
theorem exists_skolem_expansion {T : Set (AlphaFormula L)} {M : Type w} (A : L.Structure M)
    (hne : Nonempty M) (hT : TheoryRealize A T)
    (hp : ∀ n (f : ι n), ProvesFrom T (D.totalExistence f)) :
    ∃ B : (L.sum (functionSymbols ι)).Structure M,
      @LHom.IsExpansionOn _ _ inclusion M A B ∧ TheoryRealize B (D.theory T) := by
  let := A
  let d : M := Classical.choice hne
  let h := D.totalValues A hT hp
  let := D.skolemStructure d h
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro s φ hφ
  rcases hφ with ⟨ψ, hψ, rfl⟩ | ⟨n, f, rfl⟩
  · exact (ψ.mapLanguage_realize_expansion inclusion s).mpr (hT s ψ hψ)
  · exact D.skolemStructure_satisfies d h f s

/-- Skolem axioms are conservative by model expansion, though they need not define values uniquely. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Uniqueness is essential for treating function and constant definitions as mere abbreviations.
    If $T$ proves only $\forall \vec{x}\,\exists y\,\theta(\vec{x},y)$, adding a function $f$ with
    $\theta(\vec{x},f(\vec{x}))$ chooses a witness at each input. Using the set-theoretic axiom of choice,
    every model admits such a \termuse{Skolem function}, so the model-expansion criterion still gives a
    \termuse{conservative extension}. However, the expansion need not be unique and the new function is not determined
    by the old structure. In
    §{sec:appendix-set-theory}, total term notations such as $\emptyset$, $\{a,b\}$, and $\bigcup x$ are
    introduced only where
    ZFC proves unique existence. Partial notations such as $f(a)$ are treated contextually rather than as total function
    symbols.
-/
theorem conservative_skolem {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hp : ∀ n (f : ι n), ProvesFrom T (D.totalExistence f))
    {σ : AlphaFormula L} (hσ : σ ∈ Sentences L)
    (hσ' : ProvesFrom (D.theory T) (σ.mapLanguage inclusion)) : ProvesFrom T σ :=
  conservative_of_model_expansion inclusion hT (fun _ A hne h => D.exists_skolem_expansion A hne h hp) hσ hσ'

end FunctionDefinitions

namespace SkolemNonuniqueness

/-- A graph that imposes no restriction on the output. -/
def definitions : FunctionDefinitions Language.empty (fun _ => Unit) where
  graph := fun {n} _ => equal (.var n) (.var n)
  freeVars := by intro n f; change ({n} ∪ {n} : Finset ℕ) ⊆ Finset.range (n + 1); simp

abbrev expandedLanguage := Language.empty.sum (functionSymbols (fun _ => Unit))

/-- Interpret every new operation by one fixed Boolean value. -/
@[instance_reducible] def interpretation (b : Bool) : expandedLanguage.Structure Bool where
  funMap := fun f => match f with
    | Sum.inl f => nomatch f
    | Sum.inr _ => fun _ => b
  RelMap := fun R => match R with
    | Sum.inl R => nomatch R
    | Sum.inr R => nomatch R

/-- The empty old language has exactly the same interpretation in both expansions. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Uniqueness is essential for treating function and constant definitions as mere abbreviations.
    If $T$ proves only $\forall \vec{x}\,\exists y\,\theta(\vec{x},y)$, adding a function $f$ with
    $\theta(\vec{x},f(\vec{x}))$ chooses a witness at each input. Using the set-theoretic axiom of choice,
    every model admits such a \termuse{Skolem function}, so the model-expansion criterion still gives a
    \termuse{conservative extension}. However, the expansion need not be unique and the new function is not determined
    by the old structure. In
    §{sec:appendix-set-theory}, total term notations such as $\emptyset$, $\{a,b\}$, and $\bigcup x$ are
    introduced only where
    ZFC proves unique existence. Partial notations such as $f(a)$ are treated contextually rather than as total function
    symbols.
-/
theorem interpretation_expands (b : Bool) :
    @LHom.IsExpansionOn Language.empty expandedLanguage
      (FunctionDefinitions.inclusion (L := Language.empty) (ι := fun _ => Unit))
      Bool Language.emptyStructure (interpretation b) := by
  let : Language.empty.Structure Bool := Language.emptyStructure
  let : expandedLanguage.Structure Bool := interpretation b
  exact LHom.IsExpansionOn.mk (fun {_} f _ => nomatch f) (fun {_} R _ => nomatch R)

theorem satisfies (b : Bool) : TheoryRealize (interpretation b) (definitions.theory ∅) := by
  let : Language.empty.Structure Bool := Language.emptyStructure
  let : expandedLanguage.Structure Bool := interpretation b
  let : (FunctionDefinitions.inclusion (L := Language.empty) (ι := fun _ => Unit)).IsExpansionOn Bool :=
    interpretation_expands b
  intro s φ hφ
  rcases hφ with ⟨ψ, hψ, rfl⟩ | ⟨n, f, rfl⟩
  · exact False.elim hψ
  · apply (definitions.realize_axiom_iff f).mpr ?_ s
    intro t
    rfl

/-- Two models with the same old structure satisfy the same Skolem axioms and disagree on a new constant. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Uniqueness is essential for treating function and constant definitions as mere abbreviations.
    If $T$ proves only $\forall \vec{x}\,\exists y\,\theta(\vec{x},y)$, adding a function $f$ with
    $\theta(\vec{x},f(\vec{x}))$ chooses a witness at each input. Using the set-theoretic axiom of choice,
    every model admits such a \termuse{Skolem function}, so the model-expansion criterion still gives a
    \termuse{conservative extension}. However, the expansion need not be unique and the new function is not determined
    by the old structure. In
    §{sec:appendix-set-theory}, total term notations such as $\emptyset$, $\{a,b\}$, and $\bigcup x$ are
    introduced only where
    ZFC proves unique existence. Partial notations such as $f(a)$ are treated contextually rather than as total function
    symbols.
-/
theorem distinct_expansions :
    interpretation false ≠ interpretation true ∧
      TheoryRealize (interpretation false) (definitions.theory ∅) ∧
      TheoryRealize (interpretation true) (definitions.theory ∅) := by
  refine ⟨?_, satisfies false, satisfies true⟩
  intro h
  have he := congrArg (fun A : expandedLanguage.Structure Bool =>
    @Structure.funMap expandedLanguage Bool A 0 (Sum.inr ()) Fin.elim0) h
  change false = true at he
  cases he

end SkolemNonuniqueness
end PolishSpaceBook.NamedFirstOrder
