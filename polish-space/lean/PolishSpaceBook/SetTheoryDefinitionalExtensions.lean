module

public import PolishSpaceBook.SetTheoryBasicAbbreviations
public import PolishSpaceBook.SetTheoryZFCConsistency
public import PolishSpaceBook.FirstOrderDefinitionalConservativity
public import PolishSpaceBook.FirstOrderRelationConservativity

@[expose] public section

/-! # The basic set operations as actual conservative function definitions

The graph formulas live in the pure membership language. Unique existence is
proved in arbitrary models of the literal ZFC axioms, then completeness for
the book's natural deduction supplies the required derivations. No
transitivity or external set closure is assumed.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas NamedFirstOrder
open AbstractMembership
universe w

/-- Only the total operations are added; application and nonempty intersection
remain contextual notation. -/
inductive BasicSetSymbol : ℕ → Type
  | empty : BasicSetSymbol 0
  | pair : BasicSetSymbol 2
  | union : BasicSetSymbol 1
  | intersection : BasicSetSymbol 2
  | domain : BasicSetSymbol 1

/-- Inputs precede the output in each graph's finite variable context. -/
def basicSetGraph : {n : ℕ} → BasicSetSymbol n → ForcingFormulas.Formula (n + 1)
  | _, .empty => (memberAt (1 : Fin 2) 0).not.all
  | _, .pair => ((memberAt (3 : Fin 4) 2).iff
      (equalAt 3 0 ⊔ equalAt 3 1)).all
  | _, .union => ((memberAt (2 : Fin 3) 1).iff
      (memberAt (2 : Fin 4) 3 ⊓ memberAt 3 0).ex).all
  | _, .intersection => ((memberAt (3 : Fin 4) 2).iff
      (memberAt 3 0 ⊓ memberAt 3 1)).all
  | _, .domain => ((memberAt (2 : Fin 3) 1).iff
      (internalApplicationFormula (0 : Fin 4) 2 3).ex).all

/-- Concrete graph definitions in the named syntax used by conservativity. -/
def basicSetDefinitions : FunctionDefinitions membershipLanguage BasicSetSymbol where
  graph f := .mk (boundedToNamed (basicSetGraph f))
  freeVars f := boundedToNamed_fv (basicSetGraph f)

/-- Recover the literal axiom theory from its named translation. -/
theorem fullZFC_model_of_named {M : Type w} [membershipLanguage.Structure M]
    (s : ℕ → M) (hM : ∀ ψ ∈ namedFullZFCTheory, ψ.Realize s) : M ⊨ fullZFCTheory := by
  constructor
  intro φ hφ
  exact (realize_boundedToNamed_sentence φ s).mp (hM _ ⟨φ, hφ, rfl⟩)

/-- Derived Separation is available for every formula in every ZFC model. -/
theorem fullZFC_model_separation {M : Type w} [membershipLanguage.Structure M]
    (hM : M ⊨ fullZFCTheory) {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    M ⊨ separationSentence φ :=
  AbstractMembership.models_separation_of_replacement M
    (hM.realize_of_mem _ ZFCAxiom.extensionality)
    (hM.realize_of_mem _ ZFCAxiom.infinity)
    (hM.realize_of_mem _ ZFCAxiom.pairing)
    (hM.realize_of_mem _ ZFCAxiom.union) φ
    (hM.realize_of_mem _ (ZFCAxiom.replacement _))

/-- Each graph really has a unique output in arbitrary ZFC models. -/
theorem basicSetGraph_unique {M : Type w} [membershipLanguage.Structure M]
    (hM : M ⊨ fullZFCTheory) {n : ℕ} (f : BasicSetSymbol n) (s : ℕ → M) :
    ∃! b, (basicSetDefinitions.graph f).Realize (Function.update s n b) := by
  have he := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hp := hM.realize_of_mem _ ZFCAxiom.pairing
  have hu := hM.realize_of_mem _ ZFCAxiom.union
  have hi := hM.realize_of_mem _ ZFCAxiom.infinity
  cases f with
  | empty =>
    simpa [basicSetDefinitions, basicSetGraph, AlphaFormula.realize_mk,
      realize_boundedToNamed, BoundedFormula.realize_all, BoundedFormula.realize_not,
      AbstractMembership.realize_memberAt, Fin.snoc] using existsUnique_empty he hi
  | pair =>
    simpa [basicSetDefinitions, basicSetGraph, AlphaFormula.realize_mk,
      realize_boundedToNamed, BoundedFormula.realize_all, BoundedFormula.realize_iff,
      BoundedFormula.realize_sup, AbstractMembership.realize_memberAt, AbstractMembership.realize_equalAt, Fin.snoc]
      using existsUnique_pair he hp (s 0) (s 1)
  | union =>
    simpa [basicSetDefinitions, basicSetGraph, AlphaFormula.realize_mk,
      realize_boundedToNamed, BoundedFormula.realize_all, BoundedFormula.realize_iff,
      BoundedFormula.realize_ex, BoundedFormula.realize_inf, AbstractMembership.realize_memberAt, Fin.snoc]
      using existsUnique_union he hu (s 0)
  | intersection =>
    simpa [basicSetDefinitions, basicSetGraph, AlphaFormula.realize_mk,
      realize_boundedToNamed, BoundedFormula.realize_all, BoundedFormula.realize_iff,
      BoundedFormula.realize_inf, AbstractMembership.realize_memberAt, Fin.snoc]
      using existsUnique_intersection he (fullZFC_model_separation hM _) (s 0) (s 1)
  | domain =>
    simpa [basicSetDefinitions, basicSetGraph, AlphaFormula.realize_mk,
      realize_boundedToNamed, BoundedFormula.realize_all, BoundedFormula.realize_iff,
      BoundedFormula.realize_ex, realize_internalApplicationFormula, AbstractMembership.realize_memberAt, Fin.snoc]
      using existsUnique_graphDomain he hu (fullZFC_model_separation hM _) (s 0)

/-- These are derivations in the book's proof system, obtained from its
proved completeness theorem, rather than assumed unique-existence specs. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Definitional extensions** introducing a new function or constant symbol, such as $\emptyset$, $\{a,b\}$, $\bigcup
        x$, $x\cap y$, and $\mathrm{dom}\,f$: the relevant \termuse{ZFC} axiom proves a $\forall \vec{x}\, \exists! y\,
        \varphi(\vec{x}, y)$ statement (existence), Extensionality supplies uniqueness, and adjoining a new function or
        constant symbol with defining property $\varphi$ gives a conservative extension.
-/
theorem basicSetDefinitions_proves_unique {n : ℕ} (f : BasicSetSymbol n) :
    ProvesFrom namedFullZFCTheory (basicSetDefinitions.uniqueExistence f) := by
  apply (proves_iff_small_model_consequence (fun _ h => namedFullZFCTheory_sentences h)
    (basicSetDefinitions.uniqueExistence_sentence f)).mpr
  intro M inst hne s hs
  let := inst
  have hM := fullZFC_model_of_named s hs
  have hall : ∀ t : ℕ → M,
      (AlphaFormula.uniqueAt n (n + 1) (basicSetDefinitions.graph f)).Realize t := by
    intro t
    apply (AlphaFormula.realize_uniqueAt _ _ _ (by omega) ?_ t).mpr
    · exact basicSetGraph_unique hM f t
    · intro hx
      have := Finset.mem_range.mp (basicSetDefinitions.freeVars f hx)
      omega
  exact ((AlphaFormula.forall_realize_closeAll n _).mpr hall) s

/-- Adding the five actual set operations creates no new membership-language
sentence theorems. -/
theorem basicSetDefinitions_conservative {σ : AlphaFormula membershipLanguage}
    (hσ : σ ∈ Sentences membershipLanguage)
    (hp : ProvesFrom (basicSetDefinitions.theory namedFullZFCTheory)
      (σ.mapLanguage FunctionDefinitions.inclusion)) : ProvesFrom namedFullZFCTheory σ :=
  basicSetDefinitions.conservative (fun _ h => namedFullZFCTheory_sentences h)
    (fun _ f => basicSetDefinitions_proves_unique f) hσ hp

/-- Inclusion is the displayed pure relation abbreviation. -/
inductive BasicSetRelation : ℕ → Type
  | subset : BasicSetRelation 2

def basicSetRelations : RelationDefinitions membershipLanguage BasicSetRelation where
  formula
    | .subset => .mk (boundedToNamed subsetBody)
  freeVars
    | .subset => boundedToNamed_fv subsetBody

/-- Relation inlining needs neither set-theoretic axioms nor closed formulas. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Relation abbreviations** (pure formula abbreviations), such as $\IncludedIn$ and $\exists!$: a new relation symbol
        is defined by an $L_\in$-formula. Always eliminable by inlining.
-/
theorem basicSetRelations_conservative {T : Set (AlphaFormula membershipLanguage)}
    {φ : AlphaFormula membershipLanguage}
    (hp : ProvesFrom (basicSetRelations.theory T)
      (φ.mapLanguage RelationDefinitions.inclusion)) : ProvesFrom T φ :=
  basicSetRelations.conservative_syntactic hp

/-- The same relation may also be added after the five function definitions. -/
def basicSetRelationsAfterFunctions :
    RelationDefinitions (membershipLanguage.sum (functionSymbols BasicSetSymbol)) BasicSetRelation where
  formula r := (basicSetRelations.formula r).mapLanguage FunctionDefinitions.inclusion
  freeVars r := by
    rw [AlphaFormula.fv_mapLanguage]
    exact basicSetRelations.freeVars r

/-- A concrete mixed extension of the literal ZFC theory is conservative. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Each abbreviation below is a conservative shorthand over $L_\in$, in the sense of the extension-by-definition framework
    of §{sec:definitional-extensions}; see also [@Shoenfield1967, §4.6]. They come in three kinds:
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Every $L_\in$-sentence provable using the new notation is already provable in ZFC, so we may use the symbols freely and
    unfold them only when proof-theoretic precision demands.
-/
theorem basicSetNotation_conservative {σ : AlphaFormula membershipLanguage}
    (hσ : σ ∈ Sentences membershipLanguage)
    (hp : ProvesFrom
      (basicSetRelationsAfterFunctions.theory (basicSetDefinitions.theory namedFullZFCTheory))
      (σ.mapLanguage (RelationDefinitions.inclusion.comp FunctionDefinitions.inclusion))) :
    ProvesFrom namedFullZFCTheory σ := by
  apply basicSetDefinitions_conservative hσ
  apply basicSetRelationsAfterFunctions.conservative_syntactic
  simpa only [AlphaFormula.mapLanguage_comp] using hp

end PolishSpaceBook.SetTheoryModels
