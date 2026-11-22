module

public import PolishSpaceBook.SetTheoryLevyBoundedClosure
public import PolishSpaceBook.SetTheoryAbstractCollection

@[expose] public section

/-! # Bounded quantifier closure from the actual ZFC axioms

The Collection hypothesis in the intermediate prenex argument is discharged by
the arbitrary-model theorem derived from internal ranks and hierarchy stages.
Every equivalence used here is a derivation in `namedFullZFCTheory`.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas

theorem fullZFC_collectionSchema : FullZFCCollectionSchema := by
  intro M inst hM n φ ps A ht
  exact AbstractMembership.fullZFC_collection hM φ ps A ht

theorem zfc_boundedAll_ex {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 2)) :
    ZFCFormulaEquivalent (boundedAll i φ.ex) (levyCollectionMatrix i φ).ex :=
  zfc_boundedAll_ex_of_collection fullZFC_collectionSchema i φ

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For every $n\in\NN$, each of $\Sigma_n$, $\Pi_n$, and $\Delta_n$ is closed under bounded universal and existential
    quantification, with all other parameters retained. At positive levels the required equivalences are provable in ZFC.
-/
theorem LevyClass.boundedAll {p : LevyPolarity} {k n : ℕ}
    {φ : ForcingFormulas.Formula (n + 1)} (h : LevyClass p k φ) (i : Fin n) :
    LevyClass p k (boundedAll i φ) :=
  (levy_boundedQuantifiers_of_collection fullZFC_collectionSchema k h i).1

theorem LevyClass.boundedExists {p : LevyPolarity} {k n : ℕ}
    {φ : ForcingFormulas.Formula (n + 1)} (h : LevyClass p k φ) (i : Fin n) :
    LevyClass p k (boundedExists i φ) :=
  (levy_boundedQuantifiers_of_collection fullZFC_collectionSchema k h i).2

theorem LevySigma.boundedAll {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevySigma k φ) (i : Fin n) : LevySigma k (boundedAll i φ) :=
  LevyClass.boundedAll h i

theorem LevySigma.boundedExists {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevySigma k φ) (i : Fin n) : LevySigma k (boundedExists i φ) :=
  LevyClass.boundedExists h i

theorem LevyPi.boundedAll {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevyPi k φ) (i : Fin n) : LevyPi k (boundedAll i φ) :=
  LevyClass.boundedAll h i

theorem LevyPi.boundedExists {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevyPi k φ) (i : Fin n) : LevyPi k (boundedExists i φ) :=
  LevyClass.boundedExists h i

theorem LevyDelta.boundedAll {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevyDelta k φ) (i : Fin n) : LevyDelta k (boundedAll i φ) :=
  (levyDelta_boundedQuantifiers_of_collection fullZFC_collectionSchema k h i).1

theorem LevyDelta.boundedExists {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevyDelta k φ) (i : Fin n) : LevyDelta k (boundedExists i φ) :=
  (levyDelta_boundedQuantifiers_of_collection fullZFC_collectionSchema k h i).2

/-- Positive Sigma formulas admit one leading existential quantifier, up to
an actual ZFC derivation, with a matrix at the preceding Pi level. -/
theorem LevySigma.single_exists {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (h : LevySigma (k + 1) φ) :
    ∃ ψ : ForcingFormulas.Formula (n + 1), LevyPi k ψ ∧ ZFCFormulaEquivalent φ ψ.ex :=
  levySigma_single (fun h i => LevyPi.boundedExists h i) h

end PolishSpaceBook.SetTheoryModels
