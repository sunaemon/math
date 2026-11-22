module

public import PolishSpaceBook.SetTheoryLevyHierarchy
public import PolishSpaceBook.SetTheoryTransitiveModelDefinitions

@[expose] public section

/-! # Low-level absoluteness after allowing ZFC-provably equivalent formulas -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas
universe u

/-- Absoluteness retains all parameters in the smaller domain. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A formula $\varphi$ is \termdefineas{absoluteness}{absolute} between transitive classes $M \IncludedIn N$ if
    $\varphi^M \leftrightarrow
    \varphi^N$ on parameters in $M$. The standard absoluteness theorem:
-/
def IsAbsoluteBetween (M N : ZFClass.{u}) (hMN : M ⊆ N)
    {n : ℕ} (φ : ForcingFormulas.Formula n) : Prop :=
  ∀ xs : Fin n → ClassDomain M,
    φ.Realize Empty.elim xs ↔ φ.Realize Empty.elim (inclusion hMN ∘ xs)

/-- Bounded formulas satisfy the book's parameter-preserving definition. -/
theorem delta_zero_isAbsoluteBetween (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) {n : ℕ} {φ : ForcingFormulas.Formula n}
    (hφ : IsDeltaZero φ) : IsAbsoluteBetween M N hMN φ :=
  delta_zero_absolute M N hMN hM hφ

/-- Infinity ensures that models of the actual ZFC theory have a nonempty domain. -/
theorem fullZFC_model_nonempty (M : Type*) [membershipLanguage.Structure M]
    (hM : M ⊨ fullZFCTheory) : Nonempty M := by
  have hi : M ⊨ infinitySentence := hM.realize_of_mem _ ZFCAxiom.infinity
  obtain ⟨x, _⟩ := (AbstractMembership.models_infinity_iff M).mp hi
  exact ⟨x⟩

/-- ZFC equivalence can be unfolded on both domains before applying raw Sigma-one absoluteness. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\Delta_0$ formulas are absolute between any two transitive models.
    *   $\Sigma_1$ formulas are upward absolute (preserved going from $M$ to $N \supseteq M$).
    *   $\Pi_1$ formulas are downward absolute.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a formula merely provably equivalent over ZFC to one of those forms, both domains must also satisfy
    axioms sufficient for that equivalence.
-/
theorem levySigma_one_upward (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : IsTransitiveClassModel M fullZFCTheory) (hN : IsTransitiveClassModel N fullZFCTheory)
    {n : ℕ} {φ : ForcingFormulas.Formula n} (hφ : LevySigma 1 φ)
    (xs : Fin n → ClassDomain M) :
    φ.Realize Empty.elim xs → φ.Realize Empty.elim (inclusion hMN ∘ xs) := by
  classical
  obtain ⟨ψ, hψ, heq⟩ := (levySigma_one_iff φ).mp hφ
  let dM := Classical.choice (fullZFC_model_nonempty (ClassDomain M) hM.2)
  let dN := Classical.choice (fullZFC_model_nonempty (ClassDomain N) hN.2)
  intro h
  apply (heq.sound_fin hN.2 dN (inclusion hMN ∘ xs)).mpr
  exact sigma_one_upward M N hMN hM.1 hψ xs ((heq.sound_fin hM.2 dM xs).mp h)

/-- The Pi-one direction likewise retains the proof-equivalence hypotheses in both domains. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\Delta_0$ formulas are absolute between any two transitive models.
    *   $\Sigma_1$ formulas are upward absolute (preserved going from $M$ to $N \supseteq M$).
    *   $\Pi_1$ formulas are downward absolute.
-/
theorem levyPi_one_downward (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : IsTransitiveClassModel M fullZFCTheory) (hN : IsTransitiveClassModel N fullZFCTheory)
    {n : ℕ} {φ : ForcingFormulas.Formula n} (hφ : LevyPi 1 φ)
    (xs : Fin n → ClassDomain M) :
    φ.Realize Empty.elim (inclusion hMN ∘ xs) → φ.Realize Empty.elim xs := by
  classical
  obtain ⟨ψ, hψ, heq⟩ := (levyPi_one_iff φ).mp hφ
  let dM := Classical.choice (fullZFC_model_nonempty (ClassDomain M) hM.2)
  let dN := Classical.choice (fullZFC_model_nonempty (ClassDomain N) hN.2)
  intro h
  apply (heq.sound_fin hM.2 dM xs).mpr
  exact pi_one_downward M N hMN hM.1 hψ xs ((heq.sound_fin hN.2 dN _).mp h)

end PolishSpaceBook.SetTheoryModels
