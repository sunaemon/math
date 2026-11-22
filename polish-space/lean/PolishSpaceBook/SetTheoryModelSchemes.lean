module

public import PolishSpaceBook.SetTheoryModelClosure
public import PolishSpaceBook.SetTheoryAbsoluteness

@[expose] public section

/-!
# Separation and Replacement in transitive models

Instances are actual first-order sentences with a finite tuple of parameters.
Variable reindexing keeps the source formula separate from the surrounding
quantifiers of each schema.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Substitute in-scope variables without changing the membership-language formula. -/
def reindex {m n : ℕ} (φ : ForcingFormulas.Formula m) (ρ : Fin m → Fin n) :
    ForcingFormulas.Formula n :=
  BoundedFormula.relabel (Sum.elim Empty.elim (fun i => Sum.inr (ρ i))) φ.toFormula

namespace AbstractMembership

lemma realize_reindex (S : Type u) [membershipLanguage.Structure S] {m n : ℕ} (φ : ForcingFormulas.Formula m)
    (ρ : Fin m → Fin n) (v : Empty → S) (xs : Fin n → S) :
    (reindex φ ρ).Realize v xs ↔ φ.Realize v (xs ∘ ρ) := by
  rw [reindex, BoundedFormula.realize_relabel]
  rw [Subsingleton.elim (xs ∘ Fin.natAdd n) (default : Fin 0 → S)]
  change φ.toFormula.Realize (M := S)
    (Sum.elim v (xs ∘ Fin.castAdd 0) ∘ Sum.elim Empty.elim (fun i => Sum.inr (ρ i))) ↔ _
  rw [BoundedFormula.realize_toFormula]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.castAdd_zero]
  exact Iff.of_eq (congrArg (fun w => φ.Realize w (xs ∘ ρ)) (Subsingleton.elim _ v))

end AbstractMembership

lemma realize_reindex (S : ZFSet.{u}) {m n : ℕ} (φ : ForcingFormulas.Formula m)
    (ρ : Fin m → Fin n) (v : Empty → S) (xs : Fin n → S) :
    (reindex φ ρ).Realize v xs ↔ φ.Realize v (xs ∘ ρ) :=
  AbstractMembership.realize_reindex S φ ρ v xs

lemma apply_snoc {α β : Type*} {n : ℕ} (f : α → β) (ρ : Fin n → α) (a : α) :
    (fun i : Fin (n + 1) => f (Fin.snoc (α := fun _ => α) ρ a i)) =
      Fin.snoc (α := fun _ => β) (fun i => f (ρ i)) (f a) :=
  Fin.comp_snoc f ρ a

/-- The instance with parameters first and the tested element last. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    **Separation as a derived schema.** The Separation schema says that for any formula $\varphi(z,\vec p)$, with parameters
    $\vec p$ allowed and with $y$ not free in $\varphi$, the subset $\{z \in x : \varphi(z,\vec p)\}$ exists:
    $$\forall \vec p\,\forall x\, \exists y\, \forall z\,(z \in y \leftrightarrow z \in x \land \varphi(z,\vec p)).$$
-/
def separationSentence {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    membershipLanguage.Sentence :=
  (((memberAt (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc).iff
    (memberAt (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc ⊓
      reindex φ (Fin.snoc (fun i => i.castSucc.castSucc.castSucc) (Fin.last (n + 2))))).all.ex.all).alls

/-- For every input in the set there is exactly one output in the model. -/
def replacementTotal {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 1) :=
  ((memberAt (Fin.last (n + 1)) (Fin.last n).castSucc).imp
    ((reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n + 1)).castSucc) (Fin.last (n + 2)))) ⊓
      ((reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 1)).castSucc.castSucc) (Fin.last (n + 3)))).imp
        (equalAt (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc)).all).ex).all

/-- The internal image contains exactly the outputs of inputs in the set. -/
def replacementImage {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 1) :=
  (((memberAt (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc).iff
    ((memberAt (Fin.last (n + 3)) (Fin.last n).castSucc.castSucc.castSucc) ⊓
      reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 3))) (Fin.last (n + 2)).castSucc)).ex).all).ex

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    *   **Replacement.** Replacement is a schema: one instance per formula $\varphi$, in which parameters are allowed. The
        image of a set under a definable function is a set: $\forall \vec p\,\forall x\, [(\forall a \in x\, \exists!\, b\,
        \varphi(a,b,\vec p)) \to \exists y\, \forall b\,(b \in y \leftrightarrow \exists a \in x\, \varphi(a,b,\vec p))]$.
-/
def replacementSentence {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    membershipLanguage.Sentence := ((replacementTotal φ).imp (replacementImage φ)).all.alls

namespace AbstractMembership

lemma realize_separation (S : Type u) [membershipLanguage.Structure S] {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    S ⊨ separationSentence φ ↔ ∀ ps : Fin n → S, ∀ x : S, ∃ y : S, ∀ z : S,
      member z y ↔ member z x ∧ φ.Realize Empty.elim (Fin.snoc ps z) := by
  simp only [separationSentence, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, realize_memberAt, realize_reindex, apply_snoc,
    Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]
  simp only [Subsingleton.elim (default : Empty → S) Empty.elim]

end AbstractMembership

lemma realize_separation (S : ZFSet.{u}) {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    S ⊨ separationSentence φ ↔ ∀ ps : Fin n → S, ∀ x : S, ∃ y : S, ∀ z : S,
      z.val ∈ y.val ↔ z.val ∈ x.val ∧ φ.Realize Empty.elim (Fin.snoc ps z) :=
  AbstractMembership.realize_separation S φ

namespace AbstractMembership

lemma realize_replacementTotal (S : Type u) [membershipLanguage.Structure S] {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (v : Empty → S) (ps : Fin n → S) (x : S) :
    (replacementTotal φ).Realize v (Fin.snoc ps x) ↔
      ∀ a : S, member a x → ∃! b : S, φ.Realize v (Fin.snoc (Fin.snoc ps a) b) := by
  simp only [replacementTotal, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, realize_memberAt, realize_equalAt,
    realize_reindex, apply_snoc, Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last, ExistsUnique]

end AbstractMembership

lemma realize_replacementTotal (S : ZFSet.{u}) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (v : Empty → S) (ps : Fin n → S) (x : S) :
    (replacementTotal φ).Realize v (Fin.snoc ps x) ↔
      ∀ a : S, a.val ∈ x.val → ∃! b : S, φ.Realize v (Fin.snoc (Fin.snoc ps a) b) :=
  AbstractMembership.realize_replacementTotal S φ v ps x

namespace AbstractMembership

lemma realize_replacementImage (S : Type u) [membershipLanguage.Structure S] {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (v : Empty → S) (ps : Fin n → S) (x : S) :
    (replacementImage φ).Realize v (Fin.snoc ps x) ↔
      ∃ y : S, ∀ b : S, member b y ↔
        ∃ a : S, member a x ∧ φ.Realize v (Fin.snoc (Fin.snoc ps a) b) := by
  simp only [replacementImage, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, realize_memberAt,
    realize_reindex, apply_snoc, Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]

end AbstractMembership

lemma realize_replacementImage (S : ZFSet.{u}) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (v : Empty → S) (ps : Fin n → S) (x : S) :
    (replacementImage φ).Realize v (Fin.snoc ps x) ↔
      ∃ y : S, ∀ b : S, b.val ∈ y.val ↔
        ∃ a : S, a.val ∈ x.val ∧ φ.Realize v (Fin.snoc (Fin.snoc ps a) b) :=
  AbstractMembership.realize_replacementImage S φ v ps x

namespace AbstractMembership

lemma realize_replacement (S : Type u) [membershipLanguage.Structure S] {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    S ⊨ replacementSentence φ ↔ ∀ ps : Fin n → S, ∀ x : S,
      (∀ a : S, member a x → ∃! b : S, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) →
      ∃ y : S, ∀ b : S, member b y ↔
        ∃ a : S, member a x ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  simp only [replacementSentence, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_replacementTotal, realize_replacementImage]
  simp only [Subsingleton.elim (default : Empty → S) Empty.elim]

end AbstractMembership

lemma realize_replacement (S : ZFSet.{u}) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    S ⊨ replacementSentence φ ↔ ∀ ps : Fin n → S, ∀ x : S,
      (∀ a : S, a.val ∈ x.val → ∃! b : S, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) →
      ∃ y : S, ∀ b : S, b.val ∈ y.val ↔
        ∃ a : S, a.val ∈ x.val ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) :=
  AbstractMembership.realize_replacement S φ

end PolishSpaceBook.SetTheoryModels
