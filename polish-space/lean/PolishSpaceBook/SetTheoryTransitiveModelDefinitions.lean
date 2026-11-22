module

public import PolishSpaceBook.SetTheoryZFCConsistency

@[expose] public section

/-! # Set and class models with their actual relativized sentence semantics -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas
universe u

/-- A transitive set model of a specified theory or fragment. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{transitive model} is a transitive set or class $M$ in which the ZFC axioms (or some fragment) hold when
    relativized to $M$.
-/
def IsTransitiveSetModel (M : ZFSet.{u}) (T : membershipLanguage.Theory) : Prop :=
  M.IsTransitive ∧ M ⊨ T

/-- A class model quantifies over exactly the elements of the class. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{transitive model} is a transitive set or class $M$ in which the ZFC axioms (or some fragment) hold when
    relativized to $M$.
-/
def IsTransitiveClassModel (C : ZFClass.{u}) (T : membershipLanguage.Theory) : Prop :=
  (∀ x, C x → ∀ y ∈ x, C y) ∧ ClassDomain C ⊨ T

/-- Relativization interprets the same formula with only its quantifier domain changed. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{transitive model} is a transitive set or class $M$ in which the ZFC axioms (or some fragment) hold when
    relativized to $M$.
-/
theorem transitive_class_model_realizes {C : ZFClass.{u}} {T : membershipLanguage.Theory}
    (h : IsTransitiveClassModel C T) {φ : membershipLanguage.Sentence} (hφ : φ ∈ T) :
    ClassDomain C ⊨ φ := h.2.realize_of_mem φ hφ

end PolishSpaceBook.SetTheoryModels
