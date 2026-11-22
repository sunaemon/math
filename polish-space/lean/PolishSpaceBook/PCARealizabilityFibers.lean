module

public import PolishSpaceBook.PCARealizerAbstraction
public import PolishSpaceBook.HeytingPreorderQuotient
public import Mathlib.Order.Category.HeytAlg

@[expose] public section

/-! # Heyting fibers and reindexing for a general PCA -/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
open CategoryTheory Opposite
universe u v
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

structure IndexedPredicate (K : PartialCombinatoryAlgebra A) (I : Type v) where
  val : RealizabilityPredicate A I

instance predicatePreorder (I : Type v) : Preorder (IndexedPredicate K I) where
  le φ ψ := K.Entails φ.val ψ.val
  le_refl φ := K.entails_refl φ.val
  le_trans _ _ _ := K.entails_trans

instance predicateHeytingOps (I : Type v) : HeytingPreorderOps (IndexedPredicate K I) where
  meet φ ψ := ⟨K.predAnd φ.val ψ.val⟩
  join φ ψ := ⟨K.predOr φ.val ψ.val⟩
  imp φ ψ := ⟨K.predImp φ.val ψ.val⟩
  top := ⟨fun _ => Set.univ⟩
  bot := ⟨fun _ => ∅⟩
  le_meet _a b c := ⟨fun h => ⟨K.entails_trans h (K.and_left b.val c.val),
      K.entails_trans h (K.and_right b.val c.val)⟩,fun h => K.and_intro h.1 h.2⟩
  join_le a b _c := ⟨fun h => ⟨K.entails_trans (K.or_left a.val b.val) h,
      K.entails_trans (K.or_right a.val b.val) h⟩,fun h => K.or_elim h.1 h.2⟩
  imp_adj a b c := K.imp_adjunction a.val b.val c.val
  le_top φ := K.entails_top φ.val
  bot_le φ := K.bot_entails φ.val

abbrev Fiber (I : Type v) := Antisymmetrization (IndexedPredicate K I) (· ≤ ·)

def predicateClass {I : Type v} (φ : RealizabilityPredicate A I) : K.Fiber I :=
  toAntisymmetrization (· ≤ ·) ⟨φ⟩

def fiberReindex {I J : Type v} (f : I → J) : HeytingHom (K.Fiber J) (K.Fiber I) where
  toFun := Quotient.map (fun φ => ⟨realizabilityReindex f φ.val⟩)
    (fun _ _ h => ⟨K.reindex_entails f h.1,K.reindex_entails f h.2⟩)
  map_inf' a b := Quotient.inductionOn₂ a b (fun _ _ => rfl)
  map_sup' a b := Quotient.inductionOn₂ a b (fun _ _ => rfl)
  map_bot' := rfl
  map_himp' a b := Quotient.inductionOn₂ a b (fun _ _ => rfl)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Realizability operations over a PCA
-/
def indexedHeyting : (Type v)ᵒᵖ ⥤ HeytAlg.{max u v} where
  obj I := HeytAlg.of (K.Fiber I.unop)
  map f := HeytAlg.ofHom (K.fiberReindex f.unop)
  map_id I := by
    apply HeytAlg.ext
    intro a
    exact Quotient.inductionOn a (fun _ => rfl)
  map_comp f g := by
    apply HeytAlg.ext
    intro a
    exact Quotient.inductionOn a (fun _ => rfl)

end PolishSpaceBook.PartialCombinatoryAlgebra
