module

/-
Modified for the math-private book: ported Sven Manthe's formalization to Lean 4.35.0
and its mathlib. See README.md and UPSTREAM.json in the vendor root for provenance;
the original Apache-2.0 license is retained in LICENSE.
-/

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Topology.Category.TopCat.Basic
public import BorelDet.Tree.trees
public import BorelDet.Basic.misc_cat

@[expose] public section

open CategoryTheory

namespace Descriptive.Tree
noncomputable section

/-- The objects of the category of trees -/
abbrev Trees := Σ A, tree A
variable {S T U : Trees}
/-- The morphisms in the category of trees, length-preserving order-preserving maps -/
@[ext] structure LenHom (S T : Trees) extends OrderHom S.2 T.2 where
  h_length : ∀ x : S.2, (toFun x).val.length = x.val.length

/-- The category of trees has as objects trees in some set of nodes and as morphisms
  length-preserving order-preserving maps. It is a topos (although this fact is not
  proved here). Namely, the map to Presheaves on ℕ such that evaluation becomes resEq
  and the transition maps are given by `List.take` induces an equivalence -/
@[reducible] instance : Category Trees where
  Hom := LenHom
  id S := ⟨OrderHom.id, fun _ ↦ rfl⟩
  comp f g := ⟨g.toOrderHom.comp f.toOrderHom, fun h ↦ by erw [g.h_length, f.h_length]⟩
def forget_PO : Trees ⥤ PartOrd where
  obj T := { carrier := T.2 }
  map f := PartOrd.ofHom f.toOrderHom
instance : forget_PO.Faithful where
  map_injective {_ _} _ _ h := LenHom.ext (congr_arg (OrderHom.toFun ∘ PartOrd.Hom.hom) h)
instance : CoeSort Trees (Type _) where coe T := T.2
instance : FunLike (LenHom S T) S.2 T.2 where
  coe f := f.toFun
  coe_injective _ _ h := LenHom.ext h
@[reducible] instance : ConcreteCategory Trees LenHom where
  hom f := f
  ofHom f := f
instance : FunLike (S ⟶ T) S.2 T.2 where
  coe f := f.toFun
  coe_injective _ _ h := LenHom.ext h
@[macro_inline] instance (priority := 2000) : CoeFun (S ⟶ T) (fun _ => S → T) where
  coe f := DFunLike.coe (F := S ⟶ T) f
lemma concrete_hom_eq (f : S ⟶ T) : ConcreteCategory.hom f = f := rfl
instance : OrderHomClass (S ⟶ T) S.2 T.2 where
  map_rel f _ _ h := f.toOrderHom.monotone' h

@[simp] lemma rem_lenHom : LenHom S T = (S ⟶ T) := rfl
@[simp] lemma rem_trees_snd : (S.2 : Type _) = S := rfl
@[ext] lemma tree_ext {x y : S} (h : x.val = y.val) : x = y := Subtype.ext h
instance : PartialOrder S := inferInstanceAs (PartialOrder S.2)
@[simp] lemma le_def_trees (x y : T) : x ≤ y ↔ x.val <+: y.val := Iff.rfl
@[simp] lemma rem_toOrderHom (f : S ⟶ T) :
  DFunLike.coe (F := S →o T) f.toOrderHom = f := rfl
lemma rem_toFun (f : S ⟶ T) (x : S) : f.toFun x = f x := rfl
@[simp] lemma forget_map (f : S ⟶ T) : (forget Trees).map f = ↾f.toFun := rfl

@[simp] lemma tree_id_apply (x : S) : (𝟙 S) x = x := rfl
@[simp] lemma tree_comp_apply (f : S ⟶ T) (g : T ⟶ U) (x : S) :
    (f ≫ g) x = g (f x) := rfl
@[simp] lemma cancel_inv_left (f : S ⟶ T) [IsIso f] (x : S) : inv f (f x) = x :=
  _root_.cancel_inv_left f x
@[simp] lemma cancel_inv_right (f : S ⟶ T) [IsIso f] (x : T) : f (inv f x) = x :=
  _root_.cancel_inv_right f x

namespace LenHom
lemma id_toFun (S : Trees) : (𝟙 S : S ⟶ S).toFun = _root_.id := rfl
lemma comp_toFun (f : S ⟶ T) (g : T ⟶ U) :
  (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl
instance {S T : Trees} (f : S ⟶ T) [IsIso f] : IsIso (C := Type*) (↾f.toFun) :=
  inferInstanceAs (IsIso ((forget Trees).map f))
lemma inv_toFun {S T : Trees} (f : S ⟶ T) [IsIso f] :
  (inv f).toFun = (inv (C := Type*) (↾f.toFun) : T → S) :=
  congrArg (fun h : (T : Type _) ⟶ (S : Type _) => (h : T → S))
    (IsIso.Iso.inv_hom ((forget Trees).mapIso (asIso f))).symm

@[simp, simp_lengths] lemma h_length_simp (f : S ⟶ T) (x : S) :
  (f x).val.length (α := no_index _) = x.val.length (α := no_index _) := f.h_length x
@[simp] lemma h_length_inv (f : S ⟶ T) [IsIso (C := Type*) (↾f.toFun)] (x : T) :
  (inv (C := Type _) (↾f.toFun) x).val.length = x.val.length := by
  calc
    _ = (f (inv (C := Type _) (↾f.toFun) x)).val.length := (f.h_length _).symm
    _ = _ := congrArg (fun y : T => y.val.length) (cancel_inv_right_types (↾f.toFun) x)
@[simp] lemma map_nil (f : S ⟶ T) (h : [] ∈ S.2) : (f ⟨[], h⟩).val = [] := by
  apply List.eq_nil_of_length_eq_zero
  exact f.h_length ⟨[], h⟩
lemma map_ne_nil (f : S ⟶ T) {x : S} (h : x.val ≠ []) : (f x).val ≠ [] := by
  intro h'
  apply h; apply List.eq_nil_of_length_eq_zero
  rw [← h_length_simp f x, h']; rfl

lemma mk_eval (S T : Trees) (f : S → T) hf1 hf2 (x : S) :
  DFunLike.coe (F := S ⟶ T) (no_index ⟨⟨f, hf1⟩, hf2⟩) x = f x := rfl
end LenHom

lemma take_apply (f : S ⟶ T) (n : ℕ) (x : S) :
  f (take n x) = take n (f x) := by
  ext1; apply List.IsPrefix.eq_of_length
  · have hp : (f (take n x)).val <+: (f x).val :=
      f.toOrderHom.monotone' (a := take n x) (b := x) (List.take_prefix n x.val)
    change (f (take n x)).val <+: List.take n (f x).val
    rw [List.prefix_take_iff]
    exact ⟨hp, by rw [LenHom.h_length_simp]; exact List.length_take_le _ _⟩
  · simp only [LenHom.h_length_simp, take_coe, List.length_take]
lemma take_apply_val (f : S ⟶ T) (n : ℕ) (x : S) :
  (f (take n x)).val = (f x).val.take n :=
  congr_arg Subtype.val (take_apply f n x)
lemma prefix_iff (f : S ⟶ T) x y (hf : Function.Injective f) :
  f x ≤ f y ↔ x ≤ y := by
  constructor <;> intro h
  · have he : f x = f (take x.val.length y) := by
      apply Subtype.ext
      rw [take_apply_val, ← f.h_length x]
      exact List.prefix_iff_eq_take.mp h
    have he' := congrArg Subtype.val (hf he)
    change x.val <+: y.val
    rw [he']; exact List.take_prefix _ _
  · exact f.monotone' h

instance : (forget Trees).ReflectsIsomorphisms where
  reflects := by
    intro S T f _; constructor
    have : IsIso (C := Type _) (↾f.toFun) := by show IsIso ((forget Trees).map f); infer_instance
    use {
      toFun := inv (C := Type _) (↾f.toFun)
      monotone' := by
        intro a b h
        apply (prefix_iff f _ _ ((isIso_iff_bijective (↾f.toFun)).mp inferInstance).1).mp
        rw [show f (inv (↾f.toFun) a) = a from cancel_inv_right_types (↾f.toFun) a,
          show f (inv (↾f.toFun) b) = b from cancel_inv_right_types (↾f.toFun) b]
        exact h
      h_length := LenHom.h_length_inv _
    }
    constructor <;> apply LenHom.ext <;> funext x
    · exact cancel_inv_left_types (↾f.toFun) x
    · exact cancel_inv_right_types (↾f.toFun) x

end

end Descriptive.Tree
