module

/-
Modified for the math-private book: ported Sven Manthe's formalization to Lean 4.35.0
and its mathlib. See README.md and UPSTREAM.json in the vendor root for provenance;
the original Apache-2.0 license is retained in LICENSE.
-/

public import BorelDet.Tree.len_tree_hom

@[expose] public section

namespace Descriptive.Tree
open CategoryTheory Descriptive

noncomputable section
/-- A tree with a chosen base node -/
abbrev PointedTrees := Σ (T : Trees), T

/-- a base node preserving morphism of trees -/
@[ext (flat := false)] structure PointedLenHom (S T : PointedTrees)
  extends Tree.LenHom S.1 T.1 where
  hp : toFun S.2 = T.2
variable {S T : PointedTrees} {n : ℕ}
namespace PointedLenHom
def toHom (f : PointedLenHom S T) : S.1 ⟶ T.1 := f.toLenHom
instance : FunLike (PointedLenHom S T) S.1 T.1 where
  coe f := f.toHom
  coe_injective _ _ h := PointedLenHom.ext <| LenHom.ext h
instance : OrderHomClass (PointedLenHom S T) S.1 T.1 where
  map_rel f _ _ h := f.toOrderHom.monotone' h
@[simp] lemma add_toHom (f : PointedLenHom S T) (x : S.1) :
  f x = f.toHom x := rfl

/-- The category of trees with a chosen base node -/
instance : Category PointedTrees where
  Hom S T := PointedLenHom S T
  id S := ⟨𝟙 S.1, rfl⟩
  comp f g := ⟨f.toHom ≫ g.toHom, (congrArg g.toFun f.hp).trans g.hp⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
variable {S T : PointedTrees}
@[ext] lemma ext' {f g : S ⟶ T} (h : f.toLenHom = g.toLenHom) : f = g :=
  PointedLenHom.ext h
@[simp] lemma rem_pointedLenHom : PointedLenHom S T = (S ⟶ T) := rfl
@[simp] lemma rem_toLenHom' (f : S ⟶ T) x :
  DFunLike.coe (F := S.1 ⟶ T.1) f.toLenHom x = f.toHom x := rfl
@[simp] lemma pair_toHom (f : S.1 ⟶ T.1) hf :
  PointedLenHom.toHom ⟨f, hf⟩ = f := rfl
@[simp] lemma hp_simp (f : S ⟶ T) : f.toHom S.2 = T.2 := f.hp
@[simp] lemma id_toLenHom (S : PointedTrees) : (𝟙 S : S ⟶ S).toHom = 𝟙 S.1 := rfl
@[simp] lemma comp_toLenHom {S T U : PointedTrees} (f : S ⟶ T) (g : T ⟶ U) :
  (f ≫ g).toHom = f.toHom ≫ g.toHom := rfl
end PointedLenHom
abbrev forgetPoint : PointedTrees ⥤ Trees where
  obj A := A.1
  map f := f.toHom
instance : forgetPoint.ReflectsIsomorphisms where
  reflects := by
    intro _ _ f _
    use ⟨inv (forgetPoint.map f), by rw [← f.hp]; apply cancel_inv_left⟩
    constructor <;> (ext x; simp)

@[simp] lemma pointed_isIso_iff {S T : PointedTrees} (f : S ⟶ T) :
  IsIso f ↔ IsIso (forgetPoint.map f) := (isIso_iff_of_reflects_iso f _).symm

section
variable {S T : Trees} {x : List S.1} {a : S.1} (f : S ⟶ T) (hx : x ++ [a] ∈ S.2)
lemma apply_concat :
  ∃ b, (f ⟨_, hx⟩).val = (f ⟨x, mem_of_append hx⟩).val ++ [b] := by
  let ⟨lb, (hlb : (f _).val = (f _).val ++ _)⟩ := apply_append f.toOrderHom hx
  replace hbl := congr_arg List.length hlb
  simp only [LenHom.h_length_simp, List.length_append, List.length_singleton,
    add_right_inj] at hbl
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hbl.symm; use b
def concat : T.1 := (apply_concat f hx).choose
lemma concat_spec :
  (f ⟨_, hx⟩).val = (f ⟨x, mem_of_append hx⟩).val ++ [concat f hx] :=
  (apply_concat f hx).choose_spec
lemma concat_elem :
  (f ⟨x, mem_of_append hx⟩).val ++ [concat f hx] ∈ T.2 := by
  rw [← concat_spec]; apply SetLike.coe_mem
lemma concat_spec' :
  f ⟨_, hx⟩ = ⟨(f ⟨x, mem_of_append hx⟩).val ++ [concat f hx], concat_elem f hx⟩ := by
  ext1; apply concat_spec
lemma concat_uniq b (hb : (f ⟨x, mem_of_append hx⟩).val ++ [b] = (f ⟨_, hx⟩).val) :
  concat f hx = b := by
  symm; rwa [← List.singleton_inj, ← List.append_right_inj, ← concat_spec]
end

@[implicit_reducible] def extensions : PointedTrees ⥤ Type* where
  obj T := { a : T.1.1 | T.2.val ++ [a] ∈ T.1.2 }
  map f := ↾fun a => ⟨concat (forgetPoint.map f) a.prop, by
    dsimp only [Set.mem_ofPred_eq]; erw [← f.hp, ← concat_spec]; apply SetLike.coe_mem⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change concat (𝟙 T.1) a.prop = a.val
    apply concat_uniq
    rfl
  map_comp {S T U} f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    have hbase : f.toHom S.2 = T.2 := f.hp
    have hb : T.2.val ++ [concat f.toHom a.prop] ∈ T.1.2 := by
      have h := concat_elem f.toHom a.prop
      change (f.toHom S.2).val ++ [concat f.toHom a.prop] ∈ T.1.2 at h
      rwa [hbase] at h
    change concat (f.toHom ≫ g.toHom) a.prop = concat g.toHom hb
    apply concat_uniq
    have hf : f.toHom ⟨S.2.val ++ [a.val], a.prop⟩ =
        ⟨T.2.val ++ [concat f.toHom a.prop], hb⟩ := by
      apply Subtype.ext
      have h := concat_spec f.toHom a.prop
      change (f.toHom ⟨S.2.val ++ [a.val], a.prop⟩).val =
        (f.toHom S.2).val ++ [concat f.toHom a.prop] at h
      rwa [hbase] at h
    change (g.toHom (f.toHom S.2)).val ++ [concat g.toHom hb] =
      (g.toHom (f.toHom ⟨S.2.val ++ [a.val], a.prop⟩)).val
    rw [hbase, hf]
    exact (concat_spec g.toHom hb).symm

def extensions.val' {T : PointedTrees} (a : extensions.obj T) : List T.1.1 :=
  T.2.val ++ [a.val]
@[simps] def extensions.valT' {T : PointedTrees} (a : extensions.obj T) : T.1 :=
  ⟨extensions.val' a, a.prop⟩
@[simp] lemma extensions_map_val' {S T : PointedTrees}
  (f : S ⟶ T) (a : extensions.obj S) :
  extensions.val' (extensions.map f a) = (f.toHom ⟨extensions.val' a, a.prop⟩).val := by
  simp [extensions.val', extensions, concat_spec']
@[simp] lemma extensions_map_valT' {S T : PointedTrees}
  (f : S ⟶ T) (a : extensions.obj S) :
  extensions.valT' (extensions.map f a) = f.toHom ⟨extensions.val' a, a.prop⟩ :=
  tree_ext (extensions_map_val' f a)
abbrev mkPointed {T : Trees} (x : T) : PointedTrees := ⟨T, x⟩
def mkPointedMor {S T : Trees} (f : S ⟶ T) (x : S) :
  mkPointed x ⟶ mkPointed (f x) := ⟨f, rfl⟩

namespace ExtensionsAt
variable {S T : Trees} (f : S ⟶ T) {x : T}
lemma eq_obj (x : T) : ExtensionsAt x = extensions.obj (mkPointed x) := rfl
abbrev map ⦃x : S⦄ ⦃y : T⦄ (h : f x = y) (a : ExtensionsAt x) : ExtensionsAt y :=
  extensions.map (X := mkPointed x) (Y := mkPointed y) ⟨f, h⟩ a
@[simp] lemma map_val' ⦃x : S⦄ ⦃y : T⦄
  (h : f x = y) (a : ExtensionsAt x) : (map f h a).val' (A := no_index _) = (f a.valT').val :=
  extensions_map_val' (S := mkPointed x) (T := mkPointed y) ⟨f, h⟩ a
@[simp] lemma map_valT' ⦃x : S⦄ ⦃y : T⦄ (h : f x = y) (a : ExtensionsAt x) :
  (map f h a).valT' (A := no_index _) = f a.valT' :=
  extensions_map_valT' (S := mkPointed x) (T := mkPointed y) ⟨f, h⟩ a
end ExtensionsAt

end
end Descriptive.Tree
