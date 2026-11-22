module

/-
Modified for the math-private book: ported Sven Manthe's formalization to Lean 4.35.0
and its mathlib. See README.md and UPSTREAM.json in the vendor root for provenance;
the original Apache-2.0 license is retained in LICENSE.
-/

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Category.Preorder
public import BorelDet.Basic.general

@[expose] public section

open Classical CategoryTheory

universe u u1 v1
variable {α C D : Type*} [Category C] [Category D]

@[congr] lemma inv_congr {X Y : C} (f g : X ⟶ Y) [IsIso f] (h : f = g) :
  inv f = inv g (I := by subst h; infer_instance) := by simp [h]

section Concrete
variable {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
@[simp] lemma hom_inv_id_apply {c d : C}
  (f : c ≅ d) (x : ToType d) : f.hom (f.inv x) = x := by
  rw [← ConcreteCategory.comp_apply]; simp
@[simp] lemma inv_hom_id_apply {c d : C}
  (f : c ≅ d) (x : ToType c) : f.inv (f.hom x) = x := by
  rw [← ConcreteCategory.comp_apply]; simp
@[simp] lemma cancel_inv_left {c d : C}
  (f : c ⟶ d) [IsIso f] (x : ToType c) : inv f (f x) = x := by
  rw [← ConcreteCategory.comp_apply]; simp
@[simp] lemma cancel_inv_right {c d : C}
  (f : c ⟶ d) [IsIso f] (x : ToType d) : f (inv f x) = x := by
  rw [← ConcreteCategory.comp_apply]; simp
end Concrete
lemma naturality_apply {FD : D → D → Type*} {CD : D → Type*}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
  {F G : C ⥤ D} (α : F ⟶ G) {c d : C} (f : c ⟶ d) (x : ToType (F.obj c)) :
  α.app d (F.map f x) = G.map f (α.app c x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, α.naturality]
@[simp] lemma cancel_inv_left_types {c d : Type u}
  (f : c ⟶ d) [IsIso f] (x : c) : inv f (f x) = x := by
  apply cancel_inv_left (C := Type u)
@[simp] lemma cancel_inv_right_types {c d : Type u}
  (f : c ⟶ d) [IsIso f] (x : d) : f (inv f x) = x := by
  apply cancel_inv_right (C := Type u)
lemma naturality_apply_types {F G : C ⥤ Type u} (α: F ⟶ G)
  {c d : C} (f : c ⟶ d) (x : F.obj c) :
  α.app d (F.map f x) = G.map f (α.app c x) := by
  apply naturality_apply (D := Type u)

@[simp] lemma cat_preimage_id {c : Type u} (x : Set c) :
  (𝟙 c)⁻¹' x = x := Set.preimage_id
@[simp] lemma cat_preimage_comp {c d e : Type u} (f : c ⟶ d) (g : d ⟶ e) (x : Set e) :
  (f ≫ g)⁻¹' x = f⁻¹' (g⁻¹' x) := Set.preimage_comp

@[simp] lemma cancel_inv_left'' {c d : Type u}
  (f : c ⟶ d) [IsIso f]: inv f ∘ f = id := by ext x; simp
@[simp] lemma cancel_inv_right'' {c d : Type u}
  (f : c ⟶ d) [IsIso f]: f ∘ inv f = id := by ext x; simp
lemma iso_cancel_comp {a b c : Type u} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (x : b)
  [IsIso f] [IsIso h] (hc : f ≫ g = h) : inv h (g x) = inv f x := by
  have := IsIso.of_isIso_fac_left hc
  subst hc; simp

instance : Mono (X := α) (↾Option.some) := (mono_iff_injective (↾some)).mpr (Option.some_injective α)
instance {J} [Category J] {F} :
    Nonempty (Limits.IsColimit (Limits.Types.colimitCocone (J := J) F)) :=
  ⟨Limits.Types.colimitCoconeIsColimit F⟩

def coproductColimitCocone {J : Type u1} (F : Discrete J ⥤ Type _) :
    Limits.ColimitCocone F where
  cocone :=
    { pt := Σj, F.obj j
      ι := Discrete.natTrans (fun j => ↾fun x => ⟨j, x⟩)}
  isColimit :=
    { desc := fun s => ↾fun x => s.ι.app x.1 x.2
      uniq := fun s m w => ConcreteCategory.hom_ext _ _ fun ⟨j, x⟩ ↦ ConcreteCategory.congr_hom (w j) x }
lemma isCoprod_type_iff {J : Type u1} {F : Discrete J ⥤ Type (max u1 v1)} (t : Limits.Cocone F) :
    Nonempty (Limits.IsColimit t)
    ↔ (∀ i, Mono (t.ι.app i)) ∧ Set.univ.PairwiseDisjoint (fun i ↦ Set.range (t.ι.app i))
    ∧ ∀ y, ∃ i x, t.ι.app i x = y := by
  constructor
  · intro ⟨h⟩; constructor
    · intro i
      let s : Limits.Cocone F := {
        pt := Option (F.obj i)
        ι := Discrete.natTrans (fun j ↦
          if h : i = j then by subst h; exact ↾Option.some else ↾fun _ ↦ Option.none)
      }
      suffices Mono (t.ι.app i ≫ h.desc s) by apply mono_of_mono (t.ι.app i) (h.desc s)
      simp [s]; infer_instance
    · constructor
      · apply (pairwiseDisjoint_iff _).mpr; intros i x j y he
        let s : Limits.Cocone F := {
          pt := Option (F.obj i ⊕ F.obj j)
          ι := Discrete.natTrans (fun k ↦
            if h : i = k then by subst h; exact ↾(Option.some ∘ Sum.inl) else
            if h : j = k then by subst h; exact ↾(Option.some ∘ Sum.inr) else ↾fun _ ↦ Option.none)
        }
        replace he : (t.ι.app i ≫ h.desc s) x = (t.ι.app j ≫ h.desc s) y := congr_arg (h.desc s) he
        rw [h.fac, h.fac] at he; by_contra h; simp [s, h] at he
      exact Limits.Types.jointly_surjective F h
  · rintro ⟨h1, h2, h3⟩
    let s := coproductColimitCocone F
    have := Nonempty.intro s.2
    suffices s.1 ≅ t by exact (Limits.IsColimit.equivIsoColimit this.symm).nonempty
    apply Limits.Cocone.ext; swap
    let f : s.1.pt ⟶ t.pt := ↾fun ⟨i, x⟩ ↦ t.ι.app i x
    have : IsIso f := by
      rw [isIso_iff_bijective]; constructor
      · intro ⟨i, x⟩ ⟨j, y⟩ h; have he := ((pairwiseDisjoint_iff _).mp h2) h
        subst he; suffices x = y by subst this; rfl
        exact (mono_iff_injective _).mp (h1 i) h
      · intro y; obtain ⟨i, x, h⟩ := h3 y; exact ⟨⟨i, x⟩, h⟩
    exact asIso f; aesop_cat
lemma colim_isIso --exists?
  {F G : C ⥤ D} {s : Limits.Cocone F} {t : Limits.Cocone G}
  (hs : Limits.IsColimit s) (ht : Limits.IsColimit t) (f : F ≅ G) : IsIso (hs.map t f.hom) := by
  use ht.map s (f.inv); constructor <;>
    (apply Limits.IsColimit.hom_ext (by assumption); simp)
lemma coprod_type_isIso_iff {J : Type u1} {F G : Discrete J ⥤ Type (max u1 v1)}
  {s : Limits.Cocone F} {t : Limits.Cocone G} (hs : Limits.IsColimit s) (ht : Limits.IsColimit t)
  (f : ∀ j, F.obj ⟨j⟩ ⟶ G.obj ⟨j⟩) :
  IsIso (hs.map t (Discrete.natTrans (fun ⟨j⟩ ↦ f j))) ↔ ∀ j, IsIso (f j) := by
  let df := Discrete.natTrans (fun ⟨j⟩ ↦ f j)
  let ⟨_, _, h3⟩ := (isCoprod_type_iff s).mp (Nonempty.intro hs)
  let ⟨_, h2, _⟩ := (isCoprod_type_iff t).mp (Nonempty.intro ht)
  constructor <;> intro hi; swap
  · have : ∀ j, IsIso (df.app j) := fun ⟨j⟩ ↦ hi j
    have := NatIso.isIso_of_isIso_app df
    exact colim_isIso hs ht (asIso df)
  · intro j; apply (isIso_iff_bijective (f j)).mpr; constructor
    · suffices Mono (f j) by exact injective_of_mono (f j)
      have h : Mono (s.ι.app ⟨j⟩ ≫ hs.map t df) := by apply mono_comp
      simp [df] at h; exact mono_of_mono _ (t.ι.app ⟨j⟩)
    · intro y; obtain ⟨i, x, h⟩ := h3 (inv (hs.map t df) (t.ι.app ⟨j⟩ y))
      have h' : (s.ι.app i ≫ hs.map t df) x = (inv (hs.map t df) ≫ hs.map t df) (t.ι.app ⟨j⟩ y) :=
        congr_arg (hs.map t df) h
      simp [- types_comp_apply] at h'
      have heq : i = ⟨j⟩ := (pairwiseDisjoint_iff _).mp h2 h'
      subst heq; exact ⟨x, injective_of_mono (t.ι.app ⟨j⟩) h'⟩
