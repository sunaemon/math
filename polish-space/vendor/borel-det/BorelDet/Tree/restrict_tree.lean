module

/-
Modified for the math-private book: ported Sven Manthe's formalization to Lean 4.35.0
and its mathlib. See README.md and UPSTREAM.json in the vendor root for provenance;
the original Apache-2.0 license is retained in LICENSE.
-/

public import BorelDet.Tree.len_tree_hom

@[expose] public section

namespace Descriptive.Tree
open CategoryTheory

noncomputable section
variable {S T U : Trees} {k m n : ℕ}

/-- Remove all nodes of a tree beyond level k -/
@[implicit_reducible, simps! obj_fst] def res (k : ℕ) : Trees ⥤ Trees where
  obj S := @id Trees ⟨S.1, {
    val := {x | x ∈ S.2 ∧ x.length ≤ k}
    property := by as_aux_lemma =>
      intro x a ⟨h1, h2⟩; use mem_of_append h1
      simp_rw [List.length_append, List.length_singleton] at h2; omega }⟩
  map f := {
    toFun := fun x ↦ ⟨(f ⟨x.val, x.prop.1⟩).val, by
      constructor <;> simp only [SetLike.coe_mem, LenHom.h_length_simp, x.prop.2]⟩
    monotone' := fun _ _ h ↦ f.monotone' h
    h_length := by simp_rw [LenHom.h_length_simp, implies_true]
  }
  map_id _ := rfl
  map_comp _ _ := rfl

@[ext] lemma res_ext (x y : (res k).obj S) (h : x.val = y.val) : x = y := Subtype.ext h
@[simp] lemma mem_res_obj (x : List T.1) :
  Membership.mem (γ := tree T.1) ((Tree.res k).obj T).2 x ↔ x ∈ T.2 ∧ x.length ≤ k :=
  Iff.rfl
/-- Remove all nodes of a tree not on level exactly k -/
@[implicit_reducible, simps map] def resEq (k : ℕ) : Trees ⥤ Type* where
  obj := fun S ↦ {x | x ∈ S.2 ∧ x.length = k}
  map := fun f => ↾fun x ↦ ⟨(f ⟨x.val, x.prop.1⟩).val, by simp [x.prop.2]⟩
  map_id _ := rfl
  map_comp _ _ := rfl
@[ext] lemma resEq_ext (x y : (resEq k).obj S) (h : x.val = y.val) : x = y := Subtype.ext h
lemma resEq_ext_hEq (x : (resEq k).obj T) (y : (resEq m).obj T) (h' : x.val = y.val) :
  HEq x y := by rw [Subtype.heq_iff_coe_eq] <;> simp [← x.prop.2, ← y.prop.2, h']

@[simp] lemma res_mem (x : (res k).obj S) : x.val ∈ S.2 := x.prop.1
@[simps] def res.val' (x : (res k).obj S) : S := ⟨_, res_mem x⟩
lemma res.ext_val' {x y : (res k).obj S} (h : res.val' x = res.val' y) : x = y := by
  apply_fun Subtype.val at h; ext1; exact h
@[simp] lemma res_val (f : S ⟶ T) (k : ℕ) x :
  ((res k).map f x).val = (f (res.val' x)).val := rfl
@[simp] lemma res_val'_val (x : S) h :
  res.val' (k := k) (Subtype.mk (α := no_index _) x.val h) = x := by rfl
@[simp] lemma res_len_le (x : (res k).obj S) : x.val.length (α := S.1) ≤ k := x.prop.2

@[simp] lemma resEq_mem (x : (resEq k).obj S) : x.val ∈ S.2 := x.prop.1
@[simps] def resEq.val' (x : (resEq k).obj S) : S := ⟨_, resEq_mem x⟩
lemma resEq.ext_val' {x y : (resEq k).obj S} (h : resEq.val' x = resEq.val' y) : x = y := by
  apply_fun Subtype.val at h; ext1; exact h
lemma resEq_val (f : S ⟶ T) (k : ℕ) x :
  ((resEq k).map f x).val = (f (resEq.val' x)).val := rfl
@[simp] lemma resEq_val'_val (x : S) h :
  resEq.val' (k := k) (Subtype.mk (α := no_index _) x.val h) = x := by rfl
@[simp] lemma resEq_len (k : ℕ) (x : (resEq k).obj T) :
  x.val.length (α := no_index _) = k := x.prop.2

def resIncl {k m} (h : k ≤ m) : resEq k ⟶ res m ⋙ forget Trees where
  app := fun _ => ↾fun x ↦ ⟨x.val, ⟨x.prop.1, by linarith [x.prop.2]⟩⟩
  naturality _ _ _ := rfl
@[simp] lemma resIncl_len (h : k ≤ m) x :
  ((resIncl h).app S x).val.length (α := S.1) = k := x.prop.2
def res_cocone (k : ℕ) : Limits.Cocone (J := Discrete (Fin (k + 1)))
  (Discrete.functor (fun i ↦ resEq i)) where
  pt := res k ⋙ forget Trees
  ι := Discrete.natTrans (fun _ ↦ resIncl (by omega))
def res_isColimit (k : ℕ) : Limits.IsColimit (res_cocone k) := by
  apply Limits.evaluationJointlyReflectsColimits; intro _
  simp [evaluation, Functor.mapCocone, Limits.Cocone.functoriality, res_cocone]
  apply Classical.choice; apply (isCoprod_type_iff _).mpr; constructor
  · intros i; apply (mono_iff_injective _).mpr
    intros _ _ h; injection h with h; exact Subtype.coe_injective h
  constructor
  · apply (pairwiseDisjoint_iff _).mpr; rintro i x j y he
    have hh : x.val.length = y.val.length := congrArg (fun z => z.val.length) he
    ext; exact x.prop.2.symm.trans (hh.trans y.prop.2)
  · rintro ⟨x, ⟨h1, h2⟩⟩; use ⟨x.length, by omega⟩, ⟨x, ⟨h1, rfl⟩⟩; rfl
def ev_res_cocone (k : ℕ) (S : Trees) : Limits.Cocone
  (Discrete.functor (fun (i : Fin (k + 1)) ↦ resEq i) ⋙ (evaluation _ _).obj S) where
  pt := (res k).obj S
  ι := Discrete.natTrans (fun ⟨n, h⟩ ↦ (resIncl (by omega)).app S)
universe u in --why necessary?
def ev_res_isColimit (k : ℕ) (S : Trees) : Limits.IsColimit (ev_res_cocone.{u} k S) :=
  Limits.isColimitOfPreserves ((evaluation _ _).obj S) (res_isColimit k)

/-- A morphism is k-fixing if it is a bijection on the first k levels -/
class Fixing (k : outParam ℕ) (f : S ⟶ T) : Prop where prop : IsIso ((res k).map f)
instance (f : S ⟶ T) [h : Fixing k f] : IsIso ((res k).map f) := h.prop
/-- Whether a morphism is a bijection on level k -/
class FixingEq (k : outParam ℕ) (f : S ⟶ T) : Prop where prop : IsIso ((resEq k).map f)
instance (f : S ⟶ T) [h : FixingEq k f] : IsIso ((resEq k).map f) := h.prop
lemma fixing_iff_forget_isIso k (f : S ⟶ T) :
  Fixing k f ↔ IsIso ((res k ⋙ forget Trees).map f) := by
  constructor
  · intro _; exact Functor.map_isIso (forget Trees) ((res k).map f)
  · intro h; rw [Functor.comp_map] at h; constructor; apply isIso_of_reflects_iso _ (forget Trees)
lemma Fixing.bijective {k} {f : S ⟶ T} (h : Fixing k f) :
  Function.Bijective ((res k).map f) := by
  rw [fixing_iff_forget_isIso] at h; exact (isIso_iff_bijective _).mp h
lemma fixing_iff_fixingEq k (f : S ⟶ T) :
  Fixing k f ↔ ∀ n ≤ k, FixingEq n f := by
  rw [fixing_iff_forget_isIso]
  let hs := ev_res_isColimit k S; let ht := ev_res_isColimit k T
  have hres := coprod_type_isIso_iff hs ht (fun i ↦ (resEq i).map f)
  have eq2: (∀ n ≤ k, FixingEq n f) ↔ ∀ (j : Fin (k + 1)), IsIso ((resEq j).map f) := by
    constructor
    · intro h _; refine (h _ ?_).prop; apply Fin.is_le
    · intro h n _; exact ⟨h ⟨n, by omega⟩⟩
  rw [eq2, ← hres]; dsimp [Fixing]; congr!; apply hs.hom_ext
  simp only [Functor.comp_obj, evaluation_obj_obj, Functor.const_obj_obj, Limits.IsColimit.ι_map,
    Discrete.natTrans_app]; intro _; rfl
lemma Fixing.mon {f : S ⟶ T} (h : Fixing k f) (hn : n ≤ k) :
  Fixing n f := by rw [fixing_iff_fixingEq] at *; intro m _; apply h m; omega
lemma fixing_iso {f : S ⟶ T} [IsIso f] {k : ℕ} : Fixing k f := by constructor; infer_instance
instance fixing_comp {f : S ⟶ T} {g : T ⟶ U} [h : Fixing k f] [h' : Fixing k g] :
  Fixing k (f ≫ g) := by constructor; rw [Functor.map_comp]; infer_instance

attribute [simp_lengths] res.val'_coe resEq.val'_coe res_len_le resEq_len
macro "synth_fixing" : tactic => `(tactic | first | done |
  simp (config := {failIfUnchanged := false}) only [simp_fixing, simp_lengths] at * <;>
    (try exact fixing_iso) <;>
    (apply Fixing.mon inferInstance;
      simp (config := {failIfUnchanged := false}) only [simp_fixing, simp_lengths] <;> omega))
instance fixingEq_of_fixing {f : S ⟶ T} [h : Fixing k f] : FixingEq k f :=
  (fixing_iff_fixingEq k f).mp h k le_rfl

variable {S T U : Trees} (f : S ⟶ T) (g : T ⟶ U)
lemma Fixing.inj (x y : S) (ht : Fixing x.val.length f := by as_aux_lemma => synth_fixing)
  (he : f x = f y) : x = y := by
  have hl : x.val.length = y.val.length := by
    apply_fun (List.length ∘ Subtype.val) at he; simpa using he
  have he' : (res x.val.length).map f ⟨x.val, by simp [res]⟩
    = (res x.val.length).map f ⟨y.val, by simp [hl, res]⟩ := by
    ext1; apply_fun Subtype.val at he; exact he
  ext1; replace he' := ht.bijective.1 he'; apply_fun Subtype.val at he'; exact he'
def pInv (y : T) (h : Fixing y.val.length f := by as_aux_lemma => synth_fixing) : S :=
  let x := inv ((res y.val.length).map f) ⟨y.val, by simp [res]⟩; res.val' x
@[simp, simp_lengths] lemma h_length_pInv (y : T) (h : Fixing y.val.length f) :
  (pInv f y h).val.length (α := no_index _) = y.val.length (α := no_index _) :=
  by simp [pInv]
@[simp] lemma cancel_pInv_left (x : S) (h : Fixing (f x).val.length f) :
  pInv f (f x) h = x := by
  ext1; show ((inv ((res (f x).val.length).map f))
    ((res (f x).val.length).map f ⟨x.val, by simp [res]⟩)).val = _
  rw [cancel_inv_left]
@[simp] lemma cancel_pInv_right (y : T) (h : Fixing y.val.length f) :
  f (pInv f y h) = y := by
  ext1; show ((res y.val.length).map f (inv ((res y.val.length).map f) _)).val = _
  rw [cancel_inv_right]
@[simp] lemma pInv_id (x : S) : pInv (𝟙 S) x = x := by simp [pInv]
@[simp] lemma pInv_comp y (hg : Fixing y.val.length g := by as_aux_lemma => synth_fixing)
  (hf : Fixing y.val.length f := by as_aux_lemma => synth_fixing) :
  pInv (f ≫ g) y = pInv f (pInv g y hg) := by
  apply Fixing.inj f _; apply Fixing.inj g _
  show (f ≫ g) _ = _; simp_rw [cancel_pInv_right]
lemma pInv_comp' y (hg : Fixing y.val.length g) (hf : Fixing (pInv g y hg).val.length f) :
  pInv (f ≫ g) y = pInv f (pInv g y hg) hf := pInv_comp f g y
lemma take_apply_pInv x (h : Fixing x.val.length f) :
  pInv f (take n x) = take n (pInv f x h) := by
  apply Fixing.inj f _; simp [take_apply]
lemma take_apply_pInv_val x (h : Fixing x.val.length f) :
  (pInv f (take n x)).val = (pInv f x h).val.take n :=
  congr_arg Subtype.val (take_apply_pInv f x h)
@[simp] lemma inv_val'_eq_pInv x (h : Fixing k f := by as_aux_lemma => synth_fixing) :
  res.val' (inv ((res k).map f) x) = pInv f (res.val' x) := by
  apply Fixing.inj f _; ext1; show ((res k).map f _).val = _; simp
@[simp] lemma inv_val'_eq_pInv' x (h : Fixing k f := by as_aux_lemma => synth_fixing) :
  resEq.val' (inv ((resEq k).map f) x) = pInv f (resEq.val' x) := by
  apply Fixing.inj f _; ext1; show ((resEq k).map f _).val = _; rw [cancel_inv_right_types, cancel_pInv_right]; rfl
@[simp] lemma inv_val_eq_pInv_val x (h : Fixing k f := by as_aux_lemma => synth_fixing) :
  (inv ((res k).map f) x).val = (pInv f (res.val' x)).val :=
  congr_arg Subtype.val (inv_val'_eq_pInv f x)
@[simp] lemma inv_val_eq_pInv_val' x (h : Fixing k f := by as_aux_lemma => synth_fixing) :
  (inv ((resEq k).map f) x).val = (pInv f (resEq.val' x)).val :=
  congr_arg Subtype.val (inv_val'_eq_pInv' f x)
end
end Descriptive.Tree
