module

/-
Modified for the math-private book: ported Sven Manthe's formalization to Lean 4.35.0
and its mathlib. See README.md and UPSTREAM.json in the vendor root for provenance;
the original Apache-2.0 license is retained in LICENSE.
-/

public import Mathlib.CategoryTheory.Adjunction.Limits
public import BorelDet.Tree.restrict_tree
public import BorelDet.Basic.inv_limit_nat

@[expose] public section

namespace Descriptive.Tree
open Classical CategoryTheory

noncomputable section
variable {A B : Type*} {m k n : ℕ}
/-- Object function of adjoint of `res k` -/
def constTreeObj (k : ℕ) (A : Type*) : tree A where
  val := {x | ∃ m ≤ k, x ∈ Set.range (List.replicate m)}
  property := by
    rintro x a ⟨m, hm, ⟨b, h⟩⟩; rcases m with _ | m
    · simp at h
    · rw [List.replicate_succ'] at h
      exact ⟨m, ⟨by omega, ⟨b, List.append_inj_left' h rfl⟩⟩⟩
@[simp] lemma mem_constTree (a : A) (h : m ≤ k) :
  List.replicate m a ∈ constTreeObj k A := by
  use m; simp [h]
def headD (x : constTreeObj k A) : A := x.prop.choose_spec.2.choose
@[simp] lemma eq_replicate_headD (x : constTreeObj k A) :
  List.replicate x.val.length (headD x) = x := by
  nth_rw 2 [← x.prop.choose_spec.2.choose_spec]
  nth_rw 1 [← x.prop.choose_spec.2.choose_spec]
  symm; apply List.eq_replicate_of_mem; intro _; apply List.eq_of_mem_replicate
lemma headD_nonempty (x : constTreeObj k A) (h : x.val ≠ []) : headD x = x.val.head h := by
  rw [← eq_replicate_headD] at h; rw [← List.head_replicate h]; simp
@[simp] lemma constTree_length (x : constTreeObj k A) : x.val.length ≤ k := by
  obtain ⟨_, ⟨_, h, ⟨_, rfl⟩⟩⟩ := x; simp [h]
@[simp] lemma constTree_zero (x : constTreeObj 0 A) : x.val = [] := by
  apply List.eq_nil_of_length_eq_zero; linarith [constTree_length x]
/-- Adjoint of `res k` -/
@[implicit_reducible] def constTree (k : ℕ) : Type* ⥤ Trees where
  obj A := ⟨A, constTreeObj k A⟩
  map f := {
    toFun := fun ⟨x, h⟩ ↦ ⟨List.map f x, by
      obtain ⟨n, hn, ⟨a, rfl⟩⟩ := h; exact ⟨n, hn, f a, List.map_replicate.symm⟩⟩
    monotone' := fun _ _ h ↦ List.IsPrefix.map _ h
    h_length := by simp
  }
  map_id _ := LenHom.ext (funext fun x => Subtype.ext x.val.map_id)
  map_comp f g := by
    apply LenHom.ext; funext x; apply Subtype.ext
    change List.map (fun a => g (f a)) x.val = List.map g (List.map f x.val)
    exact List.map_map.symm
@[simp] lemma head_constTree_map {B} (k : ℕ) (f : A → B)
  {x : constTreeObj k A} (h : x.val ≠ []) :
  List.head (((constTree k).map (↾f)) x).val (LenHom.map_ne_nil _ h)
  = f (List.head x.val h) := by
  change (x.val.map f).head _ = _
  simp
lemma headD_constTree_map {B} (k : ℕ) (f : A → B)
    {x : constTreeObj k A} (hx : x.val ≠ []) :
    headD ((constTree k).map (↾f) x) = f (headD x) := by
  calc
    _ = (((constTree k).map (↾f)) x).val.head (LenHom.map_ne_nil _ hx) :=
      headD_nonempty _ _
    _ = f (x.val.head hx) := head_constTree_map k f hx
    _ = _ := congrArg f (headD_nonempty x hx).symm
def resEq_unit k : 𝟭 _ ⟶ constTree k ⋙ resEq k where
  app _ := ↾fun a => ⟨List.replicate k a, by simp [constTree]⟩
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun x ↦ resEq_ext _ _ List.map_replicate.symm
def resEq_counit_comp k T : (constTree k).obj ((resEq k).obj T) ⟶ T where
  toFun := fun x ↦ take x.val.length ⟨(headD x).val, by simp⟩
  monotone' := by
    intro x y h; dsimp only [rem_trees_snd]; by_cases hx : x.val = []
    · simp only [hx, take_coe, List.length_nil, le_def_trees, List.take_zero, List.nil_prefix]
    · have h' : headD x = headD y := by simpa only [← headD_nonempty] using h.head hx
      simp only [h', le_def_trees, List.prefix_take_iff,
        List.take_prefix, List.length_take, resEq_len, constTree_length,
        min_eq_left, List.IsPrefix.length_le h, and_self, take_coe]
  h_length _ := by simp only [take_coe, List.length_take, resEq_len, constTree_length, min_eq_left]
def resEq_counit k : resEq k ⋙ constTree k ⟶ 𝟭 _ where
  app := resEq_counit_comp k
  naturality := by
    rintro S T f; apply LenHom.ext; funext x
    change take (((constTree k).map ((resEq k).map f) x).val.length)
        ⟨(headD ((constTree k).map ((resEq k).map f) x)).val, _⟩ =
      f (take x.val.length ⟨(headD x).val, _⟩)
    rw [LenHom.h_length_simp]
    rw [take_apply f x.val.length]
    by_cases hxl : x.val = []
    · rw [congr_arg List.length hxl]; rfl
    · apply Subtype.ext
      exact congrArg (fun z : (resEq k).obj T => z.val.take x.val.length)
        (headD_constTree_map k (fun a => (resEq k).map f a) hxl)
def resEqAdj (k : ℕ) : constTree k ⊣ resEq k := Adjunction.mkOfUnitCounit {
  unit := resEq_unit k
  counit := resEq_counit k
  left_triangle := by
    apply NatTrans.ext; funext A; apply LenHom.ext; funext x; apply Subtype.ext
    let u : A → (resEq k).obj ((constTree k).obj A) :=
      fun a => ⟨List.replicate k a, by simp [constTree]⟩
    change (((headD ((constTree k).map (↾u) x)).val).take
      (((constTree k).map (↾u) x).val.length)) = x.val
    rw [LenHom.h_length_simp]
    by_cases hx : x.val = []
    · simp only [hx, List.length_nil, List.take_zero]
    · rw [headD_constTree_map k u hx]
      change List.take x.val.length (List.replicate k (headD x)) = x.val
      rw [List.take_replicate, Nat.min_eq_left (constTree_length x), eq_replicate_headD]
  right_triangle := by
    apply NatTrans.ext; funext T; apply ConcreteCategory.hom_ext; intro x; apply Subtype.ext
    let y : constTreeObj k ((resEq k).obj T) :=
      ⟨List.replicate k x, mem_constTree x le_rfl⟩
    change (headD y).val.take y.val.length = x.val
    have hxl : x.val.length = k := x.prop.2
    by_cases hk : k = 0
    · subst k
      simpa only [y, List.length_replicate, List.take_zero] using
        (List.eq_nil_of_length_eq_zero hxl).symm
    · have hy : y.val ≠ [] := by simp [y, hk]
      have hh : headD y = x := by
        rw [headD_nonempty y hy]
        exact List.head_replicate hy
      rw [hh]
      change x.val.take (List.replicate k x).length = x.val
      exact List.take_of_length_le (by simpa only [List.length_replicate] using le_of_eq hxl)

}
instance (k : ℕ) : Functor.IsRightAdjoint (Tree.resEq k) :=
  ⟨Tree.constTree k, ⟨Tree.resEqAdj k⟩⟩
instance (k : ℕ) : Limits.PreservesLimitsOfSize (Tree.resEq k) :=
  (Tree.resEqAdj k).rightAdjoint_preservesLimits

section TreeLimits
variable {J : Type} [Category J] (F : J ⥤ Trees)
/-- Object function of limit functor in `Trees` -/
def limObj : tree (∀ j, (F.obj j).1) where
  val := { x | ∃ (h : ∀ j, x.mapEval j ∈ (F.obj j).2),
    ∀ ⦃i j⦄ (f : i ⟶ j), (F.map f ⟨_, h i⟩).val = x.mapEval j }
  property := by
    intro x a ⟨h1, h2⟩; use fun j ↦ mem_of_append (y := [a j]) (by
      simpa only [List.map_append, List.map_cons, List.map_nil] using h1 j)
    intro _ _ f; specialize h2 f; apply_fun List.take x.length at h2
    simp_rw [List.map_append, List.map_cons, List.map_nil, ← take_apply_val] at h2
    convert h2 <;> simp only [List.length_map, le_refl, List.take_append_of_le_length,
      ← List.map_take, List.take_length, take_coe]
@[implicit_reducible] def limCone : Limits.Cone F where
  pt := ⟨_, limObj F⟩
  π := {
    app := fun j ↦ {
      toFun := fun x ↦ ⟨x.val.mapEval j, x.prop.1 j⟩
      monotone' := fun _ _ h ↦ h.map _
      h_length := by simp_rw [List.length_map, implies_true]
    }
    naturality := fun _ _ f ↦ ConcreteCategory.hom_ext _ _ fun x ↦ tree_ext (x.prop.2 f).symm
  }
def isLimit_lift (s : Limits.Cone F) : s.pt ⟶ (limCone F).pt where
  toFun x := ⟨List.zipFun (n := x.val.length) (fun j ↦ ((s.π.app j) x).val)
    (fun _ ↦ LenHom.h_length_simp _ x), by
    simp only [limCone, limObj, Functor.const_obj_obj, Set.mem_ofPred_eq, List.mapEval_zip,
      Subtype.coe_eta, SetLike.coe_mem, implies_true, exists_const]
    intro _ _ f; rw [← s.w f]; rfl⟩
  monotone' x y h := List.zipFun_mono _ _ _ _ h.length_le (fun j ↦ (s.π.app j).monotone' h)
  h_length _ := by simp only [List.zipFun_len]

def isLimit : Limits.IsLimit (limCone F) where
  lift := isLimit_lift F
  fac := by
    intro s j; apply LenHom.ext; funext x; apply Subtype.ext
    change (List.zipFun (n := x.val.length) (fun j => ((s.π.app j) x).val) _).mapEval j = _
    exact List.mapEval_zip _ _
  uniq := by
    intro s f h; apply LenHom.ext; funext x; apply Subtype.ext
    change (f x).val = List.zipFun (n := x.val.length) (fun j => ((s.π.app j) x).val) _
    apply List.mapEval_joint_epi
    · rw [List.zipFun_len]; exact f.h_length x
    · intro j
      calc
        (f x).val.mapEval j = ((s.π.app j) x).val :=
          congrArg (fun g : s.pt ⟶ F.obj j => (g x).val) (h j)
        _ = _ := by symm; apply List.mapEval_zip

end TreeLimits

lemma proj_fixing (F : ℕᵒᵖ ⥤ Trees) (k : ℕ)
  (hF : ∀ n, Tree.Fixing (k + n) (F.map (homOfLE (Nat.le_succ n)).op)) n :
  Fixing (k + n) ((limCone F).π.app (Opposite.op n)) :=
  (fixing_iff_fixingEq (k + n) _).mpr (fun m hm ↦
    ⟨nat_add_initial (Limits.isLimitOfPreserves (resEq m) (isLimit F)) n (fun p hp ↦
      ((fixing_iff_fixingEq (k + n) _).mp (by synth_fixing) m hm).prop) n le_rfl⟩)

end
end Descriptive.Tree
