module

public import PolishSpaceBook.FirstOrderEqualityTemplates

@[expose] public section

/-! # Finite equality templates for compound replacement terms

At each subtree equal to the source term, either replace the whole subtree or
continue into its children. The list may contain non-formulas; the generic
formula recognizer filters those candidates. This module proves the exact
binding-tree synthesis, independently of a signature or a size-bound premise.
-/
namespace PolishSpaceBook.NamedLambda.BindingTree

def compoundRootChoice (U : BindingTree) (z : ℕ) (A : BindingTree) : List BindingTree :=
  if A = U then [.free z] else []

def compoundTemplates (U : BindingTree) (z : ℕ) (A : BindingTree) : List BindingTree :=
  compoundRootChoice U z A ++ match A with
    | .free v => [.free v]
    | .bound i => [.bound i]
    | .app A B => (compoundTemplates U z A).flatMap
        (fun C => (compoundTemplates U z B).map (.app C))
    | .lam A => (compoundTemplates U z A).map .lam

theorem self_mem_compoundTemplates (A U : BindingTree) (z : ℕ) :
    A ∈ compoundTemplates U z A := by
  induction A with
  | free v => simp [compoundTemplates, compoundRootChoice]
  | bound i => simp [compoundTemplates, compoundRootChoice]
  | app A B ihA ihB =>
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨A, ihA, List.mem_map.mpr ⟨B, ihB, rfl⟩⟩
  | lam A ih => exact List.mem_append_right _ (List.mem_map.mpr ⟨A, ih, rfl⟩)

theorem free_mem_compoundTemplates (U : BindingTree) (z : ℕ) :
    .free z ∈ compoundTemplates U z U := by
  rw [compoundTemplates.eq_def, compoundRootChoice]
  exact List.mem_append_left _ (by simp)

theorem erase_fv_subset_compound_subst (A U : BindingTree) (x : ℕ) :
    A.fv.erase x ⊆ (A.subst x U).fv := by
  induction A with
  | free v =>
    by_cases h : v = x
    · subst v; simp [fv]
    · simp only [subst, ite_eq_right h, fv]
      exact Finset.erase_subset _ _
  | bound i => simp [fv, subst]
  | app A B ihA ihB =>
    simp only [fv, subst, Finset.erase_union_distrib]
    exact Finset.union_subset_union ihA ihB
  | lam A ih => exact ih

theorem subst_fresh_compound (A U : BindingTree) (x z : ℕ) (hz : z ∉ A.fv.erase x) :
    (A.subst x (.free z)).subst z U = A.subst x U := by
  induction A with
  | free v =>
    by_cases hx : v = x
    · simp [subst, hx]
    · have hv : v ≠ z := by intro h; subst v; exact hz (by simp [fv, hx])
      simp [subst, hx, hv]
  | bound i => rfl
  | app A B ihA ihB =>
    simp only [fv, Finset.erase_union_distrib, Finset.mem_union, not_or] at hz
    simp only [subst, ihA hz.1, ihB hz.2]
  | lam A ih => exact congrArg lam (ih hz)

theorem renamed_mem_compoundTemplates (D U : BindingTree) (x z : ℕ) :
    D.subst x (.free z) ∈ compoundTemplates U z (D.subst x U) := by
  induction D with
  | free v =>
    by_cases hx : v = x
    · simpa only [subst, ite_eq_left hx] using free_mem_compoundTemplates U z
    · simpa only [subst, ite_eq_right hx] using self_mem_compoundTemplates (.free v) U z
  | bound i => exact self_mem_compoundTemplates (.bound i) U z
  | app A B ihA ihB =>
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, ihA, List.mem_map.mpr ⟨_, ihB, rfl⟩⟩
  | lam A ih => exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

theorem compoundTemplate_subst_back {A C U : BindingTree} {z : ℕ}
    (hC : C ∈ compoundTemplates U z A) (hz : z ∉ A.fv) : C.subst z U = A := by
  induction A generalizing C with
  | free v =>
    simp only [compoundTemplates, compoundRootChoice, List.mem_append] at hC
    rcases hC with hC | hC
    · split_ifs at hC with he
      · simp only [List.mem_singleton] at hC; subst C; simp [subst, he]
      · simp at hC
    · simp only [List.mem_singleton] at hC; subst C
      exact subst_eq_self _ _ _ hz
  | bound i =>
    simp only [compoundTemplates, compoundRootChoice, List.mem_append] at hC
    rcases hC with hC | hC
    · split_ifs at hC with he
      · simp only [List.mem_singleton] at hC; subst C; simp [subst, he]
      · simp at hC
    · simp only [List.mem_singleton] at hC; subst C; rfl
  | app A B ihA ihB =>
    simp only [compoundTemplates, compoundRootChoice, List.mem_append] at hC
    rcases hC with hC | hC
    · split_ifs at hC with he
      · simp only [List.mem_singleton] at hC; subst C; simp [subst, he]
      · simp at hC
    · obtain ⟨D, hD, hC⟩ := List.mem_flatMap.mp hC
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hC
      simp only [fv, Finset.mem_union, not_or] at hz
      exact congrArg₂ app (ihA hD hz.1) (ihB hE hz.2)
  | lam A ih =>
    simp only [compoundTemplates, compoundRootChoice, List.mem_append] at hC
    rcases hC with hC | hC
    · split_ifs at hC with he
      · simp only [List.mem_singleton] at hC; subst C; simp [subst, he]
      · simp at hC
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
      exact congrArg lam (ih hD hz)

/-- The observed source alone supplies the freshness needed to recover the
unknown template with a new distinguished variable. -/
theorem exists_compoundTemplate_of_instances (A B D U V : BindingTree) (x z : ℕ)
    (hA : D.subst x U = A) (hB : D.subst x V = B) (hz : z ∉ A.fv) :
    ∃ C ∈ compoundTemplates U z A, C.subst z U = A ∧ C.subst z V = B := by
  have hf : z ∉ D.fv.erase x := fun h => hz (hA ▸ erase_fv_subset_compound_subst D U x h)
  refine ⟨D.subst x (.free z), ?_, ?_, ?_⟩
  · rw [← hA]; exact renamed_mem_compoundTemplates D U x z
  · exact (subst_fresh_compound D U x z hf).trans hA
  · exact (subst_fresh_compound D V x z hf).trans hB

theorem compoundTemplates_iff (A B U V : BindingTree) (z : ℕ) (hz : z ∉ A.fv) :
    (∃ C ∈ compoundTemplates U z A, C.subst z V = B) ↔
      ∃ (D : BindingTree) (x : ℕ), D.subst x U = A ∧ D.subst x V = B := by
  constructor
  · rintro ⟨C, hC, hB⟩
    exact ⟨C, z, compoundTemplate_subst_back hC hz, hB⟩
  · rintro ⟨D, x, hA, hB⟩
    obtain ⟨C, hC, _, hCB⟩ := exists_compoundTemplate_of_instances A B D U V x z hA hB hz
    exact ⟨C, hC, hCB⟩

end PolishSpaceBook.NamedLambda.BindingTree
