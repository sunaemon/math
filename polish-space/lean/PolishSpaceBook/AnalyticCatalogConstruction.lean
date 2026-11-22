module

public import PolishSpaceBook.AnalyticConditionCatalog

@[expose] public section

/-!
# Constructing a countable witness-closed analytic catalog

Starting with a nonempty countable family, iterate the cylinder and
closed-witness trace intersections used by fusion. Every stage and their
union are countable. Closed presentations are chosen from the continuous
image definition of analyticity. This is a boldface existence construction,
not an effective coding theorem or a construction of Silver's kernel.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

/-- A nonempty analytic set has a closed witness presentation: reverse the
graph of a continuous Baire-space parametrization. -/
theorem analytic_condition_closed_presentation (P : AnalyticCondition FusionReal) :
    ∃ K : Set (FusionReal × FusionReal), IsClosed K ∧ P.val = Prod.fst '' K := by
  have h := P.property.1
  rw [AnalyticSet] at h
  rcases h with he | ⟨f, hf, hr⟩
  · exact False.elim (P.property.2.ne_empty he)
  · refine ⟨{p | p.1 = f p.2}, isClosed_eq continuous_fst (hf.comp continuous_snd), ?_⟩
    rw [← hr]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(f y, y), rfl, rfl⟩
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact ⟨y, hxy.symm⟩

/-- Countably many binary operations admit a countable closed hull of any
countable starting family. The construction is the union of finite stages. -/
theorem countable_binary_operation_hull {A I : Type*} [Countable I]
    (op : I → A → A → A) (S : Set A) (hS : S.Countable) :
    ∃ T : Set A, T.Countable ∧ S ⊆ T ∧ ∀ i, ∀ x ∈ T, ∀ y ∈ T, op i x y ∈ T := by
  let step (T : Set A) : Set A := T ∪
    (fun p : (A × A) × I => op p.2 p.1.1 p.1.2) '' ((T ×ˢ T) ×ˢ Set.univ)
  let stages : ℕ → Set A := fun n => Nat.rec S (fun _ T => step T) n
  have hc n : (stages n).Countable := by
    induction n with
    | zero => exact hS
    | succ n ih => exact ih.union (((ih.prod ih).prod (Set.to_countable _)).image _)
  have hmono : Monotone stages := monotone_nat_of_le_succ (fun _ => Set.subset_union_left)
  refine ⟨⋃ n, stages n, Set.countable_iUnion hc, ?_, ?_⟩
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨0, hx⟩
  · intro i x hx y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨max n m + 1, Or.inr ?_⟩
    exact ⟨((x, y), i), ⟨⟨hmono (le_max_left _ _) hn, hmono (le_max_right _ _) hm⟩,
      Set.mem_univ _⟩, rfl⟩

/-- Choose a presentation once for each analytic condition. This use of
choice is non-effective and is not claimed to provide lightface codes. -/
noncomputable def chosenAnalyticPresentation (P : AnalyticCondition FusionReal) :
    Set (FusionReal × FusionReal) := (analytic_condition_closed_presentation P).choose

theorem chosenAnalyticPresentation_closed (P : AnalyticCondition FusionReal) :
    IsClosed (chosenAnalyticPresentation P) := (analytic_condition_closed_presentation P).choose_spec.1

theorem chosenAnalyticPresentation_projects (P : AnalyticCondition FusionReal) :
    P.val = Prod.fst '' chosenAnalyticPresentation P := (analytic_condition_closed_presentation P).choose_spec.2

/-- Keep the original condition when the requested intersection is empty. -/
noncomputable def intersectAnalyticCondition (P : AnalyticCondition FusionReal)
    (A : Set FusionReal) (hA : AnalyticSet A) : AnalyticCondition FusionReal := by
  classical
  exact if h : (P.val ∩ A).Nonempty then ⟨P.val ∩ A, analyticSet_inter P.property.1 hA, h⟩ else P

theorem intersectAnalyticCondition_val (P : AnalyticCondition FusionReal)
    (A : Set FusionReal) (hA : AnalyticSet A) (h : (P.val ∩ A).Nonempty) :
    (intersectAnalyticCondition P A hA).val = P.val ∩ A := by
  classical
  simp [intersectAnalyticCondition, h]

abbrev CatalogRefinementIndex := (Σ n, FusionPrefix n) ⊕ (Σ n, FusionPrefix n × FusionPrefix n)

/-- The two refinement operations of analytic-condition fusion. -/
noncomputable def catalogRefinement : CatalogRefinementIndex →
    AnalyticCondition FusionReal → AnalyticCondition FusionReal → AnalyticCondition FusionReal
  | .inl ⟨_, s⟩, P, _ => intersectAnalyticCondition P (fusionCylinder s)
      (isClosed_fusionCylinder s).measurableSet.analyticSet
  | .inr ⟨_, s, t⟩, P, Q => intersectAnalyticCondition P
      (witnessProjection (chosenAnalyticPresentation Q) s t)
      (analyticSet_witnessProjection (chosenAnalyticPresentation_closed Q) s t)

/-- A countable initial family is contained in an actual countable catalog
closed under every witness and cylinder refinement needed for fusion.
No hypothesis about presentations of future refinements is assumed. -/
theorem exists_analytic_condition_catalog_closed_under {I : Type*} [Countable I]
    (op : I → AnalyticCondition FusionReal → AnalyticCondition FusionReal → AnalyticCondition FusionReal)
    (F : Set (AnalyticCondition FusionReal)) (hFc : F.Countable) (hFn : F.Nonempty) :
    ∃ C : AnalyticConditionCatalog, F ⊆ C.conditions ∧
      ∀ i, ∀ P ∈ C.conditions, ∀ Q ∈ C.conditions, op i P Q ∈ C.conditions := by
  let operations : CatalogRefinementIndex ⊕ I → AnalyticCondition FusionReal →
      AnalyticCondition FusionReal → AnalyticCondition FusionReal := Sum.elim catalogRefinement op
  obtain ⟨T, hTc, hFT, hclosed⟩ := countable_binary_operation_hull operations F hFc
  obtain ⟨e, he⟩ := hTc.exists_eq_range (hFn.mono hFT)
  have hem i : e i ∈ T := by rw [he]; exact ⟨i, rfl⟩
  refine ⟨{
    conditions := T
    countable := hTc
    closed := fun i => chosenAnalyticPresentation (e i)
    isClosed := fun i => chosenAnalyticPresentation_closed (e i)
    presentation := ?_
    witness_refine := ?_
    cylinder_refine := ?_ }, hFT, fun i P hP Q hQ => hclosed (.inr i) P hP Q hQ⟩
  · intro P hP
    rw [he] at hP
    obtain ⟨i, rfl⟩ := hP
    exact ⟨i, chosenAnalyticPresentation_projects _⟩
  · intro P hP i n s t hne
    let Q := catalogRefinement (.inr ⟨n, s, t⟩) P (e i)
    have hQ : Q.val = P.val ∩ witnessProjection (chosenAnalyticPresentation (e i)) s t :=
      intersectAnalyticCondition_val _ _
        (analyticSet_witnessProjection (chosenAnalyticPresentation_closed (e i)) s t) hne
    refine ⟨Q, hclosed (.inl (.inr ⟨n, s, t⟩)) P hP (e i) (hem i), ?_, ?_⟩
    · change Q.val ⊆ P.val
      rw [hQ]
      exact Set.inter_subset_left
    · rw [hQ]
      exact Set.inter_subset_right
  · intro P hP n s hne
    let Q := catalogRefinement (.inl ⟨n, s⟩) P P
    have hQ : Q.val = P.val ∩ fusionCylinder s := intersectAnalyticCondition_val _ _
      (isClosed_fusionCylinder s).measurableSet.analyticSet hne
    refine ⟨Q, hclosed (.inl (.inl ⟨n, s⟩)) P hP P hP, ?_, ?_⟩
    · change Q.val ⊆ P.val
      rw [hQ]
      exact Set.inter_subset_left
    · rw [hQ]
      exact Set.inter_subset_right

/-- The witness-closed hull without additional prescribed operations. -/
theorem exists_analytic_condition_catalog
    (F : Set (AnalyticCondition FusionReal)) (hFc : F.Countable) (hFn : F.Nonempty) :
    ∃ C : AnalyticConditionCatalog, F ⊆ C.conditions := by
  obtain ⟨C, hFC, _⟩ := exists_analytic_condition_catalog_closed_under
    (fun i : Empty => i.elim) F hFc hFn
  exact ⟨C, hFC⟩

end PolishSpaceBook
