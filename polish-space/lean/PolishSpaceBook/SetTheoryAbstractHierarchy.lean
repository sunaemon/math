module

public import PolishSpaceBook.SetTheoryAbstractRank
public import PolishSpaceBook.SetTheoryAbstractHierarchyStep

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Internal cumulative stages cover every object of an arbitrary ZFC model -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

theorem hierarchyStep_total (hM : M ⊨ fullZFCTheory) (a g : M) :
    ∃! b : M, hierarchyStepBody.Realize Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 a) g) b) := by
  have he (b : M) : Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 a) g) b = ![a, g, b] := by
    ext i
    fin_cases i <;> rfl
  simpa only [he] using hierarchyStep_existsUnique hM a g

def internalHierarchyObject (hM : M ⊨ fullZFCTheory) : M → M :=
  recursiveFunction hM hierarchyStepBody Fin.elim0 (hierarchyStep_total hM)

def hierarchyValueBody : ForcingFormulas.Formula 2 := recursiveValueBody hierarchyStepBody

theorem realize_hierarchyValueBody (hM : M ⊨ fullZFCTheory) (xs : Fin 2 → M) :
    hierarchyValueBody.Realize Empty.elim xs ↔ xs 1 = internalHierarchyObject hM (xs 0) := by
  have he : Fin.snoc (Fin.snoc Fin.elim0 (xs 0)) (xs 1) = xs := by
    ext i
    fin_cases i <;> rfl
  simpa only [he, hierarchyValueBody, internalHierarchyObject] using realize_recursiveValue_iff hM hierarchyStepBody Fin.elim0
    (hierarchyStep_total hM) (xs 0) (xs 1)

theorem internalHierarchyObject_equation (hM : M ⊨ fullZFCTheory) (a z : M) :
    member z (internalHierarchyObject hM a) ↔
      ∃ x : M, member x a ∧ ∀ u : M, member u z → member u (internalHierarchyObject hM x) := by
  obtain ⟨g, _, hg, hb⟩ := recursiveFunction_equation hM hierarchyStepBody Fin.elim0
    (hierarchyStep_total hM) a
  have hgi : ∀ x y : M, GraphApplication g x y ↔ member x a ∧ y = internalHierarchyObject hM x := by
    simpa only [internalHierarchyObject] using hg
  have hs : IsHierarchyStep g (internalHierarchyObject hM a) := by
    simpa [realize_hierarchyStepBody, Fin.snoc, internalHierarchyObject] using hb
  rw [hs z]
  constructor
  · rintro ⟨x, y, hxy, hzy⟩
    obtain ⟨hxa, hy⟩ := (hgi x y).mp hxy
    exact ⟨x, hxa, hy ▸ hzy⟩
  · rintro ⟨x, hxa, hzx⟩
    exact ⟨x, internalHierarchyObject hM x, (hgi x _).mpr ⟨hxa, rfl⟩, hzx⟩

def hierarchyCoversRankBody : ForcingFormulas.Formula 1 :=
  (reindex rankValueBody ![(0 : Fin 3), 1] ⊓
    (reindex hierarchyValueBody ![1, 2] ⊓ reindex subsetBody ![0, 2])).ex.ex

theorem realize_hierarchyCoversRankBody (hM : M ⊨ fullZFCTheory) (xs : Fin 1 → M) :
    hierarchyCoversRankBody.Realize Empty.elim xs ↔
      ∀ u : M, member u (xs 0) →
        member u (internalHierarchyObject hM (internalRankObject hM (xs 0))) := by
  simp [hierarchyCoversRankBody, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, realize_rankValueBody hM, realize_hierarchyValueBody hM,
    subsetBody, BoundedFormula.realize_all, BoundedFormula.realize_imp, realize_memberAt,
    Fin.snoc]

/-- Each object is a subset of its internal rank stage. The proof is again
formula induction inside the model, not induction on external ranks. -/
theorem internalHierarchyObject_covers_rank (hM : M ⊨ fullZFCTheory) (a : M) :
    ∀ u : M, member u a → member u (internalHierarchyObject hM (internalRankObject hM a)) := by
  have hi := fullZFC_membership_induction hM hierarchyCoversRankBody Fin.elim0 (fun x ih => by
    apply (realize_hierarchyCoversRankBody hM (Fin.snoc Fin.elim0 x)).mpr
    intro y hyx
    apply (internalHierarchyObject_equation hM (internalRankObject hM x) y).mpr
    exact ⟨internalRankObject hM y, internalRankObject_member hM hyx,
      (realize_hierarchyCoversRankBody hM (Fin.snoc Fin.elim0 y)).mp (ih y hyx)⟩)
  exact (realize_hierarchyCoversRankBody hM (Fin.snoc Fin.elim0 a)).mp (hi a)

/-- Every model element belongs to a stage with an internal ordinal index.
This is the witness-stage existence needed for Collection. -/
theorem exists_ordinal_hierarchy_stage (hM : M ⊨ fullZFCTheory) (a : M) :
    ∃ α : M, IsOrdinalObject α ∧ member a (internalHierarchyObject hM α) := by
  obtain ⟨α, hα⟩ := exists_successorObject hM (internalRankObject hM a)
  refine ⟨α, (internalRankObject_ordinal hM a).successor hα, ?_⟩
  exact (internalHierarchyObject_equation hM α a).mpr
    ⟨internalRankObject hM a, (hα _).mpr (Or.inr rfl), internalHierarchyObject_covers_rank hM a⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
