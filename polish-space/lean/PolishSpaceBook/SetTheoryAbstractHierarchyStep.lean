module

public import PolishSpaceBook.SetTheoryAbstractHulls

@[expose] public section

/-! # A concrete cumulative-hierarchy step in arbitrary membership models -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def IsPowerObject (a b : M) : Prop :=
  ∀ z : M, member z b ↔ ∀ u : M, member u z → member u a

def powerObjectBody : ForcingFormulas.Formula 2 :=
  ((memberAt (2 : Fin 3) 1).iff ((memberAt (3 : Fin 4) 2).imp (memberAt 3 0)).all).all

theorem realize_powerObjectBody (xs : Fin 2 → M) :
    powerObjectBody.Realize Empty.elim xs ↔ IsPowerObject (xs 0) (xs 1) := by
  simp [powerObjectBody, IsPowerObject, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp, realize_memberAt, Fin.snoc]

theorem powerObject_existsUnique (hM : M ⊨ fullZFCTheory) (a : M) : ∃! b : M, IsPowerObject a b :=
  existsUnique_of_members (hM.realize_of_mem _ ZFCAxiom.extensionality) _
    ((models_power_iff M).mp (hM.realize_of_mem _ ZFCAxiom.power) a)

def IsHierarchyStep (g b : M) : Prop :=
  ∀ z : M, member z b ↔ ∃ x y : M, GraphApplication g x y ∧ ∀ u : M, member u z → member u y

def hierarchyStepBody : ForcingFormulas.Formula 3 :=
  ((memberAt (3 : Fin 4) 2).iff
    ((internalApplicationFormula (1 : Fin 6) 4 5 ⊓
      ((memberAt (6 : Fin 7) 3).imp (memberAt 6 5)).all).ex.ex)).all

theorem realize_hierarchyStepBody (xs : Fin 3 → M) :
    hierarchyStepBody.Realize Empty.elim xs ↔ IsHierarchyStep (xs 1) (xs 2) := by
  simp [hierarchyStepBody, IsHierarchyStep, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_imp,
    realize_memberAt, realize_internalApplicationFormula, Fin.snoc]
  rfl

/-- Replacement collects the actual internal power sets of the graph values;
Union gives the required step for every graph, not only recursive solutions. -/
theorem hierarchyStep_existsUnique (hM : M ⊨ fullZFCTheory) (a g : M) :
    ∃! b : M, hierarchyStepBody.Realize Empty.elim ![a, g, b] := by
  simp only [realize_hierarchyStepBody, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  obtain ⟨r, hr, _⟩ := existsUnique_graphRange hM g
  have ht (x : M) (_ : member x r) :
      ∃! y : M, powerObjectBody.Realize Empty.elim (Fin.snoc (Fin.snoc Fin.elim0 x) y) := by
    simpa [realize_powerObjectBody, Fin.snoc] using powerObject_existsUnique hM x
  obtain ⟨F, hF⟩ := (realize_replacement M powerObjectBody).mp
    (hM.realize_of_mem _ (ZFCAxiom.replacement _)) Fin.elim0 r ht
  have hf (y : M) : member y F ↔ ∃ x : M, member x r ∧ IsPowerObject x y := by
    simpa [realize_powerObjectBody, Fin.snoc] using hF y
  obtain ⟨b, hb, _⟩ := existsUnique_union hext (hM.realize_of_mem _ ZFCAxiom.union) F
  apply existsUnique_of_members hext
  refine ⟨b, fun z => ?_⟩
  rw [hb z]
  constructor
  · rintro ⟨v, hzv, hvF⟩
    obtain ⟨y, hyr, hv⟩ := (hf v).mp hvF
    obtain ⟨x, hxy⟩ := (hr y).mp hyr
    exact ⟨x, y, hxy, (hv z).mp hzv⟩
  · rintro ⟨x, y, hxy, hzy⟩
    obtain ⟨v, hv, _⟩ := powerObject_existsUnique hM y
    exact ⟨v, (hv z).mpr hzy, (hf v).mpr ⟨y, (hr y).mpr ⟨x, hxy⟩, hv⟩⟩

theorem hierarchyStep_transitive {g b : M} (hb : IsHierarchyStep g b)
    (hg : ∀ x y : M, GraphApplication g x y → IsTransitiveObject y) : IsTransitiveObject b := by
  intro z hz w hwz
  obtain ⟨x, y, hxy, hzy⟩ := (hb z).mp hz
  exact (hb w).mpr ⟨x, y, hxy, fun u huw => hg x y hxy w (hzy w hwz) u huw⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
