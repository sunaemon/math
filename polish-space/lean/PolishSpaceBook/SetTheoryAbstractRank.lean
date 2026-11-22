module

public import PolishSpaceBook.SetTheoryAbstractRecursionEquation
public import PolishSpaceBook.SetTheoryAbstractRankStep

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Definable ordinal ranks in arbitrary ZFC models -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

theorem rankStep_total (hM : M ⊨ fullZFCTheory) (a g : M) :
    ∃! b : M, rankStepBody.Realize Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 a) g) b) := by
  have he (b : M) : Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 a) g) b = ![a, g, b] := by
    ext i
    fin_cases i <;> rfl
  simpa only [he] using rankStep_existsUnique hM a g

def internalRankObject (hM : M ⊨ fullZFCTheory) : M → M :=
  recursiveFunction hM rankStepBody Fin.elim0 (rankStep_total hM)

def rankValueBody : ForcingFormulas.Formula 2 := recursiveValueBody rankStepBody

theorem realize_rankValueBody (hM : M ⊨ fullZFCTheory) (xs : Fin 2 → M) :
    rankValueBody.Realize Empty.elim xs ↔ xs 1 = internalRankObject hM (xs 0) := by
  have he : Fin.snoc (Fin.snoc Fin.elim0 (xs 0)) (xs 1) = xs := by
    ext i
    fin_cases i <;> rfl
  simpa only [he, rankValueBody, internalRankObject] using realize_recursiveValue_iff hM rankStepBody Fin.elim0
    (rankStep_total hM) (xs 0) (xs 1)

theorem internalRankObject_equation (hM : M ⊨ fullZFCTheory) (a z : M) :
    member z (internalRankObject hM a) ↔
      ∃ x : M, member x a ∧ (member z (internalRankObject hM x) ∨ z = internalRankObject hM x) := by
  obtain ⟨g, _, hg, hb⟩ := recursiveFunction_equation hM rankStepBody Fin.elim0
    (rankStep_total hM) a
  have hgi : ∀ x y : M, GraphApplication g x y ↔ member x a ∧ y = internalRankObject hM x := by
    simpa only [internalRankObject] using hg
  have hs : IsRankStep g (internalRankObject hM a) := by
    simpa [realize_rankStepBody, Fin.snoc, internalRankObject] using hb
  rw [hs z]
  constructor
  · rintro ⟨x, y, hxy, hzy⟩
    obtain ⟨hxa, hy⟩ := (hgi x y).mp hxy
    exact ⟨x, hxa, hy ▸ hzy⟩
  · rintro ⟨x, hxa, hzx⟩
    exact ⟨x, internalRankObject hM x, (hgi x _).mpr ⟨hxa, rfl⟩, hzx⟩

def rankOrdinalBody : ForcingFormulas.Formula 1 :=
  (rankValueBody ⊓ ordinalFormula (1 : Fin 2)).ex

theorem realize_rankOrdinalBody (hM : M ⊨ fullZFCTheory) (xs : Fin 1 → M) :
    rankOrdinalBody.Realize Empty.elim xs ↔ IsOrdinalObject (internalRankObject hM (xs 0)) := by
  simp [rankOrdinalBody, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_rankValueBody hM, realize_ordinalFormula, Fin.snoc]

/-- Ordinality is proved by the model's actual formula induction, rather
than an external rank induction. -/
theorem internalRankObject_ordinal (hM : M ⊨ fullZFCTheory) (a : M) :
    IsOrdinalObject (internalRankObject hM a) := by
  have hi := fullZFC_membership_induction hM rankOrdinalBody Fin.elim0 (fun x ih => by
    apply (realize_rankOrdinalBody hM (Fin.snoc Fin.elim0 x)).mpr
    change IsOrdinalObject (internalRankObject hM x)
    have ho (y : M) (hy : member y x) : IsOrdinalObject (internalRankObject hM y) :=
      (realize_rankOrdinalBody hM (Fin.snoc Fin.elim0 y)).mp (ih y hy)
    constructor
    · intro z hz w hwz
      obtain ⟨y, hy, hzy | hzy⟩ := (internalRankObject_equation hM x z).mp hz
      · exact (internalRankObject_equation hM x w).mpr
          ⟨y, hy, Or.inl ((ho y hy).transitive z hzy w hwz)⟩
      · exact (internalRankObject_equation hM x w).mpr ⟨y, hy, Or.inl (hzy ▸ hwz)⟩
    · intro z hz
      obtain ⟨y, hy, hzy | hzy⟩ := (internalRankObject_equation hM x z).mp hz
      · exact (ho y hy).members_transitive z hzy
      · exact hzy ▸ (ho y hy).transitive)
  exact (realize_rankOrdinalBody hM (Fin.snoc Fin.elim0 a)).mp (hi a)

theorem internalRankObject_member (hM : M ⊨ fullZFCTheory) {a b : M} (hab : member a b) :
    member (internalRankObject hM a) (internalRankObject hM b) :=
  (internalRankObject_equation hM b _).mpr ⟨a, hab, Or.inr rfl⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
