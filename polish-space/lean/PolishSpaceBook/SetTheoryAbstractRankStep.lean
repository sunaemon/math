module

public import PolishSpaceBook.SetTheoryAbstractTransitiveBounds
public import PolishSpaceBook.SetTheoryAbstractOrdinals

@[expose] public section

/-! # A concrete ordinal-rank step in arbitrary membership models -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

/-- The union of the successors of all graph values, without a well-foundedness
assumption on the external membership relation. -/
def IsRankStep (g b : M) : Prop :=
  ∀ z : M, member z b ↔ ∃ x y : M, GraphApplication g x y ∧ (member z y ∨ z = y)

def rankStepBody : ForcingFormulas.Formula 3 :=
  ((memberAt (3 : Fin 4) 2).iff
    ((internalApplicationFormula (1 : Fin 6) 4 5 ⊓ (memberAt 3 5 ⊔ equalAt 3 5)).ex.ex)).all

theorem realize_rankStepBody (xs : Fin 3 → M) :
    rankStepBody.Realize Empty.elim xs ↔ IsRankStep (xs 1) (xs 2) := by
  simp [rankStepBody, IsRankStep, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_sup,
    realize_memberAt, realize_equalAt, realize_internalApplicationFormula, Fin.snoc]
  rfl

/-- As in the concrete set-model construction, the step is `range ∪ ⋃range`.
It is total on every graph, even one whose values are not ordinals. -/
theorem rankStep_existsUnique (hM : M ⊨ fullZFCTheory) (a g : M) :
    ∃! b : M, rankStepBody.Realize Empty.elim ![a, g, b] := by
  simp only [realize_rankStepBody, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hp := hM.realize_of_mem _ ZFCAxiom.pairing
  have hu := hM.realize_of_mem _ ZFCAxiom.union
  obtain ⟨r, hr, _⟩ := existsUnique_graphRange hM g
  obtain ⟨u, hu, _⟩ := existsUnique_union hext hu r
  obtain ⟨b, hb, _⟩ := existsUnique_binaryUnion hext hp (hM.realize_of_mem _ ZFCAxiom.union) r u
  apply existsUnique_of_members hext
  refine ⟨b, fun z => ?_⟩
  rw [hb z, hr z, hu z]
  constructor
  · rintro (⟨x, hx⟩ | ⟨y, hzy, hyr⟩)
    · exact ⟨x, z, hx, Or.inr rfl⟩
    · obtain ⟨x, hxy⟩ := (hr y).mp hyr
      exact ⟨x, y, hxy, Or.inl hzy⟩
  · rintro ⟨x, y, hxy, hzy | rfl⟩
    · exact Or.inr ⟨y, hzy, (hr y).mpr ⟨x, hxy⟩⟩
    · exact Or.inl ⟨x, hxy⟩

theorem rankStep_ordinal {g b : M} (hb : IsRankStep g b)
    (hg : ∀ x y : M, GraphApplication g x y → IsOrdinalObject y) : IsOrdinalObject b := by
  constructor
  · intro z hz w hwz
    obtain ⟨x, y, hxy, hzy | rfl⟩ := (hb z).mp hz
    · exact (hb w).mpr ⟨x, y, hxy, Or.inl ((hg x y hxy).transitive z hzy w hwz)⟩
    · exact (hb w).mpr ⟨x, z, hxy, Or.inl hwz⟩
  · intro z hz
    obtain ⟨x, y, hxy, hzy | rfl⟩ := (hb z).mp hz
    · exact (hg x y hxy).members_transitive z hzy
    · exact (hg x z hxy).transitive

end PolishSpaceBook.SetTheoryModels.AbstractMembership
