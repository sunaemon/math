module

public import PolishSpaceBook.SetTheoryAbstractOmega
public import PolishSpaceBook.SetTheoryOrdinalFormulas

@[expose] public section

/-! # Ordinals in arbitrary membership models

The literal ordinal formula says that a set and each of its members are
transitive. Comparison uses two internally separated sets of counterexamples
and Foundation, without external well-foundedness of the model.
-/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

structure IsOrdinalObject (a : M) : Prop where
  transitive : ∀ x : M, member x a → ∀ y : M, member y x → member y a
  members_transitive : ∀ x : M, member x a →
    ∀ y : M, member y x → ∀ z : M, member z y → member z x

theorem realize_ordinalFormula {n : ℕ} (i : Fin n) (xs : Fin n → M) :
    (ordinalFormula i).Realize Empty.elim xs ↔ IsOrdinalObject (xs i) := by
  simp only [ordinalFormula, BoundedFormula.realize_inf, realize_boundedAll,
    realize_transitiveFormula, Fin.snoc_last]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.transitive, h.members_transitive⟩⟩

theorem IsOrdinalObject.member {a b : M} (ha : IsOrdinalObject a) (hb : member b a) :
    IsOrdinalObject b :=
  ⟨ha.members_transitive b hb,
    fun x hx => ha.members_transitive x (ha.transitive b hb x hx)⟩

theorem ordinalObject_empty {e : M} (he : IsEmptyObject e) : IsOrdinalObject e :=
  ⟨fun x hx => False.elim (he x hx), fun x hx => False.elim (he x hx)⟩

theorem IsOrdinalObject.successor {a b : M} (ha : IsOrdinalObject a)
    (hb : IsSuccessorObject a b) : IsOrdinalObject b := by
  constructor
  · intro x hx y hy
    rcases (hb x).mp hx with hxa | rfl
    · exact (hb y).mpr (Or.inl (ha.transitive x hxa y hy))
    · exact (hb y).mpr (Or.inl hy)
  · intro x hx
    rcases (hb x).mp hx with hxa | rfl
    · exact ha.members_transitive x hxa
    · exact ha.transitive

theorem exists_successorObject (hM : M ⊨ fullZFCTheory) (a : M) :
    ∃ b : M, IsSuccessorObject a b := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hp := hM.realize_of_mem _ ZFCAxiom.pairing
  obtain ⟨s, hs, _⟩ := existsUnique_pair hext hp a a
  obtain ⟨b, hb, _⟩ := existsUnique_binaryUnion hext hp (hM.realize_of_mem _ ZFCAxiom.union) a s
  refine ⟨b, fun z => ?_⟩
  rw [hb z, hs z, or_self]

theorem ordinalObject_union {A U : M}
    (hA : ∀ a : M, member a A → IsOrdinalObject a)
    (hU : ∀ x : M, member x U ↔ ∃ a : M, member x a ∧ member a A) :
    IsOrdinalObject U := by
  constructor
  · intro x hx y hy
    obtain ⟨a, hxa, haA⟩ := (hU x).mp hx
    exact (hU y).mpr ⟨a, (hA a haA).transitive x hxa y hy, haA⟩
  · intro x hx
    obtain ⟨a, hxa, haA⟩ := (hU x).mp hx
    exact (hA a haA).members_transitive x hxa

def OrdinalComparable (a b : M) : Prop := member a b ∨ a = b ∨ member b a

def ordinalIncomparableBody : ForcingFormulas.Formula 2 :=
  (memberAt (0 : Fin 2) 1 ⊔ (equalAt 0 1 ⊔ memberAt 1 0)).not

def ordinalBadLeftBody : ForcingFormulas.Formula 2 :=
  (memberAt (2 : Fin 3) 0 ⊓ reindex ordinalIncomparableBody ![1, 2]).ex

theorem realize_ordinalIncomparableBody (xs : Fin 2 → M) :
    ordinalIncomparableBody.Realize Empty.elim xs ↔ ¬OrdinalComparable (xs 0) (xs 1) := by
  simp [ordinalIncomparableBody, OrdinalComparable, BoundedFormula.realize_not,
    BoundedFormula.realize_sup, realize_memberAt, realize_equalAt]

theorem realize_ordinalBadLeftBody (xs : Fin 2 → M) :
    ordinalBadLeftBody.Realize Empty.elim xs ↔
      ∃ y : M, member y (xs 0) ∧ ¬OrdinalComparable (xs 1) y := by
  simp [ordinalBadLeftBody, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_memberAt, realize_reindex, realize_ordinalIncomparableBody, Fin.snoc]

/-- Two minimal counterexamples inside successor bounds prove comparison in
any model of the literal ZFC axioms, including externally ill-founded models. -/
theorem ordinalObject_comparable (hM : M ⊨ fullZFCTheory) {a b : M}
    (ha : IsOrdinalObject a) (hb : IsOrdinalObject b) : OrdinalComparable a b := by
  classical
  by_contra hn
  obtain ⟨A, hA⟩ := exists_successorObject hM a
  obtain ⟨B, hB⟩ := exists_successorObject hM b
  have hAo := ha.successor hA
  have hBo := hb.successor hB
  have haA : member a A := (hA a).mpr (Or.inr rfl)
  have hbB : member b B := (hB b).mpr (Or.inr rfl)
  obtain ⟨D, hD⟩ := (realize_separation M ordinalBadLeftBody).mp
    (fullZFC_model_separation hM _) ![B] A
  have hd (x : M) : member x D ↔ member x A ∧
      ∃ y : M, member y B ∧ ¬OrdinalComparable x y := by
    simpa [realize_ordinalBadLeftBody, Fin.snoc] using hD x
  obtain ⟨x, hxD, hxmin⟩ := (models_foundation_iff M).mp
    (hM.realize_of_mem _ ZFCAxiom.foundation) D ⟨a, (hd a).mpr ⟨haA, b, hbB, hn⟩⟩
  obtain ⟨hxA, y₀, hy₀B, hxy₀⟩ := (hd x).mp hxD
  obtain ⟨E, hE⟩ := (realize_separation M ordinalIncomparableBody).mp
    (fullZFC_model_separation hM _) ![x] B
  have he (y : M) : member y E ↔ member y B ∧ ¬OrdinalComparable x y := by
    simpa [realize_ordinalIncomparableBody, Fin.snoc] using hE y
  obtain ⟨y, hyE, hymin⟩ := (models_foundation_iff M).mp
    (hM.realize_of_mem _ ZFCAxiom.foundation) E ⟨y₀, (he y₀).mpr ⟨hy₀B, hxy₀⟩⟩
  obtain ⟨hyB, hxy⟩ := (he y).mp hyE
  have hxy' : ¬member x y ∧ x ≠ y ∧ ¬member y x := by
    simpa only [OrdinalComparable, not_or] using hxy
  have hsub : ∀ z : M, member z x → member z y := by
    intro z hzx
    have hcomp : OrdinalComparable z y := by
      by_contra hbad
      exact hxmin z hzx ((hd z).mpr ⟨hAo.transitive x hxA z hzx, y, hyB, hbad⟩)
    rcases hcomp with hzy | rfl | hyz
    · exact hzy
    · exact False.elim (hxy'.2.2 hzx)
    · exact False.elim (hxy'.2.2 (hAo.members_transitive x hxA z hzx y hyz))
  have hsup : ∀ z : M, member z y → member z x := by
    intro z hzy
    have hcomp : OrdinalComparable x z := by
      by_contra hbad
      exact hymin z hzy ((he z).mpr ⟨hBo.transitive y hyB z hzy, hbad⟩)
    rcases hcomp with hxz | hzx | hzx
    · exact False.elim (hxy'.1 (hBo.members_transitive y hyB z hzy x hxz))
    · exact False.elim (hxy'.1 (hzx ▸ hzy))
    · exact hzx
  exact hxy'.2.1 ((models_extensionality_iff M).mp
    (hM.realize_of_mem _ ZFCAxiom.extensionality) x y (fun z => ⟨hsub z, hsup z⟩))

/-- Inclusion of internal ordinals is equality or strict membership. -/
theorem ordinalObject_subset_iff (hM : M ⊨ fullZFCTheory) {a b : M}
    (ha : IsOrdinalObject a) (hb : IsOrdinalObject b) :
    (∀ x : M, member x a → member x b) ↔ a = b ∨ member a b := by
  constructor
  · intro hs
    rcases ordinalObject_comparable hM ha hb with hab | he | hba
    · exact Or.inr hab
    · exact Or.inl he
    · exact False.elim (not_member_self_of_foundation
        (hM.realize_of_mem _ ZFCAxiom.pairing) (hM.realize_of_mem _ ZFCAxiom.foundation) b (hs b hba))
  · rintro (rfl | hab)
    · exact fun _ hx => hx
    · exact fun x hx => hb.transitive a hab x hx

/-- A nonempty internal set of ordinals has a least member, even when its
external membership relation is not well founded. -/
theorem ordinalObject_minimum (hM : M ⊨ fullZFCTheory) (D : M)
    (hD : ∀ a : M, member a D → IsOrdinalObject a) (hne : ∃ a : M, member a D) :
    ∃ a : M, member a D ∧ ∀ b : M, member b D → a = b ∨ member a b := by
  obtain ⟨a, haD, hmin⟩ := (models_foundation_iff M).mp
    (hM.realize_of_mem _ ZFCAxiom.foundation) D hne
  refine ⟨a, haD, ?_⟩
  intro b hbD
  rcases ordinalObject_comparable hM (hD a haD) (hD b hbD) with hab | he | hba
  · exact Or.inr hab
  · exact Or.inl he
  · exact False.elim (hmin b hba hbD)

end PolishSpaceBook.SetTheoryModels.AbstractMembership
