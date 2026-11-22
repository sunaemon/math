module

public import PolishSpaceBook.SetTheoryAbstractOmegaRecursion

@[expose] public section

/-! # Internal transitive bounds in arbitrary models

Iterate Union along the internal natural-number object, collect the values,
and take their union. This construction proves the bounds needed for full
definable membership induction without external well-foundedness.
-/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def graphRangeMemberBody : ForcingFormulas.Formula 2 :=
  (internalApplicationFormula (0 : Fin 3) 2 1).ex

theorem realize_graphRangeMemberBody (xs : Fin 2 → M) :
    graphRangeMemberBody.Realize Empty.elim xs ↔ ∃ a : M, GraphApplication (xs 0) a (xs 1) := by
  simp [graphRangeMemberBody, BoundedFormula.realize_ex, realize_internalApplicationFormula, Fin.snoc]

theorem existsUnique_graphRange (hM : M ⊨ fullZFCTheory) (f : M) :
    ∃! r : M, ∀ b : M, member b r ↔ ∃ a : M, GraphApplication f a b := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hunion := hM.realize_of_mem _ ZFCAxiom.union
  obtain ⟨u, hu, _⟩ := existsUnique_union hext hunion f
  obtain ⟨v, hv, _⟩ := existsUnique_union hext hunion u
  obtain ⟨r, hr⟩ := (realize_separation M graphRangeMemberBody).mp
    (fullZFC_model_separation hM _) ![f] v
  apply existsUnique_of_members hext
  refine ⟨r, fun b => ?_⟩
  have hb : member b r ↔ member b v ∧ ∃ a : M, GraphApplication f a b := by
    simpa [realize_graphRangeMemberBody, Fin.snoc] using hr b
  exact hb.trans ⟨And.right, fun ⟨a, hab⟩ =>
    ⟨(coordinates_mem_doubleUnion hu hv hab).2, a, hab⟩⟩

theorem realize_basicUnionGraph (xs : Fin 2 → M) :
    (basicSetGraph .union).Realize Empty.elim xs ↔
      ∀ z : M, member z (xs 1) ↔ ∃ y : M, member z y ∧ member y (xs 0) := by
  simp [basicSetGraph, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, realize_memberAt, Fin.snoc]

/-- Every model element lies in an internally transitive set. The model
itself is not required to be transitive or externally well-founded. -/
theorem fullZFC_transitive_bound (hM : M ⊨ fullZFCTheory) (a : M) :
    ∃ A : M, member a A ∧ ∀ x : M, member x A → ∀ y : M, member y x → member y A := by
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hunion := hM.realize_of_mem _ ZFCAxiom.union
  obtain ⟨s, hs, _⟩ := existsUnique_pair hext (hM.realize_of_mem _ ZFCAxiom.pairing) a a
  obtain ⟨W, hW, _⟩ := existsUnique_leastInductiveObject hM
  have hstep : ∀ x : M, ∃! y : M, (basicSetGraph .union).Realize Empty.elim
      (Fin.snoc (Fin.snoc Fin.elim0 x) y) := by
    intro x
    simpa [realize_basicUnionGraph, Fin.snoc] using existsUnique_union hext hunion x
  obtain ⟨f, hf⟩ := omega_iteration_exists hM hW (basicSetGraph .union) Fin.elim0 s hstep
  have hiter := (realize_iterationBody (basicSetGraph .union) Fin.elim0 s W f).mp hf
  obtain ⟨r, hr, _⟩ := existsUnique_graphRange hM f
  obtain ⟨A, hA, _⟩ := existsUnique_union hext hunion r
  have hsrange : member s r := by
    obtain ⟨e, heW, he⟩ := hW.1.1
    exact (hr s).mpr ⟨e, hiter.2.1 e heW he⟩
  refine ⟨A, (hA a).mpr ⟨s, (hs a).mpr (Or.inl rfl), hsrange⟩, ?_⟩
  intro x hx y hyx
  obtain ⟨u, hxu, hur⟩ := (hA x).mp hx
  obtain ⟨k, hku⟩ := (hr u).mp hur
  have hkW := (hiter.1.2 k).mp ⟨u, hku⟩
  obtain ⟨l, hlW, hkl⟩ := hW.1.2 k hkW
  obtain ⟨v, hlv⟩ := (hiter.1.2 l).mpr hlW
  have huv := hiter.2.2 k l u v hlW hkl hku hlv
  have hv : ∀ z : M, member z v ↔ ∃ w : M, member z w ∧ member w u := by
    simpa [realize_basicUnionGraph, Fin.snoc] using huv
  exact (hA y).mpr ⟨v, (hv y).mpr ⟨x, hyx, hxu⟩, (hr v).mpr ⟨l, hlv⟩⟩

/-- Full definable membership induction follows from the constructed bounds
and the bounded induction theorem, retaining every formula parameter. -/
theorem fullZFC_membership_induction (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 1)) (ps : Fin p → M)
    (hstep : ∀ a : M, (∀ b : M, member b a → φ.Realize Empty.elim (Fin.snoc ps b)) →
      φ.Realize Empty.elim (Fin.snoc ps a)) :
    ∀ a : M, φ.Realize Empty.elim (Fin.snoc ps a) := by
  intro a
  obtain ⟨A, haA, hA⟩ := fullZFC_transitive_bound hM a
  exact fullZFC_definable_induction φ hM ps A hA (fun x _ => hstep x) a haA

theorem fullZFC_definable_minimum (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 1)) (ps : Fin p → M)
    (hex : ∃ a : M, φ.Realize Empty.elim (Fin.snoc ps a)) :
    ∃ a : M, φ.Realize Empty.elim (Fin.snoc ps a) ∧
      ∀ b : M, member b a → ¬φ.Realize Empty.elim (Fin.snoc ps b) := by
  obtain ⟨a, ha⟩ := hex
  obtain ⟨A, haA, hA⟩ := fullZFC_transitive_bound hM a
  obtain ⟨b, _, hb, hmin⟩ := definable_minimum_in_transitive φ
    (fullZFC_model_separation hM _) (hM.realize_of_mem _ ZFCAxiom.foundation)
    ps A hA ⟨a, haA, ha⟩
  exact ⟨b, hb, hmin⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
