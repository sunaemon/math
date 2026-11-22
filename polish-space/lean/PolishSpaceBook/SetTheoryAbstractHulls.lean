module

public import PolishSpaceBook.SetTheoryAbstractTransitiveBounds

@[expose] public section

/-! # Canonical internal transitive hulls -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def IsTransitiveObject (A : M) : Prop :=
  ∀ a : M, member a A → ∀ b : M, member b a → member b A

def IsTransitiveHull (a D : M) : Prop :=
  member a D ∧ IsTransitiveObject D ∧
    ∀ T : M, IsTransitiveObject T → member a T → ∀ z : M, member z D → member z T

def hullMembershipBody : ForcingFormulas.Formula 2 :=
  ((transitiveFormula (2 : Fin 3) ⊓ memberAt 0 2).imp (memberAt 1 2)).all

theorem realize_hullMembershipBody (xs : Fin 2 → M) :
    hullMembershipBody.Realize Empty.elim xs ↔
      ∀ T : M, IsTransitiveObject T → member (xs 0) T → member (xs 1) T := by
  simp [hullMembershipBody, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, realize_transitiveFormula, realize_memberAt,
    IsTransitiveObject, Fin.snoc, and_imp]

def hullBody : ForcingFormulas.Formula 2 :=
  ((memberAt (2 : Fin 3) 1).iff (reindex hullMembershipBody ![0, 2])).all

theorem realize_hullBody (xs : Fin 2 → M) :
    hullBody.Realize Empty.elim xs ↔ IsTransitiveHull (xs 0) (xs 1) := by
  have he : hullBody.Realize Empty.elim xs ↔ ∀ z : M,
      member z (xs 1) ↔ ∀ T : M, IsTransitiveObject T → member (xs 0) T → member z T := by
    simp [hullBody, BoundedFormula.realize_all, BoundedFormula.realize_iff,
      realize_memberAt, realize_reindex, realize_hullMembershipBody, Fin.snoc]
  rw [he]
  constructor
  · intro h
    refine ⟨(h (xs 0)).mpr (fun _ _ ha => ha), ?_, fun T ht ha z hz => (h z).mp hz T ht ha⟩
    intro a ha b hb
    exact (h b).mpr (fun T ht hT => ht a ((h a).mp ha T ht hT) b hb)
  · intro h z
    exact ⟨fun hz T ht ha => h.2.2 T ht ha z hz, fun hz => hz (xs 1) h.2.1 h.1⟩

theorem transitiveHull_unique (hext : M ⊨ extensionalitySentence) {a D E : M}
    (hD : IsTransitiveHull a D) (hE : IsTransitiveHull a E) : D = E := by
  apply (models_extensionality_iff M).mp hext D E
  intro z
  exact ⟨hD.2.2 E hE.2.1 hE.1 z, hE.2.2 D hD.2.1 hD.1 z⟩

/-- The intersection of all internally transitive sets containing `a` is
obtained by a single Separation instance inside a constructed bound. -/
theorem existsUnique_transitiveHull (hM : M ⊨ fullZFCTheory) (a : M) :
    ∃! D : M, IsTransitiveHull a D := by
  obtain ⟨A, haA, hA⟩ := fullZFC_transitive_bound hM a
  obtain ⟨D, hD⟩ := (realize_separation M hullMembershipBody).mp
    (fullZFC_model_separation hM _) ![a] A
  have hd (z : M) : member z D ↔
      ∀ T : M, IsTransitiveObject T → member a T → member z T := by
    have hh : member z D ↔ member z A ∧
        ∀ T : M, IsTransitiveObject T → member a T → member z T := by
      simpa [realize_hullMembershipBody, Fin.snoc] using hD z
    exact hh.trans ⟨And.right, fun h => ⟨h A hA haA, h⟩⟩
  have hh : IsTransitiveHull a D := by
    refine ⟨(hd a).mpr (fun _ _ ha => ha), ?_, fun T ht ha z hz => (hd z).mp hz T ht ha⟩
    intro z hz y hy
    exact (hd y).mpr (fun T ht ha => ht z ((hd z).mp hz T ht ha) y hy)
  exact ⟨D, hh, fun E hE => transitiveHull_unique (hM.realize_of_mem _ ZFCAxiom.extensionality) hE hh⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
