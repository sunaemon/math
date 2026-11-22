module

public import PolishSpaceBook.SetTheoryAbstractRecursiveFormulas
public import PolishSpaceBook.SetTheoryAbstractRecursiveExtension

@[expose] public section

/-! # Definable membership recursion in arbitrary ZFC models

Canonical transitive hulls make predecessor solution graphs single-valued.
Replacement collects those graphs; their union and a one-point extension
give the next canonical solution. The induction is internal formula induction.
-/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

theorem canonicalSolution_existsUnique (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g : M, ∃! b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) (a : M) :
    ∃! f : M, (canonicalSolutionBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) f) := by
  let R := fun a g b : M => φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hR : ∀ a g b c : M, R a g b → R a g c → b = c := by
    intro a g b c hb hc
    obtain ⟨d, _, hd⟩ := hφ a g
    exact (hd b hb).trans (hd c hc).symm
  have hex : ∀ a : M, (canonicalSolutionBody φ).ex.Realize Empty.elim (Fin.snoc ps a) := by
    apply fullZFC_membership_induction hM (canonicalSolutionBody φ).ex ps
    intro a ih
    have hpred (b : M) (hba : member b a) :
        ∃! f : M, (canonicalSolutionBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps b) f) := by
      obtain ⟨f, hf⟩ := BoundedFormula.realize_ex.mp (ih b hba)
      exact ⟨f, hf, fun g hg => canonicalSolution_unique hM φ ps hR hg hf⟩
    obtain ⟨F, hF⟩ := (realize_replacement M (canonicalSolutionBody φ)).mp
      (hM.realize_of_mem _ (ZFCAxiom.replacement _)) ps a hpred
    have hfamily (f : M) (hfF : member f F) : ∃ D : M, IsRecursiveSolution R D f := by
      obtain ⟨b, _, hf⟩ := (hF f).mp hfF
      obtain ⟨D, _, hDf⟩ := (realize_canonicalSolutionBody φ ps b f).mp hf
      exact ⟨D, hDf⟩
    obtain ⟨U, H, hUH, happ⟩ := recursiveSolutions_union hM hR F hfamily
    obtain ⟨D, hD, _⟩ := existsUnique_transitiveHull hM a
    have hUD : ∀ x : M, member x U → member x D := by
      intro x hxU
      obtain ⟨y, hxy⟩ := (hUH.2.1.2 x).mpr hxU
      obtain ⟨f, hfF, hfxy⟩ := (happ x y).mp hxy
      obtain ⟨b, hba, hf⟩ := (hF f).mp hfF
      obtain ⟨E, hE, hEf⟩ := (realize_canonicalSolutionBody φ ps b f).mp hf
      exact hE.2.2 D hD.2.1 (hD.2.1 a hD.1 b hba) x ((hEf.2.1.2 x).mp ⟨y, hfxy⟩)
    have hcover : ∀ b : M, member b a → member b U := by
      intro b hba
      obtain ⟨f, hf, _⟩ := hpred b hba
      obtain ⟨E, hE, hEf⟩ := (realize_canonicalSolutionBody φ ps b f).mp hf
      obtain ⟨c, hfbc⟩ := (hEf.2.1.2 b).mpr hE.1
      exact (hUH.2.1.2 b).mp ⟨c, (happ b c).mpr ⟨f, (hF f).mpr ⟨b, hba, hf⟩, hfbc⟩⟩
    apply BoundedFormula.realize_ex.mpr
    by_cases haU : member a U
    · have hDU := hD.2.2 U hUH.1 haU
      have hUD' : U = D := (models_extensionality_iff M).mp hext U D
        (fun x => ⟨hUD x, hDU x⟩)
      subst U
      exact ⟨H, (realize_canonicalSolutionBody φ ps a H).mpr ⟨D, hD, hUH⟩⟩
    · obtain ⟨r, hr⟩ := exists_restriction hM hUH.2.1 hcover
      obtain ⟨b, hb, _⟩ := hφ a r
      obtain ⟨B, g, hB, hg, _⟩ := recursiveSolution_extend hM hUH haU hcover hr hb
      have haB : member a B := (hB a).mpr (Or.inr rfl)
      have hDB := hD.2.2 B hg.1 haB
      have hBD : B = D := (models_extensionality_iff M).mp hext B D (fun x => by
        refine ⟨fun hx => ?_, hDB x⟩
        rcases (hB x).mp hx with hx | rfl
        · exact hUD x hx
        · exact hD.1)
      subst B
      exact ⟨g, (realize_canonicalSolutionBody φ ps a g).mpr ⟨D, hD, hg⟩⟩
  obtain ⟨f, hf⟩ := BoundedFormula.realize_ex.mp (hex a)
  exact ⟨f, hf, fun g hg => canonicalSolution_unique hM φ ps hR hg hf⟩

/-- The value formula asks for a recursive solution on the canonical hull
and reads its value at the specified input. -/
def recursiveValueBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 3)) :
    ForcingFormulas.Formula (p + 2) :=
  (reindex (canonicalSolutionBody φ) (Fin.snoc (Fin.snoc
      (fun i => i.castSucc.castSucc.castSucc) (Fin.last p).castSucc.castSucc)
      (Fin.last (p + 2))) ⊓
    internalApplicationFormula (Fin.last (p + 2)) (Fin.last p).castSucc.castSucc
      (Fin.last (p + 1)).castSucc).ex

theorem realize_recursiveValueBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 3))
    (ps : Fin p → M) (a b : M) :
    (recursiveValueBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) ↔
      ∃ D f : M, IsTransitiveHull a D ∧ IsRecursiveSolution
        (fun a g b => φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) D f ∧
          GraphApplication f a b := by
  simp only [recursiveValueBody, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, Fin.comp_snoc, realize_internalApplicationFormula, Fin.snoc_castSucc,
    Fin.snoc_last]
  simp only [Function.comp_def, Fin.snoc_castSucc, realize_canonicalSolutionBody]
  constructor
  · rintro ⟨f, ⟨D, hD, hf⟩, hab⟩
    exact ⟨D, f, hD, hf, hab⟩
  · rintro ⟨D, f, hD, hf, hab⟩
    exact ⟨f, ⟨D, hD, hf⟩, hab⟩

/-- Total unique values for the actual recursively defined formula. -/
theorem recursiveValue_existsUnique (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g : M, ∃! b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) (a : M) :
    ∃! b : M, (recursiveValueBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  obtain ⟨f, hf, _⟩ := canonicalSolution_existsUnique hM φ ps hφ a
  obtain ⟨D, hD, hDf⟩ := (realize_canonicalSolutionBody φ ps a f).mp hf
  obtain ⟨b, hab⟩ := (hDf.2.1.2 a).mpr hD.1
  refine ⟨b, (realize_recursiveValueBody φ ps a b).mpr ⟨D, f, hD, hDf, hab⟩, ?_⟩
  intro c hc
  obtain ⟨E, g, hE, hEg, hac⟩ := (realize_recursiveValueBody φ ps a c).mp hc
  have hR : ∀ a g b c : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) →
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) c) → b = c := by
    intro a g b c hb hc
    obtain ⟨d, _, hd⟩ := hφ a g
    exact (hd b hb).trans (hd c hc).symm
  exact recursiveSolutions_agree hM hR hEg hDf a c b hac hab

end PolishSpaceBook.SetTheoryModels.AbstractMembership
