module

public import PolishSpaceBook.SetTheoryAbstractRecursiveSolutions

@[expose] public section

/-! # Actual formulas for internal recursive solutions and canonical domains -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def restrictionBody : ForcingFormulas.Formula 3 :=
  reindex graphOnBody ![(1 : Fin 3), 2] ⊓
    ((internalApplicationFormula (2 : Fin 5) 3 4).iff
      (memberAt 3 1 ⊓ internalApplicationFormula 0 3 4)).all.all

theorem realize_restrictionBody (xs : Fin 3 → M) :
    restrictionBody.Realize Empty.elim xs ↔ IsRestriction (xs 0) (xs 1) (xs 2) := by
  simp only [restrictionBody, BoundedFormula.realize_inf, realize_reindex,
    realize_graphOnBody, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    realize_internalApplicationFormula, realize_memberAt, IsRestriction]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.snoc]
  rfl

def recursiveBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 3)) : ForcingFormulas.Formula (p + 2) :=
  transitiveFormula (Fin.last p).castSucc ⊓
    (reindex graphOnBody ![(Fin.last p).castSucc, Fin.last (p + 1)] ⊓
      boundedAll (Fin.last p).castSucc
        ((reindex restrictionBody ![(Fin.last (p + 1)).castSucc.castSucc.castSucc,
            (Fin.last (p + 2)).castSucc.castSucc, (Fin.last (p + 3)).castSucc] ⊓
          (internalApplicationFormula (Fin.last (p + 1)).castSucc.castSucc.castSucc
            (Fin.last (p + 2)).castSucc.castSucc (Fin.last (p + 4)) ⊓
          reindex φ (Fin.snoc (Fin.snoc (Fin.snoc
            (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
            (Fin.last (p + 2)).castSucc.castSucc) (Fin.last (p + 3)).castSucc)
            (Fin.last (p + 4))))).ex.ex))

theorem realize_recursiveBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 3))
    (ps : Fin p → M) (D f : M) :
    (recursiveBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps D) f) ↔
      IsRecursiveSolution
        (fun a g b => φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) D f := by
  simp only [recursiveBody, BoundedFormula.realize_inf, realize_transitiveFormula,
    realize_reindex, realize_graphOnBody, realize_boundedAll, BoundedFormula.realize_ex,
    realize_restrictionBody, realize_internalApplicationFormula, Fin.comp_snoc,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.snoc_castSucc, Fin.snoc_last,
    IsRecursiveSolution, IsTransitiveObject]
  simp only [Function.comp_def, Fin.snoc_castSucc]

def canonicalSolutionBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 3)) :
    ForcingFormulas.Formula (p + 2) :=
  (reindex hullBody ![(Fin.last p).castSucc.castSucc, Fin.last (p + 2)] ⊓
    reindex (recursiveBody φ) (Fin.snoc (Fin.snoc
      (fun i => i.castSucc.castSucc.castSucc) (Fin.last (p + 2)))
      (Fin.last (p + 1)).castSucc)).ex

theorem realize_canonicalSolutionBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 3))
    (ps : Fin p → M) (a f : M) :
    (canonicalSolutionBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) f) ↔
      ∃ D : M, IsTransitiveHull a D ∧ IsRecursiveSolution
        (fun a g b => φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) D f := by
  simp only [canonicalSolutionBody, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, realize_hullBody, Fin.comp_snoc, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.snoc_castSucc, Fin.snoc_last]
  simp only [Function.comp_def, Fin.snoc_castSucc, realize_recursiveBody]

theorem canonicalSolution_unique (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g b c : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) →
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) c) → b = c)
    {a f g : M}
    (hf : (canonicalSolutionBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) f))
    (hg : (canonicalSolutionBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) g)) : f = g := by
  obtain ⟨D, hD, hf⟩ := (realize_canonicalSolutionBody φ ps a f).mp hf
  obtain ⟨E, hE, hg⟩ := (realize_canonicalSolutionBody φ ps a g).mp hg
  have he := transitiveHull_unique (hM.realize_of_mem _ ZFCAxiom.extensionality) hE hD
  subst E
  exact recursiveSolution_unique hM hφ hf hg

end PolishSpaceBook.SetTheoryModels.AbstractMembership
