module

public import PolishSpaceBook.SetTheoryInternalHulls

@[expose] public section

/-! # Collecting unique recursive solutions on canonical internal domains -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Parameters are those of ψ followed by A and its internal power set; input and output come last. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Combining this formula with $\sigma(D,f,\vec p)$ gives a fixed first-order formula
    asserting that $f$ is a partial solution on $D_a$. Its parameters are $A,B,\vec p$.
-/
def hullSolutionFormula {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) : ForcingFormulas.Formula (n + 4) :=
  (hullFormula (Fin.last n).castSucc.castSucc.castSucc.castSucc
      (Fin.last (n + 1)).castSucc.castSucc.castSucc (Fin.last (n + 2)).castSucc.castSucc (Fin.last (n + 4)) ⊓
    recursiveSolutionFormula ψ (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc).ex

lemma realize_hullSolutionFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → M)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : M,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (A B a f : M) (hB : B.val = internalPowerSet M A.val) :
    (hullSolutionFormula ψ).Realize Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps A) B) a) f) ↔
      IsRecursiveSolution H (internalHull M A.val a.val) f.val := by
  have hh (D : M) :
      (hullFormula (Fin.last n).castSucc.castSucc.castSucc.castSucc
        (Fin.last (n + 1)).castSucc.castSucc.castSucc (Fin.last (n + 2)).castSucc.castSucc
        (Fin.last (n + 4))).Realize (M := M) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps A) B) a) f) D) ↔
        D.val = internalHull M A.val a.val := by
    exact (realize_hullFormula_set M hM _ _ _ _ _).trans
      (by simp only [Fin.snoc_last, Fin.snoc_castSucc, hB, internalHull])
  have hs (D : M) :
      (recursiveSolutionFormula ψ (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc).Realize Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps A) B) a) f) D) ↔
        IsRecursiveSolution H D.val f.val := by
    simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
      (recursiveSolutionFormula_iff hM hunion (hsep productSeparationFormula) ψ
        (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps A) B) a) f) D) H
        (by simpa only [Function.comp_def, Fin.snoc_castSucc] using hH))
  simp only [hullSolutionFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf, hh, hs]
  constructor
  · rintro ⟨D, he, hsol⟩
    exact he ▸ hsol
  · intro hsol
    exact ⟨⟨internalHull M A.val a.val,
      internalHull_mem hM hpower (hsep _) A.property a.property⟩, rfl, hsol⟩

/-- The union of the canonical domains of inputs in X. -/
abbrev hullUnion (M A X : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion (fun a : X => internalHull M A a.val)

/-- Unique local solutions form an internal set by Replacement, and Union glues them. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The internal-definition lemma identifies its solutions with actual partial solutions, and the agreement
    lemma makes the output graph unique. Hence, whenever these solutions exist for all inputs in a set
    $X\in M$ with $X\IncludedIn A$, Replacement collects both $\{D_a:a\in X\}$ and
    $\{f_a:a\in X\}$ inside $M$. Union then gives a partial solution on $\bigcup_{a\in X}D_a$ inside $M$.
-/
theorem collect_hull_solutions {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → M)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : M,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (A : M) {X : ZFSet.{u}} (hX : X ∈ M)
    (hlocal : ∀ a : X, ∃ f : M, IsRecursiveSolution H (internalHull M A.val a.val) f.val) :
    hullUnion M A.val X ∈ M ∧ ∃ f ∈ M, IsRecursiveSolution H (hullUnion M A.val X) f := by
  classical
  let B : M := ⟨internalPowerSet M A.val, internalPowerSet_mem hM hpower A.property⟩
  let F : X → M := fun a => (hlocal a).choose
  have hF (a : X) : IsRecursiveSolution H (internalHull M A.val a.val) (F a).val := (hlocal a).choose_spec
  have hcollectF : ZFSet.range (fun a : X => (F a).val) ∈ M := by
    apply replacement_image_mem hM (hullSolutionFormula ψ) (hrep _) (Fin.snoc (Fin.snoc ps A) B) hX F
    intro a f
    rw [realize_hullSolutionFormula hM hunion hpower hsep ψ ps H hH A B
      ⟨a.val, hM.mem_trans a.property hX⟩ f rfl]
    constructor
    · intro hf
      exact Subtype.ext (recursive_solution_unique hf (hF a))
    · rintro rfl
      exact hF a
  let D : X → M := fun a => ⟨internalHull M A.val a.val,
    internalHull_mem hM hpower (hsep _) A.property (hM.mem_trans a.property hX)⟩
  have hcollectD : ZFSet.range (fun a : X => (D a).val) ∈ M := by
    apply replacement_image_mem hM (hullFormula (0 : Fin 4) 1 2 3) (hrep _) ![A, B] hX D
    intro a d
    have hh : (hullFormula (0 : Fin 4) 1 2 3).Realize (M := M) Empty.elim
        (Fin.snoc (Fin.snoc ![A, B] ⟨a.val, hM.mem_trans a.property hX⟩) d) ↔
        d.val = internalHull M A.val a.val := by
      exact (realize_hullFormula_set M hM _ _ _ _ _).trans
        (by simp [Fin.snoc, B, internalHull])
    rw [hh]
    exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
  have hglue := recursive_solution_iUnion_mem hM hunion (fun a : X => (D a).val)
    (fun a : X => (F a).val) hF hcollectD hcollectF
  exact ⟨hglue.1, _, hglue.2.1, hglue.2.2⟩

end PolishSpaceBook.SetTheoryModels
