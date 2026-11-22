module

public import PolishSpaceBook.SetTheoryRankClosure

@[expose] public section

/-! # Internal power-set equality and images under the internal power-set operation -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma realize_boundedAll_model (M : ZFSet.{u}) {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) :
    (boundedAll i φ).Realize Empty.elim xs ↔
      ∀ y : M, y.val ∈ (xs i).val → φ.Realize Empty.elim (Fin.snoc xs y) :=
  realize_boundedAll (M : ZFClass) i φ xs

/-- This formula describes the model's power set, without using M as an internal parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{InternalPowerSet,InternalHierarchy}
    \end{mathmeta}
    For a transitive set $M$, write
    $$\InternalPowerSet{M}{x}:=\PowerSet{x}\cap M.$$
    The internal power set is defined by the first-order formula
    $$\pi(x,p)\;:\equiv\;
    \forall z\,\bigl(z\in p\leftrightarrow\forall w\in z\,(w\in x)\bigr).$$
    For $x,p\in M$, transitivity gives
    $$M\models\pi(x,p)\quad\Longleftrightarrow\quad p=\InternalPowerSet{M}{x}.$$
    The symbol $M$ does not occur as a parameter in this formula: its quantifiers are interpreted in the model.
    If the model satisfies Power Set, then $\InternalPowerSet{M}{x}\in M$ for each $x\in M$.
    For $R\in M$, Replacement applied to $\pi$ therefore collects
    $$S=\{\InternalPowerSet{M}{r}:r\in R\}\in M.$$
    The corresponding image formula is
    $$\chi(R,S)\;:\equiv\;
    \forall p\,\bigl(p\in S\leftrightarrow\exists r\in R\,\pi(r,p)\bigr).$$
    Its internal interpretation is exactly the displayed equality for $S$.
-/
def powerEqFormula {n : ℕ} (x p : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) p.castSucc).iff
    (boundedAll (Fin.last n) (memberAt (Fin.last (n + 1)) x.castSucc.castSucc))).all

lemma realize_powerEqFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x p : Fin n) (xs : Fin n → M) :
    (powerEqFormula x p).Realize Empty.elim xs ↔ (xs p).val = internalPowerSet M (xs x).val := by
  simp only [powerEqFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    realize_boundedAll_model, realize_memberAt_model, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [internalPowerSet, ZFSet.mem_sep]
    constructor
    · intro hz
      have hzM := hM.mem_trans hz (xs p).property
      exact ⟨hzM, (subset_iff_internal hM hzM).mpr ((h ⟨z, hzM⟩).mp hz)⟩
    · rintro ⟨hzM, hsub⟩
      exact (h ⟨z, hzM⟩).mpr ((subset_iff_internal hM hzM).mp hsub)
  · intro he z
    rw [he, internalPowerSet, ZFSet.mem_sep]
    exact ⟨fun hz => (subset_iff_internal hM z.property).mp hz.2,
      fun hz => ⟨z.property, (subset_iff_internal hM z.property).mpr hz⟩⟩

def powerImage (M R : ZFSet.{u}) : ZFSet.{u} := ZFSet.range (fun r : R => internalPowerSet M r.val)

lemma powerImage_mem {M R : ZFSet.{u}} (hM : M.IsTransitive) (hpower : M ⊨ powerSentence)
    (hrep : M ⊨ replacementSentence (powerEqFormula (0 : Fin 2) 1)) (hR : R ∈ M) :
    powerImage M R ∈ M := by
  let f : R → M := fun r => ⟨internalPowerSet M r.val,
    internalPowerSet_mem hM hpower (hM.mem_trans r.property hR)⟩
  apply replacement_image_mem hM (powerEqFormula (0 : Fin 2) 1) hrep Fin.elim0 hR f
  intro a b
  have he : (powerEqFormula (0 : Fin 2) 1).Realize Empty.elim
      (Fin.snoc (Fin.snoc Fin.elim0 ⟨a.val, hM.mem_trans a.property hR⟩) b) ↔
      b.val = internalPowerSet M a.val := by
    simpa [Fin.snoc] using realize_powerEqFormula hM (0 : Fin 2) 1
      (Fin.snoc (Fin.snoc Fin.elim0 ⟨a.val, hM.mem_trans a.property hR⟩) b)
  exact he.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

def powerImageMemberFormula {n : ℕ} (R p : Fin n) : ForcingFormulas.Formula n :=
  boundedExists R (powerEqFormula (Fin.last n) p.castSucc)

def powerImageFormula {n : ℕ} (R S : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) S.castSucc).iff (powerImageMemberFormula R.castSucc (Fin.last n))).all

lemma realize_powerImageMemberFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (R p : Fin n) (xs : Fin n → M) :
    (powerImageMemberFormula R p).Realize Empty.elim xs ↔ (xs p).val ∈ powerImage M (xs R).val := by
  simp only [powerImageMemberFormula, realize_boundedExists_model, realize_powerEqFormula hM,
    Fin.snoc_last, Fin.snoc_castSucc, powerImage, ZFSet.mem_range]
  constructor
  · rintro ⟨r, hr, he⟩
    exact ⟨⟨r.val, hr⟩, he.symm⟩
  · rintro ⟨r, he⟩
    exact ⟨⟨r.val, hM.mem_trans r.property (xs R).property⟩, r.property, he.symm⟩

lemma realize_powerImageFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (hpower : M ⊨ powerSentence)
    {n : ℕ} (R S : Fin n) (xs : Fin n → M) :
    (powerImageFormula R S).Realize Empty.elim xs ↔ (xs S).val = powerImage M (xs R).val := by
  simp only [powerImageFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    realize_memberAt_model, realize_powerImageMemberFormula hM, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro p
    constructor
    · intro hp; exact (h ⟨p, hM.mem_trans hp (xs S).property⟩).mp hp
    · intro hp
      obtain ⟨r, rfl⟩ := ZFSet.mem_range.mp hp
      have hpM := internalPowerSet_mem hM hpower (hM.mem_trans r.property (xs R).property)
      exact (h ⟨_, hpM⟩).mpr hp
  · intro he p; rw [he]

end PolishSpaceBook.SetTheoryModels
