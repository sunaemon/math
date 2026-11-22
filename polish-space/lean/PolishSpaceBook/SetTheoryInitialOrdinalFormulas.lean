module

public import PolishSpaceBook.SetTheoryOrdinalInitialSegments

@[expose] public section

/-! # First-order selection of predecessor order types -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def predecessorFormula {n : ℕ} (A R a D : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) D.castSucc).iff
    ((memberAt (Fin.last n) A.castSucc) ⊓
      pairMemberFormula R.castSucc (Fin.last n) a.castSucc)).all

lemma realize_predecessorFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (A R a D : Fin n) (xs : Fin n → M) :
    (predecessorFormula A R a D).Realize Empty.elim xs ↔
      (xs D).val = orderPredecessors (xs A).val (xs R).val (xs a).val := by
  simp only [predecessorFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, realize_memberAt_model, realize_pairMemberFormula_model hM,
    Fin.snoc_last, Fin.snoc_castSucc]
  change (∀ x : M, x.val ∈ (xs D).val ↔ x.val ∈ (xs A).val ∧ pair x.val (xs a).val ∈ (xs R).val) ↔ _
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [mem_orderPredecessors]
    constructor
    · intro hx
      exact (h ⟨x, hM.mem_trans hx (xs D).property⟩).mp hx
    · intro hx
      exact (h ⟨x, hM.mem_trans hx.1 (xs A).property⟩).mpr hx
  · intro he x
    rw [he, mem_orderPredecessors]

/-- Parameters A,R,a,β; witnesses D and f are sets of the model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    We now construct the representing ordinal and its graph inside the model.
    For $W,R\in M$ and $a\in W$, retain $D_a=\{x\in W:\langle x,a\rangle\in R\}$ and define
    $$\begin{aligned}
    \psi(W,R,a,\beta)\;:\equiv\;&\exists D\,\exists g\,\bigl[
      \forall x\,(x\in D\leftrightarrow
         (x\in W\land\langle x,a\rangle\in R))\\
     &\hspace{6em}{}\land\iota(D,R,\beta,g)\bigr].
    \end{aligned}$$
    This is a first-order formula whose set witnesses range over the model.
    Transitivity identifies $D$ with the actual predecessor segment.
    The recognition lemma therefore gives at most one ordinal $\beta\in M$ satisfying this formula.
-/
def initialOrdinalFormula : ForcingFormulas.Formula 4 :=
  ((predecessorFormula (0 : Fin 6) 1 2 4) ⊓
    reindex ordinalIsoFormula ![4, 1, 3, 5]).ex.ex

lemma realize_initialOrdinalFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (A R a β : M) :
    initialOrdinalFormula.Realize Empty.elim ![A, R, a, β] ↔
      ∃ D f : M, D.val = orderPredecessors A.val R.val a.val ∧
        ordinalIsoFormula.Realize Empty.elim ![D, R, β, f] := by
  have hs (D f : M) : (Fin.snoc (Fin.snoc ![A, R, a, β] D) f) ∘ ![4, 1, 3, 5] = ![D, R, β, f] := by
    funext i
    fin_cases i <;> rfl
  simp only [initialOrdinalFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_predecessorFormula hM, realize_reindex, hs]
  rfl

theorem initialOrdinal_unique {M : ZFSet.{u}} (hM : M.IsTransitive) (A R a β γ : M)
    (hβ : initialOrdinalFormula.Realize Empty.elim ![A, R, a, β])
    (hγ : initialOrdinalFormula.Realize Empty.elim ![A, R, a, γ]) : β = γ := by
  obtain ⟨D, f, hD, hf⟩ := (realize_initialOrdinalFormula hM A R a β).mp hβ
  obtain ⟨E, g, hE, hg⟩ := (realize_initialOrdinalFormula hM A R a γ).mp hγ
  have he : E = D := Subtype.ext (hE.trans hD.symm)
  subst E
  exact (internal_ordinalIso_unique hM D R β γ f g hf hg).1

end PolishSpaceBook.SetTheoryModels
