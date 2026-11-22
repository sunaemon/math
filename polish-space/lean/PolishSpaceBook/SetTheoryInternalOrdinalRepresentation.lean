module

public import PolishSpaceBook.SetTheoryInternalOrdinalGluing
public import PolishSpaceBook.SetTheoryInternalOrderMinima

@[expose] public section

/-! # Ordinal representations constructed inside a transitive model

Separate the set of points whose predecessor segment has no internal ordinal
representation. An internal minimum of that set contradicts the gluing theorem.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def badInitialFormula : ForcingFormulas.Formula 3 := initialOrdinalFormula.ex.not

lemma realize_badInitialFormula (M : ZFSet.{u}) (A R a : M) :
    badInitialFormula.Realize Empty.elim ![A, R, a] ↔
      ¬ ∃ β : M, initialOrdinalFormula.Realize Empty.elim ![A, R, a, β] := by
  have hs (β : M) : Fin.snoc ![A, R, a] β = ![A, R, a, β] := by
    funext i
    fin_cases i <;> rfl
  simp only [badInitialFormula, BoundedFormula.realize_not, BoundedFormula.realize_ex, hs]

lemma strictTotalOrder_on_subset {A D R : ZFSet.{u}}
    [IsStrictTotalOrder A (fun x y : A => pair x.val y.val ∈ R)] (hDA : D ⊆ A) :
    IsStrictTotalOrder D (fun x y : D => pair x.val y.val ∈ R) := by
  let j : D → A := fun x => ⟨x.val, hDA x.property⟩
  exact {
    irrefl := fun x => irrefl_of (fun x y : A => pair x.val y.val ∈ R) (j x)
    trans := fun x y z => trans_of (fun x y : A => pair x.val y.val ∈ R)
      (a := j x) (b := j y) (c := j z)
    trichotomous := by
      intro x y hxy hyx
      rcases trichotomous_of (fun x y : A => pair x.val y.val ∈ R) (j x) (j y) with h | he | h
      · exact False.elim (hxy h)
      · exact Subtype.ext (congrArg (fun z : A => z.val) he)
      · exact False.elim (hyx h) }

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Separation applied to $\neg\exists\beta\,\psi(W,R,a,\beta)$ gives the set of bad points
    $$B:=\{a\in W:M\models\neg\exists\beta\,\psi(W,R,a,\beta)\}\in M.$$
    If it is nonempty, $M\models\chi(W,R)$ gives a least bad point $b\in B$.
    The predecessor set $D_b$ belongs to $M$ by Separation.
    For every $x\in D_b$, minimality gives an internal ordinal representation of $D_x$.
    Transitivity of the order identifies $D_x$ with the predecessor segment of $x$ inside $D_b$.
    The gluing lemma applied to $D_b$ therefore constructs an ordinal representation of $D_b$ in $M$.
    It witnesses $\exists\beta\,\psi(W,R,b,\beta)$, contradicting $b\in B$.
    Thus no point is bad. Apply the gluing lemma once more, now to $W$, to obtain the required representation.
    Uniqueness follows from the recognition lemma.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal ordinal representation theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The ordinal representation theorem in §{sec:ordinals-representation} supplies external existence and uniqueness.
    Here we prove the additional assertion that the ordinal and its whole isomorphism graph belong to the model.
    The construction uses internal minimality and explicit Replacement instances, rather than assuming that an
    external representing map is internal.
-/
theorem internal_ordinal_representation {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (A R : M) [IsStrictTotalOrder A.val (fun x y : A.val => pair x.val y.val ∈ R.val)]
    (hmin : internalOrderMinimaFormula.Realize Empty.elim ![A, R]) :
    ∃ α F : M, ordinalIsoFormula.Realize Empty.elim ![A, R, α, F] := by
  obtain ⟨B, hB⟩ := (realize_separation M badInitialFormula).mp (hsep _) ![A, R] A
  have hs (a : M) : Fin.snoc ![A, R] a = ![A, R, a] := by
    funext i
    fin_cases i <;> rfl
  simp only [hs, realize_badInitialFormula] at hB
  have hBA : B.val ⊆ A.val := by
    intro a ha
    exact ((hB ⟨a, hM.mem_trans ha B.property⟩).mp ha).1
  have hgood (a : A.val) : ∃ β : M, initialOrdinalFormula.Realize Empty.elim
      ![A, R, ⟨a.val, hM.mem_trans a.property A.property⟩, β] := by
    by_contra hn
    have haB : a.val ∈ B.val := (hB ⟨a.val, hM.mem_trans a.property A.property⟩).mpr ⟨a.property, hn⟩
    obtain ⟨b, hbB, hbmin⟩ :=
      (realize_internalOrderMinimaFormula hM A R).mp hmin B hBA ⟨a.val, haB⟩
    let bA : A.val := ⟨b, hBA hbB⟩
    let bM : M := ⟨b, hM.mem_trans hbB B.property⟩
    let D : M := ⟨orderPredecessors A.val R.val b,
      orderPredecessors_mem hM (hsep _) A.property R.property bM.property⟩
    have hDA : D.val ⊆ A.val := fun _ hx => (mem_orderPredecessors.mp hx).1
    let := strictTotalOrder_on_subset (R := R.val) hDA
    have hlocal (x : D.val) : ∃ β : M, initialOrdinalFormula.Realize Empty.elim
        ![D, R, ⟨x.val, hM.mem_trans x.property D.property⟩, β] := by
      let xM : M := ⟨x.val, hM.mem_trans x.property D.property⟩
      have hxR : pair x.val b ∈ R.val := (mem_orderPredecessors.mp x.property).2
      have hxgood : ∃ β : M, initialOrdinalFormula.Realize Empty.elim ![A, R, xM, β] := by
        by_contra hbad
        have hxB : x.val ∈ B.val := (hB xM).mpr ⟨hDA x.property, hbad⟩
        exact hbmin x.val hxB hxR
      obtain ⟨β, hβ⟩ := hxgood
      obtain ⟨E, f, hE, hf⟩ := (realize_initialOrdinalFormula hM A R xM β).mp hβ
      have hnest : orderPredecessors D.val R.val x.val = orderPredecessors A.val R.val x.val :=
        orderPredecessors_nested (a := ⟨x.val, hDA x.property⟩) (b := bA) hxR
      exact ⟨β, (realize_initialOrdinalFormula hM D R xM β).mpr ⟨E, f, hE.trans hnest.symm, hf⟩⟩
    obtain ⟨β, f, hf⟩ := internal_ordinalIso_glue hM hpair hrep D R hlocal
    exact ((hB bM).mp hbB).2 ⟨β,
      (realize_initialOrdinalFormula hM A R bM β).mpr ⟨D, f, rfl, hf⟩⟩
  exact internal_ordinalIso_glue hM hpair hrep A R hgood

end PolishSpaceBook.SetTheoryModels
