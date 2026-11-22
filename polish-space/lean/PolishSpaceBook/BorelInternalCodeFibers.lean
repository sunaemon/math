module

public import PolishSpaceBook.BorelInternalCodeRecognition
public import PolishSpaceBook.BorelCanonicalBasis
public import PolishSpaceBook.CantorInternalMeasureBorelValues
public import PolishSpaceBook.SetTheoryDefinableFibers

@[expose] public section

/-! # A uniform formula identifying the internal set represented by a Borel code -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate CantorTreeMeasure
universe u

/-- Parameters finite words, label graph, selected label, candidate slice. -/
def labelSlicePredicate : BoundedSetPredicate 4 :=
  .conj (.subset 3 0) (.all 0 (.iff (.member 4 3) (.pairMember 1 4 2)))

lemma eval_labelSlicePredicate (l a S : ZFSet.{u}) :
    labelSlicePredicate.eval ![finiteSequences, l, a, S] ↔ S = labelSlice l a := by
  change (S ⊆ finiteSequences ∧ ∀ s ∈ finiteSequences, s ∈ S ↔ pair s a ∈ l) ↔ _
  constructor
  · rintro ⟨hS, h⟩
    ext s
    rw [labelSlice, ZFSet.mem_sep]
    exact ⟨fun hs => ⟨hS hs, (h s (hS hs)).mp hs⟩, fun ⟨hs, hl⟩ => (h s hs).mpr hl⟩
  · rintro rfl
    exact ⟨fun _ hs => (ZFSet.mem_sep.mp hs).1,
      fun s hs => ZFSet.mem_sep.trans (and_iff_right hs)⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

include hM hinf hpair hunion hpower hsep in
lemma realize_cantorInterpretationFiber (c : BorelExpression) (hw : WellFounded c.Child)
    (Ω T R U C l B Y e A : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hT : T.val = finiteSequences)
    (hR : R.val = childRelation c.labelGraph)
    (hU : U.val = labelSlice c.labelGraph (natOrdinal 1))
    (hC : C.val = labelSlice c.labelGraph (natOrdinal 2))
    (hl : l.val = c.labelGraph) (hB : B.val = basisWordGraph NamedLambda.NatListCode.decode)
    (hY : Y.val = internalCantor M) (he : e.val = wordGraph []) :
    (choiceFiberFormula interpretationFormula).Realize Empty.elim
      ![Ω,T,R,U,C,l,B,Y,e,A] ↔ A.val = internalBorelCantorSet M c hw := by
  have hv : ![Ω,T,R,U,C,l,B,Y,e,A] =
      Fin.snoc (Fin.snoc (Fin.snoc ![Ω,T,R,U,C,l,B] Y) e) A := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  apply realize_choiceFiber_eq hM
  · intro g hg
    exact hY.symm ▸ (ZFSet.mem_inter.mp hg).2
  · intro g hgY
    obtain ⟨x, hx, hxM⟩ := mem_internalCantor.mp (hY ▸ hgY)
    have hv' : Fin.snoc (Fin.snoc ![Ω,T,R,U,C,l,B] e) g = ![Ω,T,R,U,C,l,B,e,g] := by
      funext i; fin_cases i <;> rfl
    rw [hv', realize_interpretationFormula_graphs hM hinf hpair hunion hpower hsep c hw
      NamedLambda.NatListCode.decode (cantorInclusion x) Ω T R U C l B e g
      hΩ hT hR hU hC hl hB [] he hx.symm, ← hx,
      cantorPointGraph_mem_internalBorelCantorSet, and_iff_right (hx.symm ▸ hxM)]
    rfl

/-- Parameters omega, words, zero, one, two, root, word square, basis, Cantor space,
    candidate-code set, prescribed set, proposed label graph. Witnesses are R,U,C. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Uniform recognition of Borel representatives
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Require $\ell\in\mathcal C$. Quantify its live-child relation $R_\ell$ and the two slices of nodes labeled
    $1$ and $2$, using their bounded graph-membership definitions. For these parameters, the evaluation formula
    of §{sec:internal-borel-evaluations} recognizes membership of an internal point in the root interpretation.
    Require that $A$ be precisely its fiber inside $Y$: for every $g$ in the model, $g\in A$ if and only if
    $g\in Y$ and the root evaluation accepts $g$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    This is a single formula with $A$ and $\ell$ free. The validity test supplies a well-founded code, so the
    point-evaluation theorem identifies its fiber with $\BorelInterpretation{c}{M}$.
    Transitivity ensures that every element of either set is in the model; extensionality therefore identifies
    the whole sets. Conversely, the relation and slices of any such code belong to $M$, and the same pointwise
    comparison verifies the formula. We reuse the evaluation formula rather than a separate formula for each code.
-/
def representsCodeFormula : ForcingFormulas.Formula 12 :=
  memberAt 11 9 ⊓
    (reindex childGraphPredicate.compile ![0,1,2,11,6,12] ⊓
      reindex labelSlicePredicate.compile ![1,11,3,13] ⊓
      reindex labelSlicePredicate.compile ![1,11,4,14] ⊓
      reindex (choiceFiberFormula interpretationFormula) ![0,1,12,13,14,11,7,8,5,10]).ex.ex.ex

include hM hinf hpair hunion hpower hsep in
lemma realize_representsCodeFormula_of_code (c : BorelExpression) (hc : c.Valid)
    (Ω T z o b e K B Y Codes A l : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hT : T.val = finiteSequences)
    (hz : z.val = natOrdinal 0) (ho : o.val = natOrdinal 1) (hb : b.val = natOrdinal 2)
    (he : e.val = wordGraph []) (hK : K.val = ZFSet.prod finiteSequences finiteSequences)
    (hB : B.val = basisWordGraph NamedLambda.NatListCode.decode)
    (hY : Y.val = internalCantor M) (hCodes : Codes.val = internalValidCodes M)
    (hl : l.val = c.labelGraph) :
    representsCodeFormula.Realize Empty.elim ![Ω,T,z,o,b,e,K,B,Y,Codes,A,l] ↔
      A.val = internalBorelCantorSet M c hc.2.2.2.2.2 := by
  let xs : Fin 12 → M := ![Ω,T,z,o,b,e,K,B,Y,Codes,A,l]
  let ys (R U C : M) : Fin 15 → M := Fin.snoc (Fin.snoc (Fin.snoc xs R) U) C
  have hr (R U C : M) : (reindex childGraphPredicate.compile ![0,1,2,11,6,12]).Realize
      Empty.elim (ys R U C) ↔ R.val = childRelation c.labelGraph := by
    rw [realize_reindex, childGraphPredicate.realize_compile hM]
    have hv : Subtype.val ∘ (ys R U C ∘ ![0,1,2,11,6,12]) =
        ![Ω.val,T.val,z.val,l.val,K.val,R.val] := by funext i; fin_cases i <;> rfl
    rw [hv, hΩ, hT, hz, hl, hK, eval_childGraphPredicate]
  have hu (R U C : M) : (reindex labelSlicePredicate.compile ![1,11,3,13]).Realize
      Empty.elim (ys R U C) ↔ U.val = labelSlice c.labelGraph (natOrdinal 1) := by
    rw [realize_reindex, labelSlicePredicate.realize_compile hM]
    have hv : Subtype.val ∘ (ys R U C ∘ ![1,11,3,13]) = ![T.val,l.val,o.val,U.val] := by
      funext i; fin_cases i <;> rfl
    rw [hv, hT, hl, ho, eval_labelSlicePredicate]
  have hco (R U C : M) : (reindex labelSlicePredicate.compile ![1,11,4,14]).Realize
      Empty.elim (ys R U C) ↔ C.val = labelSlice c.labelGraph (natOrdinal 2) := by
    rw [realize_reindex, labelSlicePredicate.realize_compile hM]
    have hv : Subtype.val ∘ (ys R U C ∘ ![1,11,4,14]) = ![T.val,l.val,b.val,C.val] := by
      funext i; fin_cases i <;> rfl
    rw [hv, hT, hl, hb, eval_labelSlicePredicate]
  have hi (R U C : M) : (reindex (choiceFiberFormula interpretationFormula)
      ![0,1,12,13,14,11,7,8,5,10]).Realize Empty.elim (ys R U C) ↔
        (choiceFiberFormula interpretationFormula).Realize Empty.elim ![Ω,T,R,U,C,l,B,Y,e,A] := by
    rw [realize_reindex]
    have hv : ys R U C ∘ ![0,1,12,13,14,11,7,8,5,10] = ![Ω,T,R,U,C,l,B,Y,e,A] := by
      funext i; fin_cases i <;> rfl
    rw [hv]
  have hmem : l.val ∈ Codes.val := by
    rw [hCodes, mem_internalValidCodes]
    exact ⟨l.property, c, hc, hl.symm⟩
  change representsCodeFormula.Realize Empty.elim xs ↔ _
  simp only [representsCodeFormula, BoundedFormula.realize_inf, BoundedFormula.realize_ex]
  change (l.val ∈ Codes.val ∧ ∃ R U C : M,
    (((reindex childGraphPredicate.compile ![0,1,2,11,6,12]).Realize Empty.elim (ys R U C) ∧
      (reindex labelSlicePredicate.compile ![1,11,3,13]).Realize Empty.elim (ys R U C)) ∧
      (reindex labelSlicePredicate.compile ![1,11,4,14]).Realize Empty.elim (ys R U C)) ∧
      (reindex (choiceFiberFormula interpretationFormula) ![0,1,12,13,14,11,7,8,5,10]).Realize
        Empty.elim (ys R U C)) ↔ _
  simp only [hmem, true_and, hr, hu, hco, hi]
  constructor
  · rintro ⟨R,U,C,⟨⟨hR,hU⟩,hC⟩,hI⟩
    exact (realize_cantorInterpretationFiber hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2
      Ω T R U C l B Y e A hΩ hT hR hU hC hl hB hY he).mp hI
  · intro hA
    have hcM : c.labelGraph ∈ M := hl ▸ l.property
    let R : M := ⟨_, childRelation_mem hM hinf hpair hunion hpower hsep hcM⟩
    let U : M := ⟨_, labelSlice_mem hM hsep (hT ▸ T.property) hcM (ho ▸ o.property)⟩
    let C : M := ⟨_, labelSlice_mem hM hsep (hT ▸ T.property) hcM (hb ▸ b.property)⟩
    refine ⟨R,U,C,⟨⟨rfl,rfl⟩,rfl⟩, ?_⟩
    exact (realize_cantorInterpretationFiber hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2
      Ω T R U C l B Y e A hΩ hT rfl rfl rfl hl hB hY he).mpr hA

include hM hinf hpair hunion hpower hsep in
/-- The relation used by internal choice has exactly the intended mathematical meaning. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Uniform recognition of Borel representatives
-/
theorem realize_representsCodeFormula (Ω T z o b e K B Y Codes A l : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hT : T.val = finiteSequences)
    (hz : z.val = natOrdinal 0) (ho : o.val = natOrdinal 1) (hb : b.val = natOrdinal 2)
    (he : e.val = wordGraph []) (hK : K.val = ZFSet.prod finiteSequences finiteSequences)
    (hB : B.val = basisWordGraph NamedLambda.NatListCode.decode)
    (hY : Y.val = internalCantor M) (hCodes : Codes.val = internalValidCodes M) :
    representsCodeFormula.Realize Empty.elim ![Ω,T,z,o,b,e,K,B,Y,Codes,A,l] ↔
      ∃ (c : BorelExpression) (hc : c.Valid), c.labelGraph = l.val ∧
        A.val = internalBorelCantorSet M c hc.2.2.2.2.2 := by
  constructor
  · intro hφ
    have hm : l.val ∈ Codes.val := by
      have h := hφ
      simp only [representsCodeFormula, BoundedFormula.realize_inf] at h
      exact h.1
    obtain ⟨_, c, hc, hl⟩ := mem_internalValidCodes.mp (hCodes ▸ hm)
    refine ⟨c, hc, hl, ?_⟩
    exact (realize_representsCodeFormula_of_code hM hinf hpair hunion hpower hsep c hc
      Ω T z o b e K B Y Codes A l hΩ hT hz ho hb he hK hB hY hCodes hl.symm).mp hφ
  · rintro ⟨c,hc,hl,hA⟩
    exact (realize_representsCodeFormula_of_code hM hinf hpair hunion hpower hsep c hc
      Ω T z o b e K B Y Codes A l hΩ hT hz ho hb he hK hB hY hCodes hl.symm).mpr hA

end PolishSpaceBook.BorelExpression
