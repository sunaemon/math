module

public import PolishSpaceBook.InternalRandomUnionTests
public import PolishSpaceBook.BorelInternalChildFamily

@[expose] public section

/-! # The generic union witness at every node of an internal Borel code -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory ForcingAtomic
universe u

/-- The canonical Borel interpretation at a node, restricted to the model's binary points. -/
def internalCantorNodeSet (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (s : List ℕ) : ZFSet.{u} :=
  internalInterpretation M c hw NamedLambda.NatListCode.decode s ∩ internalCantor M

lemma cantorPointGraph_mem_internalCantorNodeSet (M : ZFSet.{u}) (c : BorelExpression)
    (hw : WellFounded c.Child) (s : List ℕ) (x : ℕ → Bool) :
    cantorPointGraph x ∈ internalCantorNodeSet M c hw s ↔
      cantorPointGraph x ∈ M ∧ x ∈ cantorNodeSet c hw s := by
  rw [internalCantorNodeSet, ZFSet.mem_inter, cantorPointGraph_mem_internalCantor]
  change (pointGraph (cantorInclusion x) ∈ internalInterpretation M c hw _ s ∧ _) ↔ _
  rw [pointGraph_mem_internalInterpretation]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

lemma internalCantorNodeSet_union (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (s : List ℕ) (hs : c s = 1) :
    internalCantorNodeSet M c hw s = sequenceUnion (fun n => internalCantorNodeSet M c hw (s ++ [n])) := by
  have he : cantorNodeSet c hw s = ⋃ n, cantorNodeSet c hw (s ++ [n]) := by
    rw [cantorNodeSet_equation, hs]
    norm_num
  ext g
  rw [mem_sequenceUnion]
  constructor
  · intro hg
    obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp (ZFSet.mem_inter.mp hg).2
    have hx := (cantorPointGraph_mem_internalCantorNodeSet M c hw s x).mp hg
    rw [he, Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx.2
    exact ⟨n, (cantorPointGraph_mem_internalCantorNodeSet M c hw _ x).mpr ⟨hxM, hn⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp (ZFSet.mem_inter.mp hn).2
    apply (cantorPointGraph_mem_internalCantorNodeSet M c hw s x).mpr
    rw [he]
    exact ⟨hxM, Set.mem_iUnion.mpr ⟨n, ((cantorPointGraph_mem_internalCantorNodeSet M c hw _ x).mp hn).2⟩⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Generic witnesses at Borel union nodes
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The internal child-family construction of §{sec:internal-approximation-errors} gives the whole
    sequence of Baire interpretations. Intersect each value with $Y_M$ to obtain the Cantor interpretations.
    This operation preserves an internal whole graph: apply the fixed-difference construction twice,
    using $A\cap Y_M=\SetDifference{Y_M}{(\SetDifference{Y_M}{A})}$.
    The Borel node equation gives $A_s=\bigcup_n A_{s\concat\langle n\rangle}$ exactly as sets of old point graphs.
    The preceding theorem now applies to this constructed sequence.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    At a Borel union node, the entire sequence of child interpretations is constructed
    from the code, so this statement applies without assuming that sequence as an additional parameter.
-/
lemma internalCantorChildGraph_mem (c : BorelExpression) (hw : WellFounded c.Child)
    (hcM : c.labelGraph ∈ M) (s : List ℕ) :
    sequenceGraph (fun n => internalCantorNodeSet M c hw (s ++ [n])) ∈ M := by
  exact intersect_sequence_mem hM hinf hpair hunion hsep hrep _
    (internalChildInterpretationGraph_mem hM hinf hpair hunion hpower hsep hrep c hw _ hcM
      (canonicalBasisWordGraph_mem hM hinf hpair hunion hpower hsep) s)
    ⟨_, internalCantor_mem hM hinf hpair hunion hpower hsep⟩

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Generic witnesses at Borel union nodes
-/
theorem modelGeneric_borel_union_witness {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
    (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)
    (hD : D ∈ M) (hF : F ∈ M) (hca : h.CountablyAdditiveOn M)
    (c : BorelExpression) (hw : WellFounded c.Child) (hcM : c.labelGraph ∈ M) (s : List ℕ) (hs : c s = 1)
    (hnode : ∀ t, internalCantorNodeSet M c hw t ∈ D)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    (∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨_, hnode s⟩)) ↔
      ∃ n, ∃ q ∈ G, η (internalConditionClass η q) ≤ η (nullClassOf (F := F) ⟨_, hnode (s ++ [n])⟩) := by
  let B := fun n => internalCantorNodeSet M c hw (s ++ [n])
  have he := internalCantorNodeSet_union M c hw s hs
  have hU : sequenceUnion B ∈ D := he ▸ hnode s
  have hc : (⟨internalCantorNodeSet M c hw s, hnode s⟩ : D) = ⟨sequenceUnion B, hU⟩ := Subtype.ext he
  rw [hc]
  exact modelGeneric_union_witness hM hinf hpair hunion hpower hsep hrep h η hle hD hF hca B
    (internalCantorChildGraph_mem hM hinf hpair hunion hpower hsep hrep c hw hcM s)
    (fun n => hnode (s ++ [n])) hU G hG

end PolishSpaceBook.CantorTreeMeasure
