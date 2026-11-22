module

public import PolishSpaceBook.InternalCohenAvoidance
public import PolishSpaceBook.ForcingDecisionClosure

@[expose] public section

/-! # The Cohen union name evaluates to the total generic real

Decode the actual finite-function conditions, use directedness and the length
tests to construct the real, then identify its graph with the valuation of the
displayed union name. No alternate coding of the real is substituted.
-/

noncomputable section
namespace PolishSpaceBook
open CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingAtomic ForcingNames BorelExpression ForcingFormulas
universe u

local instance cohenValuationOrder : Preorder (Condition (cohenConditionSet.{u} Set.univ)) := internalCohenOrder

theorem cohenCodedFilter_isFilter
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ))) :
    IsCohenFilter {s | cohenCodedCondition s ∈ G} := by
  rw [isCohenFilter_iff]
  constructor
  · obtain ⟨p, hp⟩ := G.nonempty
    obtain ⟨s, rfl⟩ := cohenCodedCondition_surjective p
    exact ⟨s, hp⟩
  · constructor
    · intro s hs t hst
      exact G.mem_of_le ((cohenCodedCondition_le_iff t s).mpr hst) hs
    · intro s hs t ht
      obtain ⟨p, hp, hps, hpt⟩ := G.directed (cohenCodedCondition s) hs (cohenCodedCondition t) ht
      obtain ⟨r, rfl⟩ := cohenCodedCondition_surjective p
      exact ⟨r, hp, (cohenCodedCondition_le_iff s r).mp hps,
        (cohenCodedCondition_le_iff t r).mp hpt⟩

theorem cohen_unionName_total
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)))
    (hlen : ∀ n : ℕ, ∃ s : CohenCondition, cohenCodedCondition s ∈ G ∧ n < s.length) :
    ∃ x : ℕ → Bool, (∀ s, cohenCodedCondition s ∈ G → CohenAgrees s x) ∧
      valuation (chosen (cohenConditionSet Set.univ) G)
        (unionName (cohenConditionSet Set.univ)) = cantorPointGraph x := by
  have hfilter := cohenCodedFilter_isFilter G
  obtain ⟨x, hx, _⟩ := cohen_filter_existsUnique_real hfilter hlen
  have hg : ∃ p ∈ chosen (cohenConditionSet Set.univ) G, p ∈ cohenConditionSet Set.univ := by
    obtain ⟨p, hp⟩ := G.nonempty
    exact ⟨p.val, ⟨p, hp, rfl⟩, p.property⟩
  refine ⟨x, hx, ?_⟩
  rw [valuation_unionName _ _ hg]
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨p, hp, hzp⟩
    obtain ⟨hpP, q, hqG, hqp⟩ := ZFSet.mem_sep.mp hp
    obtain ⟨s, rfl⟩ := cohenCodedCondition_surjective q
    have hsub := (binaryWordGraph_subset_pointGraph s x).mpr
      ((cohenAgrees_iff_prefixOfSeq s x).mp (hx s hqG))
    apply hsub
    change z ∈ (cohenCodedCondition s).val
    rwa [hqp]
  · intro hz
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hz
    obtain ⟨s, hsG, hns⟩ := hlen n
    refine ⟨(cohenCodedCondition s).val,
      ZFSet.mem_sep.mpr ⟨(cohenCodedCondition s).property, ⟨cohenCodedCondition s, hsG, rfl⟩⟩, ?_⟩
    apply pair_mem_wordGraph.mpr
    refine ⟨by simpa using hns, ?_⟩
    have hn := hx s hsG n hns
    have hn' : s[n] = x n := by
      simpa only [List.getElem?_eq_getElem hns, Option.some.injEq] using hn
    simpa [cantorInclusion] using congrArg Bool.toNat hn'

/-- Parameters n,g; the graph has some value at n. -/
def cohenLengthFormula : ForcingFormulas.Formula 2 :=
  (pairMemberFormula (1 : Fin 3) 0 2).ex

theorem cohenLengthRequirement_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (n : ℕ) : cohenConditionSet.{u} (cohenLengthRequirement n) ∈ M := by
  have hP : cohenConditionSet.{u} Set.univ ∈ M := binaryWords_mem hM hinf hpair hunion hpower hsep
  have hω := omegaOrdinal_mem hM hinf (hsep _)
  have hnat (k : ℕ) : natOrdinal k ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨k, rfl⟩) hω
  let nm : M := ⟨natOrdinal n, hnat n⟩
  have hbody (s : CohenCondition) (hsM : wordGraph.{u} (s.map Bool.toNat) ∈ M) :
      cohenLengthFormula.Realize Empty.elim
        (Fin.snoc ![nm] (⟨wordGraph (s.map Bool.toNat), hsM⟩ : M)) ↔ n < s.length := by
    simp only [cohenLengthFormula, BoundedFormula.realize_ex, realize_pairMemberFormula_model hM,
      Fin.snoc]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hi⟩ := mem_wordGraph.mp hb
      have he := natOrdinal_injective (ZFSet.pair_inj.mp hi).1
      have hlt : i.val < s.length := by simpa using i.isLt
      omega
    · intro hn
      refine ⟨⟨natOrdinal (s[n].toNat), hnat _⟩, pair_mem_wordGraph.mpr ?_⟩
      exact ⟨by simpa using hn, by simp⟩
  have heq : (cohenConditionSet.{u} Set.univ).sep
      (fun g => g ∈ cohenConditionSet (cohenLengthRequirement n)) =
        cohenConditionSet (cohenLengthRequirement n) := by
    ext g
    rw [ZFSet.mem_sep]
    constructor
    · exact And.right
    · intro hg
      obtain ⟨s, hs, rfl⟩ := mem_cohenConditionSet.mp hg
      exact ⟨mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩,
        mem_cohenConditionSet.mpr ⟨s, hs, rfl⟩⟩
  rw [← heq]
  apply separation_mem_of_absolute hM cohenLengthFormula (hsep _) ![nm] hP
  intro z hz
  obtain ⟨s, _, he⟩ := mem_cohenConditionSet.mp hz
  have hsM : wordGraph.{u} (s.map Bool.toNat) ∈ M := he.symm ▸ z.property
  have hzEq : z = (⟨wordGraph (s.map Bool.toNat), hsM⟩ : M) := Subtype.ext he.symm
  rw [hzEq, hbody s hsM]
  exact (cohenCodedCondition_mem_iff s (cohenLengthRequirement n)).symm

/-- Ground-model genericity supplies all length tests; they are not extra
assumptions on the resulting real. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Directedness makes this union a function, and the dense length requirements make its domain all of $\omega$.
    Thus the name evaluates to the generic real constructed in §{sec:cohen-forcing-detail}.
-/
theorem modelGeneric_cohen_unionName {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)))
    (hG : ModelGeneric (cohenConditionSet Set.univ) M G) :
    ∃ x : ℕ → Bool, (∀ s, cohenCodedCondition s ∈ G → CohenAgrees s x) ∧
      valuation (chosen (cohenConditionSet Set.univ) G)
        (unionName (cohenConditionSet Set.univ)) = cantorPointGraph x := by
  apply cohen_unionName_total G
  intro n
  obtain ⟨s, hs, hsG⟩ := (modelGeneric_iff_cohenDense M G).mp hG _
    (cohenLengthRequirement_mem hM hinf hpair hunion hpower hsep n) (cohenLengthRequirement_dense n)
  exact ⟨s, hsG, hs⟩

end PolishSpaceBook
