module

public import PolishSpaceBook.InternalCohenRequirements
public import PolishSpaceBook.SetTheoryNaturalGraphs
public import PolishSpaceBook.SetTheoryPredicateComposition

@[expose] public section

/-! # Internal word-occurrence requirements for Cohen forcing

The bounded predicate chooses an offset in omega and checks every graph entry
of the word at the translated position, using the internal addition graph.
-/
noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open CantorTreeMeasure ForcingAtomic
universe u

/-- Consecutive occurrence is exactly agreement at a finite offset. -/
lemma cohenOccurs_iff_offset (u s : CohenCondition) : CohenOccurs u s ↔
    ∃ k, ∀ i (hi : i < u.length), ∃ hj : k + i < s.length, s[k + i] = u[i] := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a.length, fun i hi => ⟨by simp; omega, ?_⟩⟩
    simp [hi]
  · rintro ⟨k, h⟩
    have hlen : u.length ≤ (s.drop k).length := by
      by_cases he : u.length = 0
      · simp [he]
      · obtain ⟨hj, _⟩ := h (u.length - 1) (by omega)
        simp only [List.length_drop]
        omega
    have hp : u.IsPrefix (s.drop k) := List.prefix_iff_getElem.mpr ⟨hlen, by
      intro i hi
      obtain ⟨hj, he⟩ := h i hi
      simpa [List.getElem_drop, Nat.add_comm] using he.symm⟩
    obtain ⟨b, hb⟩ := hp
    refine ⟨s.take k, b, ?_⟩
    rw [List.append_assoc, hb, List.take_append_drop]

/-- Parameters: omega, addition graph, word graph, proposed condition graph. -/
def cohenWordPredicate : BoundedSetPredicate 4 :=
  .ex 0 (.all 0 (.all 0 ((BoundedSetPredicate.pairMember 2 5 6).imply
    (.ex 0 (.conj (binaryMember.rename ![1, 4, 5, 7]) (.pairMember 3 7 6))))))

lemma eval_cohenWordPredicate (u s : CohenCondition) :
    cohenWordPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun i j => i + j), wordGraph.{u} (u.map Bool.toNat),
      wordGraph (s.map Bool.toNat)] ↔ CohenOccurs u s := by
  have he : cohenWordPredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun i j => i + j), wordGraph.{u} (u.map Bool.toNat),
      wordGraph (s.map Bool.toNat)] ↔
      ∃ k : ℕ, ∀ i v : ℕ,
        (pair (natOrdinal i) (natOrdinal v) ∈ wordGraph.{u} (u.map Bool.toNat)) →
        ∃ j : ℕ, k + i = j ∧ pair (natOrdinal j) (natOrdinal v) ∈ wordGraph.{u} (s.map Bool.toNat) := by
    change (∃ k ∈ Ordinal.omega0.toZFSet, ∀ i ∈ Ordinal.omega0.toZFSet,
      ∀ v ∈ Ordinal.omega0.toZFSet,
      (¬ pair i v ∈ wordGraph (u.map Bool.toNat) ∨
        ∃ j ∈ Ordinal.omega0.toZFSet,
          binaryMember.eval ![naturalBinaryGraph (fun i j => i + j), k, i, j] ∧
            pair j v ∈ wordGraph (s.map Bool.toNat))) ↔ _
    simp only [eval_binaryMember, exists_mem_omegaOrdinal, forall_mem_omegaOrdinal,
      pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff, eq_comm, ← imp_iff_not_or]
  rw [he, cohenOccurs_iff_offset]
  constructor
  · rintro ⟨k, h⟩
    refine ⟨k, ?_⟩
    intro i hi
    have hp : pair (natOrdinal i) (natOrdinal (Bool.toNat u[i])) ∈ wordGraph.{u} (u.map Bool.toNat) :=
      pair_mem_wordGraph.mpr ⟨by simpa using hi, by simp⟩
    obtain ⟨j, rfl, hj⟩ := h i _ hp
    obtain ⟨hj, hv⟩ := pair_mem_wordGraph.mp hj
    refine ⟨by simpa using hj, ?_⟩
    apply bool_toNat_injective
    simpa using hv
  · rintro ⟨k, h⟩
    refine ⟨k, ?_⟩
    intro i v hp
    obtain ⟨hi, hv⟩ := pair_mem_wordGraph.mp hp
    have hi' : i < u.length := by simpa using hi
    obtain ⟨hj, heq⟩ := h i hi'
    refine ⟨k + i, rfl, pair_mem_wordGraph.mpr ⟨by simpa using hj, ?_⟩⟩
    simpa [heq] using hv

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
include hM hinf hpair hunion hpower hsep

/-- Every word's graph is internal, and bounded separation constructs D_u inside M. -/
theorem cohenWordRequirement_mem (u : CohenCondition) :
    cohenConditionSet (cohenWordRequirement u) ∈ M := by
  have hP : cohenConditionSet.{u} Set.univ ∈ M :=
    binaryWords_mem hM hinf hpair hunion hpower hsep
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let A : M := ⟨naturalBinaryGraph (fun i j => i + j),
    naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩
  let W : M := ⟨wordGraph (u.map Bool.toNat),
    hM.mem_trans (mem_cohenConditionSet.mpr ⟨u, Set.mem_univ _, rfl⟩) hP⟩
  apply cohenWordPredicate.subset_mem hM (hsep _) ![Ω, A, W] hP
  · intro g hg
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hg
    exact mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩
  · intro g hg
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hg
    have he : Fin.snoc (Subtype.val ∘ (![Ω, A, W] : Fin 3 → M))
        (wordGraph (s.map Bool.toNat)) =
        ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun i j => i + j),
          wordGraph (u.map Bool.toNat), wordGraph (s.map Bool.toNat)] := by
      funext i
      fin_cases i <;> rfl
    rw [he, eval_cohenWordPredicate]
    constructor
    · intro hs
      exact mem_cohenConditionSet.mpr ⟨s, hs, rfl⟩
    · intro hs
      obtain ⟨t, ht, he⟩ := mem_cohenConditionSet.mp hs
      have hts := (List.map_injective_iff.mpr bool_toNat_injective) (wordGraph_injective he)
      simpa only [cohenWordRequirement, Set.mem_ofPred_eq, hts] using ht

local instance cohenWordRequirementOrder :
    Preorder (Condition (cohenConditionSet.{u} Set.univ)) := internalCohenOrder

/-- All word requirements are genuine internal dense sets, so genericity meets each one. -/
theorem modelGeneric_meets_word
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)))
    (hG : ModelGeneric (cohenConditionSet Set.univ) M G) (u : CohenCondition) :
    ∃ s ∈ cohenWordRequirement u, cohenCodedCondition s ∈ G :=
  (modelGeneric_iff_cohenDense M G).mp hG _
    (cohenWordRequirement_mem hM hinf hpair hunion hpower hsep u)
    (cohenWordRequirement_dense u)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Given $u$, choose $s\in G\cap D_u$ and write $s=a\concat u\concat b$. For every $i<|u|$, the union lemma gives
    $c_G(|a|+i)=s(|a|+i)=u(i)$. Thus $u$ occurs in $c_G$ at position $|a|$. Every finite binary word and its dense
    requirement belong to the transitive model $M$, so every Cohen real over $M$ is disjunctive.
    \end{proof}
-/
/-- Every finite word appears in a Cohen real over M. -/
theorem modelGeneric_cohen_real_disjunctive
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)))
    (hG : ModelGeneric (cohenConditionSet Set.univ) M G)
    (c : ℕ → Bool) (hc : ∀ s, cohenCodedCondition s ∈ G → CohenAgrees s c) :
    ∀ u, CohenOccursIn u c := by
  apply cohen_real_disjunctive (G := {s | cohenCodedCondition s ∈ G}) hc
  intro u
  obtain ⟨s, hsD, hsG⟩ := modelGeneric_meets_word hM hinf hpair hunion hpower hsep G hG u
  exact ⟨s, hsG, hsD⟩

end PolishSpaceBook
