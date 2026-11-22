module

public import PolishSpaceBook.FiniteAdditiveCutGraphs
public import PolishSpaceBook.NonnegativeRealCutSupremum
public import PolishSpaceBook.NonnegativeRealCutInternalInfimum
public import PolishSpaceBook.SetTheorySequenceDecomposition

@[expose] public section

/-! # Continuity from countable additivity on whole internal families -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels Filter Topology
universe u

namespace FiniteAdditiveCutGraph
variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

include h in
lemma partialUnion_domain (A : ℕ → ZFSet.{u}) (hA : ∀ n, A n ∈ D) (n : ℕ) : partialUnion A n ∈ D := by
  induction n with
  | zero => rw [partialUnion_zero]; exact h.empty_mem
  | succ n ih => rw [partialUnion_succ]; exact h.union_mem _ ih _ (hA n)

lemma value_partialUnion_sum (A : ℕ → ZFSet.{u}) (hA : ∀ n, A n ∈ D)
    (hd : Pairwise (fun i j => Disjoint (A i : Set ZFSet) (A j : Set ZFSet))) (n : ℕ) :
    h.value (partialUnion A n) = ∑ i ∈ Finset.range n, h.value (A i) := by
  induction n with
  | zero => simp only [partialUnion_zero, h.value_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    have hdis : Disjoint ((partialUnion A n : ZFSet) : Set ZFSet) (A n : Set ZFSet) := by
      rw [Set.disjoint_left]
      intro x hx hn
      obtain ⟨i, hi, hx⟩ := (mem_partialUnion A n x).mp hx
      exact Set.disjoint_left.mp (hd hi.ne) hx hn
    rw [partialUnion_succ, h.value_union (h.partialUnion_domain A hA n) (hA n) hdis,
      ih, Finset.sum_range_succ]

/-- Countable additivity in cut form, restricted to families whose entire graph belongs to M.
The union of strict cuts represents the sum of the nonnegative series of disjoint-set values. -/
def CountablyAdditiveOn (M : ZFSet.{u}) : Prop :=
  ∀ A : ℕ → ZFSet.{u}, sequenceGraph A ∈ M → (∀ n, A n ∈ D) →
    Pairwise (fun i j => Disjoint (A i : Set ZFSet) (A j : Set ZFSet)) →
      sequenceUnion A ∈ D ∧ h.code (sequenceUnion A) = sequenceUnion (fun n => h.code (partialUnion A n))

lemma partialUnion_values_tendsto {M : ZFSet.{u}} (hca : h.CountablyAdditiveOn M)
    (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M) (hA : ∀ n, A n ∈ D)
    (hd : Pairwise (fun i j => Disjoint (A i : Set ZFSet) (A j : Set ZFSet))) :
    Tendsto (fun n => h.value (partialUnion A n)) atTop (𝓝 (h.value (sequenceUnion A))) := by
  obtain ⟨hU, he⟩ := hca A hG hA hd
  apply tendsto_decode_of_code_union _ _ (fun n => h.code_valid (h.partialUnion_domain A hA n)) (h.code_valid hU)
  · intro m n hmn
    exact h.value_mono (h.partialUnion_domain A hA m) (h.partialUnion_domain A hA n) (partialUnion_mono A hmn)
  · exact he

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Continuity from above for internal families
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The differences $B_n$ belong to $D$, are pairwise disjoint, and form an entire internal sequence.
    Countable additivity therefore gives $J:=\bigcup_n B_n\in D$ and
    $\nu(P_n(B))\to\nu(J)$. Since $I=\SetDifference{A_0}{J}$, difference closure gives $I\in D$.
    The disjoint-difference identities and finite additivity yield
    $$\nu(A_n)=\nu(A_0)-\nu(P_n(B)),\qquad
    \nu(I)=\nu(A_0)-\nu(J).$$
    Subtract the convergent sequence from the finite real number $\nu(A_0)$.
    Monotonicity then identifies the limit with the infimum. The rounded-infimum identity in
    §{sec:internal-real-cut-addition} and validity of the value at $I$ give the equality of codes.
-/
theorem continuity_from_above {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hca : h.CountablyAdditiveOn M) (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M)
    (hA : ∀ n, A n ∈ D) (hanti : Antitone (fun n => (A n : Set ZFSet))) :
    sequenceIntersection A ∈ D ∧
      Tendsto (fun n => h.value (A n)) atTop (𝓝 (h.value (sequenceIntersection A))) := by
  let B := adjacentDifference A
  have hB (n : ℕ) : B n ∈ D := h.diff_mem _ (hA n) _ (hA (n + 1))
  have hBG : sequenceGraph B ∈ M := adjacentDifference_sequence_mem hM hinf hpair hunion hsep hrep A hG
  have hd := adjacentDifference_pairwise A hanti
  have hU := (hca B hBG hB hd).1
  have hu : sequenceUnion B = A 0 \ sequenceIntersection A := sequenceUnion_adjacentDifference A hanti
  have hi0 : sequenceIntersection A ⊆ A 0 := fun _ hx => (mem_sequenceIntersection A _).mp hx 0
  have hi : sequenceIntersection A ∈ D := by
    have hmem := h.diff_mem _ (hA 0) _ hU
    have he : A 0 \ sequenceUnion B = sequenceIntersection A := by
      rw [hu]
      ext x
      simp only [ZFSet.mem_sdiff]
      have hx : x ∈ sequenceIntersection A → x ∈ A 0 := fun hx => hi0 hx
      tauto
    rwa [he] at hmem
  have hlim := h.partialUnion_values_tendsto hca B hBG hB hd
  have heval (n : ℕ) : h.value (A 0) - h.value (partialUnion B n) = h.value (A n) := by
    have hadd := h.value_sdiff_add (hA n) (hA 0) (fun _ hx => hanti (Nat.zero_le n) hx)
    rw [show partialUnion B n = A 0 \ A n from partialUnion_adjacentDifference A hanti n]
    linarith
  have hevalI : h.value (A 0) - h.value (sequenceUnion B) = h.value (sequenceIntersection A) := by
    have hadd := h.value_sdiff_add hi (hA 0) hi0
    rw [hu]
    linarith
  refine ⟨hi, ?_⟩
  have hconst : Tendsto (fun _ : ℕ => h.value (A 0)) atTop (𝓝 (h.value (A 0))) := tendsto_const_nhds
  simpa only [heval, hevalI] using hconst.sub hlim

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Continuity from above for internal families
-/
theorem code_intersection_eq_infimum {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hca : h.CountablyAdditiveOn M) (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M)
    (hA : ∀ n, A n ∈ D) (hanti : Antitone (fun n => (A n : Set ZFSet))) :
    h.code (sequenceIntersection A) = roundedInfCutCode (fun n => h.code (A n)) := by
  obtain ⟨hi, ht⟩ := h.continuity_from_above hM hinf hpair hunion hsep hrep hca A hG hA hanti
  have hv : (⨅ n, h.value (A n)) = h.value (sequenceIntersection A) := by
    apply le_antisymm
    · exact ge_of_tendsto' ht (fun n => ciInf_le (nonnegative_range_bddBelow _ (fun n => h.value_nonneg (hA n))) n)
    · exact le_ciInf (fun n => h.value_mono hi (hA n) (fun _ hx => (mem_sequenceIntersection A _).mp hx n))
  rw [roundedInfCutCode_eq_decoded _ (fun n => h.code_valid (hA n))]
  change h.code (sequenceIntersection A) = nonnegativeRealCutCode (⨅ n, h.value (A n))
  rw [hv]
  exact (h.code_valid hi).encode_decode

end FiniteAdditiveCutGraph
end PolishSpaceBook.CantorTreeMeasure
