module

public import PolishSpaceBook.BorelInternalInclusion
public import PolishSpaceBook.BorelInternalDefects
public import PolishSpaceBook.CantorInternalWords
public import PolishSpaceBook.BorelCantorGraphs

@[expose] public section

/-! # Transfer of internal Borel inclusions and countable covers

Apply the established closed-disjointness theorem once, to the whole binary
space and the Borel difference. No new rank or branch selection is required.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression.Code
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate CantorTreeMeasure
universe u

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)

include hM hinf hpair hunion hpower hsep hrep hchoice

/-- Test the Borel difference for an internal counterexample on the whole binary space. -/
theorem cantor_subset_of_internal_points (c d : Code)
    (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M)
    (hsub : ∀ x : ℕ → Bool, cantorPointGraph x ∈ M → x ∈ c.cantor → x ∈ d.cantor) :
    c.cantor ⊆ d.cantor := by
  let e := diff c d
  have he : e.val.labelGraph ∈ M :=
    diff_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c d hc hd
  have hno : ∀ z ∈ treeBody (binaryLift (Set.univ : Set (List Bool))), pointGraph z ∈ M →
      z ∉ e.val.evaluate e.property.2.2.2.2.2 cylinderBasis [] := by
    intro z hz hzM
    rw [binaryLift_body] at hz
    obtain ⟨x, _, rfl⟩ := hz
    change x ∉ e.cantor
    rw [cantor_diff]
    intro hx
    exact hx.2 (hsub x hzM hx.1)
  have hn := closed_disjoint_of_internal_points hM hinf hpair hunion hpower hsep hrep hchoice
    e.val e.property he (binaryLift Set.univ) (binaryWords_mem hM hinf hpair hunion hpower hsep) hno
  intro x hx
  by_contra hxd
  have hbad : x ∈ e.cantor := by rw [cantor_diff]; exact ⟨hx, hxd⟩
  exact hn (cantorInclusion x)
    (cantorInclusion_mem_binaryLift_body (fun _ => Set.mem_univ _)) hbad

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Transfer of internally coded Borel covers
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The internal union constructor gives a code $d=\BorelUnionCode{\Sequence{d_n}{n\in\omega}}$ in $M$.
    The internal Boolean constructors give a code $e$ in $M$ for $\SetDifference{\BorelValue{c}}{\BorelValue{d}}$.
    By hypothesis, no binary point coded in $M$ belongs to $\BorelValue{e}$.
    Apply the transfer of closed disjointness from §{sec:internal-closed-inclusions} to the whole binary space
    and the code $e$. It follows that $\BorelValue{e}=\emptyset$, which gives the required inclusion.
-/
/-- The whole code table is internal; coverage of old points then covers all points. -/
theorem cantor_cover_of_internal_points (c : Code) (d : ℕ → Code)
    (hc : c.val.labelGraph ∈ M) (hd : sequenceGraph (fun n => (d n).val.labelGraph) ∈ M)
    (hcover : ∀ x : ℕ → Bool, cantorPointGraph x ∈ M → x ∈ c.cantor → ∃ n, x ∈ (d n).cantor) :
    c.cantor ⊆ ⋃ n, (d n).cantor := by
  have hu := iUnion_labelGraph_mem hM hinf hpair hunion hpower hsep hrep d hd
  have h := cantor_subset_of_internal_points hM hinf hpair hunion hpower hsep hrep hchoice c (iUnion d)
    hc hu (by
      intro x hxM hxc
      rw [cantor_iUnion]
      exact Set.mem_iUnion.mpr (hcover x hxM hxc))
  rwa [cantor_iUnion] at h

end PolishSpaceBook.BorelExpression.Code
