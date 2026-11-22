module

public import Mathlib.Data.List.GetD
public import PolishSpaceBook.BorelInclusionTree
public import PolishSpaceBook.BorelEvaluationPreimage
public import PolishSpaceBook.BorelMeasureSandwich

@[expose] public section

/-! # Ranked inclusion certificates for rational bounds on Cantor Borel measure -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open Set MeasureTheory CantorTreeMeasure

/-- Regard binary words as natural-number words without changing their entries. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Now identify binary sequences with natural-number sequences whose entries are $0$ or $1$.
    For a binary tree $T$, let $T^\uparrow$ contain the same words regarded as natural-number words, and put
    $A_c:=B_c\cap\CantorSpace$, with the intersection understood through this identification.
-/
def binaryLift (T : Set (List Bool)) : Set (List ℕ) :=
  (List.map Bool.toNat) '' T

lemma cantorInclusion_mem_binaryLift_body {T : Set (List Bool)} {x : ℕ → Bool}
    (hx : x ∈ treeBody T) : cantorInclusion x ∈ treeBody (binaryLift T) := by
  intro n
  refine ⟨seqPrefix x n, hx n, ?_⟩
  simp only [seqPrefix, List.map_ofFn, cantorInclusion, Function.comp_def]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The branches of $T^\uparrow$ are exactly the binary branches of $T$: every entry on a branch appears in a finite
    word of the tree and hence is $0$ or $1$.
-/
lemma binaryLift_body (T : Set (List Bool)) :
    treeBody (binaryLift T) = cantorInclusion '' treeBody T := by
  ext z
  constructor
  · intro hz
    have hb (n : ℕ) : ∃ b : Bool, b.toNat = z n := by
      obtain ⟨w, _, he⟩ := hz (n + 1)
      refine ⟨w.getD n false, ?_⟩
      have he' := congrArg (fun s : List ℕ => s.getD n 0) he
      have hp : (seqPrefix z (n + 1)).getD n 0 = z n := by
        rw [List.getD_eq_getElem?_getD]
        simp only [seqPrefix, List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self n), Option.getD_some]
      rw [hp] at he'
      exact (List.getD_map w false Bool.toNat).symm.trans he'
    choose x hx using hb
    have he : cantorInclusion x = z := funext hx
    refine ⟨x, ?_, he⟩
    intro n
    obtain ⟨w, hw, hew⟩ := hz n
    have hmap : (seqPrefix x n).map Bool.toNat = w.map Bool.toNat := by
      rw [hew, ← he]
      simp only [seqPrefix, List.map_ofFn, cantorInclusion, Function.comp_def]
    have hinj : Function.Injective (List.map Bool.toNat) := List.map_injective_iff.mpr
      (fun a b h => by cases a <;> cases b <;> simp_all)
    exact hinj hmap ▸ hw
  · rintro ⟨x, hx, rfl⟩
    exact cantorInclusion_mem_binaryLift_body hx

/-- Interpret the standard Baire cylinder labels on the binary subspace. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Write $\BorelValue{c}$ for the full Cantor-space interpretation of a code $c$.
-/
def cantorSet (c : BorelExpression) (hw : WellFounded c.Child) : Set (ℕ → Bool) :=
  cantorInclusion ⁻¹' c.evaluate hw cylinderBasis []

lemma measurableSet_cantorSet (c : BorelExpression) (hw : WellFounded c.Child) :
    MeasurableSet (cantorSet c hw) := by
  have hm := c.measurableSet_evaluate hw cylinderBasis
    (fun n => (isOpen_cyl _).measurableSet) []
  have hf : Continuous cantorInclusion := by
    apply continuous_pi
    intro i
    exact (continuous_of_discreteTopology (f := Bool.toNat)).comp (continuous_apply i)
  exact hm.preimage hf.measurable

/-- The rank excludes counterexamples even at points absent from the original model. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Conversely, a branch would give the strictly decreasing sequence
    $\rho(\restrict{z}{n})$ of ordinals, which is impossible.
-/
theorem binary_closed_subset_of_rank (c : BorelExpression) (hc : c.Valid)
    (T : Set (List Bool)) (ρ : inclusionTree c (binaryLift T) → Ordinal.{0})
    (hρ : ∀ u v, strictTreeExtension (inclusionTree c (binaryLift T)) u v → ρ u < ρ v) :
    treeBody T ⊆ cantorSet c hc.2.2.2.2.2 := by
  intro x hx
  exact closed_subset_of_inclusionTree_rank c hc (binaryLift T) ρ hρ
    (cantorInclusion_mem_binaryLift_body hx)

/-- Conversely, an inclusion supplies an ordinal rank on its counterexample tree. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Ranked certificate for closed inclusion
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Apply the theorem. If the counterexample tree is well-founded,
    its ordinal rank gives $\rho$.
-/
theorem binary_closed_subset_iff_rank (c : BorelExpression) (hc : c.Valid)
    (T : Set (List Bool)) :
    treeBody T ⊆ cantorSet c hc.2.2.2.2.2 ↔
      ∃ ρ : inclusionTree c (binaryLift T) → Ordinal.{0},
        ∀ u v, strictTreeExtension (inclusionTree c (binaryLift T)) u v → ρ u < ρ v := by
  constructor
  · intro h
    have hsub : treeBody (binaryLift T) ⊆ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
      rw [binaryLift_body]
      rintro _ ⟨x, hx, rfl⟩
      exact h hx
    let : WellFounded (strictTreeExtension (inclusionTree c (binaryLift T))) :=
      (closed_subset_iff_inclusionTree_wellFounded c hc _).mp hsub
    exact ⟨WellFounded.rank _, fun _ _ h => WellFounded.rank_lt_of_rel h⟩
  · rintro ⟨ρ, hρ⟩
    exact binary_closed_subset_of_rank c hc T ρ hρ

/-- Rank data and rational inequalities together certify a strict measure bound. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    In the reverse direction, the rank gives the inclusion and
    $q<r\le\mu(\TreeBody{T})\le\mu(A_c)$.
-/
theorem rational_measure_bound_of_rank (c : BorelExpression) (hc : c.Valid)
    (T : Set (List Bool)) (hT : IsSubtree T)
    (ρ : inclusionTree c (binaryLift T) → Ordinal.{0})
    (hρ : ∀ u v, strictTreeExtension (inclusionTree c (binaryLift T)) u v → ρ u < ρ v)
    (q r : ℚ) (hqr : q < r) (hr : ∀ n, r ≤ levelWeight T n) :
    (q : ℝ) < fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  apply (borel_lower_cut (measurableSet_cantorSet c _) q).mpr
  exact ⟨T, hT, binary_closed_subset_of_rank c hc T ρ hρ, r, hqr, hr⟩

/-- A strict rational cut has a tree, a rational margin, and an ordinal rank as witnesses. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Ranked certificate for a rational measure bound
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Apply the tree certificate for a rational measure bound in §{sec:coded-measure-bounds} and replace its inclusion
    condition by the preceding rank criterion.
-/
theorem rational_measure_bound_iff_rank (c : BorelExpression) (hc : c.Valid) (q : ℚ) :
    (q : ℝ) < fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) ↔
      ∃ T : Set (List Bool), IsSubtree T ∧
        (∃ ρ : inclusionTree c (binaryLift T) → Ordinal.{0},
          ∀ u v, strictTreeExtension (inclusionTree c (binaryLift T)) u v → ρ u < ρ v) ∧
        ∃ r : ℚ, q < r ∧ ∀ n, r ≤ levelWeight T n := by
  constructor
  · intro h
    obtain ⟨T, hT, hTA, r, hqr, hr⟩ :=
      (borel_lower_cut (measurableSet_cantorSet c _) q).mp h
    exact ⟨T, hT, (binary_closed_subset_iff_rank c hc T).mp hTA, r, hqr, hr⟩
  · rintro ⟨T, hT, ⟨ρ, hρ⟩, r, hqr, hr⟩
    exact rational_measure_bound_of_rank c hc T hT ρ hρ q r hqr hr

end PolishSpaceBook.BorelExpression
