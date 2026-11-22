module

public import PolishSpaceBook.LambdaBorelEvaluation
public import PolishSpaceBook.TreeWellFounded

@[expose] public section

/-! # Finite counterexample trees for closed-set inclusion

A branch stores a point and a Borel evaluation certificate of a prescribed root bit. Membership
of a finite node uses only finite words, integer arithmetic, and the supplied
code and tree. It does not ask whether a finite approximation extends to a real.
-/

namespace PolishSpaceBook.BorelExpression
open Set

/-- The two coordinates of each letter store a point entry and a certificate entry. -/
def inclusionTest (c : BorelExpression) (T : Set (List ℕ)) (w : List ℕ) (bit : Bool := false) : Prop :=
  w.map (fun a => a.unpair.1) ∈ T ∧
    LambdaTree.boundedPrefixTest (finiteCertificateClause c bit) certificatePrefixBound
      (w.map (fun a => a.unpair.1), w.map (fun a => a.unpair.2))

/-- All earlier tests are retained, including the empty-prefix test. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: construction
  title: Counterexample tree for a closed inclusion
-/
def inclusionTree (c : BorelExpression) (T : Set (List ℕ)) (bit : Bool := false) : Set (List ℕ) :=
  {w | ∀ n ≤ w.length, inclusionTest c T (w.take n) bit}

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: construction
  title: Counterexample tree for a closed inclusion
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Write $Q^\varepsilon(c,T)$ for the same construction with $P_i^\varepsilon$ in place of $P_i$, so
    $Q^0(c,T)=Q(c,T)$. Every condition concerns finite words and values of the parameters $c,T$.
    There is no test for whether a
    finite word extends to a point. Keeping the conditions for all $j\le n$ makes $Q(c,T)$ downward closed,
    including when it is empty.
-/
lemma inclusionTree_isSubtree (c : BorelExpression) (T : Set (List ℕ)) (bit : Bool := false) :
    IsSubtree (inclusionTree c T bit) := by
  intro s t hs ht
  obtain ⟨n, hn, rfl⟩ := prefixOf_iff_exists_take.mp ht
  intro k hk
  simp only [List.length_take] at hk
  simpa only [List.take_take] using hs (min k n) (by omega)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Decode a branch into two sequences $x,y$. The tree-membership tests at every length give $x\in\TreeBody{T}$.
    For each row $i$, the test is performed by length $\max\{i+1,b(i)\}$, and truncation supplies exactly its prescribed
    arguments. Thus all rows hold, and $y$ is a negative evaluation certificate for $x$.
-/
lemma mem_inclusionTree_body (c : BorelExpression) (T : Set (List ℕ)) (z : ℕ → ℕ) (bit : Bool := false) :
    z ∈ treeBody (inclusionTree c T bit) ↔
      (fun n => (z n).unpair.1) ∈ treeBody T ∧
      c.NatCertificate (fun n => (z n).unpair.1) (fun n => (z n).unpair.2) ∧
      witnessBit (fun n => (z n).unpair.2) [] = (if bit then 1 else 0) := by
  have hprefix : z ∈ treeBody (inclusionTree c T bit) ↔
      ∀ n, inclusionTest c T (seqPrefix z n) bit := by
    constructor
    · intro h n
      simpa only [seqPrefix_take_of_le z (le_refl n)] using h n n (by simp [seqPrefix_length])
    · intro h n k hk
      have hkn : k ≤ n := by simpa only [seqPrefix_length] using hk
      simpa only [seqPrefix_take_of_le z hkn] using h k
  rw [hprefix]
  simp only [inclusionTest, List.map_ofFn, seqPrefix, forall_and]
  change (_ ∧ ∀ n, LambdaTree.boundedPrefixTest _ _
    (seqPrefix (fun i => (z i).unpair.1) n, seqPrefix (fun i => (z i).unpair.2) n)) ↔ _
  rw [LambdaTree.boundedPrefixTest_iff, all_finiteCertificateClauses_iff]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    By the certificate theorem, all the tests $P_i$ with prescribed root bit $0$ hold on $(x,y)$ exactly when
    $y$ certifies $x\notin B_c$.
-/
theorem negativeCertificate_iff (c : BorelExpression) (hc : c.Valid) (x : ℕ → ℕ) :
    (∃ q, c.NatCertificate x q ∧ witnessBit q [] = 0) ↔
      x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
  change (∃ q, c.NatCertificate x q ∧ witnessBit q [] = (if false then 1 else 0)) ↔ _
  rw [natCertificate_root_iff, ← evaluationSide_iff_mem cylinderBasis c hc x]
  simpa only [not_not] using
    (not_congr (evaluationSides_complementary cylinderBasis c hc x)).symm

/-- Both truth values use the same finite evaluation-certificate construction. -/
theorem certificateSide_iff (c : BorelExpression) (hc : c.Valid) (x : ℕ → ℕ) (bit : Bool) :
    (∃ q, c.NatCertificate x q ∧ witnessBit q [] = (if bit then 1 else 0)) ↔
      (if bit then x ∈ c.evaluate hc.2.2.2.2.2 cylinderBasis [] else
        x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis []) := by
  cases bit
  · exact negativeCertificate_iff c hc x
  · rw [natCertificate_root_iff]
    exact evaluationSide_iff_mem cylinderBasis c hc x

/-- Prescribing the positive root bit in every finite row gives exactly
membership in the interpreted Borel set. Validity is supplied, with no
effectivity assumption on the label function. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The tests $P_i^1$ instead characterize positive evaluation certificates for $x\in B_c$.
-/
theorem positiveFiniteRows_iff (c : BorelExpression) (hc : c.Valid) (x : ℕ → ℕ) :
    (∃ q : ℕ → ℕ, ∀ i, finiteCertificateClause c true i
      (seqPrefix x (certificatePrefixBound i), seqPrefix q (certificatePrefixBound i))) ↔
      x ∈ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
  simp_rw [all_finiteCertificateClauses_iff]
  exact certificateSide_iff c hc x true

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Decode a branch into two sequences $x,y$. The tree-membership tests at every length give $x\in\TreeBody{T}$.
    For each row $i$, the test is performed by length $\max\{i+1,b(i)\}$, and truncation supplies exactly its prescribed
    arguments. Thus all rows hold, and $y$ is a negative evaluation certificate for $x$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Conversely, if $x\in\SetDifference{\TreeBody{T}}{B_c}$, choose such a certificate $y$
    and pair their entries coordinatewise.
    Every finite prefix passes all the required tests, giving a branch of $Q(c,T)$.
-/
theorem inclusionTree_side_branch_iff (c : BorelExpression) (hc : c.Valid)
    (T : Set (List ℕ)) (bit : Bool) :
    (∃ z, z ∈ treeBody (inclusionTree c T bit)) ↔
      ∃ x ∈ treeBody T, if bit then x ∈ c.evaluate hc.2.2.2.2.2 cylinderBasis [] else
        x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hx, hq⟩ := (mem_inclusionTree_body c T z bit).mp hz
    exact ⟨_, hx, (certificateSide_iff c hc _ bit).mp ⟨_, hq⟩⟩
  · rintro ⟨x, hx, hside⟩
    obtain ⟨q, hq⟩ := (certificateSide_iff c hc x bit).mpr hside
    refine ⟨fun n => Nat.pair (x n) (q n), (mem_inclusionTree_body c T _ bit).mpr ?_⟩
    simpa only [Nat.unpair_pair] using And.intro hx hq

/-- A branch is precisely a point in the closed body outside the coded Borel set. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Branches of the counterexample tree
-/
theorem inclusionTree_has_branch_iff (c : BorelExpression) (hc : c.Valid)
    (T : Set (List ℕ)) :
    (∃ z, z ∈ treeBody (inclusionTree c T)) ↔
      ∃ x ∈ treeBody T, x ∉ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
  exact inclusionTree_side_branch_iff c hc T false

/-- This removes the quantifier over new points from the inclusion certificate. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Branches of the counterexample tree
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    A downward-closed tree has no branch exactly when its strict-extension relation is well-founded, by the tree-rank
    construction in §{sec:edst-boundedness}. This proves the last assertion as well.
-/
theorem closed_subset_iff_inclusionTree_wellFounded (c : BorelExpression) (hc : c.Valid)
    (T : Set (List ℕ)) :
    treeBody T ⊆ c.evaluate hc.2.2.2.2.2 cylinderBasis [] ↔
      WellFounded (strictTreeExtension (inclusionTree c T)) := by
  rw [← prefixTreeWellFounded_iff _ (inclusionTree_isSubtree c T)]
  change _ ↔ ¬ ∃ z, z ∈ treeBody (inclusionTree c T)
  rw [inclusionTree_has_branch_iff c hc]
  simp only [not_exists, not_and, not_not]
  rfl

/-- An ordinal-valued function decreasing along extensions excludes every branch. -/
theorem closed_subset_of_inclusionTree_rank (c : BorelExpression) (hc : c.Valid)
    (T : Set (List ℕ)) (ρ : inclusionTree c T → Ordinal)
    (hρ : ∀ u v, strictTreeExtension (inclusionTree c T) u v → ρ u < ρ v) :
    treeBody T ⊆ c.evaluate hc.2.2.2.2.2 cylinderBasis [] := by
  apply (closed_subset_iff_inclusionTree_wellFounded c hc T).mpr
  exact (InvImage.wf ρ Ordinal.lt_wf).mono hρ

end PolishSpaceBook.BorelExpression
