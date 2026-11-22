module

public import PolishSpaceBook.LambdaGHTopology
public import PolishSpaceBook.LambdaSilverSplitting
public import PolishSpaceBook.LambdaKernelConditions

@[expose] public section

/-!
# Coanalytic local truth and Silver splitting

This is the topological form of the local-truth step in Harrington's proof.
A coanalytic relation has the Baire property in the second-countable product
Gandy--Harrington topology. Outside a meager error set it agrees with an open
set. The complements of the closed nowhere-dense errors give countably many
lower dense rectangle tests. Thus an actual generic pair in the relation has
a rectangle on which all pairs meeting the same tests are in the relation.

The existing common-right contradiction then proves Silver splitting. This
does not construct transitive set-theoretic models or generic extensions;
it supplies exactly the local truth used by that contradiction.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set Topology TopologicalSpace MeasureTheory Filter

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: Coanalytic local truth
-/
/-- Coanalytic local truth in the actual fixed-parameter product order.
The chosen rectangle may be required to strengthen any starting rectangle
containing the pair. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The \termuseas{fixed-parameter basis lemma}{basis proposition} shows that the product
    Gandy--Harrington topology is second countable and refines the ordinary product topology. By the
    closed-projection Baire lemma, $S$ agrees with an open set $U$ outside a meager set. Choose countably
    many open dense sets $V_n$ whose intersection avoids that error set. Put
    $$\mathcal J:=\{\mathcal D(V_n):n\in\NN\}.$$
    The same proposition proves that each of these rectangle tests is downward closed and dense in the
    fixed-parameter condition order. Neither choosing the open sets nor listing these dense requirements
    is asserted to be computable.

    Every $\mathcal J$-generic pair belongs to every $V_n$, so its membership in $S$ is equivalent to membership in $U$.
    For a generic pair in $S\cap(A\times B)$, choose a basic rectangle containing the pair and contained in
    $U\cap(A\times B)$. Every generic pair in that rectangle belongs to $U$ and therefore to $S$.
    \end{proof}
-/
theorem parameter_coanalytic_local_truth (ε : ℕ → ℕ)
    (S : Set (FusionReal × FusionReal)) (hS : AnalyticSet Sᶜ) :
    ∃ J : Set (Set ((parameterAnalyticCatalog ε).Condition ×
        (parameterAnalyticCatalog ε).Condition)),
      J.Countable ∧ (∀ D ∈ J, IsCoinitial D ∧ IsLowerSet D) ∧
      ∀ (A B : (parameterAnalyticCatalog ε).Condition) x y,
        x ∈ A.val.val → y ∈ B.val.val →
        CatalogProductGeneric (parameterAnalyticCatalog ε) J x y → (x, y) ∈ S →
        ∃ P Q : (parameterAnalyticCatalog ε).Condition,
          P ≤ A ∧ Q ≤ B ∧ x ∈ P.val.val ∧ y ∈ Q.val.val ∧
          ∀ u ∈ P.val.val, ∀ v ∈ Q.val.val,
            CatalogProductGeneric (parameterAnalyticCatalog ε) J u v → (u, v) ∈ S := by
  have hbc := analyticSet_baireMeasurableSet_finer Sᶜ hS
    (parameterGHProductTopology ε) (parameterGHProduct_le ε)
  let : TopologicalSpace (FusionReal × FusionReal) := parameterGHProductTopology ε
  obtain ⟨U, hU, heq⟩ := hbc.of_compl.residualEq_isOpen
  have heq' : {p | p ∈ S ↔ p ∈ U} ∈ residual (FusionReal × FusionReal) := by
    filter_upwards [heq] with p hp
    exact Iff.of_eq hp
  obtain ⟨V, hVo, hVd, hVc, hVsub⟩ := mem_residual_iff.mp heq'
  let J := parameterOpenRectangleTest ε '' V
  have hgood (x y : FusionReal)
      (hg : CatalogProductGeneric (parameterAnalyticCatalog ε) J x y) :
      (x, y) ∈ S ↔ (x, y) ∈ U := by
    apply hVsub
    rw [mem_sInter]
    intro W hW
    obtain ⟨A, B, hAB, hx, hy⟩ := hg _ ⟨W, hW, rfl⟩
    exact hAB ⟨hx, hy⟩
  refine ⟨J, hVc.image _, ?_, ?_⟩
  · rintro _ ⟨W, hW, rfl⟩
    exact ⟨parameterOpenRectangleTest_dense ε W (hVo W hW) (hVd W hW),
      parameterOpenRectangleTest_lower ε W⟩
  · intro A B x y hx hy hg hs
    have hAB : IsOpen (A.val.val ×ˢ B.val.val) :=
      (parameterGHProduct_isBasis ε).isOpen
        ⟨_, parameterCondition_projected ε A, _, parameterCondition_projected ε B, rfl⟩
    obtain ⟨P, Q, hxP, hyQ, hPQ⟩ := parameterGHProduct_neighborhood ε _
      (hU.inter hAB) x y ⟨(hgood x y hg).mp hs, hx, hy⟩
    refine ⟨P, Q, ?_, ?_, hxP, hyQ, ?_⟩
    · intro u hu
      exact (hPQ (a := (u, y)) ⟨hu, hyQ⟩).2.1
    · intro v hv
      exact (hPQ (a := (x, v)) ⟨hxP, hv⟩).2.2
    · intro u hu v hv hgen
      exact (hgood u v hgen).mpr (hPQ ⟨hu, hv⟩).1

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: lemma
  title: Silver splitting lemma
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Apply coanalytic local truth to $S=E$, and use its countable family $\mathcal J$. If an equivalent generic pair
    belonged to $H\times H$, local truth would give nonempty analytic $A,B\IncludedIn H$ such that every
    $\mathcal J$-generic pair in $A\times B$ is $E$-equivalent.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For every analytic $B'\IncludedIn B$, the point $x$ meets $\mathcal L(D,B')$.
    This supplies a rectangle from $D$ whose left coordinate contains $x$ and whose right coordinate lies in $B'$.
    Thus the admissible right conditions for $x$ are dense below $B$; the same holds for $x'$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Transitivity now gives $x\mathrel E x'$.
-/
/-- Silver splitting for actual pairs in any catalog condition inside the
actual kernel. Coanalytic local truth supplies the previously missing step
from one equivalent generic pair to a homogeneous generic rectangle. -/
theorem parameter_silver_generic_splitting (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (A : (parameterAnalyticCatalog ε).Condition)
    (hAH : A.val.val ⊆ silverKernel ε E) :
    ∃ J : Set (Set ((parameterAnalyticCatalog ε).Condition ×
        (parameterAnalyticCatalog ε).Condition)),
      J.Countable ∧ (∀ D ∈ J, IsCoinitial D ∧ IsLowerSet D) ∧
      ∀ x ∈ A.val.val, ∀ y ∈ A.val.val,
        CatalogProductGeneric (parameterAnalyticCatalog ε) J x y → ¬ E.r x y := by
  have hco : AnalyticSet {p : FusionReal × FusionReal | ¬ E.r p.1 p.2} :=
    by
      have hc : Continuous (fun p : FusionReal × FusionReal => pairBaire p.1 p.2) := by
        unfold pairBaire
        fun_prop
      convert (Projected.analyticSet hE).preimage hc using 1
      ext p
      simp only [Set.mem_preimage,Set.mem_ofPred_eq,leftBaire_pair,rightBaire_pair]
  obtain ⟨J, hJc, hJdl, hlocal⟩ := parameter_coanalytic_local_truth ε
    {p : FusionReal × FusionReal | E.r p.1 p.2} hco
  refine ⟨J, hJc, hJdl, ?_⟩
  intro x hx y hy hg hxy
  obtain ⟨P, Q, hPA, _, _, _, hall⟩ := hlocal A A x y hx hy hg hxy
  exact parameter_silver_no_equivalent_generic_rectangle ε E hE P Q
    (fun _ hxP => hAH (hPA hxP)) J hJc (fun D hD => (hJdl D hD).1)
    (fun D hD => (hJdl D hD).2) hall

/-- The complete fixed-parameter Silver antichain construction. Neither a
generic splitting lemma nor a truth/absoluteness hypothesis is supplied. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    First work on Baire space. Code pairs by coordinatewise numerical pairing, choose a closed witness
    presentation of the nonrelation of $E$, and put its finite node tests in one parameter as in
    §{sec:edst-generic-conditions}. The kernel construction then gives $H$ a pair-tree presentation at
    that same parameter, and uncountably many classes imply $H\ne\emptyset$. Thus the kernel itself is
    a condition in the fixed-parameter order. Enumerate the node witness tests and the product tests
    from the splitting lemma as $\Sequence{D_n}{n\in\omega}$ and $\Sequence{J_n}{n\in\omega}$. Replace each family by the
    intersection of its first
    $n+1$ members, and include diameter at most $2^{-n}$ in $D_n$.
-/
theorem parameter_silver_antichain (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    [Uncountable (Quotient E)] :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Function.Injective π ∧
      ∀ a b, a ≠ b → ¬ E.r (π a) (π b) := by
  let A := parameterSilverKernelCondition ε E hE
  obtain ⟨J, hJc, hJdl, hsplit⟩ := parameter_silver_generic_splitting ε E hE A Subset.rfl
  obtain ⟨π, hc, hi, _, hanti⟩ := catalog_silver_fusion (parameterAnalyticCatalog ε) A E J hJc
    (fun D hD => (hJdl D hD).1) (fun D hD => (hJdl D hD).2) hsplit
  exact ⟨π, hc, hi, hanti⟩

end LambdaTree
end PolishSpaceBook
