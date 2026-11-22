module

public import PolishSpaceBook.LambdaCatalogProjections
public import PolishSpaceBook.SuslinBaireProperty
public import PolishSpaceBook.LambdaInvariantClosure

@[expose] public section

/-!
# The fixed-parameter Gandy--Harrington topology

The actual lambda-presented analytic sets form a countable basis. Ordinary cylinders
belong to this basis, so the topology refines the usual Baire topology.
Its product basis is exactly the rectangles used in Silver's ordinary
product forcing. No assertion of metrizability or Polishness is made.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set Topology TopologicalSpace MeasureTheory

def parameterGHBasis (ε : ℕ → ℕ) : Set (Set FusionReal) :=
  {A | Projected ε A}

abbrev parameterGHTopology (ε : ℕ → ℕ) : TopologicalSpace FusionReal :=
  ghTopology ε

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: proposition
  title: Fixed-parameter bases and dense rectangles
-/
theorem parameterGHBasis_countable (ε : ℕ → ℕ) : (parameterGHBasis ε).Countable :=
  countable_projected ε

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    There are countably many finite lambda programs, so there are countably many decidable pair trees
    and their projections at a fixed parameter. The projections include the whole space and are closed
    under finite intersections. They therefore form a basis for the topology they generate. Every ordinary
    cylinder has such a presentation, which proves the refinement assertion. The product-basis theorem
    gives the stated rectangle basis.

    Downward closure of $\mathcal D(U)$ follows from containment. Given a condition $(A,B)$, the rectangle
    $A\times B$ is nonempty and open in the product topology. Density of $U$ gives a point in
    $U\cap(A\times B)$. Choose a basic rectangle $P\times Q$ containing that point and contained in this
    intersection. Its two factors are nonempty, and $(P,Q)\leq(A,B)$ belongs to $\mathcal D(U)$.
    All four factors belong to the original fixed-parameter family; the open dense set itself need not
    have an effective code.
    \end{proof}
-/
theorem parameterGHBasis_isBasis (ε : ℕ → ℕ) :
    @IsTopologicalBasis FusionReal (parameterGHTopology ε) (parameterGHBasis ε) := by
  let : TopologicalSpace FusionReal := parameterGHTopology ε
  refine ⟨?_, ?_, rfl⟩
  · intro A hA B hB x hx
    exact ⟨A ∩ B, hA.inter hB, hx, Subset.rfl⟩
  · apply sUnion_eq_univ_iff.mpr
    intro x
    refine ⟨cyl [], projected_cyl ε [], ?_⟩
    simp [cyl_nil]

instance parameterGHTopology_secondCountable (ε : ℕ → ℕ) :
    @SecondCountableTopology FusionReal (parameterGHTopology ε) :=
  SecondCountableTopology.mk' (parameterGHBasis_countable ε)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] For (1), each ordinary basic open set is $\lSigma^0_1(\varepsilon)$ from the code for $X$ and the
    chosen base, hence is $\lSigma^1_1(\varepsilon)$. Since these sets are among the generators of $\GHTopology$, every
    original open set is $\GHTopology$-open.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  excerpt: |
    \begin{fact*}[about $\GHTopology$] The following facts hold.
-/
theorem parameterGHTopology_le (ε : ℕ → ℕ) :
    parameterGHTopology ε ≤ (inferInstance : TopologicalSpace FusionReal) := by
  rw [(isTopologicalBasis_cyl (A := ℕ)).eq_generateFrom]
  apply generateFrom_anti
  rintro _ ⟨s, rfl⟩
  exact projected_cyl ε s

abbrev parameterGHProductTopology (ε : ℕ → ℕ) : TopologicalSpace (FusionReal × FusionReal) :=
  @instTopologicalSpaceProd FusionReal FusionReal (parameterGHTopology ε) (parameterGHTopology ε)

theorem parameterGHProduct_isBasis (ε : ℕ → ℕ) :
    @IsTopologicalBasis (FusionReal × FusionReal) (parameterGHProductTopology ε)
      (Set.image2 (fun A B => A ×ˢ B) (parameterGHBasis ε) (parameterGHBasis ε)) :=
  @IsTopologicalBasis.prod FusionReal FusionReal (parameterGHTopology ε) (parameterGHTopology ε)
    _ _ (parameterGHBasis_isBasis ε) (parameterGHBasis_isBasis ε)

instance parameterGHProduct_secondCountable (ε : ℕ → ℕ) :
    @SecondCountableTopology (FusionReal × FusionReal) (parameterGHProductTopology ε) := by
  let : TopologicalSpace FusionReal := parameterGHTopology ε
  infer_instance

theorem parameterGHProduct_le (ε : ℕ → ℕ) :
    parameterGHProductTopology ε ≤ (inferInstance : TopologicalSpace (FusionReal × FusionReal)) := by
  have h : @Continuous FusionReal FusionReal (parameterGHTopology ε) inferInstance id :=
    continuous_id_of_le (parameterGHTopology_le ε)
  have hp : @Continuous (FusionReal × FusionReal) (FusionReal × FusionReal)
      (parameterGHProductTopology ε) inferInstance id :=
    @Continuous.prodMap FusionReal FusionReal FusionReal FusionReal
      inferInstance inferInstance (parameterGHTopology ε) (parameterGHTopology ε) id id h h
  simpa only [induced_id] using hp.le_induced

/-- Every open neighborhood of a pair contains an actual catalog rectangle
containing that pair. In particular both basis sets are nonempty. -/
theorem parameterGHProduct_neighborhood (ε : ℕ → ℕ) (U : Set (FusionReal × FusionReal))
    (hU : @IsOpen _ (parameterGHProductTopology ε) U) (x y : FusionReal) (hxy : (x, y) ∈ U) :
    ∃ A B : (parameterAnalyticCatalog ε).Condition,
      x ∈ A.val.val ∧ y ∈ B.val.val ∧ A.val.val ×ˢ B.val.val ⊆ U := by
  let : TopologicalSpace (FusionReal × FusionReal) := parameterGHProductTopology ε
  obtain ⟨_, ⟨A, hA, B, hB, rfl⟩, hxyAB, hAB⟩ :=
    (parameterGHProduct_isBasis ε).exists_subset_of_mem_open hxy hU
  exact ⟨parameterCondition ε A hA ⟨x, hxyAB.1⟩,
    parameterCondition ε B hB ⟨y, hxyAB.2⟩, hxyAB.1, hxyAB.2, hAB⟩

/-- The forcing test attached to an open dense subset of the product. -/
def parameterOpenRectangleTest (ε : ℕ → ℕ) (U : Set (FusionReal × FusionReal)) :
    Set ((parameterAnalyticCatalog ε).Condition × (parameterAnalyticCatalog ε).Condition) :=
  {P | P.1.val.val ×ˢ P.2.val.val ⊆ U}

theorem parameterOpenRectangleTest_lower (ε : ℕ → ℕ) (U : Set (FusionReal × FusionReal)) :
    IsLowerSet (parameterOpenRectangleTest ε U) := by
  intro P Q hQP hP
  exact (Set.prod_mono hQP.1 hQP.2).trans hP

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    There are countably many finite lambda programs, so there are countably many decidable pair trees
    and their projections at a fixed parameter. The projections include the whole space and are closed
    under finite intersections. They therefore form a basis for the topology they generate. Every ordinary
    cylinder has such a presentation, which proves the refinement assertion. The product-basis theorem
    gives the stated rectangle basis.

    Downward closure of $\mathcal D(U)$ follows from containment. Given a condition $(A,B)$, the rectangle
    $A\times B$ is nonempty and open in the product topology. Density of $U$ gives a point in
    $U\cap(A\times B)$. Choose a basic rectangle $P\times Q$ containing that point and contained in this
    intersection. Its two factors are nonempty, and $(P,Q)\leq(A,B)$ belongs to $\mathcal D(U)$.
    All four factors belong to the original fixed-parameter family; the open dense set itself need not
    have an effective code.
    \end{proof}
-/
theorem parameterOpenRectangleTest_dense (ε : ℕ → ℕ) (U : Set (FusionReal × FusionReal))
    (hU : @IsOpen _ (parameterGHProductTopology ε) U)
    (hd : @Dense _ (parameterGHProductTopology ε) U) :
    IsCoinitial (parameterOpenRectangleTest ε U) := by
  let : TopologicalSpace (FusionReal × FusionReal) := parameterGHProductTopology ε
  intro P
  have hP : @IsOpen _ (parameterGHProductTopology ε) (P.1.val.val ×ˢ P.2.val.val) :=
    (parameterGHProduct_isBasis ε).isOpen
      ⟨_, parameterCondition_projected ε P.1, _, parameterCondition_projected ε P.2, rfl⟩
  obtain ⟨⟨x, y⟩, hx, hy⟩ := hd.inter_open_nonempty _ hP
    (P.1.val.property.2.prod P.2.val.property.2)
  obtain ⟨A, B, hxA, hyB, hAB⟩ := parameterGHProduct_neighborhood ε _ (hU.inter hP)
    x y ⟨hy, hx⟩
  have hAP : A ≤ P.1 := by
    intro a ha
    exact (hAB (a := (a, y)) ⟨ha, hyB⟩).2.1
  have hBP : B ≤ P.2 := by
    intro b hb
    exact (hAB (a := (x, b)) ⟨hxA, hb⟩).2.2
  exact ⟨(A, B), fun _ hz => (hAB hz).1, hAP, hBP⟩

end LambdaTree
end PolishSpaceBook
