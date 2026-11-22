module

public import PolishSpaceBook.LusinRankSeparation

@[expose] public section

/-! # Transporting tree-rank boundedness along Borel reductions

The reduction is retained explicitly: the norm is the root rank of its actual
section tree. Taking a Borel image of the analytic subset, rather than changing
the norm or assuming a bound on it, supplies the input to tree boundedness.
-/

noncomputable section
namespace PolishSpaceBook
open Set MeasureTheory TopologicalSpace

variable {X : Type} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A Borel reduction to well-founded rooted trees, with its exact tree-rank norm. -/
structure BorelTreeRank (A : Set X) where
  code : X → (ℕ → ℕ)
  measurable_code : Measurable code
  wellFounded_iff : ∀ x, WellFounded (strictTreeExtension (LambdaTree.treeFromCode (code x)).tree) ↔ x ∈ A

namespace BorelTreeRank
variable {A : Set X} (R : BorelTreeRank A)

/-- Rank on the original domain, without any ordinal relabeling. -/
def rank (x : A) : Ordinal :=
  (((R.wellFounded_iff x.val).mpr x.property).apply (LambdaTree.treeFromCode (R.code x.val)).root).rank

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X] in
/-- The norm takes countable ordinal values because each tree has countably many nodes. -/
theorem rank_lt_omega1 (x : A) : R.rank x < Ordinal.omega 1 :=
  RootedPrefixTree.root_rank_countable _ ((R.wellFounded_iff x.val).mpr x.property)

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X] in
/-- Every code in the image is the code of a point in the original domain. -/
theorem imageWellFounded {B : Set X} (hBA : B ⊆ A) :
    ∀ p ∈ R.code '' B, WellFounded (strictTreeExtension (LambdaTree.treeFromCode p).tree) := by
  rintro p ⟨x, hx, rfl⟩
  exact (R.wellFounded_iff x).mpr (hBA hx)

omit [TopologicalSpace X] [PolishSpace X] [BorelSpace X] in
/-- Passing to the image of the reduction preserves the supremum exactly. -/
theorem rankSup_eq_image {B : Set X} (hBA : B ⊆ A) :
    (⨆ x : B, R.rank ⟨x.val, hBA x.property⟩) =
      LambdaTree.familyRankSup (R.code '' B) (R.imageWellFounded hBA) := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro x
    exact Ordinal.le_iSup
      (fun p : R.code '' B =>
        ((R.imageWellFounded hBA p.val p.property).apply (LambdaTree.treeFromCode p.val).root).rank)
      ⟨R.code x.val, ⟨x.val, x.property, rfl⟩⟩
  · apply Ordinal.iSup_le
    rintro ⟨p, x, hx, rfl⟩
    exact Ordinal.le_iSup (fun x : B => R.rank ⟨x.val, hBA x.property⟩) ⟨x, hx⟩

/-- The analytic image consists of well-founded trees; its root-rank bound is
therefore a bound for the original norm. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termuseas{boundedness theorem for well-founded trees}{Rank boundedness for the tree rank}]
    If $B\IncludedIn A$ is analytic,
    then
    $$\sup\{\varphi(x):x\in B\}<\omegaOneOrd.$$
    \end{lemma*}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Under the reduction $x\mapsto T_x$, the image of $B$ is analytic inside $\WellFoundedTrees$. Apply
    the boundedness theorem for well-founded tree ranks.
    \end{proof}
-/
theorem analytic_rankSup_lt {B : Set X} (hB : AnalyticSet B) (hBA : B ⊆ A) :
    (⨆ x : B, R.rank ⟨x.val, hBA x.property⟩) < Ordinal.omega 1 := by
  rw [R.rankSup_eq_image hBA]
  exact LambdaTree.analytic_rank_sup_lt
    (analyticSet_image_via_baire_parametrization hB R.measurable_code) _

end BorelTreeRank

/-- Closed projection and neighborhood-tree coding supply a Borel reduction
for every coanalytic subset of a Polish space. -/
theorem coanalytic_borelTreeRank {A : Set X} (hA : AnalyticSet Aᶜ) :
    Nonempty (BorelTreeRank A) := by
  let := metrizableSpaceMetric X
  obtain ⟨F, hF, hproj⟩ := (analyticSet_iff_closed_baire_projection Aᶜ).mp hA
  refine ⟨⟨LusinNeighborhood.code F, LusinNeighborhood.code_measurable F, ?_⟩⟩
  intro x
  rw [LusinNeighborhood.treeFromCode_code, LusinNeighborhood.wellFounded_iff F hF, hproj]
  simp only [mem_compl_iff, not_not]

end PolishSpaceBook
