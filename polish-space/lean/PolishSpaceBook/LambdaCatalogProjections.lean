module

public import PolishSpaceBook.LambdaProjectionOperations
public import PolishSpaceBook.LambdaAnalyticCatalog

@[expose] public section

/-!
# Generic coordinates of relative analytic pair conditions

Coordinate projections and inverse images stay in the fixed-parameter
catalog. A dense family below the projected condition therefore lifts to a
dense family of pair conditions. Witnessed fusion then gives actual pair
members whose two coordinates meet all prescribed countably many tests.
-/

namespace PolishSpaceBook
open Set
namespace LambdaTree

def parameterCondition (ε : ℕ → ℕ) (A : Set FusionReal)
    (hA : Projected ε A) (hne : A.Nonempty) :
    (parameterAnalyticCatalog ε).Condition :=
  ⟨⟨A, hA.analyticSet, hne⟩, (mem_parameterAnalyticCatalog ε _).mpr hA⟩

theorem parameterCondition_projected (ε : ℕ → ℕ)
    (P : (parameterAnalyticCatalog ε).Condition) :
    Projected ε P.val.val :=
  (mem_parameterAnalyticCatalog ε _).mp P.property

def parameterLiftedDense (ε : ℕ → ℕ) (P A : (parameterAnalyticCatalog ε).Condition)
    (f : FusionReal → FusionReal) (D : Set (CatalogBelow (parameterAnalyticCatalog ε) A)) :
    Set (CatalogBelow (parameterAnalyticCatalog ε) P) :=
  {Q | ∃ U ∈ D, f '' Q.val.val.val ⊆ U.val.val.val}

theorem parameterLiftedDense_lower (ε : ℕ → ℕ) (P A : (parameterAnalyticCatalog ε).Condition)
    (f : FusionReal → FusionReal) (D : Set (CatalogBelow (parameterAnalyticCatalog ε) A)) :
    IsLowerSet (parameterLiftedDense ε P A f D) := by
  rintro Q R hRQ ⟨U, hUD, hQU⟩
  exact ⟨U, hUD, (Set.image_mono hRQ).trans hQU⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $f$ be either coordinate projection and let $D\in\mathcal F$. Below $P$, require a condition $Q$
    whose image $f[Q]$ is contained in some $U\in D$. This requirement is downward closed. To see that it
    is dense, start with any $Q\IncludedIn P$. Its image is a nonempty condition below $A$ by
    §{sec:edst-coordinate-projections}. Choose $U\in D$ with $U\IncludedIn f[Q]$, and put
    $$V=Q\cap f^{-1}(U).$$
    The set $V$ is nonempty because every point of $U$ has a preimage in $Q$. Coordinatewise inverse images
    and intersections give it a presentation at the same parameter. Thus it is a stronger condition and
    $f[V]\IncludedIn U$, as required.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Projection preserves genericity for
    $\GHConditions{2}$, since restricting one coordinate to a stronger analytic set gives a stronger pair condition
    whenever the restriction is nonempty.
-/
theorem parameterLiftedDense_coinitial (ε : ℕ → ℕ)
    (P A : (parameterAnalyticCatalog ε).Condition) (f : FusionReal → FusionReal)
    (himage : ∀ S, Projected ε S →
      Projected ε (f '' S))
    (hpreimage : ∀ S, Projected ε S →
      Projected ε (f ⁻¹' S))
    (hPA : f '' P.val.val ⊆ A.val.val)
    (D : Set (CatalogBelow (parameterAnalyticCatalog ε) A)) (hD : IsCoinitial D) :
    IsCoinitial (parameterLiftedDense ε P A f D) := by
  intro Q
  let I := parameterCondition ε (f '' Q.val.val.val)
    (himage _ (parameterCondition_projected ε Q.val)) (Q.val.val.property.2.image f)
  have hIA : I ≤ A := (Set.image_mono Q.property).trans hPA
  obtain ⟨U, hUD, hUI⟩ := hD (⟨I, hIA⟩ : CatalogBelow (parameterAnalyticCatalog ε) A)
  have hne : (Q.val.val.val ∩ f ⁻¹' U.val.val.val).Nonempty := by
    obtain ⟨u, hu⟩ := U.val.val.property.2
    obtain ⟨x, hx, rfl⟩ := hUI hu
    exact ⟨x, hx, hu⟩
  let R := parameterCondition ε (Q.val.val.val ∩ f ⁻¹' U.val.val.val)
    ((parameterCondition_projected ε Q.val).inter
      (hpreimage _ (parameterCondition_projected ε U.val))) hne
  have hRQ : R ≤ Q.val := Set.inter_subset_left
  refine ⟨⟨R, hRQ.trans Q.property⟩, ⟨U, hUD, ?_⟩, hRQ⟩
  rintro y ⟨x, hx, rfl⟩
  exact hx.2

/-- A pair condition can meet independently prescribed dense tests in both
coordinates, without replacing it by a rectangle. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Generic coordinates of a pair condition
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Lift every member of $\mathcal F$ in this way for both coordinates. The lifted family is countable,
    lower and dense below $P$. The preceding proposition gives an actual point of $P$ meeting all these
    lifted tests. Each test then supplies the required condition containing the corresponding coordinate.
    In particular, any relation imposed by the original pair condition is retained; the construction does
    not replace that condition by the product of its projections.
    \end{proof}
-/
theorem parameter_pair_generic_coordinates (ε : ℕ → ℕ)
    (P A : (parameterAnalyticCatalog ε).Condition)
    (hleft : leftBaire '' P.val.val ⊆ A.val.val)
    (hright : rightBaire '' P.val.val ⊆ A.val.val)
    (F : Set (Set (CatalogBelow (parameterAnalyticCatalog ε) A)))
    (hFc : F.Countable) (hFd : ∀ D ∈ F, IsCoinitial D) :
    ∃ p ∈ P.val.val,
      (∀ D ∈ F, ∃ U ∈ D, leftBaire p ∈ U.val.val.val) ∧
      (∀ D ∈ F, ∃ U ∈ D, rightBaire p ∈ U.val.val.val) := by
  let L := parameterLiftedDense ε P A leftBaire
  let R := parameterLiftedDense ε P A rightBaire
  have hd : ∀ D ∈ L '' F ∪ R '' F, IsCoinitial D := by
    rintro _ (⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩)
    · exact parameterLiftedDense_coinitial ε P A leftBaire
        (fun _ h => h.projectLeft) (fun _ h => h.leftPreimage) hleft D (hFd D hD)
    · exact parameterLiftedDense_coinitial ε P A rightBaire
        (fun _ h => h.projectRight) (fun _ h => h.rightPreimage) hright D (hFd D hD)
  have hl : ∀ D ∈ L '' F ∪ R '' F, IsLowerSet D := by
    rintro _ (⟨D, _, rfl⟩ | ⟨D, _, rfl⟩)
    · exact parameterLiftedDense_lower ε P A leftBaire D
    · exact parameterLiftedDense_lower ε P A rightBaire D
  obtain ⟨p, hp, hmeet⟩ := catalog_generic_point_below (parameterAnalyticCatalog ε) P
    (L '' F ∪ R '' F) ((hFc.image L).union (hFc.image R)) hd hl
  refine ⟨p, hp, ?_, ?_⟩
  · intro D hD
    obtain ⟨Q, ⟨U, hU, hQU⟩, hpQ⟩ := hmeet (L D) (Or.inl ⟨D, hD, rfl⟩)
    exact ⟨U, hU, hQU ⟨p, hpQ, rfl⟩⟩
  · intro D hD
    obtain ⟨Q, ⟨U, hU, hQU⟩, hpQ⟩ := hmeet (R D) (Or.inr ⟨D, hD, rfl⟩)
    exact ⟨U, hU, hQU ⟨p, hpQ, rfl⟩⟩

end LambdaTree
end PolishSpaceBook
