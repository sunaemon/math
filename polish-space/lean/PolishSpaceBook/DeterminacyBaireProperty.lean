module

public import PolishSpaceBook.BanachMazurStrategyLifting
public import PolishSpaceBook.SuslinBaireProperty

@[expose] public section

/-!
# Baire regularity from Banach–Mazur determinacy

Take the union of the open regions where the payoff is comeagre. Its difference
from the payoff is meagre by a countable subcover. Outside its closure, the
first-player criterion rules out I, so determinacy gives a meagre payoff there.
The remaining boundary is nowhere dense.
-/
noncomputable section
namespace PolishSpaceBook.BanachMazurGame
open Set Topology Filter TopologicalSpace
open scoped Classical symmDiff

section Topology
variable {X : Type*} [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Let $A\in\Gamma$. For every nonempty open $W$, the continuous outcome map gives $A_T=\pi^{-1}(A)\in\Gamma$.
    The coded game is therefore determined. By the coding equivalence, so is $G^{**}(A;W)$.
    Define
    $$U^*:=\bigcup\{V\IncludedIn X:V\text{ open and }A\cap V\text{ is comeager in }V\}.$$
    This set is open. For an open $V$, meagreness in $V$ and ambient meagreness agree for subsets of $V$.
    Thus the defining condition says equivalently that $\SetDifference{V}{A}$ is meager in $X$.

    Second countability gives a countable subfamily $V_n$ with the same union $U^*$. Hence
    $$\SetDifference{U^*}{A}=\bigcup_n\SetDifference{V_n}{A}$$
    is meager. This uses no regularity assumption on $A$.

    Set $W:=\SetDifference{X}{\Closure{U^*}}$. If $W=\emptyset$, then $A\cap W$ is meager. Otherwise, I cannot win
    $G^{**}(A;W)$: the first-player criterion would give a nonempty open $V\IncludedIn W$ on which $A\cap V$
    is comeager, forcing $V\IncludedIn U^*$, contrary to the definition of $W$. Determinacy therefore gives
    II a winning strategy on $W$. The Banach–Mazur–Oxtoby theorem makes $A\cap W$ meager in $W$, and hence in $X$.

    The boundary $\SetDifference{\Closure{U^*}}{U^*}$ of the open set $U^*$ is closed with empty interior,
    so it is nowhere dense. Since
    $$
    \SetDifference{A}{U^*}=(A\cap W)\cup
    \bigl(A\cap\SetDifference{\Closure{U^*}}{U^*}\bigr),
    $$
    this difference is meager too. Thus $A\triangle U^*$ is meager and $U^*$ is open, proving the Baire property.
    \end{proof}
-/
/-- Convert the relative category assertion to its ambient intersection. -/
lemma relative_meagre_to_inter {A V : Set X}
    (h : IsMeagre (Subtype.val ⁻¹' A : Set V)) : IsMeagre (A ∩ V) := by
  convert h.image_val using 1
  ext x
  simp only [mem_inter_iff, mem_image, mem_preimage]
  constructor
  · rintro ⟨ha, hv⟩
    exact ⟨⟨x, hv⟩, ha, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩

lemma relative_meagre_iff_inter {A V : Set X} (hV : IsOpen V) :
    IsMeagre (Subtype.val ⁻¹' A : Set V) ↔ IsMeagre (A ∩ V) := by
  refine ⟨relative_meagre_to_inter, fun h => ?_⟩
  have hm := h.preimage_of_isOpenMap continuous_subtype_val hV.isOpenMap_subtype_val
  simpa only [preimage_inter, Subtype.coe_preimage_self, inter_univ] using hm

/-- The largest open region on which the payoff is locally comeagre. -/
def comeagreRegion (A : Set X) : Set X :=
  ⋃₀ {V : Set X | IsOpen V ∧ IsMeagre (Aᶜ ∩ V)}

lemma comeagreRegion_eq_relative (A : Set X) :
    comeagreRegion A = ⋃₀ {V : Set X | IsOpen V ∧ IsMeagre (Subtype.val ⁻¹' Aᶜ : Set V)} := by
  unfold comeagreRegion
  congr 1
  ext V
  exact ⟨fun h => ⟨h.1, (relative_meagre_iff_inter h.1).mpr h.2⟩,
    fun h => ⟨h.1, relative_meagre_to_inter h.2⟩⟩

lemma comeagreRegion_isOpen (A : Set X) : IsOpen (comeagreRegion A) :=
  isOpen_sUnion (fun _ h => h.1)

lemma comeagreRegion_difference [SecondCountableTopology X] (A : Set X) : IsMeagre (comeagreRegion A \ A) := by
  simpa only [comeagreRegion, sdiff_eq, inter_comm] using meagre_on_union_of_open Aᶜ

lemma comeagreRegion_contains {A : Set X} (V : Move X)
    (hV : IsMeagre (Subtype.val ⁻¹' Aᶜ : Set V.openSet)) : V.openSet ⊆ comeagreRegion A :=
  subset_sUnion_of_mem ⟨V.isOpen, relative_meagre_to_inter hV⟩

lemma open_boundary_meagre {U : Set X} (hU : IsOpen U) : IsMeagre (closure U \ U) := by
  apply IsNowhereDense.isMeagre
  rw [← hU.frontier_eq]
  change interior (closure (frontier U)) = ∅
  rw [isClosed_frontier.closure_eq, ← frontier_compl]
  exact interior_frontier hU.isClosed_compl

end Topology

section Metric
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]

/-- A first-player win cannot occur outside the closure of the maximal comeagre region. -/
lemma no_firstWinning_outside {A : Set X} (W : Move X)
    (hW : W.openSet ⊆ (closure (comeagreRegion A))ᶜ) :
    ¬∃ σ : FirstStrategy X, FirstWinning A W.openSet σ := by
  intro h
  obtain ⟨V, hVW, hV⟩ := (firstWinning_iff_local_comeagre A W.openSet).mp h
  obtain ⟨x, hx⟩ := V.nonempty
  exact hW (hVW hx) (subset_closure (comeagreRegion_contains V hV hx))

/-- Determine the game on the whole complementary open region; an extra basis decomposition is unnecessary. -/
lemma payoff_outside_region_meagre (A : Set X)
    (hdet : ∀ W : Move X,
      (∃ σ : FirstStrategy X, FirstWinning A W.openSet σ) ∨ ∃ σ : Strategy X, Winning A W.openSet σ) :
    IsMeagre (A ∩ (closure (comeagreRegion A))ᶜ) := by
  by_cases hne : ((closure (comeagreRegion A))ᶜ).Nonempty
  · let W : Move X := ⟨(closure (comeagreRegion A))ᶜ, isClosed_closure.isOpen_compl, hne⟩
    rcases hdet W with hI | ⟨σ, hσ⟩
    · exact False.elim (no_firstWinning_outside W Subset.rfl hI)
    · exact relative_meagre_to_inter (isMeagre_of_winning W hσ)
  · rw [not_nonempty_iff_eq_empty.mp hne, inter_empty]
    exact IsMeagre.empty

/-- The book's maximal open region is an explicit Baire approximation to the payoff. -/
theorem determinacy_open_approximation (A : Set X)
    (hdet : ∀ W : Move X,
      (∃ σ : FirstStrategy X, FirstWinning A W.openSet σ) ∨ ∃ σ : Strategy X, Winning A W.openSet σ) :
    IsOpen (comeagreRegion A) ∧ IsMeagre (A ∆ comeagreRegion A) := by
  have hU := comeagreRegion_isOpen A
  have hout := payoff_outside_region_meagre A hdet
  have hbd := open_boundary_meagre hU
  have hdiff : IsMeagre (A \ comeagreRegion A) := (hout.union hbd).mono (by
    intro x hx
    by_cases hc : x ∈ closure (comeagreRegion A)
    · exact Or.inr ⟨hc, hx.2⟩
    · exact Or.inl ⟨hx.1, hc⟩)
  exact ⟨hU, by simpa [symmDiff_def] using hdiff.union (comeagreRegion_difference A)⟩

theorem baireMeasurable_of_open_determinacy (A : Set X)
    (hdet : ∀ W : Move X,
      (∃ σ : FirstStrategy X, FirstWinning A W.openSet σ) ∨ ∃ σ : Strategy X, Winning A W.openSet σ) :
    BaireMeasurableSet A := by
  obtain ⟨hU, hm⟩ := determinacy_open_approximation A hdet
  apply BaireMeasurableSet.iff_residualEq_isOpen.mpr
  refine ⟨comeagreRegion A, hU, ?_⟩
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hm] with x hx
  simp only [mem_compl_iff, mem_symmDiff] at hx
  tauto

theorem baireMeasurable_of_code_determinacy (A : Set X)
    (hdet : ∀ W : Move X, ∃ B : CodeBasis X, (codeTree B W).Determined (codePayoff B W A)) :
    BaireMeasurableSet A := by
  apply baireMeasurable_of_open_determinacy A
  intro W
  obtain ⟨B, hB⟩ := hdet W
  exact (code_determined_iff B W A).mp hB

end Metric

/-- Continuous-preimage closure alone suffices, since legality belongs to the Polish branch domain. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: Baire regularity from determinacy
-/
theorem pointclass_determinacy_baire
    (Γ : (Y : Type) → TopologicalSpace Y → Set Y → Prop)
    (hpull : ∀ {Y Z : Type} [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]
      [PolishSpace Y] [PolishSpace Z] {f : Y → Z} {A : Set Z},
      Continuous f → Γ Z tZ A → Γ Y tY (f ⁻¹' A))
    (hdet : ∀ (T : TreeGames.GameTree ℕ) (A : Set T.Play),
      Γ T.Play inferInstance A → T.Determined A)
    {X : Type} [tX : TopologicalSpace X] [PolishSpace X] {A : Set X} (hA : Γ X tX A) :
    BaireMeasurableSet A := by
  let := upgradeIsCompletelyMetrizable X
  apply baireMeasurable_of_code_determinacy A
  intro W
  obtain ⟨B⟩ := exists_codeBasis W
  exact ⟨B, hdet (codeTree B W) (codePayoff B W A) (hpull (continuous_codeOutcome B W) hA)⟩

end PolishSpaceBook.BanachMazurGame
