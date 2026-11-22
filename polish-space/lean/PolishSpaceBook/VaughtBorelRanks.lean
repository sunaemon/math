module

public import PolishSpaceBook.VaughtTransforms
public import PolishSpaceBook.BorelHierarchyClosure

@[expose] public section

/-! # Borel ranks of Vaught transforms

Simultaneous transfinite induction preserves additive classes for the nonmeager
transform and multiplicative classes for the comeager transform. Localization
handles the other polarity with one additional Borel level.
-/
namespace PolishSpaceBook
open Set Topology TopologicalSpace

section Metric
variable {G X : Type*} [Group G] [TopologicalSpace G] [BaireSpace G]
  [SecondCountableTopology G] [MetricSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Localization turns a uniform multiplicative bound on the comeager transforms
into an additive successor bound on the nonmeager transform. -/
theorem vaughtStar_mem_succ_of_triangle [MeasurableSpace X] [BorelSpace X]
    {α : Ordinal} (hα : 1 ≤ α) {A : Set X} (hA : MeasurableSet A)
    (hT : ∀ V : Set G, IsOpen V → vaughtTriangle V A ∈ borelPi α)
    {U : Set G} (hU : IsOpen U) : vaughtStar U A ∈ borelSigma (α + 1) := by
  let : Countable (countableBasis G) := (countable_countableBasis G).to_subtype
  let I := {V : countableBasis G // V.val.Nonempty ∧ V.val ⊆ U}
  have he : vaughtStar U A = ⋃ V : I, vaughtTriangle V.val.val A := by
    ext x
    change x ∈ categoryStar U (actionRelation A) ↔ _
    rw [mem_categoryStar_local (isBasis_countableBasis G) hU _ x
      (baireMeasurable_actionSection hA x)]
    simp only [mem_iUnion]
    constructor
    · rintro ⟨V, hVB, hVne, hVU, hx⟩
      exact ⟨⟨⟨V, hVB⟩, hVne, hVU⟩, hx⟩
    · rintro ⟨V, hx⟩
      exact ⟨V.val.val, V.val.property, V.property.1, V.property.2, hx⟩
  rw [he]
  apply borelSigma_iUnion_countable (le_trans hα le_self_add)
  intro V
  exact borelPi_subset_borelSigma_succ hα
    (hT V.val.val (isOpen_of_mem_countableBasis V.val.property))

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    We now prove simultaneously, for every open $U$, that the non-meager transform preserves $\bSigma^0_\alpha$
    and the comeager transform preserves $\bPi^0_\alpha$, for $1\le\alpha<\omegaOneOrd$.
    The open case and its dual give the base. Suppose $\alpha>1$ and the assertion holds at every earlier level.
    Write $A\in\bSigma^0_\alpha$ as $A=\bigcup_n C_n$, where $C_n\in\bPi^0_{\beta_n}$ and
    $1\le\beta_n<\alpha$. Baire-property localization gives
    $$
    C_n^{*U}=\bigcup_{\substack{W\in\mathcal U\\\emptyset\ne W\IncludedIn U}}C_n^{\triangle W}.
    $$
    The induction hypothesis puts every term on the right in $\bPi^0_{\beta_n}$, so the countable union belongs to
    $\bSigma^0_{\beta_n+1}$. Since $\beta_n+1\le\alpha$, monotonicity of the hierarchy and the direct union rule give
    $$
    A^{*U}=\bigcup_n C_n^{*U}\in\bSigma^0_\alpha.
    $$
    Duality now gives preservation of $\bPi^0_\alpha$ by the comeager transform.
    The argument permits the $\beta_n$ to vary and therefore covers limit stages as well.
-/
/-- The additive and multiplicative preservation statements are proved together. -/
theorem vaught_preserves_borel_levels_metric (α : Ordinal) : 1 ≤ α →
    (∀ {A : Set X}, A ∈ borelSigma α → ∀ {U : Set G}, IsOpen U →
      vaughtStar U A ∈ borelSigma α) ∧
    (∀ {A : Set X}, A ∈ borelPi α → ∀ {U : Set G}, IsOpen U →
      vaughtTriangle U A ∈ borelPi α) := by
  borelize X
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro hα
    have hS : ∀ {A : Set X}, A ∈ borelSigma α → ∀ {U : Set G}, IsOpen U →
        vaughtStar U A ∈ borelSigma α := by
      intro A hA U hU
      by_cases hα1 : α ≤ 1
      · have he : α = 1 := le_antisymm hα1 hα
        subst α
        rw [borelSigma_one] at hA ⊢
        exact isOpen_vaughtStar hU hA
      · rw [borelSigma, ite_eq_right hα1] at hA
        obtain ⟨f, hf, rfl⟩ := hA
        rw [vaughtStar_iUnion]
        apply borelSigma_iUnion
        intro n
        obtain ⟨β, hβ⟩ := hf n
        have hsucc : vaughtStar U (f n) ∈ borelSigma (β.val + 1) :=
          vaughtStar_mem_succ_of_triangle β.property.1
            (measurableSet_of_mem_borelPi β.val hβ)
            (fun _ hV => (ih β.val β.property.2 β.property.1).2 hβ hV) hU
        exact borelSigma_mono (le_trans β.property.1 le_self_add)
          (by rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt β.property.2) hsucc
    refine ⟨hS, ?_⟩
    intro A hA U hU
    change (vaughtTriangle U A)ᶜ ∈ borelSigma α
    have he : (vaughtTriangle U A)ᶜ = vaughtStar U Aᶜ := by
      simpa only [compl_compl] using congrArg compl (vaughtStar_compl U Aᶜ).symm
    rw [he]
    exact hS hA hU

end Metric

section Polish
variable {G X : Type*} [Group G] [TopologicalSpace G] [PolishSpace G]
  [TopologicalSpace X] [PolishSpace X] [MulAction G X] [ContinuousSMul G X]

/-- The rank-preservation statement uses the given Polish topologies, independently
of any particular compatible metrics. -/
theorem vaught_preserves_borel_levels (α : Ordinal) (hα : 1 ≤ α) :
    (∀ {A : Set X}, A ∈ borelSigma α → ∀ {U : Set G}, IsOpen U →
      vaughtStar U A ∈ borelSigma α) ∧
    (∀ {A : Set X}, A ∈ borelPi α → ∀ {U : Set G}, IsOpen U →
      vaughtTriangle U A ∈ borelPi α) := by
  let := upgradeIsCompletelyMetrizable X
  exact vaught_preserves_borel_levels_metric α hα

/-- Either transform raises the level by at most one for either input polarity. -/
theorem vaught_borel_successor_bounds {α : Ordinal} (hα : 1 ≤ α)
    {A : Set X} (hA : A ∈ borelSigma α ∨ A ∈ borelPi α)
    {U : Set G} (hU : IsOpen U) :
    vaughtStar U A ∈ borelSigma (α + 1) ∧ vaughtTriangle U A ∈ borelPi (α + 1) := by
  let := upgradeIsCompletelyMetrizable X
  have hS : A ∈ borelSigma (α + 1) := hA.elim
    (fun h => borelSigma_mono hα le_self_add h) (fun h => borelPi_subset_borelSigma_succ hα h)
  have hP : A ∈ borelPi (α + 1) := hA.elim
    (fun h => borelSigma_subset_borelPi_succ hα h) (fun h => borelPi_mono hα le_self_add h)
  exact ⟨(vaught_preserves_borel_levels (α + 1) (le_trans hα le_self_add)).1 hS hU,
    (vaught_preserves_borel_levels (α + 1) (le_trans hα le_self_add)).2 hP hU⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Finally, the inclusions $\bSigma^0_\alpha\IncludedIn\bPi^0_{\alpha+1}$ and
    $\bPi^0_\alpha\IncludedIn\bSigma^0_{\alpha+1}$ give the two remaining bounds in (1).
    Thus, for either input class at level $\alpha$, the non-meager transform belongs to
    $\bSigma^0_{\alpha+1}$ and the comeager transform to $\bPi^0_{\alpha+1}$.
    Every Borel set lies at a countable level, so this also proves Borelness of both transforms.
-/
/-- The four bounds, with no loss for the matching polarity. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{Vaught lemma}{Vaught}] Let $G$ act continuously on a Polish space $X$, and let $U
-/
theorem vaught_borel_level_bounds {α : Ordinal} (hα : 1 ≤ α)
    {A : Set X} {U : Set G} (hU : IsOpen U) :
    (A ∈ borelSigma α →
      vaughtStar U A ∈ borelSigma α ∧ vaughtTriangle U A ∈ borelPi (α + 1)) ∧
    (A ∈ borelPi α →
      vaughtStar U A ∈ borelSigma (α + 1) ∧ vaughtTriangle U A ∈ borelPi α) := by
  exact ⟨fun hA => ⟨(vaught_preserves_borel_levels α hα).1 hA hU,
      (vaught_borel_successor_bounds hα (Or.inl hA) hU).2⟩,
    fun hA => ⟨(vaught_borel_successor_bounds hα (Or.inr hA) hU).1,
      (vaught_preserves_borel_levels α hα).2 hA hU⟩⟩

end Polish
end PolishSpaceBook
