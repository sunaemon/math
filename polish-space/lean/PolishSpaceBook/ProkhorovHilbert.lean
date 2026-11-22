module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import PolishSpaceBook.PolishEmbeddingsBorelRefinements
public import PolishSpaceBook.BorelMeasureRegularity

@[expose] public section

/-!
# Prokhorov's theorem through a Hilbert-cube embedding

The compact ambient space supplies compactness of probability measures. Open-set
semicontinuity gives a uniform compact approximation inside each open neighborhood
of the embedded space. Their intersection supplies the book's compact approximant.
-/

noncomputable section
namespace PolishSpaceBook.ProkhorovHilbert
open Set Filter Topology TopologicalSpace MeasureTheory MeasurableSpace Function
open scoped ENNReal

section Ambient
variable {H : Type*} [MetricSpace H] [MeasurableSpace H] [BorelSpace H]

lemma open_eval_lowerSemicontinuous {G : Set H} (hG : IsOpen G) :
    LowerSemicontinuous (fun μ : ProbabilityMeasure H => (μ : Measure H) G) := by
  intro μ
  exact lowerSemicontinuousAt_iff_le_liminf.mpr
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hG)

lemma closed_eval_upperSemicontinuous {K : Set H} (hK : IsClosed K) :
    UpperSemicontinuous (fun μ : ProbabilityMeasure H => (μ : Measure H) K) := by
  intro μ
  exact upperSemicontinuousAt_iff_limsup_le.mpr
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hK)

variable [CompactSpace H] [PolishSpace H]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Conversely, let $C:=\Closure{\Gamma}$ be compact. Write
    $$X=\bigcap_{n\in\omega}G_n$$
    with each $G_n$ open in $H$, and fix $\varepsilon>0$. First let $G\IncludedIn H$ be open with
    $\hat\mu(G)=1$ for every $\mu\in C$. We claim that there is a compact $L\IncludedIn G$ such that
    $$\hat\mu(L)>1-\varepsilon\qquad(\mu\in C).$$
    For each $\mu\in C$, inner regularity gives a compact $L_\mu\IncludedIn G$ with
    $\hat\mu(L_\mu)>1-\varepsilon$. Choose an open $V_\mu$ with
    $$L_\mu\IncludedIn V_\mu\IncludedIn\Closure{V_\mu}\IncludedIn G.$$
    By the open-set clause of Portmanteau, evaluation on $V_\mu$ is lower semicontinuous, so
    $$\{\lambda\in C:\hat\lambda(V_\mu)>1-\varepsilon\}$$
    is open in $C$. These neighborhoods cover $C$. Choose a finite subcover indexed by $\mu_0,\ldots,\mu_r$ and put
    $$L:=\bigcup_{j\le r}\Closure{V_{\mu_j}}.$$
    Then $L$ is compact, is contained in $G$, and has $\hat\lambda(L)>1-\varepsilon$ for every $\lambda\in C$.
-/
/-- A compact family concentrated on one open set has a common compact
approximation contained in that open set. -/
theorem uniform_compact_in_open (C : Set (ProbabilityMeasure H)) (hC : IsCompact C)
    {G : Set H} (hG : IsOpen G) (hmass : ∀ μ ∈ C, (μ : Measure H) G = 1)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ L : Set H, IsCompact L ∧ L ⊆ G ∧ ∀ μ ∈ C, (μ : Measure H) Lᶜ < ε := by
  classical
  let r : ℝ≥0∞ := 1 - ε
  have hr : r < 1 := ENNReal.sub_lt_self (by norm_num) (by norm_num) hε.ne'
  have hex (μ : C) : ∃ V : Set H, IsOpen V ∧ closure V ⊆ G ∧ r < (μ.val : Measure H) V := by
    obtain ⟨K, hKG, ⟨hK, _⟩, hKr⟩ := BorelMeasureRegularity.innerRegular_compact
      (μ.val : Measure H) hG.measurableSet r
      (show r < (μ.val : Measure H) G by rw [hmass μ.val μ.property]; exact hr)
    obtain ⟨V, hV, hKV, hVG⟩ := hK.exists_isOpen_closure_subset (hG.mem_nhdsSet.mpr hKG)
    exact ⟨V, hV, hVG, hKr.trans_le (measure_mono hKV)⟩
  choose V hV hVG hVr using hex
  let U (μ : C) : Set (ProbabilityMeasure H) := {ν | r < (ν : Measure H) (V μ)}
  have hU (μ : C) : IsOpen (U μ) := (open_eval_lowerSemicontinuous (hV μ)).isOpen_preimage r
  have hcover : C ⊆ ⋃ μ : C, U μ := by
    intro μ hμ
    exact mem_iUnion.mpr ⟨⟨μ, hμ⟩, hVr ⟨μ, hμ⟩⟩
  obtain ⟨F, hF⟩ := hC.elim_finite_subcover U hU hcover
  let L : Set H := ⋃ μ ∈ F, closure (V μ)
  have hL : IsCompact L := F.finite_toSet.isCompact_biUnion (fun _ _ => isClosed_closure.isCompact)
  have hLG : L ⊆ G := iUnion₂_subset fun μ _ => hVG μ
  refine ⟨L, hL, hLG, ?_⟩
  intro μ hμ
  obtain ⟨ν, hν, hμU⟩ := mem_iUnion₂.mp (hF hμ)
  have hVL : V ν ⊆ L := subset_closure.trans (by intro x hx; exact mem_iUnion₂.mpr ⟨ν, hν, hx⟩)
  have hbound : 1 - ε < (μ : Measure H) L := hμU.trans_le (measure_mono hVL)
  rw [measure_compl hL.isClosed.measurableSet (measure_ne_top _ _), measure_univ]
  exact ENNReal.sub_lt_of_sub_lt (prob_le_one) (Or.inl (by norm_num)) hbound

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Apply the claim to $G_n$ with error $\varepsilon 2^{-(n+1)}$. This gives compact $L_n\IncludedIn G_n$ with
    $$\hat\mu(\SetDifference{H}{L_n})<\varepsilon 2^{-(n+1)}\qquad(\mu\in C).$$
    Set
    $$K:=\bigcap_{n\in\omega}L_n.$$
    This is a closed subset of the compact space $H$ and lies in $\bigcap_nG_n=X$, so it is compact in $X$.
    For every $\mu\in C$,
    $$\begin{aligned}
    \mu(\SetDifference{X}{K})
    &=\hat\mu(\SetDifference{H}{K})\\
    &\le\sum_{n\in\omega}\hat\mu(\SetDifference{H}{L_n})<\varepsilon.
    \end{aligned}$$
    The final inequality follows by retaining the strict bound at $n=0$ and using the non-strict bounds for the other
    terms; the bounding geometric series has finite sum $\varepsilon$.
    Thus $C$ is tight, and its subset $\Gamma$ is tight as well.
-/
/-- Intersect compact approximants in the open sets of a G-delta representation. -/
theorem uniform_compact_in_gdelta (C : Set (ProbabilityMeasure H)) (hC : IsCompact C)
    {S : Set H} (hS : IsGδ S) (hmass : ∀ μ ∈ C, (μ : Measure H) S = 1)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set H, IsCompact K ∧ K ⊆ S ∧ ∀ μ ∈ C, (μ : Measure H) Kᶜ < ε := by
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, empty_subset _, fun μ _ => by simp [htop]⟩
  obtain ⟨G, hG, hSG⟩ := hS.eq_iInter_nat
  let δ : ℕ → ℝ≥0∞ := fun n => ε * (2⁻¹ : ℝ≥0∞) ^ (n + 1)
  have hδpos (n : ℕ) : 0 < δ n :=
    ENNReal.mul_pos hε.ne' (pow_ne_zero _ (by simp))
  have hδsum : ∑' n, δ n = ε := by
    simp only [δ, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one,
      ENNReal.one_sub_inv_two, inv_inv]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have hex n : ∃ L : Set H, IsCompact L ∧ L ⊆ G n ∧ ∀ μ ∈ C, (μ : Measure H) Lᶜ < δ n := by
    apply uniform_compact_in_open C hC (hG n) _ (hδpos n)
    intro μ hμ
    apply le_antisymm prob_le_one
    rw [← hmass μ hμ]
    exact measure_mono (hSG ▸ iInter_subset G n)
  choose L hL hLG herror using hex
  let K : Set H := ⋂ n, L n
  have hK : IsCompact K := (isClosed_iInter (fun n => (hL n).isClosed)).isCompact
  have hKS : K ⊆ S := by
    rw [hSG]
    exact iInter_mono hLG
  refine ⟨K, hK, hKS, ?_⟩
  intro μ hμ
  have hsumle : (∑' n, (μ : Measure H) (L n)ᶜ) ≤ ε := by
    rw [← hδsum]
    exact ENNReal.tsum_le_tsum (fun n => (herror n μ hμ).le)
  calc
    (μ : Measure H) Kᶜ = (μ : Measure H) (⋃ n, (L n)ᶜ) := by
      change (μ : Measure H) (⋂ n, L n)ᶜ = _
      rw [compl_iInter]
    _ ≤ ∑' n, (μ : Measure H) (L n)ᶜ := measure_iUnion_le _
    _ < ∑' n, δ n := ENNReal.tsum_lt_tsum
      (ne_top_of_le_ne_top htop hsumle) (fun n => (herror n μ hμ).le) (herror 0 μ hμ)
    _ = ε := hδsum

end Ambient

section Embedding
variable {X H : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace H] [MeasurableSpace H] [BorelSpace H]
variable (f : X → H) (hf : IsEmbedding f)

/-- Regard a measure on the original space as a measure on the ambient space. -/
def push (f : X → H) (_hf : IsEmbedding f) (μ : ProbabilityMeasure X) : ProbabilityMeasure H :=
  μ.map f

lemma push_apply (μ : ProbabilityMeasure X) {A : Set H} (hA : MeasurableSet A) :
    (push f hf μ : Measure H) A = (μ : Measure X) (f ⁻¹' A) :=
  μ.map_apply' hf.continuous.measurable.aemeasurable hA

lemma push_continuous : Continuous (push f hf) := ProbabilityMeasure.continuous_map hf.continuous

lemma push_mass_range (hR : MeasurableSet (range f)) (μ : ProbabilityMeasure X) :
    (push f hf μ : Measure H) (range f) = 1 := by
  rw [push_apply f hf μ hR]
  simp

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    If $\Gamma=\emptyset$, both assertions hold trivially, so assume $\Gamma\ne\emptyset$.
    By §{sec:hilbert-cube-embedding}, identify $X$ with a $\Gdelta$ subspace of the Hilbert cube
    $H=[0,1]^\omega$. Extend each $\mu\in\ProbMeasures{X}$ to $H$ by
    $$\hat\mu(B):=\mu(B\cap X).$$
    The map $\mu\mapsto\hat\mu$ is injective and continuous for the weak topologies: bounded continuous functions
    on $H$ restrict to bounded continuous functions on $X$. To prove continuity of its inverse on the image,
    it suffices to check sequences, since both weak topologies are metrizable by §{sec:prob-measure-space}.
    Suppose $\hat\mu_i\to\hat\mu$. For an open $O\IncludedIn X$, choose an open $U\IncludedIn H$ with $O=X\cap U$.
    The Portmanteau inequality gives
    $$\mu(O)=\hat\mu(U)\le\liminf_i\hat\mu_i(U)=\liminf_i\mu_i(O).$$
    Its converse gives $\mu_i\to\mu$, so the extension map is a topological embedding.
-/
/-- Portmanteau on ambient open sets proves that the pushforward is an embedding. -/
lemma push_isEmbedding [SeparableSpace H] (hR : MeasurableSet (range f)) : IsEmbedding (push f hf) := by
  refine ⟨isInducing_iff_nhds.mpr (fun μ => le_antisymm ?_ ?_), ?_⟩
  · exact tendsto_iff_comap.mp (push_continuous f hf).continuousAt
  · have ht : Tendsto (push f hf) (comap (push f hf) (𝓝 (push f hf μ)))
        (𝓝 (push f hf μ)) := map_comap_le
    have hinv : Tendsto id (comap (push f hf) (𝓝 (push f hf μ))) (𝓝 μ) := by
      apply tendsto_of_forall_isOpen_le_liminf'
      intro O hO
      obtain ⟨U, hU, hpre⟩ := hf.isInducing.isOpen_iff.mp hO
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht hU
      simpa only [push_apply f hf _ hU.measurableSet, hpre, id_eq] using h
    simpa only [Tendsto, Filter.map_id] using hinv
  · intro μ ν h
    apply ProbabilityMeasure.toMeasure_injective
    apply (hf.measurableEmbedding hR).map_injective
    exact congrArg ProbabilityMeasure.toMeasure h

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Its image consists exactly of the probabilities $\nu$ on $H$ with $\nu(X)=1$.
    Indeed, $X$ is Borel in $H$, and restricting such a measure to the Borel subspace $X$ gives a probability measure
    whose extension is $\nu$. The equality follows because the complement of $X$ has measure zero.
-/
/-- The image consists exactly of the ambient probabilities concentrated on the range. -/
lemma mem_range_push_iff (hR : MeasurableSet (range f)) (ν : ProbabilityMeasure H) :
    ν ∈ range (push f hf) ↔ (ν : Measure H) (range f) = 1 := by
  constructor
  · rintro ⟨μ, rfl⟩
    exact push_mass_range f hf hR μ
  · intro hν
    have hj := hf.measurableEmbedding hR
    have hp : IsProbabilityMeasure ((ν : Measure H).comap f) := by
      constructor
      rw [hj.comap_apply, image_univ, hν]
    let μ : ProbabilityMeasure X := ⟨(ν : Measure H).comap f, hp⟩
    refine ⟨μ, ProbabilityMeasure.toMeasure_injective ?_⟩
    change ((ν : Measure H).comap f).map f = (ν : Measure H)
    rw [hj.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff_prob_eq_one hR).mpr hν)

include hf

/-- Compact families on a G-delta subspace are tight, through compact
approximants in each ambient open set. -/
theorem compact_tight [CompactSpace H] [PolishSpace H] (hR : IsGδ (range f)) (C : Set (ProbabilityMeasure X)) (hC : IsCompact C) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ C} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K, hK, hKR, herror⟩ := uniform_compact_in_gdelta (push f hf '' C)
    (hC.image (push_continuous f hf)) hR
    (by rintro _ ⟨μ, hμ, rfl⟩; exact push_mass_range f hf hR.measurableSet μ) hε
  have hpre : IsCompact (f ⁻¹' K) := hf.isCompact_iff.mpr (by rwa [image_preimage_eq_of_subset hKR])
  refine ⟨f ⁻¹' K, hpre, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have h := herror (push f hf μ) (mem_image_of_mem _ hμ)
  rw [push_apply f hf μ hK.isClosed.isOpen_compl.measurableSet, preimage_compl] at h
  exact h.le

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Assume that $\Gamma$ is tight, and put $\widehat\Gamma:=\{\hat\mu:\mu\in\Gamma\}$.
    The space $\ProbMeasures{H}$ is compact by §{sec:prob-measure-space}.
    For every $\delta>0$, choose a compact $K_\delta\IncludedIn X$ with
    $$\mu(\SetDifference{X}{K_\delta})\le\delta\qquad(\mu\in\Gamma).$$
    Viewed in $H$, this set is still compact and hence closed. Portmanteau implies that the set
    $$\{\nu\in\ProbMeasures{H}:\nu(K_\delta)\ge1-\delta\}$$
    is closed. It contains $\widehat\Gamma$, and therefore also its closure.
    Every $\nu\in\Closure{\widehat\Gamma}$ consequently satisfies
    $$\nu(X)\ge\nu(K_\delta)\ge1-\delta.$$
    Since $\delta>0$ was arbitrary, $\nu(X)=1$. Thus the compact set $\Closure{\widehat\Gamma}$ lies in the image
    of the extension map. Pulling it back gives a compact set containing $\Gamma$, so $\Closure{\Gamma}$ is compact.
-/
/-- Tightness prevents limit measures in the compact ambient space from losing mass
outside the original range. -/
lemma tight_closure_concentrated
    (Γ : Set (ProbabilityMeasure X))
    (htight : IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ Γ})
    {ν : ProbabilityMeasure H} (hν : ν ∈ closure (push f hf '' Γ)) :
    (ν : Measure H) (range f) = 1 := by
  apply le_antisymm prob_le_one
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨K, hK, herror⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
    ε (by exact_mod_cast hε)
  have hclosed : IsClosed {ρ : ProbabilityMeasure H | 1 - (ε : ℝ≥0∞) ≤ (ρ : Measure H) (f '' K)} :=
    (closed_eval_upperSemicontinuous (hK.image hf.continuous).isClosed).isClosed_preimage _
  have hsub : push f hf '' Γ ⊆ {ρ : ProbabilityMeasure H | 1 - (ε : ℝ≥0∞) ≤
      (ρ : Measure H) (f '' K)} := by
    rintro _ ⟨μ, hμ, rfl⟩
    change 1 - (ε : ℝ≥0∞) ≤ (push f hf μ : Measure H) (f '' K)
    rw [push_apply f hf μ (hK.image hf.continuous).isClosed.measurableSet,
      hf.injective.preimage_image]
    have hc := herror (μ : Measure X) ⟨μ, hμ, rfl⟩
    rw [prob_compl_eq_one_sub hK.isClosed.measurableSet] at hc
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using tsub_le_iff_right.mp hc)
  have hbound := closure_minimal hsub hclosed hν
  have hle : 1 - (ε : ℝ≥0∞) ≤ (ν : Measure H) (range f) :=
    hbound.trans (measure_mono (image_subset_range _ _))
  simpa [add_comm] using tsub_le_iff_right.mp hle

/-- The compact ambient closure lies in the embedded copy of the probability space. -/
theorem tight_compactClosure [CompactSpace H] [SeparableSpace H] (hR : MeasurableSet (range f))
    (Γ : Set (ProbabilityMeasure X))
    (htight : IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ Γ}) :
    IsCompact (closure Γ) := by
  have he := push_isEmbedding f hf hR
  have hsub : closure (push f hf '' Γ) ⊆ range (push f hf) := by
    intro ν hν
    exact (mem_range_push_iff f hf hR ν).mpr (tight_closure_concentrated f hf Γ htight hν)
  have hpre : IsCompact ((push f hf) ⁻¹' closure (push f hf '' Γ)) := by
    apply he.isCompact_iff.mpr
    rw [image_preimage_eq_of_subset hsub]
    exact isClosed_closure.isCompact
  apply hpre.of_isClosed_subset isClosed_closure
  exact closure_minimal (fun μ hμ => subset_closure (mem_image_of_mem _ hμ))
    (isClosed_closure.preimage (push_continuous f hf))

end Embedding

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Prokhorov
-/
/-- Prokhorov's equivalence with the book's Hilbert-cube proof in both directions. -/
theorem compactClosure_iff_tight {X : Type*} [MetricSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (Γ : Set (ProbabilityMeasure X)) :
    IsCompact (closure Γ) ↔
      IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ Γ} := by
  let : PolishSpace hilbert_cube := hilbert_cube_polish
  let := metrizableSpaceMetric hilbert_cube
  obtain ⟨f, hf, hR⟩ := exists_hilbert_cube_embedding X
  constructor
  · intro hC
    apply (compact_tight f hf hR (closure Γ) hC).subset
    rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨μ, subset_closure hμ, rfl⟩
  · exact tight_compactClosure f hf hR.measurableSet Γ

end PolishSpaceBook.ProkhorovHilbert
