module

public import PolishSpaceBook.PolishEmbeddingsBorelRefinements

@[expose] public section

/-! # The sigma-algebra proof of Polish clopen refinement

Open sets are split from their complements by a topological sum. Its Borel
structure is checked with the measurable sum equivalence. Countable unions
use the closed-diagonal join and another open-set split.
-/
namespace PolishSpaceBook
noncomputable section
open Set TopologicalSpace Topology MeasureTheory
universe u
variable {X : Type u}

/-- The class of sets used in the book's one-set refinement argument. -/
def ClopenRefinable (t : TopologicalSpace X) (B : Set X) : Prop :=
  ∃ s : TopologicalSpace X, s ≤ t ∧ @PolishSpace X s ∧
    @borel X s = @borel X t ∧ @IsClopen X s B

/-- Split an open set from its closed complement, checking Borel sets directly. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: proof
  excerpt: |
    If $B$ is $\tau$-open, then $B$ is Polish by §{sec:polish-key-properties}, and $\SetDifference{X}{B}$ is closed, hence
    Polish.
    Put on $X$ the topological sum of the two subspaces $B$ and $\SetDifference{X}{B}$. This topology refines $\tau$, makes
    $B$ clopen, and is Polish by the countable-disjoint-union result of §{sec:polish-key-properties}. It has the same Borel
    sets as $\tau$, because its open sets are unions of relatively open subsets of $B$ and $\SetDifference{X}{B}$, all of
    which are $\tau$-Borel.
-/
theorem clopenRefinable_of_isOpen [t : TopologicalSpace X] [PolishSpace X]
    {B : Set X} (hB : IsOpen B) : ClopenRefinable t B := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have : PolishSpace B := hB.polishSpace
  have : PolishSpace (Bᶜ : Set X) := hB.isClosed_compl.polishSpace
  let f : B ⊕ (Bᶜ : Set X) ≃ X := Equiv.Set.sumCompl B
  have hm : Measurable f.symm :=
    (MeasurableEquiv.sumCompl hB.measurableSet).symm.measurable
  have hv₁ : Continuous (fun x : B => (x : X)) := continuous_subtype_val
  have hv₂ : Continuous (fun x : (Bᶜ : Set X) => (x : X)) := continuous_subtype_val
  let tSum : TopologicalSpace (B ⊕ (Bᶜ : Set X)) := inferInstance
  have hmsum : @borel (B ⊕ (Bᶜ : Set X)) tSum ≤
      (inferInstance : MeasurableSpace (B ⊕ (Bᶜ : Set X))) := by
    apply MeasurableSpace.generateFrom_le
    intro U hU
    exact measurableSet_sum_iff.mpr
      ⟨(hU.preimage continuous_inl).measurableSet,
        (hU.preimage continuous_inr).measurableSet⟩
  have hpre₁ : Sum.inl ⁻¹' f ⁻¹' B = (univ : Set B) := by
    ext x
    change ((x : X) ∈ B) ↔ True
    exact iff_true_intro x.property
  have hpre₂ : Sum.inr ⁻¹' f ⁻¹' B = (∅ : Set (Bᶜ : Set X)) := by
    ext x
    change ((x : X) ∈ B) ↔ False
    exact iff_false_intro x.property
  let s := TopologicalSpace.coinduced f tSum
  let : TopologicalSpace X := t
  have hle : s ≤ t := by
    simp only [s, tSum, instTopologicalSpaceSum, coinduced_sup, coinduced_compose,
      sup_le_iff, ← continuous_iff_coinduced_le]
    exact ⟨hv₁, hv₂⟩
  have hp : @PolishSpace X s := by
    change @PolishSpace X (TopologicalSpace.coinduced f tSum)
    rw [← f.induced_symm]
    exact f.symm.polishSpace_induced
  have hc : @IsClopen X s B := by
    constructor
    · change @IsClosed X (TopologicalSpace.coinduced f tSum) B
      rw [isClosed_coinduced, isClosed_sum_iff, hpre₁, hpre₂]
      exact ⟨isClosed_univ, isClosed_empty⟩
    · change @IsOpen X (TopologicalSpace.coinduced f tSum) B
      rw [isOpen_coinduced, isOpen_sum_iff, hpre₁, hpre₂]
      exact ⟨isOpen_univ, isOpen_empty⟩
  have hb : @borel X s = @borel X t := by
    apply le_antisymm
    · change @borel X (TopologicalSpace.coinduced f tSum) ≤ @borel X t
      rw [← f.induced_symm, borel_comap]
      exact (MeasurableSpace.comap_mono hmsum).trans hm.comap_le
    · exact borel_anti hle
  exact ⟨s, hle, hp, hb, hc⟩

/-- Taking complements preserves the same refinement witness. -/
theorem ClopenRefinable.compl {t : TopologicalSpace X} {B : Set X}
    (hB : ClopenRefinable t B) : ClopenRefinable t Bᶜ := by
  obtain ⟨s, hle, hp, hb, hc⟩ := hB
  exact ⟨s, hle, hp, hb, hc.compl⟩

/-- Join the witnesses and split their now-open union once more. -/
theorem clopenRefinable_iUnion [t : TopologicalSpace X] [PolishSpace X]
    (B : ℕ → Set X) (hB : ∀ n, ClopenRefinable t (B n)) :
    ClopenRefinable t (⋃ n, B n) := by
  choose ts hle hp hb hc using hB
  obtain ⟨hjoin, hbjoin⟩ := polish_borel_iInf_of_common_refinement ts hle hp hb
  let : TopologicalSpace X := ⨅ n, ts n
  let : PolishSpace X := hjoin
  have hU : IsOpen (⋃ n, B n) :=
    isOpen_iUnion (fun n => (hc n).2.mono (iInf_le ts n))
  obtain ⟨s, hs, hsp, hbs, hcs⟩ := clopenRefinable_of_isOpen hU
  exact ⟨s, hs.trans ((iInf_le ts 0).trans (hle 0)), hsp,
    hbs.trans hbjoin, hcs⟩

/-- The class in the book is a sigma-algebra, rather than just a collection. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: proof
  excerpt: |
    Next prove the one-set case. Let $\mathcal C$ be the class of $\tau$-Borel sets $B\IncludedIn X$ for which there is a
    Polish topology $\tau_B\supseteq\tau$ satisfying $\mathcal B(\tau_B)=\mathcal B(\tau)$ and making $B$ clopen. We show
    that $\mathcal C$ is a $\sigma$-algebra containing every $\tau$-open set.
-/
abbrev clopenRefinementMeasurableSpace [t : TopologicalSpace X] [PolishSpace X] :
    MeasurableSpace X where
  MeasurableSet' := ClopenRefinable t
  measurableSet_empty := ⟨t, le_rfl, inferInstance, rfl, isClopen_empty⟩
  measurableSet_compl := fun _ h => h.compl
  measurableSet_iUnion := clopenRefinable_iUnion

/-- Since this sigma-algebra contains every open set, it contains all Borel sets. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: proof
  excerpt: |
    The class $\mathcal C$ is closed under complements, since a topology that makes $B$ clopen also makes
    $\SetDifference{X}{B}$
    clopen. Now suppose $B=\bigcup_m B_m$ with each $B_m\in\mathcal C$. Choose $\tau_m$ making $B_m$ clopen, and form the
    joined topology $\tau_\infty$ above. Then every $B_m$ is clopen in $\tau_\infty$, so $B$ is $\tau_\infty$-open. Apply
    the open-set case, now with $\tau_\infty$ as the starting Polish topology, to obtain a further Polish refinement making
    $B$ clopen and preserving the same Borel $\sigma$-algebra. Hence $B\in\mathcal C$. Therefore $\mathcal C$ is a
    $\sigma$-algebra containing $\tau$, so it contains every $\tau$-Borel set.
-/
theorem clopenRefinable_of_borel [t : TopologicalSpace X] [PolishSpace X]
    {B : Set X} (hB : @MeasurableSet X (borel X) B) : ClopenRefinable t B := by
  have hle : borel X ≤ clopenRefinementMeasurableSpace := by
    apply MeasurableSpace.generateFrom_le
    exact fun _ h => clopenRefinable_of_isOpen h
  exact hle B hB

/-- A refinement witness also shows that the original set was Borel. -/
theorem ClopenRefinable.measurableSet {t : TopologicalSpace X} {B : Set X}
    (hB : ClopenRefinable t B) : @MeasurableSet X (@borel X t) B := by
  obtain ⟨s, _, _, hb, hc⟩ := hB
  let : TopologicalSpace X := s
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  rw [← hb]
  exact hc.2.measurableSet

/-- The countable-family construction now uses the book's sigma-algebra proof. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    For the given countable family $\{B_n\}$, choose for each $n$ a Polish refinement $\tau_n$ with the same Borel sets in
    which $B_n$ is clopen. The joined topology $\tau'$ from the first paragraph is Polish, refines $\tau$, has $\mathcal
    B(\tau')=\mathcal B(\tau)$, and makes every $B_n$ clopen.
-/
theorem exists_polish_refinement_clopen_via_sigma
    [t : TopologicalSpace X] [PolishSpace X]
    (B : ℕ → Set X) (hB : ∀ n, @MeasurableSet X (borel X) (B n)) :
    ∃ s : TopologicalSpace X, s ≤ t ∧ @PolishSpace X s ∧
      @borel X s = @borel X t ∧ ∀ n, @IsClopen X s (B n) := by
  choose ts hle hp hb hc using fun n => clopenRefinable_of_borel (hB n)
  obtain ⟨hjoin, hbjoin⟩ := polish_borel_iInf_of_common_refinement ts hle hp hb
  refine ⟨⨅ n, ts n, (iInf_le ts 0).trans (hle 0), hjoin, hbjoin, ?_⟩
  exact fun n => ⟨(hc n).1.mono (iInf_le ts n), (hc n).2.mono (iInf_le ts n)⟩

end
end PolishSpaceBook
