module

public import PolishSpaceBook.LambdaHKLDichotomy
public import PolishSpaceBook.ZeroDimensionalPolishRefinement

@[expose] public section

/-!
# Transport of the HKL embedding to a general Polish space

Extend a relation on a closed Baire subspace by one class outside the
subspace. Its nonsmoothness persists. The preimage of the closed subspace
under an E0 embedding is nonempty, closed, and E0 invariant, hence all of
Cantor space. Finally use the continuous Borel isomorphism supplied by the
book's graph refinement and closed partition-tree presentation.
-/
namespace PolishSpaceBook
open Set Function Filter Topology MeasureTheory

/-- Adjoin one equivalence class containing all points outside a subspace. -/
def outsideClassExtension {X : Type*} (F : Set X) (E : Setoid F) : Setoid X where
  r x y := (∃ hx : x ∈ F, ∃ hy : y ∈ F, E.r ⟨x, hx⟩ ⟨y, hy⟩) ∨ (x ∉ F ∧ y ∉ F)
  iseqv := by
    classical
    refine ⟨?_, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ F
      · exact Or.inl ⟨hx, hx, E.refl _⟩
      · exact Or.inr ⟨hx, hx⟩
    · rintro x y (⟨hx, hy, h⟩ | ⟨hx, hy⟩)
      · exact Or.inl ⟨hy, hx, E.symm h⟩
      · exact Or.inr ⟨hy, hx⟩
    · rintro x y z (⟨hx, hy, hxy⟩ | ⟨hx, hy⟩) (⟨hy', hz, hyz⟩ | ⟨hy', hz⟩)
      · exact Or.inl ⟨hx, hz, E.trans hxy hyz⟩
      · exact False.elim (hy' hy)
      · exact False.elim (hy hy')
      · exact Or.inr ⟨hx, hz⟩

@[simp] theorem outsideClassExtension_subtype {X : Type*} (F : Set X) (E : Setoid F) (x y : F) :
    (outsideClassExtension F E).r x.val y.val ↔ E.r x y := by
  constructor
  · rintro (⟨hx, hy, h⟩ | ⟨hx, _⟩)
    · exact h
    · exact False.elim (hx x.property)
  · intro h
    exact Or.inl ⟨x.property, y.property, h⟩

theorem outsideClassExtension_mem_iff {X : Type*} (F : Set X) (E : Setoid F) {x y : X}
    (h : (outsideClassExtension F E).r x y) : x ∈ F ↔ y ∈ F := by
  rcases h with ⟨hx, hy, _⟩ | ⟨hx, hy⟩
  · exact ⟨fun _ => hy, fun _ => hx⟩
  · exact ⟨fun h => False.elim (hx h), fun h => False.elim (hy h)⟩

theorem measurableSet_outsideClassExtension {X : Type*} [MeasurableSpace X]
    (F : Set X) (hF : MeasurableSet F) (E : Setoid F)
    (hE : MeasurableSet {p : F × F | E.r p.1 p.2}) :
    MeasurableSet {p : X × X | (outsideClassExtension F E).r p.1 p.2} := by
  have he : {p : X × X | (outsideClassExtension F E).r p.1 p.2} =
      (Prod.map (Subtype.val : F → X) (Subtype.val : F → X) '' {p | E.r p.1 p.2}) ∪
        (Fᶜ ×ˢ Fᶜ) := by
    ext p
    constructor
    · rintro (⟨hx, hy, hxy⟩ | h)
      · exact Or.inl ⟨(⟨p.1, hx⟩, ⟨p.2, hy⟩), hxy, rfl⟩
      · exact Or.inr h
    · rintro (⟨⟨x, y⟩, hxy, rfl⟩ | h)
      · exact Or.inl ⟨x.property, y.property, hxy⟩
      · exact Or.inr h
  rw [he]
  exact (((MeasurableEmbedding.subtype_coe hF).prodMap
    (MeasurableEmbedding.subtype_coe hF)).measurableSet_image.mpr hE).union (hF.compl.prod hF.compl)

theorem smooth_of_outsideClassExtension_smooth {X : Type*} [MeasurableSpace X]
    (F : Set X) (E : Setoid F) (h : Smooth (outsideClassExtension F E).r) : Smooth E.r := by
  obtain ⟨c, hc, hcomplete⟩ := h
  exact ⟨c ∘ Subtype.val, hc.comp measurable_subtype_coe, fun x y =>
    (outsideClassExtension_subtype F E x y).symm.trans (hcomplete x.val y.val)⟩

/-- Every nonempty closed E0-invariant subset of Cantor space is the whole
space: overwrite successively longer prefixes of one of its members. -/
theorem closed_e0_invariant_eq_univ (S : Set (ℕ → Bool)) (hS : IsClosed S)
    (hne : S.Nonempty) (hi : ∀ a b, E0 a b → a ∈ S → b ∈ S) : S = univ := by
  obtain ⟨a, ha⟩ := hne
  apply eq_univ_of_forall
  intro b
  let q : ℕ → (ℕ → Bool) := fun n k => if k < n then b k else a k
  have hq (n : ℕ) : q n ∈ S := hi a (q n) ⟨n, by
    intro k hk
    simp [q, not_lt.mpr hk]⟩ ha
  have hlim : Tendsto q atTop (𝓝 b) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop k] with n hn
    simp [q, hn]
  exact hS.mem_of_tendsto hlim (Eventually.of_forall hq)

/-- A continuous E0 reduction into the extended relation cannot leave the
closed subspace. Its nonempty closed invariant preimage must be all Cantor space. -/
theorem hkl_embedding_stays_in_closed {F : Set FusionReal} (hF : IsClosed F) (E : Setoid F)
    {π : (ℕ → Bool) → FusionReal} (hc : Continuous π)
    (hred : ∀ a b, E0 a b ↔ (outsideClassExtension F E).r (π a) (π b)) : ∀ a, π a ∈ F := by
  have hn : (π ⁻¹' F).Nonempty := by
    by_contra h
    have ha : π (fun _ => false) ∉ F := fun hx => h ⟨_, hx⟩
    have hb : π (fun _ => true) ∉ F := fun hx => h ⟨_, hx⟩
    obtain ⟨N, hN⟩ := (hred (fun _ => false) (fun _ => true)).mpr (Or.inr ⟨ha, hb⟩)
    exact Bool.false_ne_true (hN N le_rfl)
  have heq := closed_e0_invariant_eq_univ (π ⁻¹' F) (hF.preimage hc) hn
    (fun a b hab ha => (outsideClassExtension_mem_iff F E ((hred a b).mp hab)).mp ha)
  intro a
  exact (eq_univ_iff_forall.mp heq) a

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    This proves both directions of the reduction on Baire space. For a general Polish $X$, take a closed
    $F\IncludedIn\BaireSpace$ and a continuous Borel isomorphism from $F$ onto $X$, as constructed in
    §{sec:closed-presentation-baire}. Pull $E$ back to $F$ and extend it to Baire space by putting all points outside
    $F$ into one new class. This extension is Borel and nonsmooth: a complete Borel invariant for it would restrict
    to one for $E$. Apply the Baire-space result. The inverse image of $F$ under the resulting embedding is closed
    and $\EventualEqualityER$-invariant. It is nonempty, since otherwise all images would be equivalent. Every nonempty
    closed $\EventualEqualityER$-invariant subset of Cantor space is the whole space: changing increasingly long
    prefixes of one member approximates any prescribed binary sequence. Hence the embedding takes values in $F$.
    Composing with the continuous Borel isomorphism onto $X$ preserves continuity, injectivity, and the reduction
    equivalence.
-/
/-- HKL on a closed Baire subspace, with its embedding taking actual values
in the subspace rather than merely in the ambient Baire space. -/
theorem hkl_embedding_closed_baire (F : Set FusionReal) (hF : IsClosed F) (E : Setoid F)
    (hE : MeasurableSet {p : F × F | E.r p.1 p.2}) (hns : ¬ Smooth E.r) :
    ∃ π : (ℕ → Bool) → F, Continuous π ∧ Injective π ∧
      ∀ a b, E0 a b ↔ E.r (π a) (π b) := by
  obtain ⟨π, hc, hinj, hred⟩ := LambdaTree.hkl_embedding_baire (outsideClassExtension F E)
    (measurableSet_outsideClassExtension F hF.measurableSet E hE)
    (fun h => hns (smooth_of_outsideClassExtension_smooth F E h))
  have hm := hkl_embedding_stays_in_closed hF E hc hred
  refine ⟨fun a => ⟨π a, hm a⟩, hc.subtype_mk hm, ?_, ?_⟩
  · intro a b h
    exact hinj (congrArg Subtype.val h)
  · intro a b
    exact (hred a b).trans (outsideClassExtension_subtype F E ⟨π a, hm a⟩ ⟨π b, hm b⟩)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: theorem
  title: HKL embedding; Glimm--Effros form
-/
/-- HKL embedding for a nonsmooth Borel equivalence relation on an arbitrary
Polish space. The closed presentation, common oracle, kernel, splitting and
fusion are all constructed by the preceding modules. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    The final step transfers the result
    through the closed presentation to any Polish space.
-/
theorem hkl_embedding_polish (X : Type) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) (hns : ¬ Smooth E.r) :
    ∃ π : (ℕ → Bool) → X, Continuous π ∧ Injective π ∧
      ∀ a b, E0 a b ↔ E.r (π a) (π b) := by
  obtain ⟨F, hF, e, he, hinv⟩ := exists_continuous_closed_baire_presentation X
  let R : Setoid F := Setoid.comap e E
  have hR : MeasurableSet {p : F × F | R.r p.1 p.2} :=
    hE.preimage ((he.comp continuous_fst).prodMk (he.comp continuous_snd)).measurable
  have hinv' : Measurable e.symm := hinv.mono
    (le_of_eq (BorelSpace.measurable_eq (α := X)).symm)
    (le_of_eq (BorelSpace.measurable_eq (α := F)))
  have hnR : ¬ Smooth R.r := by
    rintro ⟨c, hc, hclass⟩
    apply hns
    refine ⟨c ∘ e.symm, hc.comp hinv', ?_⟩
    intro x y
    have hh : E.r (e (e.symm x)) (e (e.symm y)) ↔ c (e.symm x) = c (e.symm y) :=
      hclass (e.symm x) (e.symm y)
    simpa only [Equiv.apply_symm_apply, Function.comp_apply] using hh
  obtain ⟨π, hc, hi, hr⟩ := hkl_embedding_closed_baire F hF R hR hnR
  exact ⟨e ∘ π, he.comp hc, e.injective.comp hi, hr⟩

/-- The exhaustive alternatives follow from the embedding theorem. Mutual
exclusivity additionally uses the separate nonsmoothness proof for E0. -/
theorem hkl_alternatives_polish (X : Type) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) :
    Smooth E.r ∨ ∃ π : (ℕ → Bool) → X, Continuous π ∧ Injective π ∧
      ∀ a b, E0 a b ↔ E.r (π a) (π b) := by
  classical
  by_cases h : Smooth E.r
  · exact Or.inl h
  · exact Or.inr (hkl_embedding_polish X E hE h)

end PolishSpaceBook
