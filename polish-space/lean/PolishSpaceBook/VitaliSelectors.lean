module

public import PolishSpaceBook.PolishGroupCategory
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Instances.Rat

@[expose] public section

/-! # Least representatives of rational cosets and their regularity obstructions -/

noncomputable section
namespace PolishSpaceBook
open Set MeasureTheory Topology Filter
open scoped Pointwise

/-- Projective predicates on finite tuples of reals: Borel predicates and
finitely many Boolean operations, continuous substitutions and real projections.
There is no closure under arbitrary countable families of projective ranks. -/
inductive ProjectiveRealSet : (n : ℕ) → Set (Fin n → ℝ) → Prop where
  | borel {n} {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) : ProjectiveRealSet n A
  | compl {n A} : ProjectiveRealSet n A → ProjectiveRealSet n Aᶜ
  | inter {n A B} : ProjectiveRealSet n A → ProjectiveRealSet n B → ProjectiveRealSet n (A ∩ B)
  | preimage {m n A} (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : Continuous f) :
      ProjectiveRealSet n A → ProjectiveRealSet m (f ⁻¹' A)
  | existsReal {n A} : ProjectiveRealSet (n + 1) A →
      ProjectiveRealSet n {x | ∃ y : ℝ, Fin.snoc x y ∈ A}

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The mechanism behind the negative direction is simple once a definable well-order of the reals is available. A
    projectively definable well-order lets one choose canonical representatives from equivalence classes that normally admit
    no definable selector. For example, applying the first-in-the-well-order choice to the cosets of $\QQ$ in $\R$ gives a
    projectively definable Vitali selector. Such a selector cannot be Lebesgue measurable and cannot have the Baire
    property. Thus the definable well-order of $\R$ in $L$ turns set-theoretic constructibility into explicit projective
    counterexamples to regularity.
-/
def leastRationalSelector (r : ℝ → ℝ → Prop) : Set ℝ :=
  {x | ∀ q : ℚ, ¬r (x + q) x}

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The mechanism behind the negative direction is simple once a definable well-order of the reals is available. A
    projectively definable well-order lets one choose canonical representatives from equivalence classes that normally admit
    no definable selector. For example, applying the first-in-the-well-order choice to the cosets of $\QQ$ in $\R$ gives a
    projectively definable Vitali selector. Such a selector cannot be Lebesgue measurable and cannot have the Baire
    property. Thus the definable well-order of $\R$ in $L$ turns set-theoretic constructibility into explicit projective
    counterexamples to regularity.
-/
theorem leastRationalSelector_projective (r : ℝ → ℝ → Prop)
    (hr : ProjectiveRealSet 2 {z | r (z 0) (z 1)}) :
    ProjectiveRealSet 1 {z | z 0 ∈ leastRationalSelector r} := by
  have hrat : MeasurableSet {z : Fin 2 → ℝ | ∃ q : ℚ, z 1 = z 0 + q} := by
    have he : {z : Fin 2 → ℝ | ∃ q : ℚ, z 1 = z 0 + q} =
        ⋃ q : ℚ, {z : Fin 2 → ℝ | z 1 = z 0 + q} := by ext z; simp
    rw [he]
    exact MeasurableSet.iUnion (fun q =>
      (isClosed_eq (continuous_apply 1) ((continuous_apply 0).add continuous_const)).measurableSet)
  have hswap : ProjectiveRealSet 2 {z | r (z 1) (z 0)} := by
    exact hr.preimage (fun z => ![z 1, z 0]) (by fun_prop)
  have hbad := (ProjectiveRealSet.borel hrat |>.inter hswap).existsReal.compl
  convert hbad using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff, Fin.snoc,
    Fin.isValue]
  change (∀ q : ℚ, ¬r (z 0 + q) (z 0)) ↔ ¬∃ y : ℝ, (∃ q : ℚ, y = z 0 + q) ∧ r y (z 0)
  simp only [not_exists, not_and, forall_exists_index]
  constructor
  · intro h y q he
    exact he ▸ h q
  · intro h q
    exact h (z 0 + q) q rfl

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The mechanism behind the negative direction is simple once a definable well-order of the reals is available. A
    projectively definable well-order lets one choose canonical representatives from equivalence classes that normally admit
    no definable selector. For example, applying the first-in-the-well-order choice to the cosets of $\QQ$ in $\R$ gives a
    projectively definable Vitali selector. Such a selector cannot be Lebesgue measurable and cannot have the Baire
    property. Thus the definable well-order of $\R$ in $L$ turns set-theoretic constructibility into explicit projective
    counterexamples to regularity.
-/
theorem leastRationalSelector_covers (r : ℝ → ℝ → Prop) [IsWellOrder ℝ r] (x : ℝ) :
    ∃ y ∈ leastRationalSelector r, ∃ q : ℚ, x = y + q := by
  let C : Set ℝ := {y | ∃ q : ℚ, y = x + q}
  have hC : C.Nonempty := ⟨x, 0, by simp⟩
  obtain ⟨y, ⟨q, hq⟩, hy⟩ := (show WellFounded r from inferInstance).has_min C hC
  refine ⟨y, ?_, -q, ?_⟩
  · intro p
    apply hy (y + p)
    exact ⟨q + p, by push_cast; linarith⟩
  · push_cast
    linarith

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The mechanism behind the negative direction is simple once a definable well-order of the reals is available. A
    projectively definable well-order lets one choose canonical representatives from equivalence classes that normally admit
    no definable selector. For example, applying the first-in-the-well-order choice to the cosets of $\QQ$ in $\R$ gives a
    projectively definable Vitali selector. Such a selector cannot be Lebesgue measurable and cannot have the Baire
    property. Thus the definable well-order of $\R$ in $L$ turns set-theoretic constructibility into explicit projective
    counterexamples to regularity.
-/
theorem leastRationalSelector_unique (r : ℝ → ℝ → Prop) [IsWellOrder ℝ r]
    {x y : ℝ} (hx : x ∈ leastRationalSelector r) (hy : y ∈ leastRationalSelector r)
    (q : ℚ) (hq : x - y = q) : x = y := by
  rcases trichotomous_of r x y with (hxy | he | hyx)
  · exact False.elim (hy q (by convert hxy using 1; linarith))
  · exact he
  · exact False.elim (hx (-q) (by convert hyx using 1; push_cast; linarith))

/-- A rational-coset transversal has no identity neighborhood in its difference set. -/
theorem rational_transversal_difference_not_nhds (V : Set ℝ)
    (hunique : ∀ x ∈ V, ∀ y ∈ V, ∀ q : ℚ, x - y = q → x = y) :
    V - V ∉ 𝓝 (0 : ℝ) := by
  intro hn
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hqin : (q : ℝ) ∈ Metric.ball 0 ε := by
    change dist (q : ℝ) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_pos hq0]
    exact hqε
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_sub.mp (hball hqin)
  have he := hunique x hx y hy q hxy
  have hz : (q : ℝ) = 0 := by rw [← hxy, he, sub_self]
  exact (ne_of_gt hq0) hz

theorem rational_transversal_nonmeagre (V : Set ℝ)
    (hcover : ∀ x : ℝ, ∃ y ∈ V, ∃ q : ℚ, x = y + q) : ¬ IsMeagre V := by
  intro hV
  have hfull : (⋃ q : ℚ, (fun x : ℝ => x + q) ⁻¹' V) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy, q, rfl⟩ := hcover x
    apply Set.mem_iUnion.mpr
    refine ⟨-q, ?_⟩
    simpa using hy
  have hall : IsMeagre (⋃ q : ℚ, (fun x : ℝ => x + q) ⁻¹' V) :=
    isMeagre_iUnion (fun q => hV.preimage_of_isOpenMap (Homeomorph.addRight (q : ℝ)).continuous
      (Homeomorph.addRight (q : ℝ)).isOpenMap)
  rw [hfull] at hall
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hall

theorem rational_transversal_not_baire (V : Set ℝ)
    (hcover : ∀ x : ℝ, ∃ y ∈ V, ∃ q : ℚ, x = y + q)
    (hunique : ∀ x ∈ V, ∀ y ∈ V, ∀ q : ℚ, x - y = q → x = y) :
    ¬ BaireMeasurableSet V := by
  intro hV
  let A : Set (Multiplicative ℝ) := V
  have hA : BaireMeasurableSet A := hV
  have hne : ¬ IsMeagre A := rational_transversal_nonmeagre V hcover
  obtain ⟨W, ho, h0, hsub⟩ := pettis_open_identity_neighborhood hA hne
  apply rational_transversal_difference_not_nhds V hunique
  apply Filter.mem_of_superset (ho.mem_nhds h0)
  intro z hz
  obtain ⟨a, ha, b, hb, he⟩ := Set.mem_mul.mp (hsub hz)
  have haV : -Multiplicative.toAdd a ∈ V := ha
  have hbV : Multiplicative.toAdd b ∈ V := hb
  change Multiplicative.toAdd z ∈ V - V
  apply Set.mem_sub.mpr
  refine ⟨Multiplicative.toAdd b, hbV, -Multiplicative.toAdd a, haV, ?_⟩
  change Multiplicative.toAdd a + Multiplicative.toAdd b = Multiplicative.toAdd z at he
  linarith

theorem rational_transversal_nonnull (V : Set ℝ)
    (hcover : ∀ x : ℝ, ∃ y ∈ V, ∃ q : ℚ, x = y + q) : volume V ≠ 0 := by
  intro hV
  have hfull : (⋃ q : ℚ, (fun x : ℝ => x + q) ⁻¹' V) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy, q, rfl⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨-q, by simpa using hy⟩
  have hall : volume (⋃ q : ℚ, (fun x : ℝ => x + q) ⁻¹' V) = 0 := by
    apply measure_iUnion_null
    intro q
    rwa [measure_preimage_add_right]
  rw [hfull] at hall
  simp at hall

theorem rational_transversal_not_nullMeasurable (V : Set ℝ)
    (hcover : ∀ x : ℝ, ∃ y ∈ V, ∃ q : ℚ, x = y + q)
    (hunique : ∀ x ∈ V, ∀ y ∈ V, ∀ q : ℚ, x - y = q → x = y) :
    ¬ NullMeasurableSet V volume := by
  intro hV
  obtain ⟨B, hBV, hBm, hBeq⟩ := hV.exists_measurable_subset_ae_eq
  have hBpos : 0 < volume B := by
    rw [measure_congr hBeq]
    exact pos_iff_ne_zero.mpr (rational_transversal_nonnull V hcover)
  have hn := MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume B hBm hBpos
  apply rational_transversal_difference_not_nhds V hunique
  exact Filter.mem_of_superset hn (Set.sub_subset_sub hBV hBV)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The mechanism behind the negative direction is simple once a definable well-order of the reals is available. A
    projectively definable well-order lets one choose canonical representatives from equivalence classes that normally admit
    no definable selector. For example, applying the first-in-the-well-order choice to the cosets of $\QQ$ in $\R$ gives a
    projectively definable Vitali selector. Such a selector cannot be Lebesgue measurable and cannot have the Baire
    property. Thus the definable well-order of $\R$ in $L$ turns set-theoretic constructibility into explicit projective
    counterexamples to regularity.
-/
theorem leastRationalSelector_nonregular (r : ℝ → ℝ → Prop) [IsWellOrder ℝ r] :
    ¬ NullMeasurableSet (leastRationalSelector r) volume ∧
      ¬ BaireMeasurableSet (leastRationalSelector r) :=
  ⟨rational_transversal_not_nullMeasurable _ (leastRationalSelector_covers r)
      (fun _ hx _ hy q hq => leastRationalSelector_unique r hx hy q hq),
    rational_transversal_not_baire _ (leastRationalSelector_covers r)
      (fun _ hx _ hy q hq => leastRationalSelector_unique r hx hy q hq)⟩

/-- The construction uses the supplied projective well-order, whose existence
in L is a cited external input in the book. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The mechanism behind the negative direction is simple once a definable well-order of the reals is available. A
    projectively definable well-order lets one choose canonical representatives from equivalence classes that normally admit
    no definable selector. For example, applying the first-in-the-well-order choice to the cosets of $\QQ$ in $\R$ gives a
    projectively definable Vitali selector. Such a selector cannot be Lebesgue measurable and cannot have the Baire
    property. Thus the definable well-order of $\R$ in $L$ turns set-theoretic constructibility into explicit projective
    counterexamples to regularity.
-/
theorem projective_wellOrder_vitali (r : ℝ → ℝ → Prop) [IsWellOrder ℝ r]
    (hr : ProjectiveRealSet 2 {z | r (z 0) (z 1)}) :
    ProjectiveRealSet 1 {z | z 0 ∈ leastRationalSelector r} ∧
      ¬ NullMeasurableSet (leastRationalSelector r) volume ∧
      ¬ BaireMeasurableSet (leastRationalSelector r) :=
  ⟨leastRationalSelector_projective r hr, leastRationalSelector_nonregular r⟩

end PolishSpaceBook
