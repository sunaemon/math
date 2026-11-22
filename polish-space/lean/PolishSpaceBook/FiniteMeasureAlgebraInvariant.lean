module

public import PolishSpaceBook.AtomicMeasureDecomposition
public import PolishSpaceBook.MaharamStandardBorel

@[expose] public section

/-!
# Complete invariant for finite standard Borel measure algebras

Normalize the positive nonatomic factors and compare the zero factors directly
as one-element Boolean algebras. The atomic invariant is a weight-preserving
equivalence of the countable types of positive-mass points.
-/

noncomputable section
namespace PolishSpaceBook.FiniteMeasureAlgebraInvariant
open Set Filter Function MeasureTheory
open scoped ENNReal
open AtomicMeasureDecomposition

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Multiplication by a nonzero scalar leaves the quotient order unchanged. -/
def scaleEquiv (μ : Measure X) (c : ℝ≥0∞) (hc : c ≠ 0) :
    MeasureAlgebra μ ≃o MeasureAlgebra (c • μ) where
  toFun := Quotient.lift (fun s => MeasureAlgebra.mk (s : Set X) s.property)
    (fun _ _ h => Quotient.sound (Measure.ae_ennreal_smul_measure_iff hc |>.mpr h))
  invFun := Quotient.lift (fun s => MeasureAlgebra.mk (s : Set X) s.property)
    (fun _ _ h => Quotient.sound (Measure.ae_ennreal_smul_measure_iff hc |>.mp h))
  left_inv a := Quotient.inductionOn a fun _ => rfl
  right_inv a := Quotient.inductionOn a fun _ => rfl
  map_rel_iff' := by
    intro a b
    induction a using Quotient.inductionOn with
    | h s =>
      induction b using Quotient.inductionOn with
      | h t => exact Measure.ae_ennreal_smul_measure_iff hc

lemma scaleEquiv_mass (μ : Measure X) (c : ℝ≥0∞) (hc : c ≠ 0) (a : MeasureAlgebra μ) :
    MeasureAlgebra.mass (scaleEquiv μ c hc a) = c * MeasureAlgebra.mass a :=
  Quotient.inductionOn a fun _ => rfl

/-- Zero measures have one-element measure algebras, even on empty spaces. -/
lemma zero_mass_subsingleton (μ : Measure X) (hμ : μ univ = 0) :
    Subsingleton (MeasureAlgebra μ) := by
  have hbot (a : MeasureAlgebra μ) : a = ⊥ := by
    apply (MeasureAlgebra.mass_eq_zero_iff a).mp
    induction a using Quotient.inductionOn with
    | h s => exact le_antisymm ((measure_mono (subset_univ _)).trans_eq hμ) bot_le
  exact ⟨fun a b => (hbot a).trans (hbot b).symm⟩

/-- Equal finite total mass suffices for nonatomic standard Borel algebras.
The zero case does not require maps between the underlying spaces. -/
theorem nonatomic_isomorphism (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [StandardBorelSpace X] [StandardBorelSpace Y]
    [NullSingletonClass μ] [NullSingletonClass ν] (hm : μ univ = ν univ) :
    ∃ e : MeasureAlgebra μ ≃o MeasureAlgebra ν,
      ∀ a, MeasureAlgebra.mass (e a) = MeasureAlgebra.mass a := by
  by_cases hz : μ univ = 0
  · let :=  zero_mass_subsingleton μ hz
    let :=  zero_mass_subsingleton ν (hm ▸ hz)
    let e : MeasureAlgebra μ ≃o MeasureAlgebra ν :=
      { toFun := fun _ => ⊥
        invFun := fun _ => ⊥
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        map_rel_iff' := by intro a b; simp [Subsingleton.elim a b] }
    refine ⟨e, fun a => ?_⟩
    rw [Subsingleton.elim (e a) ⊥, Subsingleton.elim a ⊥]
    exact (measure_empty : ν ∅ = 0).trans (measure_empty : μ ∅ = 0).symm
  · let c := (μ univ)⁻¹
    have hc : c ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top μ univ)
    have : IsProbabilityMeasure (c • μ) := ⟨by
      simp only [Measure.smul_apply, smul_eq_mul, c]
      exact ENNReal.inv_mul_cancel hz (measure_ne_top μ univ)⟩
    have : IsProbabilityMeasure (c • ν) := ⟨by
      simp only [Measure.smul_apply, smul_eq_mul, c, ← hm]
      exact ENNReal.inv_mul_cancel hz (measure_ne_top μ univ)⟩
    have : NullSingletonClass (c • μ) := ⟨fun x => by simp⟩
    have : NullSingletonClass (c • ν) := ⟨fun x => by simp⟩
    obtain ⟨f, hf⟩ := MaharamStandardBorel.measureAlgebra_isomorphism (c • μ) (c • ν)
    let e := (scaleEquiv μ c hc).trans (f.trans (scaleEquiv ν c hc).symm)
    refine ⟨e, fun a => ?_⟩
    have h := hf (scaleEquiv μ c hc a)
    have he : scaleEquiv ν c hc (e a) = f (scaleEquiv μ c hc a) := by simp [e]
    rw [← he, scaleEquiv_mass, scaleEquiv_mass] at h
    exact (ENNReal.mul_right_inj hc (ENNReal.inv_ne_top.mpr hz)).mp h

/-- The Boolean atom represented by a positive-mass point. -/
def pointAtom (μ : Measure X) [MeasurableSingletonClass X] (x : atomicPoints μ) :
    {a : MeasureAlgebra μ // IsAtom a} :=
  ⟨MeasureAlgebra.mk {x.val} (measurableSet_singleton x.val), singleton_isAtom μ x.property⟩

lemma pointAtom_injective (μ : Measure X) [MeasurableSingletonClass X] :
    Injective (pointAtom μ) := by
  intro x y h
  have he := (MeasureAlgebra.mk_eq_mk _ _).mp (congrArg Subtype.val h)
  have hx : x.val ∈ ({y.val} : Set X) := by
    by_contra hn
    have hzero : μ {x.val} = 0 := by
      apply le_antisymm _ bot_le
      apply (measure_mono (show {x.val} ⊆ {z | ¬ ((z ∈ ({x.val} : Set X)) = (z ∈ ({y.val} : Set X)))} from ?_)).trans_eq
        (ae_iff.mp he)
      intro z hz
      rcases mem_singleton_iff.mp hz with rfl
      simpa using hn
    exact x.property.ne' hzero
  exact Subtype.ext (mem_singleton_iff.mp hx)

/-- Atoms of the quotient correspond exactly to positive-mass points. -/
def pointAtomEquiv (μ : Measure X) [StandardBorelSpace X] :
    atomicPoints μ ≃ {a : MeasureAlgebra μ // IsAtom a} :=
  Equiv.ofBijective (pointAtom μ) ⟨pointAtom_injective μ, by
    intro a
    obtain ⟨x, hx, he⟩ := atom_is_singleton μ a.property
    exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩⟩

/-- Every order isomorphism induces an equivalence on positive-mass points. -/
def atomEquiv (μ : Measure X) (ν : Measure Y) [StandardBorelSpace X] [StandardBorelSpace Y]
    (e : MeasureAlgebra μ ≃o MeasureAlgebra ν) : atomicPoints μ ≃ atomicPoints ν :=
  (pointAtomEquiv μ).trans ((e.toEquiv.subtypeEquiv (fun a => (e.isAtom_iff a).symm)).trans
    (pointAtomEquiv ν).symm)

lemma atomEquiv_mass (μ : Measure X) (ν : Measure Y)
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (e : MeasureAlgebra μ ≃o MeasureAlgebra ν)
    (he : ∀ a, MeasureAlgebra.mass (e a) = MeasureAlgebra.mass a) (x : atomicPoints μ) :
    ν {(atomEquiv μ ν e x).val} = μ {x.val} := by
  have h : (pointAtomEquiv ν) (atomEquiv μ ν e x) =
      e.toEquiv.subtypeEquiv (fun a => (e.isAtom_iff a).symm) (pointAtomEquiv μ x) := by
    simp [atomEquiv]
  have hm := congrArg (fun a : {a : MeasureAlgebra ν // IsAtom a} => MeasureAlgebra.mass a.val) h
  exact hm.trans (he _)

/-- Transport arbitrary, possibly infinite, sets of atoms by a weighted equivalence. -/
lemma atomicWeight_image (μ : Measure X) (ν : Measure Y)
    (e : atomicPoints μ ≃ atomicPoints ν)
    (he : ∀ x, ν {(e x).val} = μ {x.val}) (S : Set (atomicPoints μ)) :
    atomicWeight ν (e '' S) = atomicWeight μ S := by
  unfold atomicWeight
  rw [← (e.image S).tsum_eq]
  exact tsum_congr (fun x => he x.val)

/-- Total nonatomic mass, including zero. -/
def nonatomicMass (μ : Measure X) : ℝ≥0∞ :=
  subspaceMeasure μ (atomicPoints μ)ᶜ univ

lemma total_mass (μ : Measure X) [IsFiniteMeasure μ] [MeasurableSingletonClass X] :
    μ univ = nonatomicMass μ + atomicWeight μ univ := by
  have h := decomposition_mass μ ⊤
  rw [(decomposition μ).map_top] at h
  exact h

lemma atomicWeight_univ_ne_top (μ : Measure X) [IsFiniteMeasure μ] [MeasurableSingletonClass X] :
    atomicWeight μ univ ≠ ∞ := by
  apply ne_top_of_le_ne_top (measure_ne_top μ univ)
  rw [total_mass μ]
  exact le_add_left le_rfl

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Conversely, a Boolean algebra isomorphism preserves atoms. By the atomic decomposition, the atoms
    are exactly the classes of the singletons at positive-mass points. Distinct such points give distinct
    classes, so a measure-preserving isomorphism induces a bijection $f:A\to B$ preserving their masses.
    It therefore preserves the sum of all atomic masses. It also preserves the top element and hence
    the total mass. In the decompositions
    $$\mu(X)=\mu_{\mathrm{na}}(\SetDifference{X}{A})+\sum_{x\in A}\mu(\{x\}),\qquad
    \nu(Y)=\nu_{\mathrm{na}}(\SetDifference{Y}{B})+\sum_{y\in B}\nu(\{y\}),$$
    all terms are finite. Cancelling the equal atomic masses proves equality of the non-atomic masses.
-/
/-- An isomorphism preserves the full invariant: nonatomic mass and every atom weight. -/
theorem invariant_of_isomorphism (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [StandardBorelSpace X] [StandardBorelSpace Y]
    (e : MeasureAlgebra μ ≃o MeasureAlgebra ν)
    (he : ∀ a, MeasureAlgebra.mass (e a) = MeasureAlgebra.mass a) :
    nonatomicMass μ = nonatomicMass ν ∧
      ∃ f : atomicPoints μ ≃ atomicPoints ν, ∀ x, ν {(f x).val} = μ {x.val} := by
  let f := atomEquiv μ ν e
  have hf := atomEquiv_mass μ ν e he
  refine ⟨?_, f, hf⟩
  have hw : atomicWeight ν univ = atomicWeight μ univ := by
    simpa using atomicWeight_image μ ν f hf univ
  have ht : ν univ = μ univ := by
    have h := he ⊤
    rw [e.map_top] at h
    exact h
  rw [total_mass μ, total_mass ν, hw] at ht
  exact (ENNReal.add_left_inj (atomicWeight_univ_ne_top μ)).mp ht.symm

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Suppose first that the non-atomic masses agree, with common value $m$, and that $f$ is such a bijection.
    If $m>0$, normalize the two non-atomic measures by $m^{-1}$ and apply Maharam's theorem to obtain an
    isomorphism of their probability algebras. Scaling back by $m$ preserves the same null ideals and
    makes this isomorphism preserve the original measures. If $m=0$, each non-atomic measure algebra
    has just one element, so the unique map is a measure-preserving Boolean algebra isomorphism.
    On the atomic factors, direct image under $f$ is an isomorphism $\PowerSet{A}\to\PowerSet{B}$,
    and for every $S\IncludedIn A$ it preserves weight because
    $$\sum_{y\in f(S)}\nu(\{y\})=\sum_{x\in S}\mu(\{x\}).$$
    Combining these two isomorphisms with the atomic decompositions gives the required isomorphism.
-/
/-- Assemble equal nonatomic masses and a weight-preserving equivalence of atoms. -/
theorem isomorphism_of_invariant (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [StandardBorelSpace X] [StandardBorelSpace Y]
    (hm : nonatomicMass μ = nonatomicMass ν)
    (f : atomicPoints μ ≃ atomicPoints ν)
    (hf : ∀ x, ν {(f x).val} = μ {x.val}) :
    ∃ e : MeasureAlgebra μ ≃o MeasureAlgebra ν,
      ∀ a, MeasureAlgebra.mass (e a) = MeasureAlgebra.mass a := by
  have : StandardBorelSpace ↥((atomicPoints μ)ᶜ) := (atomicPoints_measurable μ).compl.standardBorel
  have : StandardBorelSpace ↥((atomicPoints ν)ᶜ) := (atomicPoints_measurable ν).compl.standardBorel
  obtain ⟨dμ, _, hnμ, _, hdμ⟩ := standardBorel_decomposition μ
  obtain ⟨dν, _, hnν, _, hdν⟩ := standardBorel_decomposition ν
  have : NullSingletonClass (subspaceMeasure μ (atomicPoints μ)ᶜ) := hnμ
  have : NullSingletonClass (subspaceMeasure ν (atomicPoints ν)ᶜ) := hnν
  have : IsFiniteMeasure (subspaceMeasure μ (atomicPoints μ)ᶜ) :=
    inferInstanceAs (IsFiniteMeasure (μ.comap Subtype.val))
  have : IsFiniteMeasure (subspaceMeasure ν (atomicPoints ν)ᶜ) :=
    inferInstanceAs (IsFiniteMeasure (ν.comap Subtype.val))
  obtain ⟨g, hg⟩ := nonatomic_isomorphism
    (subspaceMeasure μ (atomicPoints μ)ᶜ) (subspaceMeasure ν (atomicPoints ν)ᶜ) hm
  let p : (MeasureAlgebra (subspaceMeasure μ (atomicPoints μ)ᶜ) × Set (atomicPoints μ)) ≃o
      (MeasureAlgebra (subspaceMeasure ν (atomicPoints ν)ᶜ) × Set (atomicPoints ν)) :=
    { toEquiv := g.toEquiv.prodCongr f.toOrderIsoSet.toEquiv
      map_rel_iff' := by
        intro a b
        exact and_congr g.map_rel_iff f.toOrderIsoSet.map_rel_iff }
  let e := dμ.trans (p.trans dν.symm)
  refine ⟨e, fun a => ?_⟩
  have hda : dν (e a) = p (dμ a) := by simp [e]
  rw [hdν, hda, hdμ]
  change MeasureAlgebra.mass (g (dμ a).1) + atomicWeight ν (f '' (dμ a).2) = _
  rw [hg, atomicWeight_image μ ν f hf]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: proposition
  title: Complete invariant for finite measure algebras
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Thus the \termforward{complete invariant} of a standard probability algebra is the total mass of the non-atomic
    part together with the multiset of atom masses. \termuseas{Maharam theorem}{Maharam's theorem} is the special case
    where the non-atomic mass is $1$ and the atom list is empty.
-/
/-- The complete invariant for finite standard Borel measure algebras. The
atomic data are a weighted equivalence of types, so countably infinitely many
atoms and their multiplicities are retained. -/
theorem isomorphism_iff (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [StandardBorelSpace X] [StandardBorelSpace Y] :
    (∃ e : MeasureAlgebra μ ≃o MeasureAlgebra ν,
      ∀ a, MeasureAlgebra.mass (e a) = MeasureAlgebra.mass a) ↔
    nonatomicMass μ = nonatomicMass ν ∧
      ∃ f : atomicPoints μ ≃ atomicPoints ν, ∀ x, ν {(f x).val} = μ {x.val} := by
  constructor
  · rintro ⟨e, he⟩
    exact invariant_of_isomorphism μ ν e he
  · rintro ⟨hm, f, hf⟩
    exact isomorphism_of_invariant μ ν hm f hf

end PolishSpaceBook.FiniteMeasureAlgebraInvariant
