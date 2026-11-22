module

public import PolishSpaceBook.DynkinPiLambda
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.ClopenBox

@[expose] public section

/-!
# Extending a probability content on clopen sets

Compactness turns a disjoint countable clopen cover of a clopen set into a
finite union. This supplies the premeasure hypothesis for Caratheodory's
extension in the book's disintegration construction. The same construction
works for a measurably parametrized family of contents.
-/

namespace PolishSpaceBook.ClopenMeasureExtension

noncomputable section
open Set Topology TopologicalSpace MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal Function

variable {X : Type*} [TopologicalSpace X]

lemma clopens_isSetRing : IsSetRing {A : Set X | IsClopen A} where
  empty_mem := isClopen_empty
  union_mem := fun _ _ hA hB => hA.union hB
  sdiff_mem := fun _ _ hA hB => hA.diff hB

lemma clopens_isPiSystem : IsPiSystem {A : Set X | IsClopen A} :=
  fun _ hA _ hB _ => hA.inter hB

/-- Extend clopen values by zero off the algebra, solely to use the canonical
`AddContent` interface. The off-algebra values have no mathematical role. -/
def contentFromClopens (v : Clopens X → ℝ≥0∞) (h0 : v ⊥ = 0)
    (hadd : ∀ C D : Clopens X, Disjoint (C : Set X) D → v (C ⊔ D) = v C + v D) :
    AddContent ℝ≥0∞ {A : Set X | IsClopen A} := by
  classical
  let a : Set X → ℝ≥0∞ := fun A => if h : IsClopen A then v ⟨A, h⟩ else 0
  apply IsSetRing.addContent_of_union a clopens_isSetRing
  · dsimp [a]
    rw [dite_eq_left isClopen_empty]
    exact h0
  · intro C D hC hD hdis
    change IsClopen C at hC
    change IsClopen D at hD
    dsimp [a]
    rw [dite_eq_left (hC.union hD), dite_eq_left hC, dite_eq_left hD]
    exact hadd ⟨C, hC⟩ ⟨D, hD⟩ hdis

lemma contentFromClopens_apply (v : Clopens X → ℝ≥0∞) (h0 : v ⊥ = 0)
    (hadd : ∀ C D : Clopens X, Disjoint (C : Set X) D → v (C ⊔ D) = v C + v D)
    (C : Clopens X) : contentFromClopens v h0 hadd C = v C := by
  classical
  change (if h : IsClopen (C : Set X) then v ⟨C, h⟩ else 0) = v C
  rw [dite_eq_left C.isClopen]
  rfl

variable [CompactSpace X]

/-- In a disjoint countable clopen family with clopen union, all but finitely
many members are empty: a finite subcover leaves no room for another member. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Fix $y$. If pairwise disjoint clopens $C_n$ have a clopen union $C$, compactness of $C$ gives a finite
    $J\IncludedIn\omega$ such that $C=\bigcup_{n\in J}C_n$. Disjointness forces $C_n=\emptyset$ for $n\notin J$.
-/
theorem disjoint_clopen_cover_finite_support (U : ℕ → Set X)
    (hU : ∀ n, IsClopen (U n)) (hUnion : IsClopen (⋃ n, U n))
    (hdis : Pairwise (Disjoint on U)) :
    ∃ J : Finset ℕ, (⋃ n, U n) = ⋃ n ∈ J, U n ∧ ∀ n ∉ J, U n = ∅ := by
  obtain ⟨J, hJ⟩ := hUnion.isClosed.isCompact.elim_finite_subcover U
    (fun n => (hU n).isOpen) Subset.rfl
  refine ⟨J, subset_antisymm hJ (iUnion₂_subset (fun n _ => subset_iUnion U n)), ?_⟩
  intro n hn
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hJ (mem_iUnion.mpr ⟨n, hx⟩))
  exact Set.disjoint_left.mp (hdis (by intro h; exact hn (h ▸ hj))) hx hxj

/-- Finite additivity becomes countable additivity on the clopen algebra. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Finite additivity therefore gives
    $$g_C(y)=\sum_{n\in J}g_{C_n}(y)=\sum_{n\in\omega}g_{C_n}(y).$$
-/
theorem content_iUnion (a : AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (U : ℕ → Set X) (hU : ∀ n, IsClopen (U n)) (hUnion : IsClopen (⋃ n, U n))
    (hdis : Pairwise (Disjoint on U)) :
    a (⋃ n, U n) = ∑' n, a (U n) := by
  classical
  obtain ⟨J, hJ, hzero⟩ := disjoint_clopen_cover_finite_support U hU hUnion hdis
  calc
    a (⋃ n, U n) = a (⋃ n ∈ J, U n) := congrArg a hJ
    _ = ∑ n ∈ J, a (U n) := addContent_biUnion (fun n _ => hU n)
      (fun _ _ _ _ hne => hdis hne) (by rw [← hJ]; exact hUnion)
    _ = ∑' n, a (U n) := (tsum_eq_sum (fun n hn => by simp [hzero n hn])).symm

lemma content_sigmaSubadditive (a : AddContent ℝ≥0∞ {A : Set X | IsClopen A}) :
    a.IsSigmaSubadditive :=
  isSigmaSubadditive_of_addContent_iUnion_eq_tsum clopens_isSetRing (content_iUnion a)

variable [T2Space X] [TotallyDisconnectedSpace X] [SecondCountableTopology X]
  [mX : MeasurableSpace X] [BorelSpace X]

lemma measurable_eq_generateFrom_clopens :
    mX = MeasurableSpace.generateFrom {A : Set X | IsClopen A} := by
  rw [show mX = borel X from BorelSpace.measurable_eq]
  exact isTopologicalBasis_isClopen.borel_eq_generateFrom

/-- The Caratheodory extension of a content on clopen sets. -/
def extension (a : AddContent ℝ≥0∞ {A : Set X | IsClopen A}) : Measure X :=
  a.measure clopens_isSetRing.isSetSemiring measurable_eq_generateFrom_clopens.le
    (content_sigmaSubadditive a)

lemma extension_clopen (a : AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    {C : Set X} (hC : IsClopen C) : extension a C = a C :=
  a.measure_eq clopens_isSetRing.isSetSemiring measurable_eq_generateFrom_clopens
    (content_sigmaSubadditive a) hC

lemma extension_probability (a : AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : a univ = 1) : IsProbabilityMeasure (extension a) :=
  ⟨by rw [extension_clopen a isClopen_univ, ha]⟩

/-- Agreement on the clopen algebra determines a probability measure uniquely. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Thus $C\mapsto g_C(y)$ is a premeasure. The clopens form an algebra generating the Borel sets, so
    Carathéodory extension gives a probability measure $\lambda_y$. Uniqueness of finite measures on a generating
    algebra shows that this extension is unique.
-/
theorem extension_unique (a : AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : a univ = 1) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ C, IsClopen C → μ C = a C) : μ = extension a := by
  let := extension_probability a ha
  apply ext_of_generate_finite {C : Set X | IsClopen C}
    measurable_eq_generateFrom_clopens clopens_isPiSystem
  · intro C hC
    rw [extension_clopen a hC, hμ C hC]
  · simp

variable {Y : Type*} [MeasurableSpace Y]

/-- The Dynkin-system argument: measurable evaluations on clopens extend to
all Borel sets by complements and disjoint countable unions. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    To check measurability of all Borel evaluations, let $\mathcal D$ consist of the Borel sets $B$ for which
    $y\mapsto\lambda_y(B)$ is Borel. It contains $\mathcal C$ and is a Dynkin system: complements and disjoint
    countable unions are handled by
    $$\lambda_y(B^c)=1-\lambda_y(B),\qquad
    \lambda_y\!\left(\bigcup_n B_n\right)=\sum_n\lambda_y(B_n).
    $$
    Since $\mathcal C$ is closed under intersections, the $\pi$--$\lambda$ theorem gives
    $\mathcal D=\mathcal B(\CantorSpace)$. Hence the family is a Markov kernel.
-/
theorem measurable_evaluation_of_clopens (p : Y → Measure X)
    (hp : ∀ y, IsProbabilityMeasure (p y))
    (hcl : ∀ C : Set X, IsClopen C → Measurable (fun y => p y C)) :
    ∀ B : Set X, MeasurableSet B → Measurable (fun y => p y B) := by
  apply DynkinPiLambda.induction_on_inter
    (C := fun B => Measurable (fun y => p y B))
    measurable_eq_generateFrom_clopens clopens_isPiSystem
  · simp
  · exact hcl
  · intro B hB ih
    have heq : (fun y => p y Bᶜ) = fun y => 1 - p y B := by
      funext y
      let := hp y
      rw [measure_compl hB (measure_ne_top (p y) B), measure_univ]
    rw [heq]
    exact measurable_const.sub ih
  · intro B hdis hB ih
    simp_rw [measure_iUnion hdis hB]
    exact Measurable.tsum ih

/-- Clopen evaluations already test measurability of probability-valued maps. -/
theorem measurable_probability_iff_clopens (p : Y → ProbabilityMeasure X) :
    Measurable p ↔ ∀ C : Set X, IsClopen C → Measurable (fun y => (p y : Measure X) C) := by
  constructor
  · intro hp C hC
    exact (Measure.measurable_coe hC.isOpen.measurableSet).comp (measurable_subtype_coe.comp hp)
  · intro hcl
    apply Measurable.subtype_mk
    exact Measure.measurable_of_measurable_coe _
      (measurable_evaluation_of_clopens (fun y => (p y : Measure X)) (fun y => (p y).property) hcl)

/-- The family obtained by extending the clopen probabilities pointwise. -/
def probabilityFamily (a : Y → AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : ∀ y, a y univ = 1) : Y → ProbabilityMeasure X :=
  fun y => ⟨extension (a y), extension_probability (a y) (ha y)⟩

lemma probabilityFamily_measurable
    (a : Y → AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : ∀ y, a y univ = 1)
    (hcl : ∀ C : Set X, IsClopen C → Measurable (fun y => a y C)) :
    Measurable (probabilityFamily a ha) := by
  apply (measurable_probability_iff_clopens _).mpr
  intro C hC
  change Measurable (fun y => extension (a y) C)
  simpa only [extension_clopen _ hC] using hcl C hC

/-- The same family bundled as the probability kernel used in disintegration. -/
def kernel (a : Y → AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : ∀ y, a y univ = 1)
    (hcl : ∀ C : Set X, IsClopen C → Measurable (fun y => a y C)) : Kernel Y X where
  toFun y := extension (a y)
  measurable' := Measure.measurable_of_measurable_coe _
    (measurable_evaluation_of_clopens _ (fun y => extension_probability (a y) (ha y))
      (fun C hC => by simpa only [extension_clopen _ hC] using hcl C hC))

instance kernel_isMarkov (a : Y → AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : ∀ y, a y univ = 1)
    (hcl : ∀ C : Set X, IsClopen C → Measurable (fun y => a y C)) :
    IsMarkovKernel (kernel a ha hcl) :=
  ⟨fun y => extension_probability (a y) (ha y)⟩

lemma kernel_clopen (a : Y → AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : ∀ y, a y univ = 1)
    (hcl : ∀ C : Set X, IsClopen C → Measurable (fun y => a y C))
    {C : Set X} (hC : IsClopen C) (y : Y) : kernel a ha hcl y C = a y C :=
  extension_clopen (a y) hC

/-- The coordinates recording the values on all clopen sets. -/
def clopenEvaluations (μ : ProbabilityMeasure X) : Clopens X → ℝ≥0∞ :=
  fun C => (μ : Measure X) C

lemma clopenEvaluations_injective : Function.Injective (clopenEvaluations (X := X)) := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite {C : Set X | IsClopen C}
    measurable_eq_generateFrom_clopens clopens_isPiSystem
  · intro C hC
    exact congrFun h ⟨C, hC⟩
  · simp

omit [T2Space X] [TotallyDisconnectedSpace X] [SecondCountableTopology X] in
lemma clopenEvaluations_continuous : Continuous (clopenEvaluations (X := X)) := by
  apply continuous_pi
  intro C
  let f : ContinuousMap X ℝ≥0 := ⟨(C : Set X).indicator (fun _ => 1),
    continuous_indicator (by simp [C.isClopen]) continuousOn_const⟩
  have hc := ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact f)
  have heq (μ : ProbabilityMeasure X) :
      (∫⁻ x, (BoundedContinuousFunction.mkOfCompact f x : ℝ≥0∞) ∂(μ : Measure X)) =
        (μ : Measure X) C := by
    have hi : (fun x => (BoundedContinuousFunction.mkOfCompact f x : ℝ≥0∞)) =
        (C : Set X).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ C <;> simp [f, hx]
    rw [hi, lintegral_indicator C.isClopen.isOpen.measurableSet]
    simp
  simpa only [heq, clopenEvaluations] using hc

/-- Compactness and uniqueness turn the continuous evaluation map into a
closed embedding into a countable product of Hausdorff spaces. -/
theorem clopenEvaluations_isClosedEmbedding :
    IsClosedEmbedding (clopenEvaluations (X := X)) :=
  clopenEvaluations_continuous.isClosedEmbedding clopenEvaluations_injective

/-- Clopen evaluations generate the Borel structure of the weak topology,
not merely the abstract measurable structure on measures. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    It remains to verify Borel measurability into the weak topology. The algebra $\mathcal C$ is countable:
    every clopen is a finite union of basic cylinders, by compactness. Consider
    $$E:\ProbMeasures{\CantorSpace}\longrightarrow[0,1]^{\mathcal C},\qquad
    E(\lambda)=(C\mapsto\lambda(C)).
    $$
    For each clopen $C$, its indicator is continuous, so $\lambda\mapsto\lambda(C)=\int1_C\,d\lambda$ is
    continuous in the weak topology. Thus $E$ is continuous; uniqueness on the generating algebra makes it injective.
    By §{sec:prob-measure-space}, $\ProbMeasures{\CantorSpace}$ is compact. The target is Hausdorff, so $E$ is a
    homeomorphism onto its closed image. The Borel structure of the countable product $[0,1]^{\mathcal C}$ is
    generated by its coordinates. Consequently, the clopen evaluations generate the Borel structure of
    $\ProbMeasures{\CantorSpace}$. Since their compositions with $y\mapsto\lambda_y$ are exactly the Borel functions
    $g_C$, this map is Borel.
-/
theorem borel_measurable_probability_iff_clopens (p : Y → ProbabilityMeasure X) :
    @Measurable Y (ProbabilityMeasure X) ‹MeasurableSpace Y› (borel (ProbabilityMeasure X)) p ↔
      ∀ C : Set X, IsClopen C → Measurable (fun y => (p y : Measure X) C) := by
  let : Countable (Clopens X) := Clopens.countable_iff_secondCountable.mpr inferInstance
  let : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  let : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  have he := (clopenEvaluations_isClosedEmbedding (X := X)).measurableEmbedding
  constructor
  · intro hp C hC
    have hc := (clopenEvaluations_continuous (X := X)).measurable.comp hp
    exact (measurable_pi_apply ⟨C, hC⟩).comp hc
  · intro hcl
    apply he.measurable_comp_iff.mp
    exact Measurable.of_eval (fun C => hcl C C.isClopen)

lemma probabilityFamily_borel_measurable
    (a : Y → AddContent ℝ≥0∞ {A : Set X | IsClopen A})
    (ha : ∀ y, a y univ = 1)
    (hcl : ∀ C : Set X, IsClopen C → Measurable (fun y => a y C)) :
    @Measurable Y (ProbabilityMeasure X) ‹MeasurableSpace Y› (borel (ProbabilityMeasure X))
      (probabilityFamily a ha) := by
  apply (borel_measurable_probability_iff_clopens _).mpr
  intro C hC
  change Measurable (fun y => extension (a y) C)
  simpa only [extension_clopen _ hC] using hcl C hC

/-- The clopen probability extension lemma in its measurable-family form. -/
theorem existsUnique_probabilityFamily
    (v : Y → Clopens X → ℝ≥0∞) (h0 : ∀ y, v y ⊥ = 0) (h1 : ∀ y, v y ⊤ = 1)
    (hadd : ∀ y (C D : Clopens X), Disjoint (C : Set X) D →
      v y (C ⊔ D) = v y C + v y D)
    (hv : ∀ C, Measurable (fun y => v y C)) :
    ∃! p : Y → ProbabilityMeasure X,
      @Measurable Y (ProbabilityMeasure X) ‹MeasurableSpace Y› (borel (ProbabilityMeasure X)) p ∧
      ∀ y (C : Clopens X), (p y : Measure X) C = v y C := by
  let a y := contentFromClopens (v y) (h0 y) (hadd y)
  have ha y : a y univ = 1 := by
    rw [show univ = ((⊤ : Clopens X) : Set X) from rfl,
      contentFromClopens_apply, h1]
  have hcl (C : Set X) (hC : IsClopen C) : Measurable (fun y => a y C) := by
    have heq : (fun y => a y C) = fun y => v y ⟨C, hC⟩ := by
      funext y
      exact contentFromClopens_apply _ _ _ ⟨C, hC⟩
    rw [heq]
    exact hv ⟨C, hC⟩
  refine ⟨probabilityFamily a ha, ⟨probabilityFamily_borel_measurable a ha hcl, ?_⟩, ?_⟩
  · intro y C
    change extension (a y) C = v y C
    rw [extension_clopen _ C.isClopen]
    exact contentFromClopens_apply _ _ _ C
  · intro q hq
    funext y
    apply clopenEvaluations_injective
    funext C
    change (q y : Measure X) C = extension (a y) C
    rw [hq.2 y C, extension_clopen _ C.isClopen, contentFromClopens_apply]

/-- In particular the construction applies to the ambient Cantor space used
in the book, without any further presentation hypotheses. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: lemma
  title: Clopen probability extension
-/
theorem cantor_probabilityFamily
    (v : Y → Clopens (ℕ → Bool) → ℝ≥0∞)
    (h0 : ∀ y, v y ⊥ = 0) (h1 : ∀ y, v y ⊤ = 1)
    (hadd : ∀ y (C D : Clopens (ℕ → Bool)), Disjoint (C : Set (ℕ → Bool)) D →
      v y (C ⊔ D) = v y C + v y D)
    (hv : ∀ C, Measurable (fun y => v y C)) :
    ∃! p : Y → ProbabilityMeasure (ℕ → Bool),
      @Measurable Y (ProbabilityMeasure (ℕ → Bool)) ‹MeasurableSpace Y›
        (borel (ProbabilityMeasure (ℕ → Bool))) p ∧
      ∀ y (C : Clopens (ℕ → Bool)), (p y : Measure (ℕ → Bool)) C = v y C :=
  existsUnique_probabilityFamily v h0 h1 hadd hv

end
end PolishSpaceBook.ClopenMeasureExtension
