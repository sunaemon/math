module

public import PolishSpaceBook.LambdaBorelTruth
public import PolishSpaceBook.LambdaAnalyticCatalog
public import PolishSpaceBook.LambdaHKLFusion
public import Mathlib.Topology.MetricSpace.PiNat

@[expose] public section

/-!
# HKL embedding for a fixed relative Baire presentation

Borel completeness supplies a code on cylinder rectangles. Its countable
truth tests close the backward implication of the relative HKL fusion.
The hypotheses are relative analytic presentations of E and its complement,
not a supplied kernel, splitting lemma, fusion map, or truth assumption.
A common oracle is also constructed from Borel measurability. Transport
from arbitrary Polish spaces is supplied by `HKLPolishTransport`; Silver's
coanalytic truth remains a separate obligation.
-/
namespace PolishSpaceBook.LambdaTree
open Set Function MeasureTheory
attribute [local instance] PiNat.metricSpaceNatNat

/-- Bridge the canonical Borel measurable sets to the book's code theorem. -/
theorem BorelCode.exists_decode_eq_of_measurable {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (U : ℕ → Set X)
    (hU : TopologicalSpace.IsTopologicalBasis (range U)) {A : Set X} (hA : MeasurableSet A) :
    ∃ c : BorelCode, c.decode U = A := by
  apply BorelCode.exists_decode_eq U hU
  induction A, hA using MeasurableSet.induction_on_open with
  | isOpen A hA =>
    apply borelSigma_mono (le_refl 1)
      (lt_trans Ordinal.one_lt_omega0 Ordinal.omega0_lt_omega_one).le
    rwa [borelSigma_one]
  | compl A hA ih => exact borelSigma_omega1_compl ih
  | iUnion f hd hf ih => exact borelSigma_omega1_iUnion ih

def pairCylinderLeft (n : ℕ) : Set FusionReal :=
  cyl (Denumerable.ofNat (List ℕ × List ℕ) n).1

def pairCylinderRight (n : ℕ) : Set FusionReal :=
  cyl (Denumerable.ofNat (List ℕ × List ℕ) n).2

theorem pairCylinder_basis : TopologicalSpace.IsTopologicalBasis
    (range (fun n => pairCylinderLeft n ×ˢ pairCylinderRight n)) := by
  have heq : range (fun n => pairCylinderLeft n ×ˢ pairCylinderRight n) =
      image2 (· ×ˢ ·) {A : Set FusionReal | ∃ s : List ℕ, A = cyl s}
        {B : Set FusionReal | ∃ t : List ℕ, B = cyl t} := by
    ext W
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨A, ⟨s, rfl⟩, B, ⟨t, rfl⟩, rfl⟩
      refine ⟨Encodable.encode (s, t), ?_⟩
      simp [pairCylinderLeft, pairCylinderRight, Denumerable.ofNat_encode]
  rw [heq]
  exact (isTopologicalBasis_cyl (A := ℕ)).prod (isTopologicalBasis_cyl (A := ℕ))

theorem pairCylinderLeft_projected (ε : ℕ → ℕ) (n : ℕ) :
    Projected ε (pairCylinderLeft n) :=
  projected_cyl ε _

theorem pairCylinderRight_projected (ε : ℕ → ℕ) (n : ℕ) :
    Projected ε (pairCylinderRight n) :=
  projected_cyl ε _

/-- The actual relative analytic presentations give a Borel code of E on
the fixed cylinder-rectangle basis. -/
theorem parameter_relation_borel_code (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y)) :
    ∃ c : BorelCode,
      c.decode (fun n => pairCylinderLeft n ×ˢ pairCylinderRight n) = {p | E.r p.1 p.2} := by
  have ha : AnalyticSet {p : FusionReal × FusionReal | E.r p.1 p.2} :=
    ProjectedPairs.analyticSet (P := {p : FusionReal × FusionReal | E.r p.1 p.2}) hE
  have hn : AnalyticSet {p : FusionReal × FusionReal | ¬ E.r p.1 p.2} :=
    ProjectedPairs.analyticSet (P := {p : FusionReal × FusionReal | ¬ E.r p.1 p.2}) hneE
  exact BorelCode.exists_decode_eq_of_measurable _ pairCylinder_basis (ha.measurableSet_of_compl hn)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    and the HKL generic-pair lemma gives $\pi(a)\mathrel{\not E}\pi(b)$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Thus the descending rectangle sequence is generic,
-/
/-- The full two-way HKL embedding in the fixed relative Baire presentation.
The backward implication uses the actual Borel truth tests and common-right
contradiction; all construction and fusion remain in the original oracle. -/
theorem parameter_hkl_embedding (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hns : ¬ Smooth E.r) :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      ∀ a b, E0 a b ↔ E.r (π a) (π b) := by
  classical
  obtain ⟨c, hc⟩ := parameter_relation_borel_code ε E hE hneE
  let J := parameterBorelTests ε E pairCylinderLeft pairCylinderRight c
  have hJc : J.Countable := parameterBorelTests_countable _ _ c
  have hJdl := parameterBorelTests_dense_lower hE pairCylinderLeft pairCylinderRight c
  obtain ⟨S, π, hcont, hinj, hmem, hforward, hmeet⟩ :=
    parameter_hkl_forward_embedding ε E hE hneE hns J hJc
      (fun D hD => (hJdl D hD).1) (fun D hD => (hJdl D hD).2)
  refine ⟨π, hcont, hinj, fun a b => ⟨hforward a b, ?_⟩⟩
  intro hab
  by_contra hn
  have hg : ParameterRectangleGeneric ε E J (π a) (π b) := by
    intro D hD
    obtain ⟨n, _, hnD⟩ := hmeet a b hn D hD 0
    exact ⟨S.branchRectangle a b n, hnD, hmem a n, hmem b n⟩
  exact parameter_hkl_generic_inequivalent_of_code hE hneE pairCylinderLeft pairCylinderRight
    (pairCylinderLeft_projected ε) (pairCylinderRight_projected ε) c hc
    (S.branchRectangle a b 0) (S.node_subset 0 (binaryBranchPrefix a 0))
    (hmem a 0) (hmem b 0) hg hab

/-- Choose one oracle for a Borel relation and its complement. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For the rest of the argument $E$ is Borel. First work on Baire space, and choose one parameter coding analytic
    presentations of both $E$ and its complement, so that $E$ is $\lDelta^1_1$.
-/
theorem borel_relation_in_one_parameter (E : Setoid FusionReal)
    (hE : MeasurableSet {p : FusionReal × FusionReal | E.r p.1 p.2}) :
    ∃ ε : ℕ → ℕ,
      ProjectedRelation ε E.r ∧
      ProjectedRelation ε (fun x y => ¬ E.r x y) := by
  have hl : Continuous (leftBaire : FusionReal → FusionReal) := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun k : ℕ => k.unpair.1)).comp (continuous_apply n)
  have hr : Continuous (rightBaire : FusionReal → FusionReal) := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun k : ℕ => k.unpair.2)).comp (continuous_apply n)
  let A : Set FusionReal := {p | E.r (leftBaire p) (rightBaire p)}
  have hm : MeasurableSet A := hE.preimage (hl.prodMk hr).measurable
  obtain ⟨ε, T, hT, _⟩ := analytic_family_in_one_parameter
    (fun n => if n = 0 then A else Aᶜ) (by
      intro n
      split_ifs
      · exact hm.analyticSet
      · exact hm.compl.analyticSet)
  refine ⟨ε, ?_, ?_⟩
  · exact ⟨T 0, by simpa [A] using hT 0⟩
  · exact ⟨T 1, by simpa [A, Set.compl_ofPred] using hT 1⟩

/-- HKL embedding for an arbitrary Borel equivalence relation on Baire
space. The common oracle is constructed, rather than supplied as data. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    The deduction of the \termuse{Glimm--Effros dichotomy} in §{sec:e0-glimm-effros} now uses this proved embedding.
    The node conditions retain point witnesses, the edge conditions retain equivalence witnesses, and the restricted
    rectangles separate branches with infinitely many disagreements. These are three distinct roles; ordinary diameter
    shrinking alone supplies none of the two relation conclusions.
-/
theorem hkl_embedding_baire (E : Setoid FusionReal)
    (hE : MeasurableSet {p : FusionReal × FusionReal | E.r p.1 p.2})
    (hns : ¬ Smooth E.r) :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      ∀ a b, E0 a b ↔ E.r (π a) (π b) := by
  obtain ⟨ε, hεE, hεne⟩ := borel_relation_in_one_parameter E hE
  exact parameter_hkl_embedding ε E hεE hεne hns

end PolishSpaceBook.LambdaTree
